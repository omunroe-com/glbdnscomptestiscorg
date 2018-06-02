/*
 * Copyright (C) 2016, 2017  Internet Systems Consortium, Inc. ("ISC")
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#define FD_SETSIZE 1600

#include <config.h>

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stddef.h>
#include <unistd.h>
#include <assert.h>
#include <ctype.h>

#include <sys/types.h>
#include <netinet/in.h>
#include <arpa/nameser.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <sys/time.h>
#include <sys/ioctl.h>
#include <sys/uio.h>
#include <netinet/ip.h>
#include <netinet/ip_icmp.h>
#include <netinet/ip6.h>
#include <netinet/icmp6.h>
#include <netinet/udp.h>
#include <netinet/tcp.h>

#include <errno.h>
#include <netdb.h>
#include <resolv.h>
#include <signal.h>

#ifndef FD_COPY
#define FD_COPY(x, y) memmove(y, x, sizeof(*x))
#endif

#define ns_t_dname 39
#define ns_t_sink 40
#define ns_t_apl 42
#define ns_t_ds 43
#define ns_t_sshfp 44
#define ns_t_ipseckey 45
#define ns_t_rrsig 46
#define ns_t_nsec 47
#define ns_t_dnskey 48
#define ns_t_dhcid 49
#define ns_t_nsec3 50
#define ns_t_nsec3param 51
#define ns_t_tlsa 52
#define ns_t_smimea 53
#define ns_t_hip 55
#define ns_t_ninfo 56
#define ns_t_talink 58
#define ns_t_cds 59
#define ns_t_cdnskey 60
#define ns_t_openpgpkey 61
#define ns_t_csync 62
#define ns_t_spf 99
#define ns_t_nid 104
#define ns_t_l32 105
#define ns_t_l34 106
#define ns_t_lp 107
#define ns_t_eui48 108
#define ns_t_eui64 109
#define ns_t_uri 256
#define ns_t_caa 257
#define ns_t_avc 258
#define ns_t_doa 259
#define ns_t_ta 32768
#define ns_t_dlv 32769

#define ns_r_badcookie 23

static int eof = 0;
static int maxfd = -1;
static fd_set rfds, wfds;
static int outstanding = 0;
static int maxoutstanding = 100;

static void(*rhandlers[FD_SETSIZE])(int);
static void(*whandlers[FD_SETSIZE])(int);

static int udp4 = -1;
static int udp6 = -1;
static int icmp4 = -1;
static int icmp6 = -1;

static int ipv4only = 0;
static int ipv6only = 0;

static int allok  = 0;
static int bad  = 0;
static int badtag  = 0;
static int ednsonly  = 0;
static int debug = 0;
static int inorder = 0;
static int serial = 0;
static int printnsid = 0;
static long long sent;


#ifdef HAVE_RES_GETSERVERS
static union res_sockaddr_union servers[10];
#else
static union {
        struct sockaddr_in sin;
        struct sockaddr_in6 sin6;
} servers[10];
#endif

static int nservers = 0;
int ident = 0;

/*
 * Doubly linked list macros.
 */
#define APPEND(list, item, link) do { \
	if ((list).tail) \
		(list).tail->link.next = (item); \
	else \
		(list).head = (item); \
	(item)->link.prev = list.tail; \
	(item)->link.next = NULL; \
	(list).tail = (item); \
	(item)->link.linked = 1; \
} while (0)

#define PREPEND(list, item, link) do { \
	if ((list).head) \
		(list).head->link.prev = (item); \
	else \
		(list).tail = (item); \
	(item)->link.prev = NULL; \
	(item)->link.next = list.head; \
	(list).head = (item); \
	(item)->link.linked = 1; \
} while (0)

#define INSERTBEFORE(list, before, item, link) do { \
	assert(LINKED(before, link)); \
	if ((before)->link.prev == NULL) \
		PREPEND(list, item, link); \
	else { \
		(item)->link.prev = (before)->link.prev; \
		(before)->link.prev = (item); \
		(item)->link.prev->link.next = (item); \
		(item)->link.next = (before); \
		(item)->link.linked = 1; \
	} \
} while (0)

#define UNLINK(list, item, link) do { \
	if ((item)->link.next) \
		(item)->link.next->link.prev = (item)->link.prev; \
	else \
		list.tail = (item)->link.prev; \
	if ((item)->link.prev) \
		(item)->link.prev->link.next = (item)->link.next; \
	else \
		list.head = (item)->link.next; \
	(item)->link.next = (item)->link.prev = NULL; \
	(item)->link.linked = 0; \
} while (0)

#define NEXT(item, link) (item)->link.next
#define PREV(item, link) (item)->link.prev
#define LINKED(item, link) (item)->link.linked

#define HEAD(list) (list).head
#define TAIL(list) (list).tail

/*
 * Test groupings
 */
#define EDNS 0x01
#define COMM 0x02
#define FULL 0x04
#define TYPE 0x08
#define EXPL 0x10

static int what = EDNS;

static struct {
	const char *name;		/* test nmemonic */
	unsigned int what;		/* select what test to make / report */
	unsigned short rdlen;		/* edns rdata length */
	const char *rdata;		/* edns rdata */
	unsigned short udpsize;		/* edns UDP size (0 == no EDNS) */
	unsigned short flags;		/* edns flags to be set */
	unsigned short version;		/* edns version */
	unsigned int tcp;		/* use tcp */
	unsigned int cookie;		/* opt record has cookie */
	unsigned int ignore;		/* ignore tc in response */
	unsigned int tc;		/* set tc in request */
	unsigned int rd;		/* set rd in request */
	unsigned int ra;		/* set ra in request */
	unsigned int cd;		/* set cd in request */
	unsigned int ad;		/* set ad  in request */
	unsigned int aa;		/* set aa in request */
	unsigned int z;			/* set z in request */
	unsigned int opcode;		/* use opcode for request */
	unsigned short type;		/* query type code */
	const char *dig;		/* dig command */
} opts[] = {
	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "dns",       EDNS,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +noedns +noad +norec SOA <zone>"
	},
	{ "aa",        FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,  0, ns_t_soa,
	  "dig +noedns +noad +norec +aaflag SOA <zone>"
	},
	{ "ad",        FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,  0, ns_t_soa,
	  "dig +noedns +ad +norec SOA <zone>"
	},
	{ "cd",        FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,  0, ns_t_soa,
	  "dig +noedns +noad +norec +cd SOA <zone>"
	},
	{ "ra",        FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,  0, ns_t_soa,
	  "### dig +noedns +noad +norec +raflag SOA <zone> ###"
	},
	{ "rd",        FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +noedns +noad +rec SOA <zone>"
	},
	{ "tc",        FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "### dig +noedns +noad +norec +tcflag SOA <zone> ###"
	},
	{ "zflag",     FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,  0, ns_t_soa,
	  "dig +noedns +noad +norec +zflag SOA <zone>"
	},
	{ "opcode",    FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0,
	  "dig +noedns +noad +norec +header-only +opcode=15"
	},
	{ "opcodeflg", FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 15, 0,
	  "### dig +noedns +header-only +opcode=15 +tcflag +rec +raflag +cd +ad +aaflag +zflag ###"
	},
	{ "type666",   FULL,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, 666,
	  "dig +noedns +noad +norec TYPE666 <zone>"
	},
	{ "tcp",       FULL,  0, "",    0, 0x0000, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +noedns +noad +norec +tcp SOA <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "edns",      EDNS,  0, "", 4096, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +nocookie +noad +norec SOA <zone>"
	},
	{ "edns1",     EDNS,  0, "", 4096, 0x0000, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=1 +noednsneg +nocookie +noad +norec SOA <zone>"
	},
	{ "edns@512",  EDNS,  0, "",  512, 0x0000, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_dnskey,
	  "dig +edns=0 +nocookie +noad +norec +dnssec +ignoretc +bufsize=512 DNSKEY <zone>"
	},
	{ "ednsopt",   EDNS,  4, "\x00\x64\x00\x00",	/* 100 */
				     4096, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +nocookie +noad +norec +ednsopt=100 SOA <zone>"
	},
	{ "edns1opt",  EDNS,  4, "\x00\x64\x00\x00",	/* 100 */
				     4096, 0x0000, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=1 +noednsneg +nocookie +noad +norec +ednsopt=100 SOA <zone>"
	},
	{ "do",        EDNS,  0, "",
				     4096, 0x8000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +nocookie +noad +norec +dnssec SOA <zone>"
	},
	{ "edns1do",   FULL,  0, "", 4096, 0x8000, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=1 +noednsneg +nocookie +noad +norec +dnssec SOA <zone>"
	},
	{ "ednsflags", EDNS,  0, "", 4096, 0x0080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +nocookie +noad +norec +ednsflags=0x0080 SOA <zone>"
	},
	{ "optlist",   EDNS,  4 + 8 + 4 + 12,
	  "\x00\x03\x00\x00" 		     /* NSID */
	  "\x00\x08\x00\x04\x00\x01\x00\x00" /* ECS */
	  "\x00\x09\x00\x00" 		     /* EXPIRE */
	  "\x00\x0a\x00\x08\x01\x02\x03\x04\x05\x06\x07\x08",	/* COOKIE */
				     4096, 0x0000, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +noad +norec +nsid +subnet=0.0.0.0/0 +expire +cookie=0102030405060708 SOA <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "ednsnsid", FULL,  4, "\x00\x03\x00\x00",	/* NSID */
				     4096, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +nocookie +noad +norec +nsid SOA <zone>"
	},
	{ "ednscookie", FULL, 12, "\x00\x0a\x00\x08\x01\x02\x03\x04\x05\x06\x07\x08", /* COOKIE */
				     4096, 0x0000, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +noad +norec +cookie=0102030405060708 SOA <zone>"
	},
	{ "ednsexpire", FULL, 4, "\x00\x09\x00\x00",	/* EXPIRE */
				     4096, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +nocookie +noad +norec +expire SOA <zone>"
	},
	{ "ednssubnet", FULL,  8, "\x00\x08\x00\x04\x00\x01\x00\x00",	/* ECS */
				     4096, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +nocookie +noad +norec +subnet=0.0.0.0/0 SOA <zone>"
	},

	{ "edns1nsid", FULL,  4, "\x00\x03\x00\x00",	/* NSID */
				     4096, 0x0000, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=1 +noednsneg +nocookie +noad +norec +nsid SOA <zone>"
	},
	{ "edns1cookie", FULL, 12, "\x00\x0a\x00\x08\x01\x02\x03\x04\x05\x06\x07\x08", /* COOKIE */
				     4096, 0x0000, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=1 +noednsneg +noad +norec +cookie=0102030405060708 SOA <zone>"
	},
	{ "edns1expire", FULL, 4, "\x00\x09\x00\x00",	/* EXPIRE */
				     4096, 0x0000, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=1 +noednsneg +nocookie +noad +norec +expire SOA <zone>"
	},
	{ "edns1subnet", FULL,  8, "\x00\x08\x00\x04\x00\x01\x00\x00",	/* ECS */
				     4096, 0x0000, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=1 +noednsneg +nocookie +noad +norec +subnet=0.0.0.0/0 SOA <zone>"
	},
	{ "ednstcp",   EDNS,  0, "",  512, 0x8000, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_dnskey,
	  "dig +edns=0 +nocookie +noad +norec +dnssec +bufsize=512 +tcp DNSKEY <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "bind11",    COMM, 12, "\x00\x0a\x00\x08\x01\x02\x03\x04\x05\x06\x07\x08", /* COOKIE */
				     4096, 0x8000, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +cookie=0102030405060708 +noad +norec +dnssec SOA <zone>"
	},
	{ "dig11",     COMM, 12, "\x00\x0a\x00\x08\x01\x02\x03\x04\x05\x06\x07\x08", /* COOKIE */
				     4096, 0x0000, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0,  0, ns_t_soa,
	  "dig +edns=0 +cookie=0102030405060708 +ad +rec SOA <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "A",         TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_a,
	  "dig +noedns +noad +norec A <zone>"
	},
	{ "NS",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_ns,
	  "dig +noedns +noad +norec NS <zone>"
	},
	{ "MD",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_md,
	  "dig +noedns +noad +norec MD <zone>"
	},
	{ "MF",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_mf,
	  "dig +noedns +noad +norec MF <zone>"
	},
	{ "CNAME",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_cname,
	  "dig +noedns +noad +norec CNAME <zone>"
	},
	{ "SOA",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_soa,
	  "dig +noedns +noad +norec SOA <zone>"
	},
	{ "MB",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_mb,
	  "dig +noedns +noad +norec MB <zone>"
	},
	{ "MG",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_mg,
	  "dig +noedns +noad +norec MG <zone>"
	},
	{ "MR",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_mr,
	  "dig +noedns +noad +norec MR <zone>"
	},
	{ "NULL",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_null,
	  "dig +noedns +noad +norec NULL <zone>"
	},
	{ "WKS",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_wks,
	  "dig +noedns +noad +norec WKS <zone>"
	},
	{ "PTR",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_ptr,
	  "dig +noedns +noad +norec PTR <zone>"
	},
	{ "HINFO",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_hinfo,
	  "dig +noedns +noad +norec HINFO <zone>"
	},
	{ "MINFO",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_minfo,
	  "dig +noedns +noad +norec MINFO <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "MX",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_mx,
	  "dig +noedns +noad +norec MX <zone>"
	},
	{ "TXT",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_txt,
	  "dig +noedns +noad +norec TXT <zone>"
	},
	{ "RP",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_rp,
	  "dig +noedns +noad +norec RP <zone>"
	},
	{ "AFSDB",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_afsdb,
	  "dig +noedns +noad +norec AFSDB <zone>"
	},
	{ "X25",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_x25,
	  "dig +noedns +noad +norec X25 <zone>"
	},
	{ "ISDN",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_isdn,
	  "dig +noedns +noad +norec ISDN <zone>"
	},
	{ "RT",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_rt,
	  "dig +noedns +noad +norec RT <zone>"
	},
	{ "NSAP",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_nsap,
	  "dig +noedns +noad +norec NSAP <zone>"
	},
	{ "NSAP-PTR",  TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_nsap_ptr,
	  "dig +noedns +noad +norec NSAP-PTR <zone>"
	},
	{ "SIG",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_sig,
	  "dig +noedns +noad +norec SIG <zone>"
	},
	{ "KEY",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_key,
	  "dig +noedns +noad +norec KEY <zone>"
	},
	{ "PX",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_px,
	  "dig +noedns +noad +norec PX <zone>"
	},
	{ "GPOS",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_gpos,
	  "dig +noedns +noad +norec GPOS <zone>"
	},
	{ "AAAA",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_aaaa,
	  "dig +noedns +noad +norec AAAA <zone>"
	},
	{ "LOC",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_loc,
	  "dig +noedns +noad +norec LOC <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "NXT",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_nxt,
	  "dig +noedns +noad +norec NXT <zone>"
	},
	{ "SRV",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_srv,
	  "dig +noedns +noad +norec SRV <zone>"
	},
	{ "NAPTR",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_naptr,
	  "dig +noedns +noad +norec NAPTR <zone>"
	},
	{ "KX",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_kx,
	  "dig +noedns +noad +norec KX <zone>"
	},
	{ "CERT",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_cert,
	  "dig +noedns +noad +norec CERT <zone>"
	},
	{ "A6",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_a6,
	  "dig +noedns +noad +norec A6 <zone>"
	},
	{ "DNAME",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_dname,
	  "dig +noedns +noad +norec DNAME <zone>"
	},
	{ "APL",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_apl,
	  "dig +noedns +noad +norec APL <zone>"
	},
	{ "DS",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_ds,
	  "dig +noedns +noad +norec DS <zone>"
	},
	{ "SSHFP",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_sshfp,
	  "dig +noedns +noad +norec SSHFP <zone>"
	},
	{ "IPSECKEY",  TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_ipseckey,
	  "dig +noedns +noad +norec IPSECKEY <zone>"
	},
	{ "RRSIG",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_rrsig,
	  "dig +noedns +noad +norec RRSIG <zone>"
	},
	{ "NSEC",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_nsec,
	  "dig +noedns +noad +norec NSEC <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "DNSKEY",    TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_dnskey,
	  "dig +noedns +noad +norec DNSKEY <zone>"
	},
	{ "DHCID",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_dhcid,
	  "dig +noedns +noad +norec DHCID <zone>"
	},
	{ "NSEC3",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_nsec3,
	  "dig +noedns +noad +norec NSEC3 <zone>"
	},
	{ "NSEC3PARAM",TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_nsec3param,
	  "dig +noedns +noad +norec NSEC3PARAM <zone>"
	},
	{ "TLSA",      TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_tlsa,
	  "dig +noedns +noad +norec TLSA <zone>"
	},
	{ "SMIMEA",    TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_smimea,
	  "dig +noedns +noad +norec SMIMEA <zone>"
	},
	{ "HIP",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_hip,
	  "dig +noedns +noad +norec HIP <zone>"
	},
	{ "CDS",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_cds,
	  "dig +noedns +noad +norec CDS <zone>"
	},
	{ "CDNSKEY",   TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_cdnskey,
	  "dig +noedns +noad +norec CDNSKEY <zone>"
	},
	{ "OPENPGPKEY",TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_openpgpkey,
	  "dig +noedns +noad +norec OPENPGPKEY <zone>"
	},
	{ "SPF",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_spf,
	  "dig +noedns +noad +norec SPF <zone>"
	},
	{ "NID",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_nid,
	  "dig +noedns +noad +norec NID <zone>"
	},
	{ "L32",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_l32,
	  "dig +noedns +noad +norec L32 <zone>"
	},

	/*                           size   eflgs vr  T ck ig tc rd ra cd ad aa  z  op  type */
	{ "L64",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_l34,
	  "dig +noedns +noad +norec L64 <zone>"
	},
	{ "LP",        TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_lp,
	  "dig +noedns +noad +norec LP <zone>"
	},
	{ "EUI48",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_eui48,
	  "dig +noedns +noad +norec EUI48 <zone>"
	},
	{ "EUI64",     TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_eui64,
	  "dig +noedns +noad +norec EUI64 <zone>"
	},
	{ "URI",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_uri,
	  "dig +noedns +noad +norec URI <zone>"
	},
	{ "CAA",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_caa,
	  "dig +noedns +noad +norec CAA <zone>"
	},
	{ "AVC",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_avc,
	  "dig +noedns +noad +norec AVC <zone>"
	},
	{ "DOA",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_doa,
	  "dig +noedns +noad +norec DOA <zone>"
	},
	{ "DLV",       TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, ns_t_dlv,
	  "dig +noedns +noad +norec DLV <zone>"
	},
	{ "TYPE1000",  TYPE,  0, "",    0, 0x0000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, 1000,
	  "dig +noedns +noad +norec TYPE1000 <zone>"
	}
};

/*
 * Summary structure where results from multiple lookups are recorded.
 */
struct summary {
	struct {
		struct summary *prev;
		struct summary *next;
		int linked;
	} link;
	char zone[1024];		/* the zone's name */
	char ns[1024];			/* the server's name */
	struct sockaddr_storage storage;/* server we are talking to */
	int tests;			/* number of outstanding tests */
	int last;			/* last test sent */
	int deferred;			/* was the printing deferred */
	int done;			/* we are done */
	int type;			/* recursive query lookup type */
	int nodataa;			/* recursive query got nodata */
	int nodataaaaa;			/* recursive query got nodata */
	int nxdomain;			/* recursive query got nxdomain */
	int nxdomaina;			/* recursive query got nxdomain */
	int nxdomainaaaa;		/* recursive query got nxdomain */
	int faileda;
	int failedaaaa;
	int cnamea;			/* Nameserver is CNAME */
	int cnameaaaa;			/* Nameserver is CNAME */
	int seenrrsig;			/* a rrsig was seen in "do" test */
	int seenopt;			/* see a EDNS response */
	int seenedns;			/* see a EDNS response */
	int seenfailure;		/* see a lookup failure */
	int allok;			/* all answers are current ok */
	int allrefused;			/* all answers are current ok */
	int allservfail;		/* all answers are current ok */
	struct summary *xlink;		/* cross link of recursive A/AAAA */
	int nsidlen;
	char nsid[100];			/* nsid if found */
	char results[sizeof(opts)/sizeof(opts[0])][100];
};

static struct {
	struct summary *head;
	struct summary *tail;
} summaries;

struct workitem {
	struct {
		struct workitem *next;
		struct workitem *prev;
		int linked;
	} link, clink, plink, rlink, idlink, seqlink;
	unsigned short id;		/* the query id we are waiting for */
	struct timeval when;		/* when we will timeout */
	int type;			/* the query type being looked up */
	int test;			/* test number / server number */
	int sends;			/* number of times this UDP request
					 * has been sent */
	int buflen;			/* the size of the request to be sent */
	int tcpfd;			/* the tcp file descriptor */
	int outstanding;		/* outstanding has been set */
	int havelen;			/* readlen is tcp message length */
	int readlen;			/* how much we need to read */
	int read;			/* how much has been read so far */
	unsigned char buf[512];		/* the question we sent */
	unsigned char tcpbuf[0x10000];	/* where to accumulate the tcp response */
	struct summary *summary;	/* where this test is summaried */
};

/*
 * Work queues:
 *	'work' udp qeries;
 *	'connecting' tcp qeries;
 *	'reading' tcp qeries;
 *	'pending' deferred work items;
 *
 * Outstanding queries by qid.
 *	'ids'
 *
 * Outstanding icmp by seq.
 *	'ids'
 */
static struct {
	struct workitem *head;
	struct workitem *tail;
} work, connecting, reading, pending, ids[0x10000], seq[0x10000];

static void
dotest(struct workitem *item);

static void
nextserver(struct workitem *item);

static void
connecttoserver(struct workitem *item);

static void
report(struct summary *summary);

static int
storage_equal(struct sockaddr_storage *s1, struct sockaddr_storage *s2) {
	struct sockaddr_in *sin1, *sin2;
	struct sockaddr_in6 *sin61, *sin62;

	if (s1->ss_family != s2->ss_family)
		return (0);

	switch (s1->ss_family) {
	case AF_INET:
		sin1 = (struct sockaddr_in *)s1;
		sin2 = (struct sockaddr_in *)s2;

		if (sin1->sin_port != sin2->sin_port ||
		    sin1->sin_addr.s_addr != sin2->sin_addr.s_addr)
			return (0);
		return (1);
	case AF_INET6:
		sin61 = (struct sockaddr_in6 *)s1;
		sin62 = (struct sockaddr_in6 *)s2;

		if (sin61->sin6_port != sin62->sin6_port ||
		    memcmp(&sin61->sin6_addr, &sin62->sin6_addr, 16) != 0)
			return (0);
		return (1);
	}
	return (0);
}

/*
 * Check if it is safe to use this id to this address.
 */
static int
checkid(struct sockaddr_storage *storage, int id) {
	struct workitem *item;

	item = HEAD(ids[id]);
	while (item != NULL &&
	       !storage_equal(storage, &item->summary->storage))
		item = NEXT(item, idlink);
	return ((item == NULL) ? 1 : 0);
}

/*
 * Check if we have a outstanding icmp with this sequence number
 * to this address.
 */
static int
checkseq(struct sockaddr_storage *storage, int id) {
	struct workitem *item;

	item = HEAD(seq[id]);
	while (item != NULL &&
	       !storage_equal(storage, &item->summary->storage))
		item = NEXT(item, seqlink);
	return ((item == NULL) ? 1 : 0);
}

static void
freesummary(struct summary *summary) {
	if (LINKED(summary, link))
		UNLINK(summaries, summary, link);
	free(summary);
}

/*
 * Generate a report line.
 */
static void
printandfree(struct summary *summary) {
	struct sockaddr_in *s = (struct sockaddr_in *)&summary->storage;
	struct sockaddr_in6 *s6 = (struct sockaddr_in6 *)&summary->storage;;
	char addrbuf[64];
	void *addr;
	unsigned int i;
	int x;

	if ((summary->type == ns_t_a || summary->type == ns_t_aaaa) &&
	    summary->nodataa && summary->nodataaaaa) {
		printf("%s. %s: no address records found\n",
		       summary->zone, summary->ns);
		freesummary(summary);
		return;
	}

	if ((summary->type == ns_t_a || summary->type == ns_t_aaaa) &&
	    summary->nxdomaina && summary->nxdomainaaaa) {
		printf("%s. %s: no address records found (NXDOMAIN)\n",
		       summary->zone, summary->ns);
		freesummary(summary);
		return;
	}

	if ((summary->type == ns_t_a || summary->type == ns_t_aaaa) &&
	    summary->faileda && summary->failedaaaa) {
		printf("%s. %s: address lookups failed\n",
		       summary->zone, summary->ns);
		freesummary(summary);
		return;
	}

	if ((summary->type == ns_t_a || summary->type == ns_t_aaaa) &&
	    (summary->cnamea || summary->cnameaaaa)) {
		printf("%s. %s: nameserver is a CNAME\n",
		       summary->zone, summary->ns);
		freesummary(summary);
		return;
	}

	/*
	 * Do deferred xlink failure reports.
	 */
	if (summary->type == ns_t_a &&
	    summary->nodataa && summary->failedaaaa) {
		printf("%s. %s:", summary->zone, summary->ns);
		printf(" AAAAA lookup failed\n");
		freesummary(summary);
		return;
	}
	if (summary->type == ns_t_aaaa &&
	    summary->nodataaaaa && summary->faileda) {
		printf("%s. %s:", summary->zone, summary->ns);
		printf(" A lookup failed\n");
		freesummary(summary);
		return;
	}
	if (summary->type == ns_t_a &&
	    summary->faileda && summary->nxdomainaaaa) {
		printf("%s. %s:", summary->zone, summary->ns);
		printf(" AAAAA nxdomain\n");
		freesummary(summary);
		return;
	}
	if (summary->type == ns_t_aaaa &&
	    summary->failedaaaa && summary->nxdomaina) {
		printf("%s. %s:", summary->zone, summary->ns);
		printf(" A nxdomain\n");
		freesummary(summary);
		return;
	}

	if (summary->done || summary->nodataa || summary->nodataaaaa) {
		freesummary(summary);
		return;
	}

	if (summary->type != 0 && summary->nxdomain) {
		if (summary->type == ns_t_ns) {
			printf("%s.: NS nxdomain\n", summary->zone);
			freesummary(summary);
			return;
		}
		printf("%s. %s:", summary->zone, summary->ns);
		if (summary->type == ns_t_a) printf(" A");
		if (summary->type == ns_t_aaaa) printf(" AAAA");
		printf(" nxdomain\n");
		freesummary(summary);
		return;
	}
	if (summary->type == ns_t_a) {
		printf("%s. %s:", summary->zone, summary->ns);
		printf(" A lookup failed\n");
		freesummary(summary);
		return;
	}
	if (summary->type == ns_t_aaaa) {
		printf("%s. %s:", summary->zone, summary->ns);
		printf(" AAAA lookup failed\n");
		freesummary(summary);
		return;
	}
	if (summary->type == ns_t_ns) {
		printf("%s.:", summary->zone);
		printf(" NS lookup failed\n");
		freesummary(summary);
		return;
	}

	if (summary->seenopt && (summary->allrefused && summary->allservfail))
		summary->seenedns = 1;

	if (summary->type != 0 || (summary->allok && bad) ||
	    (!summary->seenfailure && !summary->seenedns && ednsonly)) {
		freesummary(summary);
		return;
	}

	switch (summary->storage.ss_family) {
	case AF_INET: addr = &s->sin_addr; break;
	case AF_INET6: addr = &s6->sin6_addr; break;
	default: addr = NULL; break;
	}

	if (addr == NULL)
		strncpy(addrbuf, "<unknown>", sizeof(addrbuf));
	else
		inet_ntop(summary->storage.ss_family, addr,
			  addrbuf, sizeof(addrbuf));

	x = -1;
	printf("%s. @%s (%s.):", summary->zone, addrbuf, summary->ns);
	if (allok && summary->allok)
		printf(" all ok");
	else
		for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
			if (opts[i].what != 0 && (opts[i].what & what) == 0)
				continue;
			if (summary->results[i][0] == 0)
				strncpy(summary->results[i], "skipped", 100);
			if (strcmp(opts[i].name, "do") == 0)
				x = i;
			if (strcmp(opts[i].name, "ednstcp") == 0 && x != -1 &&
			    (!badtag || (strcmp(summary->results[x], "ok") != 0 &&
					 strncmp(summary->results[x], "ok,", 3) != 0)))
			{
				printf(" signed=%s", summary->results[x]);
				if (summary->seenrrsig)
					printf(",yes");
			}
			if (badtag) {
				if (strcmp(summary->results[i], "ok") == 0 ||
				    strncmp(summary->results[i], "ok,", 3) == 0)
					continue;
			}
			printf(" %s=%s", opts[i].name, summary->results[i]);
		}
fprintf(stderr, "printnsid=%d summary->nsidlen=%u\n", printnsid, summary->nsidlen);
	if (printnsid && summary->nsidlen != 0) {
		printf(" (");
		for (i = 0; i < summary->nsidlen; i++) {
			if (isprint(summary->nsid[i] & 0xff))
				putchar(summary->nsid[i]);
			else
				putchar('.');
		}
		printf(")");
	}
	printf("\n");
	freesummary(summary);
}

static void
report(struct summary *summary) {

	/*
	 * Send the next test now that we have completed the last test.
	 */
	if (serial && summary->type == 0 && summary->tests == 1) {
		for (summary->last++;
		     summary->last < sizeof(opts)/sizeof(opts[0]);
		     summary->last++) {
			struct workitem *item;
			if (opts[summary->last].what != 0 &&
			    (opts[summary->last].what & what) == 0)
				continue;
			item = calloc(1, sizeof(*item));
			if (item == NULL)
				continue;
			item->summary = summary;
			item->test = item->summary->last;
			item->tcpfd = -1;
			dotest(item);
			return;
		}
	}

	/*
	 * Have all the tests completed?
	 */
	summary->tests--;
	if (summary->tests)
		return;

	/*
	 * If we are cross linked record the lookup details on the other
	 * structure.
	 */
	if (summary->xlink) {
		if (summary->cnamea) {
			summary->xlink->cnamea = 1;
			summary->done = 1;
		}
		if (summary->cnameaaaa) {
			summary->xlink->cnameaaaa = 1;
			summary->done = 1;
		}
		if (summary->nodataa) {
			summary->xlink->nodataa = 1;
			summary->done = 1;
		}
		if (summary->nodataaaaa) {
			summary->xlink->nodataaaaa = 1;
			summary->done = 1;
		}
		if (summary->nxdomaina) {
			summary->xlink->nxdomaina = 1;
			summary->done = 1;
		}
		if (summary->nxdomainaaaa) {
			summary->xlink->nxdomainaaaa = 1;
			summary->done = 1;
		}
		if (!summary->done) {
			if (summary->type == ns_t_a) {
				summary->xlink->faileda = 1;
				summary->done = 1;
			}
			if (summary->type == ns_t_aaaa) {
				summary->xlink->failedaaaa = 1;
				summary->done = 1;
			}
		}

		/*
		 * Remove the cross link.
		 */
		summary->xlink->xlink = NULL;
		summary->xlink = NULL;
		if (summary->done) {
			freesummary(summary);
			goto print_deferred;
		}
	}
	if (!summary->done) {
		if (summary->type == ns_t_a)
			summary->faileda = 1;
		if (summary->type == ns_t_aaaa)
			summary->failedaaaa = 1;
	}

	if (inorder && PREV(summary, link)) {
		summary->deferred = 1;
		return;
	}
	printandfree(summary);

 print_deferred:
	while ((summary = HEAD(summaries)) && summary->deferred)
		printandfree(summary);
}

/*
 * Free a work item and unlink.
 */
static void
freeitem(struct workitem * item) {
	if (item->summary)
		report(item->summary);
	if (item->tcpfd != -1) {
		FD_CLR(item->tcpfd, &rfds);
		FD_CLR(item->tcpfd, &wfds);
		rhandlers[item->tcpfd] = NULL;
		whandlers[item->tcpfd] = NULL;
		close(item->tcpfd);
	}
	if (item->outstanding)
		outstanding--;
	if (LINKED(item, link))
		UNLINK(work, item, link);
	if (LINKED(item, plink))
		UNLINK(pending, item, plink);
	if (LINKED(item, rlink))
		UNLINK(reading, item, rlink);
	if (LINKED(item, clink))
		UNLINK(connecting, item, clink);
	if (LINKED(item, idlink))
		UNLINK(ids[item->id], item, idlink);
	if (LINKED(item, seqlink))
		UNLINK(seq[item->id], item, seqlink);
	free(item);
}

/*
 * Add a tag to the report.
 */
static void
addtag(struct workitem *item, const char *tag) {
	char *result = item->summary->results[item->test];
	if (result[0]) strncat(result, ",", 100);
	strncat(result, tag, 100);
}

/*
 * Resend a UDP request.
 */
static void
resend(struct workitem *item) {
	int n, fd = -1;
	socklen_t ss_len;

	switch (item->summary->storage.ss_family) {
	case AF_INET:
		fd = udp4;
		ss_len = sizeof(struct sockaddr_in);
		break;
	case AF_INET6:
		fd = udp6;
		ss_len = sizeof(struct sockaddr_in6);
		break;
	}

	if (fd == -1) {
		addtag(item, "skipped");
		item->summary->allok = 0;
		freeitem(item);
		return;
	}

	if (!item->outstanding && outstanding > maxoutstanding) {
		gettimeofday(&item->when, NULL);
		item->when.tv_sec += 1;
		if (LINKED(item, link))
			UNLINK(work, item, link);
		APPEND(pending, item, plink);
		return;
	}

	n = sendto(fd, item->buf, item->buflen, 0,
		   (struct sockaddr *)&item->summary->storage, ss_len);
	if (n > 0) {
		if (debug)
			printf("resend %s rdlen=%u udpsize=%u flags=%04x "
			       "version=%u tcp=%u ignore=%u id=%u\n",
			       opts[item->test].name, opts[item->test].rdlen,
			       opts[item->test].udpsize, opts[item->test].flags,
			       opts[item->test].version, opts[item->test].tcp,
			       opts[item->test].ignore, item->id);
		sent++;
		if (!item->outstanding++)
			outstanding++;
		gettimeofday(&item->when, NULL);
		item->when.tv_sec += 1;
		item->sends++;
		if (LINKED(item, link))
			UNLINK(work, item, link);
		APPEND(work, item, link);
	} else if (item->summary->type) {
		nextserver(item);
	} else {
		addtag(item, "failed");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
	}
}

/*
 * Start a individual test.
 */
static void
dotest(struct workitem *item) {
	unsigned char *cp;
	unsigned int ttl;
	int n, fd, id, tries = 0, opcode;
	socklen_t ss_len;
	

	switch (item->summary->storage.ss_family) {
	case AF_INET:
		fd = udp4;
		ss_len = sizeof(struct sockaddr_in);
		break;
	case AF_INET6:
		fd = udp6;
		ss_len = sizeof(struct sockaddr_in6);
		break;
	}

	if (fd == -1) {
		addtag(item, "skipped");
		item->summary->allok = 0;
		freeitem(item);
		return;
	}

	/*
	 * res_mkquery only really knows about QUERY but it is useful
	 * for initalising the header when the opcode isn't QUERY.
	 */
	opcode = opts[item->test].opcode;
	switch (opcode) {
	case 0: break;
	default:
		opcode = ns_o_query;
	}

	n = res_mkquery(opcode, item->summary->zone, ns_c_in,
			opts[item->test].type, NULL, 0, NULL,
			item->buf, sizeof(item->buf));
	/* fixup opcode? */
	if (n > 0 && opts[item->test].opcode != opcode) {
		item->buf[2] &= 0x17;
		item->buf[2] |= (opts[item->test].opcode & 0x0f) << 3;
		/* Zero question section. */
		if (opts[item->test].opcode == 15)
			item->buf[4] = item->buf[5] = 0;
		n = 12;
	}

	/*
	 * Set DNS flags as specified by test.
	 */
	if (opts[item->test].tc)
		item->buf[2] |= 0x2;	/* set tc */
	if (opts[item->test].rd)
		item->buf[2] |= 0x1;	/* set rd */
	else
		item->buf[2] &= ~0x1;	/* clear rd */
	if (opts[item->test].ra)
		item->buf[3] |= 0x80;	/* set ra */
	if (opts[item->test].z)
		item->buf[3] |= 0x40;	/* set z */
	if (opts[item->test].ad)
		item->buf[3] |= 0x20;	/* set ad */
	if (opts[item->test].cd)
		item->buf[3] |= 0x10;	/* set cd */

	if (n > 12) {
		char name[1024];
		/*
		 * Make zone canonical.
		 */
		dn_expand(item->buf, item->buf + n, item->buf + 12,
			  name, sizeof(name));
		strncpy(item->summary->zone, name,
			sizeof(item->summary->zone));
	}

	/*
	 * Add OPT record if required by test.
	 */
	if (n > 0 && opts[item->test].udpsize > 0 &&
	    11 + opts[item->test].rdlen < 512 - n) {
		cp = item->buf + n;
		*cp++ = 0;				/* name */
		ns_put16(ns_t_opt, cp);			/* type */
		cp += 2;
		ns_put16(opts[item->test].udpsize, cp);	/* class */
		cp += 2;
		ttl = (opts[item->test].version << 16) |
		      opts[item->test].flags;
		ns_put32(ttl, cp);			/* ttl */
		cp += 4;
		ns_put16(opts[item->test].rdlen, cp);	/* rdlen */
		cp += 2;
		memcpy(cp, opts[item->test].rdata, opts[item->test].rdlen);
		cp += opts[item->test].rdlen;
		item->buf[11] = 1;			/* adcount */
		n = cp - item->buf;			/* total length */
	}

	if (n > 0) {
		/*
		 * Adjust id if it clashes with a outstanding request.
		 */
		id = item->buf[0] << 8 | item->buf[1];

		while (!checkid(&item->summary->storage, id) &&
		       tries++ < 0xffff)
			id = (id + 1) & 0xffff;

		if (tries == 0xffff) {
			addtag(item, "skipped");
			item->summary->allok = 0;
			item->summary->seenfailure = 1;
			freeitem(item);
			return;
		}

		item->buf[0] = id >> 8;
		item->buf[1] = id & 0xff;
		item->id = id;
		item->buflen = n;

		if (opts[item->test].tcp) {
			connecttoserver(item);
			return;
		}

		/*
		 * If there is too much outstanding work queue this item.
		 */
		if (!item->outstanding && outstanding > maxoutstanding) {
			gettimeofday(&item->when, NULL);
			item->when.tv_sec += 1;
			APPEND(pending, item, plink);
			APPEND(ids[item->id], item, idlink);
			return;
		}

		n = sendto(fd, item->buf, item->buflen, 0,
			   (struct sockaddr *)&item->summary->storage, ss_len);
	}

	if (n > 0) {
		if (debug)
			printf("%s rdlen=%u udpsize=%u flags=%04x version=%u "
			       "tcp=%u ignore=%u id=%u\n",
			       opts[item->test].name, opts[item->test].rdlen,
			       opts[item->test].udpsize, opts[item->test].flags,
			       opts[item->test].version, opts[item->test].tcp,
			       opts[item->test].ignore, item->id);
		if (!item->outstanding++)
			outstanding++;
		sent++;
		gettimeofday(&item->when, NULL);
		item->when.tv_sec += 1;
		item->sends = 1;
		APPEND(work, item, link);
		APPEND(ids[item->id], item, idlink);
	} else {
		addtag(item, "failed");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
	}
}

/*
 * Start a series of tests.
 */
static void
check(char *zone, char *ns, char *address, struct summary *parent) {
	size_t i;
	int fd;
	struct in_addr addr;
	struct in6_addr addr6;
	struct sockaddr_storage storage;
	struct summary *summary;

	memset(&storage, 0, sizeof(storage));
	if (inet_pton(AF_INET6, address, &addr6) == 1) {
		struct sockaddr_in6 *s = (struct sockaddr_in6 *)&storage;
#ifdef HAVE_SIN6_LEN
		s->sin6_len = sizeof(struct sockaddr_in6);
#endif
		s->sin6_family = AF_INET6;
		s->sin6_port = htons(53);
		s->sin6_addr = addr6;
		fd = udp6;
	} else if (inet_pton(AF_INET, address, &addr) == 1) {
		struct sockaddr_in *s = (struct sockaddr_in *)&storage;
#ifdef HAVE_SIN_LEN
		s->sin_len = sizeof(struct sockaddr_in);
#endif
		s->sin_family = AF_INET;
		s->sin_port = htons(53);
		s->sin_addr = addr;
		fd = udp4;
	} else
		return;

	if (fd == -1)
		return;

	summary = calloc(1, sizeof(*summary));
	if (summary == NULL)
		return;

	/*
	 * Hold a reference until all the tests have been initiated.
	 */
	summary->tests++;
	if (parent)
		INSERTBEFORE(summaries, parent, summary, link);
	else
		APPEND(summaries, summary, link);

	summary->storage = storage;
	summary->allok = 1;
	summary->allrefused = 1;
	summary->allservfail = 1;

	ns_makecanon(zone, summary->zone, sizeof(summary->zone));
	i = strlen(summary->zone);
	if (i) summary->zone[i-1] = 0;

	ns_makecanon(ns, summary->ns, sizeof(summary->ns));
	i = strlen(summary->ns);
	if (i) summary->ns[i-1] = 0;

	for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
		struct workitem *item;
		if (opts[i].what != 0 && (opts[i].what & what) == 0)
			continue;

		item = calloc(1, sizeof(*item));
		if (item == NULL)
			break;
		item->summary = summary;
		item->summary->tests++;
		item->summary->last = item->test = i;
		item->tcpfd = -1;
		dotest(item);
		if (serial)
			break;
	}
	report(summary);	/* Release reference. */
}

static char *
opcodetext(int code) {
	static char buf[64];

	switch(code) {
	case ns_o_query: return("query");
	case ns_o_iquery: return("iquery");
	case ns_o_status: return("status");
	case ns_o_notify: return("notify");
	case ns_o_update: return("update");
	default:
		snprintf(buf, sizeof(buf), "opcode%u", code);
		return (buf);
	}
}

static char *
rcodetext(int code) {
	static char buf[64];

	switch(code) {
	case ns_r_noerror: return("noerror");
	case ns_r_formerr: return("formerr");
	case ns_r_servfail: return("servfail");
	case ns_r_nxdomain: return("nxdomain");
	case ns_r_notimpl: return("notimp");
	case ns_r_refused: return("refused");
	case ns_r_yxdomain: return("yxdomain");
	case ns_r_yxrrset: return("yxrrset");
	case ns_r_nxrrset: return("nxrrset");
	case ns_r_notauth: return("notauth");
	case ns_r_notzone: return("notzone");
	case ns_r_badvers: return("badvers");
	case ns_r_badcookie: return("badcookie");
	default:
		snprintf(buf, sizeof(buf), "rcode%u", code);
		return (buf);
	}
}

/*
 * Start a lookup using the recursive server(s).
 */
static void
dolookup(struct workitem *item, int type) {
	char name[1024];
	int n, fd = -1;
	socklen_t ss_len;

	item->summary->tests++;
	item->summary->type = item->type = type;

 again:
	if (servers[item->test].sin.sin_family == AF_INET)
		memcpy(&item->summary->storage, &servers[item->test].sin,
		       sizeof(servers[item->test].sin));
	else
		memcpy(&item->summary->storage, &servers[0].sin6,
		       sizeof(servers[item->test].sin6));

	switch (item->summary->storage.ss_family) {
	case AF_INET:
		fd = udp4;
		ss_len = sizeof(struct sockaddr_in);
		break;
	case AF_INET6:
		fd = udp6;
		ss_len = sizeof(struct sockaddr_in6);
		break;
	}

	if (fd == -1) {
		if (++item->test < nservers)
			goto again;
		addtag(item, "skipped");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}

	if (type == ns_t_ns)
		n = res_mkquery(ns_o_query, item->summary->zone, ns_c_in,
				type, NULL, 0, NULL,
				item->buf, sizeof(item->buf));
	else
		n = res_mkquery(ns_o_query, item->summary->ns, ns_c_in,
				type, NULL, 0, NULL,
				item->buf, sizeof(item->buf));
	if (n > 0) {
		int id, tries = 0;

		/*
		 * Make name canonical.
		 */
		dn_expand(item->buf, item->buf + n, item->buf + 12,
			  name, sizeof(name));

		switch (type) {
		case ns_t_ns:
			strncpy(item->summary->zone, name,
				sizeof(item->summary->zone));
			break;
		case ns_t_a:
		case ns_t_aaaa:
			strncpy(item->summary->ns, name,
				sizeof(item->summary->zone));
			break;
		}

		item->buf[2] |= 0x1;	/* set rd */
		id = item->buf[0] << 8 | item->buf[1];

		while (!checkid(&item->summary->storage, id) &&
		       tries++ < 0xffff)
			id = (id + 1) & 0xffff;

		if (tries == 0xffff) {
			nextserver(item);
			return;
		}

		item->buf[0] = id >> 8;
		item->buf[1] = id & 0xff;
		item->id = id;
		item->buflen = n;
		if (!item->outstanding && outstanding > maxoutstanding) {
			gettimeofday(&item->when, NULL);
			item->when.tv_sec += 1;
			APPEND(pending, item, plink);
			APPEND(ids[item->id], item, idlink);
			return;
		}

		n = sendto(fd, item->buf, item->buflen, 0,
			   (struct sockaddr *)&item->summary->storage, ss_len);
	}
	if (n > 0) {
		if (debug)
			printf("lookup %u id=%u\n", item->type, item->id);
		if (!item->outstanding++)
			outstanding++;
		sent++;
		gettimeofday(&item->when, NULL);
		item->when.tv_sec += 1;
		item->sends++;
		APPEND(work, item, link);
		APPEND(ids[item->id], item, idlink);
	} else 
		nextserver(item);
}

/*
 * Start a A lookup.
 */
static struct summary *
lookupa(char *zone, char *ns, struct summary *parent) {
	struct summary *summary;
	struct workitem *item;
	unsigned int i;

	if (ipv6only)
		return (NULL);

	summary = calloc(1, sizeof(*summary));
	if (summary == NULL)
		return (NULL);

	ns_makecanon(zone, summary->zone, sizeof(summary->zone));
	i = strlen(summary->zone);
	if (i) summary->zone[i-1] = 0;

	ns_makecanon(ns, summary->ns, sizeof(summary->ns));
	i = strlen(summary->ns);
	if (i) summary->ns[i-1] = 0;

	item = calloc(1, sizeof(*item));
	if (item == NULL) {
		free(summary);
		return (NULL);
	}
	if (parent)
		INSERTBEFORE(summaries, parent, summary, link);
	else
		APPEND(summaries, summary, link);

	item->summary = summary;
	item->tcpfd = -1;
	/*
	 * Hold a reference so that caller can xlink.
	 */
	summary->tests++;
	dolookup(item, ns_t_a);
	return (summary);
}

/*
 * Start a AAAA lookup.
 */
static struct summary *
lookupaaaa(char *zone, char *ns, struct summary *parent) {
	struct summary *summary;
	struct workitem *item;
	unsigned int i;

	if (ipv4only)
		return (NULL);

	summary = calloc(1, sizeof(*summary));
	if (summary == NULL)
		return (NULL);

	ns_makecanon(zone, summary->zone, sizeof(summary->zone));
	i = strlen(summary->zone);
	if (i) summary->zone[i-1] = 0;

	ns_makecanon(ns, summary->ns, sizeof(summary->ns));
	i = strlen(summary->ns);
	if (i) summary->ns[i-1] = 0;

	item = calloc(1, sizeof(*item));
	if (item == NULL) {
		free(summary);
		return (NULL);
	}
	if (parent)
		INSERTBEFORE(summaries, parent, summary, link);
	else
		APPEND(summaries, summary, link);

	item->summary = summary;
	item->tcpfd = -1;
	/*
	 * Hold a reference so that caller can xlink.
	 */
	summary->tests++;
	dolookup(item, ns_t_aaaa);
	return (summary);
}

/*
 * Start a NS lookup.
 */
static void
lookupns(char *zone) {
	struct summary *summary;
	struct workitem *item;
	unsigned int i;

	summary = calloc(1, sizeof(*summary));
	if (summary == NULL)
		return;

	ns_makecanon(zone, summary->zone, sizeof(summary->zone));
	i = strlen(summary->zone);
	if (i) summary->zone[i-1] = 0;

	item = calloc(1, sizeof(*item));
	if (item == NULL) {
		free(summary);
		return;
	}

	APPEND(summaries, summary, link);
	item->summary = summary;
	item->tcpfd = -1;
	dolookup(item, ns_t_ns);
}

static void
copy_nsid(struct summary *summary, unsigned char *options, size_t optlen) {
	size_t i;

	for (i= 0; i < optlen && i < sizeof(summary->nsid); i++) {
		summary->nsid[i] = options[i];
	}
	summary->nsidlen = i;
}

/*
 * Process a recieved response.
 */
static void
process(struct workitem *item, unsigned char *buf, int buflen) {
	char name[1024], ns[1024];
	unsigned int i, id, qr, aa, tc, rd, ra, z, ad, cd;
	unsigned int qrcount, ancount, aucount, adcount;
	unsigned int opcode, rcode;
	unsigned int type, ednssize = 0, class, ednsttl = 0, ttl, rdlen;
	unsigned char *cp, *eom;
	int seenopt = 0, seensoa = 0, seenrrsig = 0;
	int seennsid = 0, seenecs = 0, seenexpire = 0, seencookie = 0;
	int seenecho = 0;
	int n;
	char addrbuf[64];
	int ednsvers = 0;
	int ok = 1;

	/* process message header */

	id = buf[0] << 8| buf[1];

	qr = (buf[2] >> 7) & 0x1;
	opcode = (buf[2] >> 3) & 0xf;
	aa = (buf[2] >> 2) & 0x1;
	tc = (buf[2] >> 1) & 0x1;
	rd = buf[2] & 0x1;

	ra = (buf[3] >> 7) & 0x1;
	z = (buf[3] >> 6) & 0x1;
	ad = (buf[3] >> 5) & 0x1;
	cd = (buf[3] >> 4) & 0x1;
	rcode = buf[3] & 0xf;

	qrcount = buf[4] << 8 | buf[5];
	ancount = buf[6] << 8 | buf[7];
	aucount = buf[8] << 8 | buf[9];
	adcount = buf[10] << 8 | buf[11];


	/* process message body */
	cp = buf + 12;
	eom = buf + buflen;
	if (opts[item->test].opcode != 0 && qrcount != 0) {
		addtag(item, "non-empty-question-section"), ok = 0;
	} else {
		for (i = 0; i < qrcount; i++) {
			n = dn_expand(buf, eom, cp, name, sizeof(name));
			if (n < 0 || (eom - cp) < n)
				goto err;
			cp += n;
			if ((eom - cp) < 4)
				goto err;
			type = ns_get16(cp);
			cp += 2;
			class = ns_get16(cp);
			cp += 2;
			if (debug)
				printf("QR: %s./%u/%u\n", name, type, class);

			/*
			 * Does the QNAME / QTYPE match?
			 */
			if (item->type == 0 &&
			    (strcasecmp(item->summary->zone, name) != 0 ||
			     type != opts[item->test].type)) {
				if (item->tcpfd != -1) {
					addtag(item, "mismatch");
					freeitem(item);
				}
				return;
			}

			if (item->type == ns_t_ns &&
			    (strcasecmp(item->summary->zone, name) != 0 ||
			     type != ns_t_ns)) {
				if (item->tcpfd != -1) {
					addtag(item, "mismatch");
					freeitem(item);
				}
				return;
			}

			if ((item->type == ns_t_a ||
			     item->type == ns_t_aaaa) &&
			    (strcasecmp(item->summary->ns, name) != 0 ||
			     type != item->type)) {
				if (item->tcpfd != -1) {
					addtag(item, "mismatch");
					freeitem(item);
				}
				return;
			}

			/*
			 * If the answer is trunctated continue processing
			 * this section then fallback to TCP.
			 */
			if (tc && item->tcpfd == -1)
				continue;

			/*
			 * No address / NS records?
			 */
			if (item->type == ns_t_a && type == ns_t_a &&
			    strcasecmp(item->summary->ns, name) == 0 &&
			    rcode == ns_r_noerror && ancount == 0) {
				item->summary->nodataa = 1;
			}
			if (item->type == ns_t_aaaa && type == ns_t_aaaa &&
			    strcasecmp(item->summary->ns, name) == 0 &&
			    rcode == ns_r_noerror && ancount == 0) {
				item->summary->nodataaaaa = 1;
			}
			if (item->type == ns_t_ns && type == ns_t_ns &&
			    strcasecmp(item->summary->zone, name) == 0 &&
			    rcode == ns_r_noerror && ancount == 0)
				item->summary->done = 1;

			/*
			 * NXDOMAIN?
			 */
			if (item->type == ns_t_a && type == ns_t_a &&
			    strcasecmp(item->summary->ns, name) == 0 &&
			    rcode == ns_r_nxdomain && ancount == 0)
				item->summary->nxdomaina = 1;
			if (item->type == ns_t_aaaa && type == ns_t_aaaa &&
			    strcasecmp(item->summary->ns, name) == 0 &&
			    rcode == ns_r_nxdomain && ancount == 0)
				item->summary->nxdomainaaaa = 1;
			if (item->type == ns_t_ns && type == ns_t_ns &&
			    strcasecmp(item->summary->zone, name) == 0 &&
			    rcode == ns_r_nxdomain && ancount == 0)
				item->summary->nxdomain = 1;
		}
	}

	if (tc && item->tcpfd == -1 &&
	    (item->summary->type || !opts[item->test].ignore)) {
		if (LINKED(item, link))
			UNLINK(work, item, link);
		connecttoserver(item);
		return;
	}

	if (opts[item->test].opcode != 0 && ancount != 0) {
		addtag(item, "non-empty-answer-section"), ok = 0;
	} else {
		for (i = 0; i < ancount; i++) {
			n = dn_expand(buf, eom, cp, name, sizeof(name));
			if (n < 0 || (eom - cp) < n)
				goto err;
			cp += n;
			if ((eom - cp) < 8)
				goto err;
			type = ns_get16(cp);
			cp += 2;
			class = ns_get16(cp);
			cp += 2;
			ttl = ns_get32(cp);
			cp += 4;
			rdlen = ns_get16(cp);
			cp += 2;
			if ((eom - cp) < rdlen)
				goto err;
			/* Don't follow CNAME for A and AAAA lookups. */
			if ((item->type == ns_t_a ||
			     item->type == ns_t_aaaa) &&
			    type == ns_t_cname &&
			    strcasecmp(item->summary->ns, name) == 0) {
				if (item->type == ns_t_a)
					item->summary->cnamea = 1;
				else
					item->summary->cnameaaaa = 1;
			}
			/* Don't follow CNAME for NS lookups. */
			if (item->type == ns_t_ns && type == ns_t_cname &&
			    strcasecmp(item->summary->zone, name) == 0) {
				item->summary->done = 1;
			}
			if (item->type == ns_t_a && type == ns_t_a &&
			    strcasecmp(item->summary->ns, name) == 0)
			{
				if (rdlen != 4)
					goto err;
				inet_ntop(AF_INET, cp,
					  addrbuf, sizeof(addrbuf));
				check(item->summary->zone, item->summary->ns,
				      addrbuf, item->summary);
				item->summary->done = 1;
			}
			if (item->type == ns_t_aaaa && type == ns_t_aaaa &&
			    strcasecmp(item->summary->ns, name) == 0)
			{
				if (rdlen != 16)
					goto err;
				inet_ntop(AF_INET6, cp,
					  addrbuf, sizeof(addrbuf));
				check(item->summary->zone, item->summary->ns,
				      addrbuf, item->summary);
				item->summary->done = 1;
			}
			if (item->type == ns_t_ns && type == ns_t_ns &&
			    strcasecmp(item->summary->zone, name) == 0)
			{
				struct summary *summarya, *summaryaaaa;
				n = dn_expand(buf, eom, cp, ns, sizeof(ns));
				if (n != rdlen)
					goto err;
				item->summary->done = 1;
				/*
				 * Cross link A/AAAA lookups so that we can
				 * generate a single NXDOMAIN / no address
				 * report.
				 */
				summarya = lookupa(item->summary->zone, ns,
						   item->summary);
				summaryaaaa = lookupaaaa(item->summary->zone,
							 ns, item->summary);
				if (summarya && summaryaaaa) {
					summarya->xlink = summaryaaaa;
					summaryaaaa->xlink = summarya;
				}
				/*
				 * Release references.
				 */
				if (summarya) report(summarya);
				if (summaryaaaa) report(summaryaaaa);
			}
			cp += rdlen;
			if (type == ns_t_soa &&
			    strcasecmp(item->summary->zone, name) == 0)
				seensoa = 1;
			else if (type == ns_t_soa)
			    printf("%s %s\n", item->summary->zone, name);
			if (type == ns_t_rrsig)
				seenrrsig = 1;
			if (debug)
				printf("AN: %s./%u/%u/%u/%u\n",
				       name, type, class, ttl, rdlen);
		}
	}

	if (opts[item->test].opcode != 0 && aucount != 0) {
		addtag(item, "non-empty-authority-section"), ok = 0;
	} else {
		for (i = 0; i < aucount; i++) {
			n = dn_expand(buf, eom, cp, name, sizeof(name));
			if (n < 0 || (eom - cp) < n)
				goto err;
			cp += n;
			if ((eom - cp) < 8)
				goto err;
			type = ns_get16(cp);
			cp += 2;
			class = ns_get16(cp);
			cp += 2;
			ttl = ns_get32(cp);
			cp += 4;
			rdlen = ns_get16(cp);
			cp += 2;
			if ((eom - cp) < rdlen)
				goto err;
			cp += rdlen;
			if (debug)
				printf("AU: %s./%u/%u/%u/%u\n",
				       name, type, class, ttl, rdlen);
		}
	}

	if (opts[item->test].opcode != 0 && adcount != 0) {
		addtag(item, "non-empty-additional-section"), ok = 0;
	} else {
		for (i = 0; i < adcount; i++) {
			n = dn_expand(buf, eom, cp, name, sizeof(name));
			if (n < 0 || (eom - cp) < n)
				goto err;
			cp += n;
			if ((eom - cp) < 8)
				goto err;
			type = ns_get16(cp);
			cp += 2;
			class = ns_get16(cp);
			cp += 2;
			ttl = ns_get32(cp);
			cp += 4;
			rdlen = ns_get16(cp);
			cp += 2;
			if ((eom - cp) < rdlen)
				goto err;
			if (type == ns_t_opt && !seenopt) {
				unsigned char *options;
				ednsttl = ttl;
				ednssize = class;
				seenopt = 1;
				options = cp;
				while (((cp + rdlen) - options) >= 4) {
					unsigned int code, optlen;
					code = ns_get16(options);
					options += 2;
					optlen = ns_get16(options);
					options += 2;
					if ((cp + rdlen) - options < optlen)
						goto err;
					if (code == 3 && optlen > 0) {
						seennsid = 1;
						copy_nsid(item->summary,
							  options, optlen);
					}
					if (code == 8)
						seenecs = 1;
					if (code == 9 && optlen == 4)
						seenexpire = 1;
					/* Server Cookie. */
					if (code == 10 &&
					    optlen >= 16 && optlen <= 40)
						seencookie = 1;
					if (code == 100)
						seenecho = 1;
					options += optlen;
				}
				if (options != (cp + rdlen))
					goto err;
			} else if (type == ns_t_opt)
				goto err;
			cp += rdlen;
			if (debug)
				printf("AD: %s./%u/%u/%u/%u\n",
				       name, type, class, ttl, rdlen);
		}
	}
	if (cp != eom)
		goto err;

	rcode += (ednsttl & 0xff000000) >> 20;

	if (debug) {
		const char *testname;
		if (item->summary->type == 0)
			testname = opts[item->test].name;
		else
			testname = "";
		printf("id=%-5u %-9s opcode=%u rcode=%u aa=%u tc=%u rd=%u "
		       "ra=%u z=%u ad=%u cd=%u qrcount=%u ancount=%u "
		       "aucount=%u adcount=%u\n"
		       "\tseensoa=%u seenrrsig=%u seenopt=%u "
		       "seennsid=%u seenecs=%u seenexpire=%u seencookie=%u\n",
		       id, testname, opcode, rcode,
		       aa, tc, rd, ra, z, ad, cd,
		       qrcount, ancount, aucount, adcount,
		       seensoa, seenrrsig, seenopt,
		       seennsid, seenecs, seenexpire, seencookie);
	}

	if (item->summary->type) {
		if (rcode == ns_r_noerror || rcode == ns_r_nxdomain)
			goto done;
		nextserver(item);
		return;
	}

	if (seenopt)
		item->summary->seenopt = 1;

	if (seenopt && opcode == ns_o_query &&
	    (rcode == ns_r_noerror || rcode == ns_r_nxdomain ||
	     (rcode == ns_r_badvers && opts[item->test].version != 0)))
		item->summary->seenedns = 1;

	if (rcode != ns_r_refused && opts[item->test].version == 0)
		item->summary->allrefused = 0;

	if (rcode != ns_r_servfail && opts[item->test].version == 0)
		item->summary->allservfail = 0;

	if (opts[item->test].opcode != opcode)
		addtag(item, opcodetext(opcode)), ok = 0;

	if (opts[item->test].version == 0) {
		/* Expect NOERROR / BADCOOKIE */
		if (opts[item->test].opcode == 0 &&
		    ((rcode != 0 && !opts[item->test].cookie) ||
		     (rcode != 0 && (rcode != ns_r_badcookie || !seencookie) &&
		      opts[item->test].cookie)))
			addtag(item, rcodetext(rcode)), ok = 0;
		/* Expect NOTIMP */
		if (opts[item->test].opcode != 0 && rcode != 4)
			addtag(item, rcodetext(rcode)), ok = 0;
	}

	/* Expect BADVERS to EDNS Version != 0 */
	if (opts[item->test].version != 0)
		if (rcode != ns_r_badvers)
			addtag(item, rcodetext(rcode)), ok = 0;

	/*
	 * Check seenopt as the default value for ednsttl is
	 * not sufficient to prevent false positives.
	 */
	ednsvers = (ednsttl >> 16) & 0xff;
	if (seenopt && ednsvers != 0)
		addtag(item, "version-not-zero"), ok = 0;
	if (seenopt && 
	    ((ednsvers < opts[item->test].version && rcode != ns_r_badvers) ||
	     (ednsvers >= opts[item->test].version && rcode == ns_r_badvers)))
		addtag(item, "badversion"), ok = 0;
	if (!seenopt && opts[item->test].udpsize)
		addtag(item, "noopt"), ok = 0;
	if (seenopt && opts[item->test].udpsize == 0)
		addtag(item, "opt"), ok = 0;
	if (opts[item->test].type == ns_t_soa)
		if (opts[item->test].version == 0 &&
		    !opts[item->test].ignore && !seensoa &&
		    rcode == ns_r_noerror)
			addtag(item, "nosoa"), ok = 0;
	if (opts[item->test].type == ns_t_soa && seensoa)
		if (opts[item->test].version != 0 ||
		    (rcode != ns_r_noerror &&
		     opts[item->test].version == 0))
			addtag(item, "soa"), ok = 0;
	if (seenecho)
		addtag(item, "echoed"), ok = 0;
	if (seenopt && (opts[item->test].flags & 0x8000) != 0 &&
		       (ednsttl & 0x8000) == 0)
		addtag(item, "nodo"), ok = 0;

	/* AA is only defined for QUERY */
	if (!aa && opts[item->test].version == 0 &&
	    rcode == ns_r_noerror && opts[item->test].opcode == 0)
		addtag(item, "noaa"), ok = 0;

	if (aa && opts[item->test].opcode != 0)
		addtag(item, "aa"), ok = 0;

	/* RA is only defined for QUERY */
	if (ra && opts[item->test].opcode)
		addtag(item, "ra"), ok = 0;

	/* RD is only defined for QUERY */
	if (rd && (opts[item->test].opcode || !opts[item->test].rd))
		addtag(item, "rd"), ok = 0;
	if (!rd && opts[item->test].rd && opts[item->test].opcode == 0)
		addtag(item, "nord"), ok = 0;

	/* AD is only defined for QUERY */
	if (ad && (opts[item->test].opcode ||
	    (!opts[item->test].ad && (opts[item->test].flags & 0x8000) == 0)))
		addtag(item, "ad"), ok = 0;

	/* CD is only defined for QUERY */
	if (cd && (opts[item->test].opcode || !opts[item->test].cd))
		addtag(item, "cd"), ok = 0;

	/* Last reserved bit.  It is not supposed to be echoed per
	   RFC 1034. */
	if (z)
		addtag(item, "z"), ok = 0;

	/* Only DO is currently defined. */
	if ((ednsttl & 0x7fff) != 0)
		addtag(item, "mbz"), ok = 0;

	if (opts[item->test].ignore &&
	    buflen > (opts[item->test].udpsize ? opts[item->test].udpsize : 512))
		addtag(item, "toobig"), ok = 0;

	/* Only record seenrrsig if the test is "do". */
	if (seenrrsig && strcmp(opts[item->test].name, "do") == 0)
		item->summary->seenrrsig = 1;
	if (ok)
		addtag(item, "ok");
	else
		item->summary->allok = 0;
	if (seennsid)
		addtag(item, "nsid");
	if (seenexpire)
		addtag(item, "expire");
	if (seencookie) {
		if (rcode == ns_r_badcookie && opts[item->test].cookie)
			addtag(item, "cookie+badcookie");
		else
			addtag(item, "cookie");
	}
	if (seenecs)
		addtag(item, "subnet");

	goto done;
 err:
	addtag(item, "malformed");
	item->summary->allok = 0;
	item->summary->seenfailure = 1;
 done:
	freeitem(item);
}

/*
 * Read a TCP response.
 */
static void
tcpread(int fd) {
	struct workitem *item;
	int n;

	item = HEAD(reading);
	while (item && item->tcpfd != fd)
		item = NEXT(item, rlink);
	if (item == NULL)
		return;
 again:
	n = read(fd, item->tcpbuf + item->read, item->readlen - item->read);
	if (n == 0) {
		addtag(item, "eof");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}
	if (n < 0 && (errno == EAGAIN || errno == EINTR))
		return;
	if (n < 0) {
		if (errno == ECONNRESET)
			addtag(item, "reset");
		else if (errno == EPIPE)
			addtag(item, "pipe");
		else
			addtag(item, "read");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}
	item->read += n;
	if (item->read == item->readlen) {
		if (!item->havelen) {
			item->readlen = item->tcpbuf[0] << 8 | item->tcpbuf[1];
			item->havelen = 1;
			item->read = 0;
			goto again;
		}
		process(item, item->tcpbuf, item->readlen);
	}
}

/*
 * Send the TCP request and start the read process.
 */
static void
startread(struct workitem *item) {
	struct iovec iov[2];
	int iovcnt = 2;
	unsigned char buf[2];
	int n;

	FD_SET(item->tcpfd, &rfds);
	if (item->tcpfd > maxfd)
		maxfd = item->tcpfd;
	rhandlers[item->tcpfd] = tcpread;
	gettimeofday(&item->when, NULL);
	item->when.tv_sec += 10;
	APPEND(reading, item, rlink);
	item->havelen = 0;
	item->readlen = 2;
	item->read = 0;

	buf[0] = item->buflen>>8;
	buf[1] = item->buflen&0xff;
	iov[0].iov_base = &buf;
	iov[0].iov_len = 2;
	iov[1].iov_base = &item->buf;
	iov[1].iov_len = item->buflen;
	n = writev(item->tcpfd, iov, iovcnt);
	if (n != 2 + item->buflen) {
		addtag(item, "writev");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
	}
}

/*
 * Check if the connect succeeded and start perform a TCP request if it has.
 */
static void
connectdone(int fd) {
	struct workitem *item;
	socklen_t optlen;
	int cc;

	item = HEAD(connecting);
	while (item && item->tcpfd != fd)
		item = NEXT(item, clink);
	if (item == NULL)
		return;

	optlen = sizeof(cc);
	if (getsockopt(item->tcpfd, SOL_SOCKET, SO_ERROR,
		       (void *)&cc, (void *)&optlen) < 0)
		cc = errno;
	if (cc != 0) {
		if (cc == ECONNRESET)
			addtag(item, "reset");
		else if (cc == ECONNREFUSED)
			addtag(item, "connection-refused");
		else
			addtag(item, "failed");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}
	UNLINK(connecting, item, clink);
	FD_CLR(item->tcpfd, &wfds);
	whandlers[item->tcpfd] = NULL;
	startread(item);
}

/*
 * Connect to a server over TCP.
 */
static void
connecttoserver(struct workitem *item) {
	int fd, n, on = 1;
	socklen_t ss_len;

	fd = socket(item->summary->storage.ss_family,
		    SOCK_STREAM, IPPROTO_TCP);
	if (fd == -1) {
		addtag(item, "failed");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}
	if (fd >= FD_SETSIZE) {
		close(fd);
		addtag(item, "fdsetsize");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}

	/*
	 * Make the socket non blocking.
	 */
	n = ioctl(fd, FIONBIO, (void *)&on);
	if (n == -1) {
		close(fd);
		addtag(item, "failed");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}

#ifdef SO_NOSIGPIPE
	/*
	 * Don't generate a SIG_PIPE if there is a I/O error on this socket.
	 */
	n = setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, (void *)&on, sizeof(on));
	if (n == -1) {
		close(fd);
		addtag(item, "failed");
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}
#endif

	switch (item->summary->storage.ss_family) {
	case AF_INET:
		ss_len = sizeof(struct sockaddr_in);
		break;
	case AF_INET6:
		ss_len = sizeof(struct sockaddr_in6);
		break;
	}

	/*
	 * Start the actual connect.
	 */
	n = connect(fd, (struct sockaddr *)&item->summary->storage, ss_len);
	if (n == -1 && errno == EINPROGRESS) {
		if (!item->outstanding++)
			outstanding++;
		item->tcpfd = fd;
		whandlers[fd] = connectdone;
		FD_SET(fd, &wfds);
		if (fd > maxfd)
			maxfd = fd;
		gettimeofday(&item->when, NULL);
		item->when.tv_sec += 10;
		APPEND(connecting, item, clink);
		return;
	}
	if (n == -1) {
		if (errno == ECONNRESET)
			addtag(item, "reset");
		else if (errno == ECONNREFUSED)
			addtag(item, "connection-refused");
		else
			addtag(item, "failed");
		close(fd);
		item->summary->allok = 0;
		item->summary->seenfailure = 1;
		freeitem(item);
		return;
	}
	if (!item->outstanding++)
		outstanding++;
	item->tcpfd = fd;
	startread(item);
}

/*
 * Read zone [server [address]]
 */
static void
readstdin(int fd) {
	char line[4096];
	char zone[1204];
	char ns[1204];
	char address[1204];
	int n;

	/*
	 * Too much outstanding work then wait to be called again.
	 */
	if (outstanding > maxoutstanding / 2)
		return;

	if (fgets(line, sizeof(line), stdin) == NULL) {
		eof = 1;
		return;
	}
	n = sscanf(line, "%1024s%1024s%1024s", zone, ns, address);
	if (n == 3)
		check(zone, ns, address, NULL);
	if (n == 2) {
		struct summary *summarya, *summaryaaaa;

		/*
		 * Cross link A/AAAA lookups so that we can generate
		 * a single NXDOMAIN / no address report.
		 */
		summarya = lookupa(zone, ns, NULL);
		summaryaaaa = lookupaaaa(zone, ns, NULL);
		if (summarya && summaryaaaa) {
			summarya->xlink = summaryaaaa;
			summaryaaaa->xlink = summarya;
		}
		/*
		 * Release references.
		 */
		if (summarya) report(summarya);
		if (summaryaaaa) report(summaryaaaa);
	}
	if (n == 1)
		lookupns(zone);
}

static struct workitem *
finditem(struct sockaddr_storage *storage, int id) {
        struct workitem *item = HEAD(ids[id]);
        while (item != NULL &&
               !storage_equal(storage, &item->summary->storage))
                item = NEXT(item, idlink);
	return (item);
}

static void
icmp4read(int fd) {
	struct workitem *item = NULL;
	struct sockaddr_storage storage;
	struct sockaddr_in *sin = (struct sockaddr_in *)&storage;
	socklen_t len = sizeof(storage);
	unsigned char buf[4096];
	int n, hlen, offset, msgdata, id;
	struct icmp *icmp;
	struct udphdr *udphdr;
	struct tcphdr *tcphdr;
	const char *reason = NULL;

	n = recvfrom(fd, buf, sizeof(buf), 0,
		     (struct sockaddr *)&storage, &len);
	if (n < 0)
		return;
	icmp = (struct icmp *)(buf);
#if 0
	fprintf(stderr, "icmp_type=%u icmp_code=%u icmp_cksum=%u\n",
		icmp->icmp_type, icmp->icmp_code, icmp->icmp_cksum);
#endif
	switch (icmp->icmp_type) {
	case ICMP_ECHOREPLY:
		if (icmp->icmp_id != ident)
			return;
		int found = checkseq(&storage, icmp->icmp_seq);
		fprintf(stderr, "found=%u icmp_id=%u icmp_seq=%u\n",
			found, icmp->icmp_id, ntohs(icmp->icmp_seq));
		break;
	case ICMP_UNREACH:
		hlen = icmp->icmp_ip.ip_hl << 2;
		offset = offsetof(struct icmp, icmp_ip) + hlen;
		if (icmp->icmp_ip.ip_p == IPPROTO_UDP &&
		    n >= offset + sizeof(struct udphdr)) {
			udphdr = (struct udphdr *)&buf[offset];
			if (n >= offset + sizeof(struct udphdr) + 2) {
				msgdata = offset + sizeof(struct udphdr);
				id = (buf[msgdata] << 8) + buf[msgdata + 1];
				memset(&storage, 0, sizeof(storage));
				sin->sin_family = AF_INET;
#ifdef HAVE_SIN_LEN
				sin->sin_len = sizeof(*sin);
#endif
				sin->sin_addr = icmp->icmp_ip.ip_dst;
				sin->sin_port = udphdr->uh_dport;
				item = finditem(&storage, id);
			}
		}
		if (icmp->icmp_ip.ip_p == IPPROTO_TCP &&
		    n >= offset + sizeof(struct tcphdr)) {
			tcphdr = (struct tcphdr *)&buf[offset];
			if (n >= offset + sizeof(struct tcphdr) + 4) {
				msgdata = offset + sizeof(struct tcphdr);
				id = (buf[msgdata + 2] << 8) + buf[msgdata + 3];
				memset(&storage, 0, sizeof(storage));
				sin->sin_family = AF_INET;
#ifdef HAVE_SIN_LEN
				sin->sin_len = sizeof(*sin);
#endif
				sin->sin_addr = icmp->icmp_ip.ip_dst;
				sin->sin_port = tcphdr->th_dport;
				item = finditem(&storage, id);
			}
		}
		reason = "unreachable";
		switch (icmp->icmp_code) {
		case ICMP_UNREACH_NET:
			reason = "net-unreachable";
			break;
		case ICMP_UNREACH_HOST:
			reason = "host-unreachable";
			break;
		case ICMP_UNREACH_PROTOCOL:
			reason = "proto-unreachable";
			break;
		case ICMP_UNREACH_PORT:
			reason = "port-unreachable";
			break;
		case ICMP_UNREACH_NEEDFRAG:
			reason = "need-frag";
			break;
		case ICMP_UNREACH_SRCFAIL:
			reason = "source-fail";
			break;
		case ICMP_UNREACH_NET_UNKNOWN:
			reason = "net-unknown";
			break;
		case ICMP_UNREACH_HOST_UNKNOWN:
			reason = "host-unknown";
			break;
		case ICMP_UNREACH_ISOLATED:
			reason = "isolated";
			break;
		case ICMP_UNREACH_NET_PROHIB:
			reason = "net-prohibited";
			break;
		case ICMP_UNREACH_HOST_PROHIB:
			reason = "host-prohibited";
			break;
		case ICMP_UNREACH_TOSNET:
			reason = "net-tos";
			break;
		case ICMP_UNREACH_TOSHOST:
			reason = "host-tos";
			break;
		case ICMP_UNREACH_FILTER_PROHIB:
			reason = "filter-prohibited";
			break;
		case ICMP_UNREACH_HOST_PRECEDENCE:
			reason = "host-precedence";
			break;
		case ICMP_UNREACH_PRECEDENCE_CUTOFF:
			reason = "host-cutoff";
			break;
		}
		break;
	case ICMP_TIMXCEED:
		hlen = icmp->icmp_ip.ip_hl << 2;
		offset = offsetof(struct icmp, icmp_ip) + hlen;
		if (icmp->icmp_ip.ip_p == IPPROTO_UDP &&
		    n >= offset + sizeof(struct udphdr)) {
			udphdr = (struct udphdr *)&buf[offset];
			if (n >= offset + sizeof(struct udphdr) + 2) {
				msgdata = offset + sizeof(struct udphdr);
				id = (buf[msgdata] << 8) + buf[msgdata + 1];
				memset(&storage, 0, sizeof(storage));
				sin->sin_family = AF_INET;
#ifdef HAVE_SIN_LEN
				sin->sin_len = sizeof(*sin);
#endif
				sin->sin_addr = icmp->icmp_ip.ip_dst;
				sin->sin_port = udphdr->uh_dport;
				item = finditem(&storage, id);
			}
		}
		if (icmp->icmp_ip.ip_p == IPPROTO_TCP &&
		    n >= offset + sizeof(struct tcphdr)) {
			tcphdr = (struct tcphdr *)&buf[offset];
			if (n >= offset + sizeof(struct tcphdr) + 4) {
				msgdata = offset + sizeof(struct tcphdr);
				id = (buf[msgdata + 2] << 8) + buf[msgdata + 3];
				memset(&storage, 0, sizeof(storage));
				sin->sin_family = AF_INET;
#ifdef HAVE_SIN_LEN
				sin->sin_len = sizeof(*sin);
#endif
				sin->sin_addr = icmp->icmp_ip.ip_dst;
				sin->sin_port = tcphdr->th_dport;
				item = finditem(&storage, id);
			}
		}
		reason = "time-exceeded";
		switch (icmp->icmp_code) {
		case ICMP_TIMXCEED_INTRANS:
			reason = "time-exceeded-intransit";
			break;
		case ICMP_TIMXCEED_REASS:
			reason = "time-exceeded-reassembly";
			break;
		}
		break;
	case ICMP_UNREACH_NEEDFRAG:
		fprintf(stderr, "icmp needfrag: %u for %s\n",
			ntohs(icmp->icmp_nextmtu),
			inet_ntoa(icmp->icmp_ip.ip_dst));
		break;
	}
	if (item && reason) {
		addtag(item, reason);
		freeitem(item);
	}
}

static void
icmp6read(int fd) {
	struct workitem *item = NULL;
	struct sockaddr_storage storage;
	struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)&storage;
	socklen_t len = sizeof(storage);
	unsigned char buf[4096];
	struct ip6_hdr *ip6;
	struct icmp6_hdr *icmp6;
	struct udphdr *udphdr;
	struct tcphdr *tcphdr;
	int n, offset, msgdata, id, nxt;
	const char *reason = NULL;

	n = recvfrom(fd, buf, sizeof(buf), 0,
		     (struct sockaddr *)&storage, &len);
	if (n < 0)
		return;
	icmp6 = (struct icmp6_hdr *)buf;
#if 0
	fprintf(stderr, "icmp6_type=%u icmp6_code=%u icmp6_cksum=%u\n",
		icmp6->icmp6_type, icmp6->icmp6_code, icmp6->icmp6_cksum);
#endif

	switch (icmp6->icmp6_type) {
	case ICMP6_ECHO_REPLY:
		if (icmp6->icmp6_id != ident)
			return;
		int found = checkseq(&storage, icmp6->icmp6_seq);
		fprintf(stderr, "found=%u icmp6_id=%u icmp6_seq=%u\n",
			found, icmp6->icmp6_id, ntohs(icmp6->icmp6_seq));
		break;
	case ICMP6_PACKET_TOO_BIG:
		offset = offsetof(struct icmp6_hdr, icmp6_data8) + 4;
		ip6 = (struct ip6_hdr *)&buf[offset];
		offset += sizeof(struct ip6_hdr);
		nxt = ip6->ip6_nxt;
		/*
		 * If this is the initial part of the packet extract
		 * the next header value.
		 */
		if (nxt == IPPROTO_FRAGMENT && icmp6->icmp6_data8[2] == 0 &&
		    (icmp6->icmp6_data8[3] & 0xf7) == 0) {
			nxt = icmp6->icmp6_data8[0];
			offset += 8;
		}
		if (nxt == IPPROTO_UDP &&
		    n >= offset + sizeof(struct udphdr)) {
			udphdr = (struct udphdr *)&buf[offset];
			if (n >= offset + sizeof(struct udphdr) + 2) {
				msgdata = offset + sizeof(struct udphdr);
				id = (buf[msgdata] << 8) + buf[msgdata + 1];
				memset(&storage, 0, sizeof(storage));
				sin6->sin6_family = AF_INET6;
#ifdef HAVE_SIN6_LEN
				sin6->sin6_len = sizeof(*sin6);
#endif
				memcpy(&sin6->sin6_addr, &ip6->ip6_dst, 16);
				sin6->sin6_port = udphdr->uh_dport;
				item = finditem(&storage, id);
				if (item) {
					resend(item);
					item = NULL;
				}
			}
		}
		break;
	case ICMP6_DST_UNREACH:
		offset = offsetof(struct icmp6_hdr, icmp6_data8) + 4;
		ip6 = (struct ip6_hdr *)&buf[offset];
		offset += sizeof(struct ip6_hdr);
		nxt = ip6->ip6_nxt;
		/*
		 * If this is the initial part of the packet extract
		 * the next header value.
		 */
		if (nxt == IPPROTO_FRAGMENT && icmp6->icmp6_data8[2] == 0 &&
		    (icmp6->icmp6_data8[3] & 0xf7) == 0) {
			nxt = icmp6->icmp6_data8[0];
			offset += 8;
		}
		if (nxt == IPPROTO_UDP &&
		    n >= offset + sizeof(struct udphdr)) {
			udphdr = (struct udphdr *)&buf[offset];
			if (n >= offset + sizeof(struct udphdr) + 2) {
				msgdata = offset + sizeof(struct udphdr);
				id = (buf[msgdata] << 8) + buf[msgdata + 1];
				memset(&storage, 0, sizeof(storage));
				sin6->sin6_family = AF_INET6;
#ifdef HAVE_SIN6_LEN
				sin6->sin6_len = sizeof(*sin6);
#endif
				memcpy(&sin6->sin6_addr, &ip6->ip6_dst, 16);
				sin6->sin6_port = udphdr->uh_dport;
				item = finditem(&storage, id);
			}
		}
		if (nxt == IPPROTO_TCP &&
		    n >= offset + sizeof(struct tcphdr)) {
			tcphdr = (struct tcphdr *)&buf[offset];
			if (n >= offset + sizeof(struct tcphdr) + 2) {
				msgdata = offset + sizeof(struct tcphdr);
				id = (buf[msgdata + 2] << 8) + buf[msgdata + 3];
				memset(&storage, 0, sizeof(storage));
				sin6->sin6_family = AF_INET6;
#ifdef HAVE_SIN6_LEN
				sin6->sin6_len = sizeof(*sin6);
#endif
				memcpy(&sin6->sin6_addr, &ip6->ip6_dst , 16);
				sin6->sin6_port = tcphdr->th_dport;
				item = finditem(&storage, id);
			}
		}
		reason = "unreachable";
		switch (icmp6->icmp6_code) {
		case ICMP6_DST_UNREACH_NOROUTE:
			reason = "unreachable-noroute";
			break;
		case ICMP6_DST_UNREACH_ADMIN:
			reason = "unreachable-admin";
			break;
		case ICMP6_DST_UNREACH_BEYONDSCOPE:
			reason = "unreachable-scope";
			break;
		case ICMP6_DST_UNREACH_ADDR:
			reason = "unreachable-address";
			break;
		case ICMP6_DST_UNREACH_NOPORT:
			reason = "unreachable-port";
			break;
		}
		break;
	case ICMP6_TIME_EXCEEDED:
		offset = offsetof(struct icmp6_hdr, icmp6_data8) + 4;
		ip6 = (struct ip6_hdr *)&buf[offset];
		offset += sizeof(struct ip6_hdr);
		nxt = ip6->ip6_nxt;
		/*
		 * If this is the initial part of the packet extract
		 * the next header value.
		 */
		if (nxt == IPPROTO_FRAGMENT && icmp6->icmp6_data8[2] == 0 &&
		    (icmp6->icmp6_data8[3] & 0xf7) == 0) {
			nxt = icmp6->icmp6_data8[0];
			offset += 8;
		}
		if (nxt == IPPROTO_UDP &&
		    n >= offset + sizeof(struct udphdr)) {
			udphdr = (struct udphdr *)&buf[offset];
			if (n >= offset + sizeof(struct udphdr) + 2) {
				msgdata = offset + sizeof(struct udphdr);
				id = (buf[msgdata] << 8) + buf[msgdata + 1];
				memset(&storage, 0, sizeof(storage));
				sin6->sin6_family = AF_INET6;
#ifdef HAVE_SIN6_LEN
				sin6->sin6_len = sizeof(*sin6);
#endif
				memcpy(&sin6->sin6_addr, &ip6->ip6_dst, 16);
				sin6->sin6_port = udphdr->uh_dport;
				item = finditem(&storage, id);
			}
		}
		if (nxt == IPPROTO_TCP &&
		    n >= offset + sizeof(struct tcphdr)) {
			tcphdr = (struct tcphdr *)&buf[offset];
			if (n >= offset + sizeof(struct tcphdr) + 2) {
				msgdata = offset + sizeof(struct tcphdr);
				id = (buf[msgdata + 2] << 8) + buf[msgdata + 3];
				memset(&storage, 0, sizeof(storage));
				sin6->sin6_family = AF_INET6;
#ifdef HAVE_SIN6_LEN
				sin6->sin6_len = sizeof(*sin6);
#endif
				memcpy(&sin6->sin6_addr, &ip6->ip6_dst , 16);
				sin6->sin6_port = tcphdr->th_dport;
				item = finditem(&storage, id);
			}
		}
		reason = "time-exceeded";
		switch (icmp6->icmp6_code) {
		case ICMP6_TIME_EXCEED_TRANSIT:
			reason = "time-exceeded-intransit";
			break;
		case ICMP6_TIME_EXCEED_REASSEMBLY:
			reason = "time-exceeded-reassembly";
			break;
		}
		break;
	}
	if (item && reason) {
		addtag(item, reason);
		freeitem(item);
	}
}

static void
udpread(int fd) {
	struct workitem *item;
	struct sockaddr_storage storage;
	socklen_t len = sizeof(storage);
	unsigned char buf[4096];
	int n;
	unsigned int id, qr;

	n = recvfrom(fd, buf, sizeof(buf), 0,
		     (struct sockaddr *)&storage, &len);
	if (n < 12)
		return;

	qr = (buf[2] & 0x80) != 0;
	if (!qr)
		return;

	id = buf[0] << 8 | buf[1];
	item = HEAD(ids[id]);
	while (item != NULL &&
	       !storage_equal(&storage, &item->summary->storage))
		item = NEXT(item, idlink);

	/* Late response? */
	if (item == NULL)
		return;

	process(item, buf, n);
}

static void
nextserver(struct workitem *item) {
	struct sockaddr_storage storage;
	int id, tries;

	/*
	 * If we are in TCP mode cleanup.
	 */
	if (item->tcpfd != -1) {
		FD_CLR(item->tcpfd, &rfds);
		FD_CLR(item->tcpfd, &wfds);
		rhandlers[item->tcpfd] = NULL;
		whandlers[item->tcpfd] = NULL;
		close(item->tcpfd);
		item->tcpfd = -1;
	}

	/*
	 * Ensure we are on all the correct lists.
	 */
	if (LINKED(item, rlink))
		UNLINK(reading, item, rlink);
	if (LINKED(item, clink))
		UNLINK(connecting, item, clink);
	if (!LINKED(item, link))
		UNLINK(work, item, clink);

 again:
	if (++item->test > nservers) {
		addtag(item, "timeout");
		freeitem(item);
		return;
	}

	switch(servers[item->test].sin.sin_family) {
	case AF_INET:
		if (udp4 == -1)
			goto again;
		memcpy(&storage, &servers[item->test].sin,
		       sizeof(servers[item->test].sin));
		break;
	case AF_INET6:
		if (udp6 == -1)
			goto again;
		memcpy(&storage, &servers[0].sin6,
		       sizeof(servers[item->test].sin6));
		break;
	default:
		goto again;
	}

	/*
	 * Find a new query id if required.
	 */
	id = item->id;
	tries = 0;
	while (!checkid(&storage, id) && tries++ < 0xffff)
		id = (id + 1) & 0xffff;
	if (tries == 0xffff)
		goto again;

	if (id != item->id) {
		UNLINK(ids[item->id], item, idlink);
		item->buf[0] = id >> 8;
		item->buf[1] = id & 0xff;
		item->id = id;
		APPEND(ids[item->id], item, idlink);
	}

	item->summary->storage = storage;
	item->sends = 0;
	resend(item);
}

static void
addserver(const char *hostname) {
	struct addrinfo hints, *res, *res0;

	if (nservers < 10) {
		memset(&hints, 0, sizeof(hints));
		hints.ai_family = PF_UNSPEC;
		if (ipv4only)
			hints.ai_family = PF_INET;
		if (ipv6only)
			hints.ai_family = PF_INET6;
		hints.ai_socktype = SOCK_DGRAM;
		hints.ai_protocol = IPPROTO_UDP;
		hints.ai_flags = AI_ADDRCONFIG | AI_NUMERICSERV;
		if (getaddrinfo(hostname, "53", &hints, &res) == 0) {
			res0 = res;
			while (res && nservers < 10) {
				memcpy(&servers[nservers++].sin,
				       res->ai_addr, res->ai_addrlen);
				res = res->ai_next;
			}
			freeaddrinfo(res0);
		}
	}
}

static int stats;

static void
info(int sig) {
	stats = 1;
}

int
main(int argc, char **argv) {
	struct timeval now, to, start, *tpo = NULL;
	struct workitem *item = NULL, *citem, *ritem;
	fd_set myrfds, mywfds;
	unsigned int i;
	int n;
	int fd;
	int nfds = 0;
	int done = 0;
	char *end;
	int on = 1;

	while ((n = getopt(argc, argv, "46abBcdDeEfi:I:Lm:nopr:stT")) != -1) {
		switch (n) {
		case '4': ipv4only = 1; ipv6only = 0; break;
		case '6': ipv6only = 1; ipv4only = 0; break;
		case 'a': allok = 1; break;
		case 'b': bad = 1; break;
		case 'B': badtag = 1; break;
		case 'c': what |= COMM; break;
		case 'd': debug = 1; break;
		case 'D':
			for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
				if (opts[i].dig != NULL)
					printf("%-12s'%s'\n", opts[i].name, opts[i].dig);
			}
			exit (0);
		case 'e': what |= EDNS; break;
		case 'E': ednsonly = 1; break;
		case 'f': what |= EDNS | FULL; break;
		case 'i': what = EXPL;
			  for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
				if (strcasecmp(opts[i].name, optarg) == 0)
					opts[i].what |= EXPL;
			  }
			  break;
		case 'I': 
			  for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
				if ((what & opts[i].what) != 0)
					opts[i].what |= EXPL;
				if (strcasecmp(opts[i].name, optarg) == 0)
					opts[i].what &= ~EXPL;
			  }
			  what = EXPL;
			  break;
		case 'L': 
			for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
				printf("%s", opts[i].name);
				if ((opts[i].what & EDNS) != 0) printf(" EDNS");
				if ((opts[i].what & COMM) != 0) printf(" COMM");
				if ((opts[i].what & FULL) != 0) printf(" FULL");
				if ((opts[i].what & TYPE) != 0) printf(" TYPE");
				printf("\n");
			}
			exit (0);
		case 'm': n = strtol(optarg, &end, 10);
			  if (*end == '0' && n > 10)
				maxoutstanding = n;
			  if (maxoutstanding > FD_SETSIZE - 10)
				maxoutstanding = FD_SETSIZE - 10;
			  break;
		case 'n': printnsid = 1; break;
		case 'o': inorder = 1; break;
		case 'p': serial = 0; break;
		case 'r': addserver(optarg); break;
		case 's': serial = 1; break;
		case 't': what = TYPE; serial = 1; break;
		case 'T': what = TYPE;
			for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
				if (opts[i].what != 0 && (opts[i].what & what) == 0)
					continue;
				printf("%s\n", opts[i].name);
			}
			exit (0);
		default:
			printf("usage: genreport [-46abBcdeEfLnopstT] "
			       "[-i test] [-I test] [-m maxoutstanding] "
			       "[-r server]\n");
			printf("\t-4: IPv4 servers only\n");
			printf("\t-6: IPv6 servers only\n");
			printf("\t-a: only emit all ok\n");
			printf("\t-b: only emit bad servers\n");
			printf("\t-B: only emit bad tests\n");
			printf("\t-c: add common queries\n");
			printf("\t-d: enable debugging\n");
			printf("\t-D: list test and DiG command\n");
			printf("\t-e: edns test\n");
			printf("\t-E: EDNS only\n");
			printf("\t-f: add full mode tests (incl edns)\n");
			printf("\t-i: individual test\n");
			printf("\t-I: remove individual test\n");
			printf("\t-L: list tests and their grouping\n");
			printf("\t-m: set maxoutstanding\n");
			printf("\t-n: printnsid\n");
			printf("\t-o: inorder output\n");
			printf("\t-p: parallelize tests\n");
			printf("\t-r: use specified recursive server\n");
			printf("\t-s: serialize tests\n");
			printf("\t-t: type tests (serial)\n");
			printf("\t-T: print type list for type test (-t)\n");
			exit(0);
		}
	}

	ident = getpid() & 0xFFFF;

#ifdef SIGINFO
	/* Preferred signal. */
	signal(SIGINFO, info);
#endif
	signal(SIGUSR1, info);

#ifndef SO_NOSIGPIPE
	/* Ignore SIGPIPE if we can't set SO_NOSIGPIPE. */
	signal(SIGPIPE, SIG_IGN);
#endif

	FD_ZERO(&rfds);
	FD_ZERO(&wfds);

	FD_SET(0, &rfds);
	maxfd = 0;
	rhandlers[0] = readstdin;

	if (!ipv6only)
		udp4 = socket(PF_INET, SOCK_DGRAM, IPPROTO_UDP);
	if (udp4 >= FD_SETSIZE) {
		close(udp4);
		udp4 = -1;
	}
	if (udp4 >= 0) {
		/*
		 * Make the socket non blocking.
		 */
		n = ioctl(udp4, FIONBIO, (void *)&on);
		if (n == -1) {
			close(udp4);
			udp4 = -1;
		}
	}
	if (udp4 >= 0) {
		FD_SET(udp4, &rfds);
		if (udp4 > maxfd)
			maxfd = udp4;
		rhandlers[udp4] = udpread;
	}

	if (!ipv4only)
		udp6 = socket(PF_INET6, SOCK_DGRAM, IPPROTO_UDP);
	if (udp6 >= FD_SETSIZE) {
		close(udp6);
		udp6 = -1;
	}
	if (udp6 >= 0) {
		/*
		 * Make the socket non blocking.
		 */
		n = ioctl(udp6, FIONBIO, (void *)&on);
		if (n == -1) {
			close(udp6);
			udp6 = -1;
		}
	}
	if (udp6 >= 0) {
		FD_SET(udp6, &rfds);
		if (udp6 > maxfd)
			maxfd = udp6;
		rhandlers[udp6] = udpread;
	}

	if (!ipv6only)
		icmp4 = socket(AF_INET, SOCK_DGRAM, IPPROTO_ICMP);
	if (icmp4 >= FD_SETSIZE) {
		close(icmp4);
		icmp4 = -1;
	}
	if (icmp4 >= 0) {
		/*
		 * Make the socket non blocking.
		 */
		n = ioctl(icmp4, FIONBIO, (void *)&on);
		if (n == -1) {
			close(icmp4);
			icmp4 = -1;
		}
	}
	if (icmp4 >= 0) {
#ifdef IP_STRIPHDR
		n = setsockopt(icmp4, IPPROTO_IP, IP_STRIPHDR,
			       (void *)&on, sizeof(on));
#else
		n = -1;
#endif
		if (n == -1) {
			close(icmp4);
			icmp4 = -1;
		}
	}
	if (icmp4 >= 0) {
		FD_SET(icmp4, &rfds);
		if (icmp4 > maxfd)
			maxfd = icmp4;
		rhandlers[icmp4] = icmp4read;
	}

	if (!ipv4only)
		icmp6 = socket(AF_INET6, SOCK_DGRAM, IPPROTO_ICMPV6);
	if (icmp6 >= FD_SETSIZE) {
		close(icmp6);
		icmp6 = -1;
	}
	if (icmp6 >= 0) {
		/*
		 * Make the socket non blocking.
		 */
		n = ioctl(icmp6, FIONBIO, (void *)&on);
		if (n == -1) {
			close(icmp6);
			icmp6 = -1;
		}
	}
	if (icmp6 >= 0) {
		FD_SET(icmp6, &rfds);
		if (icmp6 > maxfd)
			maxfd = icmp6;
		rhandlers[icmp6] = icmp6read;
	}

	res_init();

	/*
	 * If we haven't been given recursive servers to use the
	 * get the system's default servers.
	 */
#ifdef HAVE_RES_GETSERVERS
	if (!nservers) {
		nservers = res_getservers(&_res, servers,
					  sizeof(servers)/sizeof(servers[0]));
	}
#else
	/*
	 * This does not support IPv6 nameservers.
	 */
	if (!nservers) {
		memset(servers, 0, sizeof(servers));
		for (;nservers < _res.nscount; nservers++)
			servers[nservers].sin = _res.nsaddr_list[nservers];
	}
#endif

	gettimeofday(&start, NULL);

	/*
	 * Main work loop.
	 */
	do {
		FD_COPY(&rfds, &myrfds);
		FD_COPY(&wfds, &mywfds);
		nfds = maxfd + 1;
		if (item) {
			to.tv_sec = item->when.tv_sec - now.tv_sec;
			to.tv_usec = item->when.tv_usec - now.tv_usec;
			if (to.tv_usec < 0) {
				to.tv_usec += 1000000;
				to.tv_sec -= 1;
			}
			if (to.tv_sec < 0) {
				to.tv_sec = 0;
				to.tv_usec = 0;
			}
			tpo = &to;
		} else
			tpo = NULL;

		/*
		 * Too much outstanding work stop looking for more.
		 */
		if (eof || outstanding > maxoutstanding/2)
			FD_CLR(0, &myrfds);
		n = select(nfds, &myrfds, &mywfds, NULL, tpo);
		if (n > 0) {
			for (fd = 0; fd <= maxfd; fd++) {
				if (FD_ISSET(fd, &myrfds) &&
				    rhandlers[fd] != NULL)
					(*rhandlers[fd])(fd);
				if (FD_ISSET(fd, &mywfds) &&
				    whandlers[fd] != NULL)
					(*whandlers[fd])(fd);
			}
		}

		/*
		 * Find the next item that needs to be handled on the
		 * three work queues.  Also timeout / resend if approriate.
		 */
		item = HEAD(work);
		ritem = HEAD(reading);
		citem = HEAD(connecting);
		if (item || citem || ritem || stats)
			gettimeofday(&now, NULL);
		if (stats) {
			long long usecs, qps;
			usecs = (now.tv_sec - start.tv_sec) * 1000000;
			usecs += now.tv_usec - start.tv_usec;
			qps = (sent * 1000000000) / usecs;
			fprintf(stderr, "%llu.%03llu\n", qps/1000, qps%1000);
			stats = 0;
		}

		/*
		 * UDP work queue.
		 */
		while (item) {
			if (item->when.tv_sec > now.tv_sec ||
			    (item->when.tv_sec == now.tv_sec &&
			     item->when.tv_usec > now.tv_usec))
				break;
			if (item->sends < 3) {
				resend(item);
			} else if (item->type) {
				nextserver(item);
			} else {
				addtag(item, "timeout");
				item->summary->allok = 0;
				item->summary->seenfailure = 1;
				freeitem(item);
			}
			item = HEAD(work);
		}

		/*
		 * Has the connect timed out?
		 */
		while (citem) {
			if (citem->when.tv_sec > now.tv_sec ||
			    (citem->when.tv_sec == now.tv_sec &&
			     citem->when.tv_usec > now.tv_usec))
				break;
			if (citem->type) {
				nextserver(citem);
			} else {
				addtag(citem, "timeout");
				citem->summary->allok = 0;
				citem->summary->seenfailure = 1;
				freeitem(citem);
			}
			citem = HEAD(connecting);
		}

		/*
		 * Has the TCP read timed out?
		 */
		while (ritem) {
			if (ritem->when.tv_sec > now.tv_sec ||
			    (ritem->when.tv_sec == now.tv_sec &&
			     ritem->when.tv_usec > now.tv_usec))
				break;
			if (ritem->type) {
				nextserver(ritem);
			} else {
				addtag(ritem, "timeout");
				ritem->summary->allok = 0;
				ritem->summary->seenfailure = 1;
				freeitem(ritem);
			}
			ritem = HEAD(reading);
		}

		/*
		 * If we have space for pending items do them now.
		 */
		for (;;) {
			item = HEAD(pending);
			if (item == NULL || outstanding > maxoutstanding)
				break;
			UNLINK(pending, item, plink);
			resend(item);
		} 

		/*
		 * New items may have been added as the result of
		 * calling freeitem when sending requests serially.
		 * Get the current list heads so we can workout which
		 * queue we are waiting for first.
		 */
		item = HEAD(work);
		ritem = HEAD(reading);
		citem = HEAD(connecting);
		/*
		 * Make item be the earliest of item, citem.
		 */
		if (item && citem) {
			if (citem->when.tv_sec < item->when.tv_sec ||
			    (citem->when.tv_sec == item->when.tv_sec &&
			     citem->when.tv_usec < item->when.tv_usec))
				item = citem;
		} else if (item == NULL)
			item = citem;

		/*
		 * Make item be the earliest of item, ritem.
		 */
		if (item && ritem) {
			if (ritem->when.tv_sec < item->when.tv_sec ||
			    (ritem->when.tv_sec == item->when.tv_sec &&
			     ritem->when.tv_usec < item->when.tv_usec))
				item = ritem;
		} else if (item == NULL)
			item = ritem;

		if (eof && item == NULL)
			done = 1;
	} while (!done);
}
