#include <stdio.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <arpa/nameser.h>
#include <resolv.h>
#include <string.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <stdlib.h>
#include <sys/time.h>

#define ns_t_dnskey 48

int eof = 0;
static int maxfd = -1;
static fd_set rfds, wfds;

static void(*rhandlers[FD_SETSIZE])(int);
static void(*whandlers[FD_SETSIZE])(int);

static int udp4 = -1;
static int udp6 = -1;

#define APPEND(list, item, link) do { \
	if ((list).tail) \
		(list).tail->link.next = (item); \
	else \
		(list).head = (item); \
	(item)->link.prev = list.tail; \
	(item)->link.next = NULL; \
	(list).tail = (item); \
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
} while (0)

#define NEXT(item, link) (item)->link.next
#define PREV(item, link) (item)->link.next

#define HEAD(list) (list).head
#define TAIL(list) (list).tail

struct workitem {
	struct {
		struct workitem *next;
		struct workitem *prev;
	} link, idlink;
	char zone[1024];
	char ns[1024];
	unsigned short id;
	struct timeval when;
	struct sockaddr_storage storage;
	int test;
	int sends;
	int buflen;
	int tcpfd;
	unsigned char buf[512];
};

static struct {
	struct workitem *head;
	struct workitem *tail;
} work, ids[0x10000];

struct {
	const char *name;
	unsigned short rdlen;
	const char *rdata;
	unsigned short udpsize;
	unsigned short flags;
	unsigned short version;
	unsigned int tcp;
	unsigned int ignore;
	unsigned short type;
} opts[] = {
	{ "dns", 0, NULL, 0, 0, 0, 0, 0, ns_t_soa },
	{ "edns", 0, "", 4096, 0, 0, 0, 0, ns_t_soa },
	{ "edns@512", 0, "" , 512, 0, 0, 0, 1, ns_t_dnskey },
	{ "edns1", 0, "" , 4096, 0, 1, 0, 0, ns_t_soa },
	{ "ednsopt", 4, "\0\144\0", 4096, 0, 0, 0, 0, ns_t_soa },
	{ "edns1opt", 4, "\0\144\0", 4096, 0, 1, 0, 0, ns_t_soa },
	{ "do", 4, "\0\144\0", 4096, 1, 0, 0, 0, ns_t_soa },
	{ "ednsflags", 4, "", 4096, 0x80, 0, 0, 0, ns_t_soa },
	{ "optlist", 4 + 8 + 4 + 12, "\0\3\0\0" "\0\10\0\4\0\1\0\0"
	  "\0\11\0\0" "\0\12\0\10\0\0\0\0\0\0\0\0", 4096, 0, 0, 0, 0,
	   ns_t_soa },
	{ "ednstcp", 0, "", 512, 1, 0, 1, 0, ns_t_dnskey }
};

static int
storage_equal(struct sockaddr_storage *s1, struct sockaddr_storage *s2) {
	struct sockaddr_in *sin1, *sin2;
	struct sockaddr_in6 *sin61, *sin62;

	if (s1->ss_len != s2->ss_len || s1->ss_family != s2->ss_family)
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

static int
checkid(struct sockaddr_storage *storage, int id) {
	struct workitem *item;

	item = HEAD(ids[id]);
	while (item != NULL &&
	       !storage_equal(storage, &item->storage))
		item = NEXT(item, idlink);
	return ((item == NULL) ? 1 : 0);
}

static void
dotest(struct workitem *item) {
	unsigned char *cp;
	unsigned int ttl;
	int n, fd, id, tries = 0;

	switch (item->storage.ss_family) {
	case AF_INET:
		fd = udp4;
		break;
	case AF_INET6:
		fd = udp6;
		break;
	}

	if (fd == -1) {
		free(item);
		return;
	}
	
	n = res_mkquery(ns_o_query, item->zone, ns_c_in, opts[item->test].type,
			NULL, 0, NULL, item->buf, sizeof(item->buf));

	if (n > 0 && opts[item->test].rdata != NULL) {
		cp = item->buf + n;
		ns_put16(ns_t_opt, cp);
		ns_put16(opts[item->test].udpsize, cp);
		ttl = (opts[item->test].version << 16) | opts[item->test].flags;
		ns_put32(ttl, cp);
		ns_put16(opts[item->test].rdlen, cp);
		memcpy(cp, opts[item->test].rdata, opts[item->test].rdlen);
		cp += opts[item->test].rdlen;
		n = cp - item->buf;
	}

	if (n > 0) {
		id = item->buf[0] << 8 | item->buf[1];

		while (!checkid(&item->storage, id) && tries++ < 0xffff)
			id = (id + 1) & 0xffff;
		
		if (tries == 0xffff) {
			free(item);
			return;
		}

		item->buf[0] = id >> 8;
		item->buf[1] = id & 0xff;
		item->id = id;
		item->buflen = n;

		n = sendto(fd, item->buf, item->buflen, 0,
			   (struct sockaddr *)&item->storage,
			   item->storage.ss_len);
	}

	if (n > 0) {
		printf("%s rdlen=%u udpsize=%u flags=%04x version=%u "
		       "tcp=%u ignore=%u id=%u\n",
		       opts[item->test].name, opts[item->test].rdlen,
		       opts[item->test].udpsize, opts[item->test].flags,
		       opts[item->test].version, opts[item->test].tcp,
		       opts[item->test].ignore, item->id);
		gettimeofday(&item->when, NULL);
		item->sends = 1;
		APPEND(work, item, link);
		APPEND(ids[item->id], item, idlink);
	} else
		free(item);
}

static void
check(char *zone, char *ns, char *address) {
	size_t i;
	int n, fd;
	struct in_addr addr;
	struct in6_addr addr6;
	struct sockaddr_storage storage;
	
	memset(&storage, 0, sizeof(storage));
	if (inet_pton(AF_INET6, address, &addr6) == 1) {
		struct sockaddr_in6 *s = (struct sockaddr_in6 *)&storage;
		s->sin6_len = sizeof(struct sockaddr_in6);
		s->sin6_family = AF_INET6;
		s->sin6_port = htons(53);
		s->sin6_addr = addr6;
		fd = udp6;
	} else if (inet_pton(AF_INET, address, &addr) == 1) {
		struct sockaddr_in *s = (struct sockaddr_in *)&storage;
		s->sin_len = sizeof(struct sockaddr_in);
		s->sin_family = AF_INET;
		s->sin_port = htons(53);
		s->sin_addr = addr;
		fd = udp4;
	} else
		return;

	if (fd == -1)
		return;

	for (i = 0; i < sizeof(opts)/sizeof(opts[0]); i++) {
		struct workitem *item = calloc(1, sizeof(*item));
		if (item == NULL)
			break;
		strcpy(item->zone, zone);
		strcpy(item->ns, ns);
		item->storage = storage;
		item->test = i;
		dotest(item);
	}
}

static void
readstdin(int fd) {
	char zone[1204];
	char ns[1204];
	char address[1204];
	int n;

	n = scanf("%1024s%1024s%1024s", zone, ns, address);
	if (n == 3)
	      check(zone, ns, address);
	if (n == EOF) {
		eof = 1;
		FD_CLR(0, &rfds);
		for (fd = maxfd; fd >= 0; fd--) {
			if (FD_ISSET(fd, &rfds) || FD_ISSET(fd, &wfds)) {
				break;
			}
		}
		maxfd = fd;
	}
}

static void
udpread(int fd) {
	struct workitem *item;
	struct sockaddr_storage storage;
	socklen_t len = sizeof(storage);
	unsigned char buf[4096];
	int n, id;
		
	n = recvfrom(fd, buf, sizeof(buf), 0,
		     (struct sockaddr *)&storage, &len);
	id = buf[0] << 8| buf[1];
	printf("recvfrom => %d (id=%u)\n", n, id);
	item = HEAD(ids[id]);
	while (item != NULL &&
	       !storage_equal(&storage, &item->storage))
		item = NEXT(item, idlink);

	/* Late response? */
	if (item == NULL)
		return;

	printf("found item = %p\n", item);
	UNLINK(work, item, link);
	UNLINK(ids[id], item, idlink);
	free(item);
}

static void
resend(struct workitem *item) {
	unsigned int ttl;
	int n, fd;

	switch (item->storage.ss_family) {
	case AF_INET:
		fd = udp4;
		break;
	case AF_INET6:
		fd = udp6;
		break;
	}

	if (fd == -1) {
		UNLINK(work, item, link);
		UNLINK(ids[item->id], item, idlink);
		free(item);
		return;
	}

	n = sendto(fd, item->buf, item->buflen, 0,
		   (struct sockaddr *)&item->storage,
		   item->storage.ss_len);
	if (n > 0) {
		printf("resend %s rdlen=%u udpsize=%u flags=%04x version=%u "
		       "tcp=%u ignore=%u id=%u\n",
		       opts[item->test].name, opts[item->test].rdlen,
		       opts[item->test].udpsize, opts[item->test].flags,
		       opts[item->test].version, opts[item->test].tcp,
		       opts[item->test].ignore, item->id);
		gettimeofday(&item->when, NULL);
		item->sends++;
		UNLINK(work, item, link);
		APPEND(work, item, link);
	} else {
		UNLINK(work, item, link);
		UNLINK(ids[item->id], item, idlink);
		free(item);
	}
}

int
main() {
	struct timeval now, to, *tpo = NULL;
	struct workitem *item = NULL;
	fd_set myrfds, mywfds;
	int n;
	int fd;
	int nfds = 0;
	int done = 0;

	FD_ZERO(&rfds);
	FD_ZERO(&wfds);

	FD_SET(0, &rfds);
	maxfd = 0;
	rhandlers[0] = readstdin;

	udp4 = socket(PF_INET, SOCK_DGRAM, IPPROTO_UDP);
	if (udp4 >= 0) {
		FD_SET(udp4, &rfds);
		if (udp4 > maxfd)
			maxfd = udp4;
		rhandlers[udp4] = udpread;
	}

	udp6 = socket(PF_INET6, SOCK_DGRAM, IPPROTO_UDP);
	if (udp6 >= 0) {
		FD_SET(udp6, &rfds);
		if (udp6 > maxfd)
			maxfd = udp6;
		rhandlers[udp6] = udpread;
	}

	do {
		FD_COPY(&rfds, &myrfds);
		FD_COPY(&wfds, &mywfds);
		nfds = maxfd + 1;
		if (item) {
			to.tv_sec = item->when.tv_sec + 1 - now.tv_sec;
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
			printf("tpo=%p tv_sec=%ld, tv_usec=%u\n", tpo,
			       to.tv_sec, to.tv_usec);
		} else
			tpo = NULL;
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
		item = HEAD(work);
		if (item)
			gettimeofday(&now, NULL);
		while (item) {
			if (item->when.tv_sec + 1 > now.tv_sec ||
			    (item->when.tv_sec + 1 == now.tv_sec &&
			     item->when.tv_usec > now.tv_usec))
				break;
			if (item->sends < 3) {
				resend(item);
			} else {
				printf("timeout item = %p\n", item);
				UNLINK(work, item, link);
				UNLINK(ids[item->id], item, idlink);
				free(item);
			}
			item = HEAD(work);
		}
		
		if (eof && item == NULL)
			done = 1;
	} while (!done);
}
