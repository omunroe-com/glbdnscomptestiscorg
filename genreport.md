% GENREPORT(1)
% Internet Systems Consortium
% March 2018

# NAME

genreport - generate a report about DNS server compliance.

# SYNOPSIS

**genreport** **[-46abBcdeEfLopstT]** **[-i *test*]** **[-I *test*]** **[-m *maxoutstanding*]** **[-r *server*]**

# DESCRIPTION

**genreport** tests DNS servers responses to a variety of different
queries and remotes if the response is compliant with the relevant
RFCs.

**genreport** takes a list of zone names with optional server names
and/or IP address (one per line).  If only the zone name is provided
the list of name servers for the zone will be looked up followed
by the addresses of all the servers for those name servers.  If the
zone and name server name is specified then only the addresses of
that name server will be used for testing.  If zone, server and
address are given then only that address will be used for testing.
The server is a placeholder field.

There are four grouping of tests EDNS (default), FULL (includes EDNS),
COMMON and TYPE.

Options are order dependent.

# OPTIONS

**-4**
: only query IPv4 servers.

**-6**
: only query IPv6 servers.

**-a**
: only emit 'all ok' rather than a result for each sub test.

**-b**
: only emit bad servers.

**-B**
: only emit bad tests.

**-c**
: add common queries to the set of tests to be made.

**-d**
: enable debugging.

**-e**
: edns test.

**-E**
: EDNS only.

**-f**
: add full mode tests (includes edns).

**-i test**
: add a individual test.

**-I test**
: remove a individual test.

**-L**
: list tests and their grouping.

**-m maxoutstanding**
: set the maximum number of outstanding DNS queries in progress.

**-o**
: restore the output order rather than printing each server as the
tests for that server complete.

**-p**
: run tests in parallel.

**-r server**
: use specified recursive server to look up name servers for a zone
and addresses.

**-s**
: serialize tests.

**-t**
: type tests (serial) - test the server's handling of different query types.

**-T**
: print type list for type test (-t).

# EXAMPLES

## Test all servers for a zone

`% echo isc.org | genreport`

## Test a specific server for a zone

`% echo isc.org ams.sns-pb.isc.org | genreport`

## Test all servers in the root zone

`% dig axfr . | awk '$4 == "NS" { print $1, $5 }' > list`  
`% genreport -po < list`

This generates a seperate list as the AXFR will timeout when the
pipeline stalls. The tests are run in parallel (-p) and the output
is reordered to preserve the input order (-o).

## Test all the root servers handling of different query types.

`echo . | /genreport -ta`

As the type list is long we also collapse the output to "all ok" (-a)
if all subtests to a particular server succeed.

# TESTS

**dns EDNS**
: Send a plain DNS query with type code SOA.

**aa FULL**
: Send a plain DNS query with type code SOA and AA set to 1.

**ad FULL**
: Send a plain DNS query with type code SOA and AD set to 1.

**cd FULL**
: Send a plain DNS query with type code SOA and CD set to 1.

**ra FULL**
: Send a plain DNS query with type code SOA and RA set to 1.

**rd FULL**
: Send a plain DNS query with type code SOA and RD set to 1.

**tc FULL**
: Send a plain DNS query with type code SOA and TC set to 1.

**zflag FULL**
: Send a plain DNS query with type code SOA and the remaining reserved DNS header flag set to 1.

**opcode FULL**
: Send a request with a unknown opcode (15);

**opcodeflg FULL**
: Send a request with a unknown opcode (15) and the following flag bits set to 1 (tc, rd, ra, cd, ad, aa, and z).

**type666 FULL**
: Send a plain DNS query with type code 666.  This is used to test unknown type code handling.

**tcp FULL**
: Send a plain DNS query with type code SOA over TCP.

**edns EDNS**
: Send a EDNS version 0 query with type code SOA.

**edns1 EDNS**
: Send a EDNS version 1 query with type code SOA.

**edns@512 EDNS**
: Send a EDNS version 0 query with type code DNSKEY, DO set to 1 and the EDNS buffer size set to 512.  This query is attempting to elicit a truncated EDNS response.

**ednsopt EDNS**
: Send a EDNS version 0 query with type code SOA and a undefined EDNS option code (100).

**edns1opt EDNS**
: Send a EDNS version 1 query with type code SOA and a undefined EDNS option code (100).

**do EDNS**
: Send a EDNS version 0 query with type code SOA and DO set to 1.

**edns1do FULL**
: Send a EDNS version 1 query with type code SOA and DO set to 1.

**ednsflags EDNS**
: Send a EDNS version 0 query with type code SOA and a undefined EDNS flag bit set to 1.

**optlist EDNS**
: Send a EDNS version 0 query with type code SOA and EDNS options NSID, ECS, EXPIRE, and COOKIE.

**ednsnsid FULL**
: Send a EDNS version 0 query with type code SOA and EDNS option NSID.

**ednscookie FULL**
: Send a EDNS version 0 query with type code SOA and EDNS option COOKIE.

**ednsexpire FULL**
: Send a EDNS version 0 query with type code SOA and EDNS option EXPIRE.

**ednssubnet FULL**
: Send a EDNS version 0 query with type code SOA and EDNS option ECS.

**edns1nsid FULL**
: Send a EDNS version 1 query with type code SOA and EDNS option NSID.

**edns1cookie FULL**
: Send a EDNS version 1 query with type code SOA and EDNS option COOKIE.

**edns1expire FULL**
: Send a EDNS version 1 query with type code SOA and EDNS option EXPIRE.

**edns1subnet FULL**
: Send a EDNS version 1 query with type code SOA and EDNS option ECS.

**ednstcp EDNS**
: Send a EDNS version 0 query with type code SOA over TCP.

**bind11 COMM**
: Send a query that is typical of what named from BIND 9.11 sends.

**dig11 COMM**
: Send a query that is typical of what dig from BIND 9.11 sends.

**A TYPE**
: Send a plain DNS query with type code A.

**NS TYPE**
: Send a plain DNS query with type code NS.

**MD TYPE**
: Send a plain DNS query with type code MD.

**MF TYPE**
: Send a plain DNS query with type code MF.

**CNAME TYPE**
: Send a plain DNS query with type code CNAME.

**SOA TYPE**
: Send a plain DNS query with type code SOA.

**MB TYPE**
: Send a plain DNS query with type code MB.

**MG TYPE**
: Send a plain DNS query with type code MG.

**MR TYPE**
: Send a plain DNS query with type code MR.

**NULL TYPE**
: Send a plain DNS query with type code NULL.

**WKS TYPE**
: Send a plain DNS query with type code WKS.

**PTR TYPE**
: Send a plain DNS query with type code PTR.

**HINFO TYPE**
: Send a plain DNS query with type code HINFO.

**MINFO TYPE**
: Send a plain DNS query with type code MINFO.

**MX TYPE**
: Send a plain DNS query with type code MX.

**TXT TYPE**
: Send a plain DNS query with type code TXT.

**RP TYPE**
: Send a plain DNS query with type code RP.

**AFSDB TYPE**
: Send a plain DNS query with type code AFSDB.

**X25 TYPE**
: Send a plain DNS query with type code X25.

**ISDN TYPE**
: Send a plain DNS query with type code ISDN.

**RT TYPE**
: Send a plain DNS query with type code RT.

**NSAP TYPE**
: Send a plain DNS query with type code NSAP.

**NSAP-PTR TYPE**
: Send a plain DNS query with type code NSAP-PTR.

**SIG TYPE**
: Send a plain DNS query with type code SIG.

**KEY TYPE**
: Send a plain DNS query with type code KEY.

**PX TYPE**
: Send a plain DNS query with type code PX.

**GPOS TYPE**
: Send a plain DNS query with type code GPOS.

**AAAA TYPE**
: Send a plain DNS query with type code AAAA.

**LOC TYPE**
: Send a plain DNS query with type code LOC.

**NXT TYPE**
: Send a plain DNS query with type code NXT.

**SRV TYPE**
: Send a plain DNS query with type code SRV.

**NAPTR TYPE**
: Send a plain DNS query with type code NAPTR.

**KX TYPE**
: Send a plain DNS query with type code KX.

**CERT TYPE**
: Send a plain DNS query with type code CERT.

**A6 TYPE**
: Send a plain DNS query with type code A6.

**DNAME TYPE**
: Send a plain DNS query with type code DNAME.

**APL TYPE**
: Send a plain DNS query with type code APL.

**DS TYPE**
: Send a plain DNS query with type code DS.

**SSHFP TYPE**
: Send a plain DNS query with type code SSHFP.

**IPSECKEY TYPE**
: Send a plain DNS query with type code IPSECKEY.

**RRSIG TYPE**
: Send a plain DNS query with type code RRSIG.

**NSEC TYPE**
: Send a plain DNS query with type code NSEC.

**DNSKEY TYPE**
: Send a plain DNS query with type code DNSKEY.

**DHCID TYPE**
: Send a plain DNS query with type code DHCID.

**NSEC3 TYPE**
: Send a plain DNS query with type code NSEC3.

**NSEC3PARAM TYPE**
: Send a plain DNS query with type code NSEC3PARAM.

**TLSA TYPE**
: Send a plain DNS query with type code TLSA.

**SMIMEA TYPE**
: Send a plain DNS query with type code SMIME.

**HIP TYPE**
: Send a plain DNS query with type code HIP.

**CDS TYPE**
: Send a plain DNS query with type code CDS.

**CDNSKEY TYPE**
: Send a plain DNS query with type code CDNSKEY.

**OPENPGPKEY TYPE**
: Send a plain DNS query with type code OPENPGPKEY.

**SPF TYPE**
: Send a plain DNS query with type code SPF.

**NID TYPE**
: Send a plain DNS query with type code NID.

**L32 TYPE**
: Send a plain DNS query with type code L32.

**L64 TYPE**
: Send a plain DNS query with type code L64.

**LP TYPE**
: Send a plain DNS query with type code LP.

**EUI48 TYPE**
: Send a plain DNS query with type code EUI48.

**EUI64 TYPE**
: Send a plain DNS query with type code EUI64.

**URI TYPE**
: Send a plain DNS query with type code URI.

**CAA TYPE**
: Send a plain DNS query with type code CAA.

**AVC TYPE**
: Send a plain DNS query with type code AVC.

**DOA TYPE**
: Send a plain DNS query with type code DOA.

**DLV TYPE**
: Send a plain DNS query with type code DLV.

**TYPE1000 TYPE**
: Send a plain DNS query with type code 1000.  This is used to test unknown type code handling.

# SEE ALSO

dig(1), named(8).