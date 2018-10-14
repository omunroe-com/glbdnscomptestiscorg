AC_INIT([DNS Compliance Tester], [1.0], [marka@isc.org], , [https://gitlab.isc.org/isc-projects/DNS-Compliance-Testing])
AM_INIT_AUTOMAKE([subdir-objects no-dist-gzip dist-xz -Wall -Werror])
AM_SILENT_RULES([yes])
AC_PROG_CC_C99
AC_CONFIG_SRCDIR([genreport.c])
AC_CONFIG_HEADER([config.h])
AC_CONFIG_FILES([Makefile])
AC_CANONICAL_HOST
AC_CHECK_FUNCS(strlcpy strlcat)
AC_SEARCH_LIBS([res_mkquery],[resolv bind])
AC_SEARCH_LIBS([res_9_mkquery],[resolv bind])
AC_SEARCH_LIBS([__res_mkquery],[resolv bind])
AC_CHECK_HEADERS(sys/types.h netinet/in.h arpa/nameser.h resolv.h)
AX_CHECK_OPENSSL
CFLAGS="$CFLAGS $OPENSSL_INCLUDES"
LIBS="$LIBS $OPENSSL_LIBS"
LDFLAGS="$LDFLAGS $OPENSSL_LDFLAGS"
AC_MSG_CHECKING(for res_getservers)
AC_TRY_COMPILE([
#include <sys/types.h>
#include <netinet/in.h>
#include <arpa/nameser.h>
#include <resolv.h>
],
[
union res_sockaddr_union servers[10];
res_getservers(&_res, &servers, sizeof(servers)/sizeof(*servers));
],
[
AC_DEFINE([HAVE_RES_GETSERVERS], [1],
	 [Define to 1 if you have the `res_getservers' function.])
AC_MSG_RESULT(yes)
],
[AC_MSG_RESULT(no)])
AC_MSG_CHECKING(for struct sockaddr_in.sin_len)
AC_TRY_COMPILE([
#include <sys/socket.h>
#include <netinet/in.h>
],
[
struct sockaddr_in sin;
sin.sin_len = 0;
],
[
AC_DEFINE([HAVE_SIN_LEN], [1],
	 [Define to 1 struct sockaddr_in has sin_len.])
AC_MSG_RESULT(yes)
],
[AC_MSG_RESULT(no)])
AC_MSG_CHECKING(for struct sockaddr_in6.sin6_len)
AC_TRY_COMPILE([
#include <sys/socket.h>
#include <netinet/in.h>
],
[
struct sockaddr_in6 sin6;
sin6.sin6_len = 0;
],
[
AC_DEFINE([HAVE_SIN6_LEN], [1],
	 [Define to 1 struct sockaddr_in6 has sin6_len.])
AC_MSG_RESULT(yes)
],
[AC_MSG_RESULT(no)])
AC_OUTPUT
