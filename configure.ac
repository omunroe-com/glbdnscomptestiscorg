AC_INIT([DNS Compliance Tester], [1.0], [marka@isc.org], , [https://gitlab.isc.org/isc-projects/DNS-Compliance-Testing])
AM_INIT_AUTOMAKE([subdir-objects no-dist-gzip dist-xz -Wall -Werror])
AM_SILENT_RULES([yes])
AC_PROG_CC_C99
AC_CONFIG_SRCDIR([genreport.c])
AC_CONFIG_HEADER([config.h])
AC_CONFIG_FILES([Makefile])
AC_USE_SYSTEM_EXTENSIONS
AC_CANONICAL_HOST
AC_CHECK_LIB(resolv,res_init)
AC_CHECK_LIB(bind,res_init)
AC_OUTPUT
