## Process this file with automake to produce Makefile.in

lib_LTLIBRARIES = libpynac.la
libpynac_la_SOURCES = add.cpp archive.cpp assume.cpp basic.cpp \
  constant.cpp context.cpp ex.cpp expair.cpp exprseq.cpp \
  fderivative.cpp function_info.cpp \
  infinity.cpp inifcns.cpp inifcns_trig.cpp inifcns_zeta.cpp \
  inifcns_hyperb.cpp inifcns_trans.cpp inifcns_gamma.cpp inifcns_nstdsums.cpp \
  inifcns_orthopoly.cpp inifcns_hyperg.cpp inifcns_comb.cpp \
  lst.cpp matrix.cpp mpoly-giac.cpp mpoly-ginac.cpp \
  mpoly-singular.cpp mpoly.cpp mul.cpp normal.cpp numeric.cpp \
  operators.cpp py_funcs.cpp registrar.cpp relational.cpp \
  remember.cpp \
  pseries.cpp print.cpp symbol.cpp upoly-ginac.cpp \
  utils.cpp wildcard.cpp templates.cpp infoflagbase.cpp sum.cpp \
  remember.h tostring.h utils.h compiler.h order.cpp useries.cpp

#The -no-undefined breaks Pynac on OS X 10.4.  See #9135
if CYGWIN
libpynac_la_LDFLAGS = -version-info $(LT_VERSION_INFO) -no-undefined
else
libpynac_la_LDFLAGS = -version-info $(LT_VERSION_INFO)
endif
libpynac_la_CPPFLAGS = $(PYTHON_CPPFLAGS) @FACTORY_CFLAGS@ -Wall -Wextra -Wshadow -Wnon-virtual-dtor -Wno-unused-parameter -Wno-unknown-pragmas -Wno-parentheses-equality

noinst_LTLIBRARIES = libpynac17.la
libpynac17_la_SOURCES = expairseq.cpp cmatcher.cpp power.cpp function.cpp
libpynac17_la_CPPFLAGS = $(PYTHON_CPPFLAGS) --std=c++17

libpynac_la_LIBADD = $(PYTHON_LDFLAGS) $(LIBS) libpynac17.la @FACTORY_LIBS@ $(LIBGIAC)

ginacincludedir = $(includedir)/pynac
ginacinclude_HEADERS = ginac.h py_funcs.h add.h archive.h assertion.h \
  basic.h class_info.h cmatcher.h constant.h container.h context.h \
  ex.h ex_utils.h expair.h expairseq.h exprseq.h \
  fderivative.h flags.h function.h \
  inifcns.h infinity.h lst.h matrix.h mpoly.h mul.h \
  normal.h numeric.h operators.h \
  power.h print.h pseries.h ptr.h registrar.h relational.h extern_templates.h \
  symbol.h version.h wildcard.h order.h templates.h \
  infoflagbase.h assume.h upoly.h useries.h useries-flint.h sum.h

EXTRA_DIST = version.h.in
