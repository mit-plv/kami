IGNORE:=

LIBVS:=$(wildcard lib/*.v)
LIBVS:=$(filter-out $(IGNORE:%=%.v),$(LIBVS))

VS:=$(wildcard src/*.v)
VS:=$(filter-out $(IGNORE:%=%.v),$(VS))

EXVS:=$(wildcard examples/*.v)
EXVS:=$(filter-out $(IGNORE:%=%.v),$(EXVS))

EXSVS:=$(wildcard examples/isa_rv32/*.v)
EXSVS:=$(filter-out $(IGNORE:%=%.v),$(EXSVS))

EXTVS:=$(wildcard extraction/*.v)
EXTVS:=$(filter-out $(IGNORE:%=%.v),$(EXTVS))

RTLVS:=$(wildcard compilation/*.v)
RTLVS:=$(filter-out $(IGNORE:%=%.v),$(RTLVS))

.PHONY: coq src clean

LIBARGS := -R lib Lib
ARGS := -R src Kami
EXARGS := -R examples Ex
EXTARGS := -R extraction Ext
RTLARGS := -R compilation Compile

coq: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: Makefile $(LIBVS) $(VS) $(EXVS) $(EXSVS) $(EXTVS) $(RTLVS)
	coq_makefile $(LIBARGS) $(ARGS) $(EXARGS) $(EXTARGS) $(RTLARGS) $(LIBVS) $(VS) $(EXVS) $(EXSVS) $(EXTVS) $(RTLVS) -o Makefile.coq.all

src: Makefile.coq.src
	$(MAKE) -f Makefile.coq.src

Makefile.coq.src: Makefile $(LIBVS) $(VS)
	coq_makefile $(LIBARGS) $(ARGS) $(LIBVS) $(VS) -o Makefile.coq.src

clean:: Makefile.coq.all Makefile.coq.src
	$(MAKE) -f Makefile.coq.all clean || $(MAKE) -f Makefile.coq.src clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq.all
	rm -f Makefile.coq.src
