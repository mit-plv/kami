IGNORE:=MemCacheInvariants

LIBVS:=$(wildcard lib/*.v)
LIBVS:=$(filter-out $(IGNORE:%=%.v),$(LIBVS))

VS:=$(wildcard src/*.v)
VS:=$(filter-out $(IGNORE:%=%.v),$(VS))

EXVS:=$(wildcard examples/*.v)
EXVS:=$(filter-out $(IGNORE:%=%.v),$(EXVS))

.PHONY: coq clean

LIBARGS := -R lib Lib

ARGS := -R src Lts

EXARGS := -R examples Ex

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	echo Cchefef [$(LIBVS)]
	coq_makefile $(LIBARGS) $(ARGS) $(EXARGS) $(LIBVS) $(VS) $(EXVS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
