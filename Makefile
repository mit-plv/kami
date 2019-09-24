IGNORE:=

LIBVS:=$(wildcard Kami/Lib/*.v)
LIBVS:=$(filter-out $(IGNORE:%=%.v),$(LIBVS))

EXSVS:=$(wildcard Kami/Ex/IsaRv32/*.v)
EXSVS:=$(filter-out $(IGNORE:%=%.v),$(EXSVS))

EXVS:=$(wildcard Kami/Ex/*.v)
EXVS:=$(filter-out $(EXSVS) $(IGNORE:%=%.v),$(EXVS))

EXTVS:=$(wildcard Kami/Ext/*.v)
EXTVS:=$(filter-out $(IGNORE:%=%.v),$(EXTVS))

VS:=$(wildcard Kami/*.v)
VS:=$(filter-out $(LIBVS) $(EXSVS) $(EXVS) $(EXTVS) $(IGNORE:%=%.v),$(VS))

PARENT_DIR := $(shell cd .. && (cygpath -m "$$(pwd)" 2>/dev/null || pwd))

DEPS_DIR ?= $(PARENT_DIR)

default_target: coq
.PHONY: coq clean

SUPPRESS_WARN=-arg "-w" -arg "-cannot-define-projection,-implicit-core-hint-db,-notation-overridden"

ARGS_NL=-R Kami Kami\n$(SUPPRESS_WARN)\n
ARGS=$(subst \n, ,$(ARGS_NL))

_CoqProject:
	printf -- '$(ARGS_NL)' > _CoqProject

EXTERNAL_DEPENDENCIES?=

ifneq ($(EXTERNAL_DEPENDENCIES),1)
COQPATH?=$(DEPS_DIR)/coqutil/src:$(DEPS_DIR)/riscv-coq/src
export COQPATH
endif

coq: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: Makefile _CoqProject $(LIBVS) $(VS) $(EXVS) $(EXSVS) $(EXTVS)
	$(COQBIN)coq_makefile -f _CoqProject $(LIBVS) $(VS) $(EXVS) $(EXSVS) $(EXTVS) -o Makefile.coq.all

src: Makefile.coq.src
	$(MAKE) -f Makefile.coq.src

Makefile.coq.src: Makefile _CoqProject $(LIBVS) $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(LIBVS) $(VS) -o Makefile.coq.src

clean:: Makefile.coq.all Makefile.coq.src
	$(MAKE) -f Makefile.coq.all clean || $(MAKE) -f Makefile.coq.src clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq.all
	rm -f Makefile.coq.src
	rm -f _CoqProject
