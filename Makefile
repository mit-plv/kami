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
.PHONY: coq clean install

SUPPRESS_WARN=-arg "-w" -arg "-cannot-define-projection,-implicit-core-hint-db,-notation-overridden"

ARGS_NL=-R Kami Kami\n$(SUPPRESS_WARN)\n
DEPFLAGS_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n-Q $(DEPS_DIR)/riscv-coq/src/riscv riscv\n

EXTERNAL_DEPENDENCIES?=

# If we get our dependencies externally, then we should not bind the local versions of things
ifneq ($(EXTERNAL_DEPENDENCIES),1)
ALLARGS_NL=$(DEPFLAGS_NL)$(ARGS_NL)
else
ALLARGS_NL=$(ARGS_NL)
endif

ALLARGS=$(subst \n, ,$(ALLARGS_NL))

_CoqProject:
	printf -- '$(ALLARGS_NL)' > _CoqProject

coq: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: Makefile _CoqProject $(LIBVS) $(VS) $(EXVS) $(EXSVS) $(EXTVS)
	@echo "Generating Makefile"
	@$(COQBIN)coq_makefile -f _CoqProject $(LIBVS) $(VS) $(EXVS) $(EXSVS) $(EXTVS) -o Makefile.coq.all

src: Makefile.coq.src
	$(MAKE) -f Makefile.coq.src

Makefile.coq.src: Makefile _CoqProject $(LIBVS) $(VS)
	@echo "Generating Makefile"
	@$(COQBIN)coq_makefile -f _CoqProject $(LIBVS) $(VS) -o Makefile.coq.src

clean:: Makefile.coq.all Makefile.coq.src
	$(MAKE) -f Makefile.coq.all clean || $(MAKE) -f Makefile.coq.src clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq.all
	rm -f Makefile.coq.src
	rm -f _CoqProject

install:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all install
