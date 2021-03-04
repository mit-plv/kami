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

default_target: proc_ext
.PHONY: coq clean install

SUPPRESS_WARN=-arg "-w" -arg "-cannot-define-projection,-implicit-core-hint-db,-notation-overridden"
ALLARGS_NL=-R Kami Kami\n$(SUPPRESS_WARN)\n

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

EXT_VO=Kami/Ext/Extraction.vo
EXT_OCAML_PATH=Kami/Ext/Ocaml
EXT_PROC_BSV=Proc.bsv
EXT_VERILOG_PATH=Kami/Ext/BluespecFrontEnd/verilog

proc_ext: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all $(EXT_VO)
	$(MAKE) -C $(EXT_OCAML_PATH)
	cd $(EXT_OCAML_PATH); ./Main.native -top Proc $(EXT_PROC_BSV)
	$(MAKE) -C $(EXT_VERILOG_PATH)

clean:: Makefile.coq.all Makefile.coq.src
	$(MAKE) -f Makefile.coq.all clean || $(MAKE) -f Makefile.coq.src clean
	rm -f */*.v.d */*.glob */*.vo */*~ *~
	rm -f Makefile.coq.all
	rm -f Makefile.coq.src
	rm -f _CoqProject

install:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all install
