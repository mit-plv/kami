OCAMLOPT ?= ocamlopt
OCAMLC ?= ocamlc

SRCS := Target.mli Target.ml PP.ml Main.ml

all: native

native: Main.native

byte: Main.byte

Main.native: $(SRCS)
	$(OCAMLOPT) -o $@ $(SRCS)

Main.byte: $(SRCS)
	$(OCAMLC) -o $@ $(SRCS)

Proc.bsv: Main.native Header.bsv
	./Main.native -header Header.bsv $@

clean:
	rm -f Main.native Main.byte Proc.bsv *.cmi *.cmo *.cmx *.o

.PHONY: all native byte clean
