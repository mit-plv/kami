OCB = ocamlbuild -use-ocamlfind

all: native

clean:
	$(OCB) -clean

native:
	$(OCB) Main.native

byte:
	$(OCB) Main.byte

debug:
	$(OCB) -tag debug Main.native

.PHONY: all clean native byte debug
