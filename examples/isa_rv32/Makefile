OCB = ocamlbuild -use-ocamlfind
TARGET = "BinaryToKamiPgm"

all: native

clean:
	$(OCB) -clean

native:
	$(OCB) $(TARGET).native

byte:
	$(OCB) $(TARGET).byte

debug:
	$(OCB) -tag debug $(TARGET).native

.PHONY: all clean native byte debug
