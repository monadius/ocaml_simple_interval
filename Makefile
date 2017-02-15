ML = ocamlc
OPT_ML = ocamlopt

SRC=	interval1.mli\
	interval1.ml\
	interval3.mli\
	interval3.ml

OBJ_BYTE0 = $(SRC:.ml=.cmo)
OBJ_BYTE = $(OBJ_BYTE0:.mli=.cmi)

OBJ_NATIVE = $(OBJ_BYTE:.cmo=.cmx)

all: interval.cma interval.cmxa

docs: interval1.mli interval3.mli
	mkdir -p docs
	ocamldoc -d docs -html interval1.mli interval3.mli

interval.cma: $(OBJ_BYTE)
	$(ML) -a -o interval.cma $(OBJ_BYTE0)

interval.cmxa: $(OBJ_NATIVE)
	$(OPT_ML) -a -o interval.cmxa $(OBJ_BYTE0:.cmo=.cmx)

%.cmi : %.mli
	$(ML) -c $^

%.cmo : %.ml
	$(ML) -c $^

%.cmx : %.ml
	$(OPT_ML) -c $^

clean:
	rm -f *.cmo *.cmi *.cmx *.cma *.cmxa *.o *.a
