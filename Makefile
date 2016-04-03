
CFLAGS="-ccopt -Wno-discard-qual"
XCDBG="-g -ccopt -g $CFLAGS"
XCOPT="-ccopt -O3 -ccopt -fomit-frame-pointer $CFLAGS"
PATH_TO_Z3A="./z3/src/api/ml/"
PATH_TO_CIL		= $(shell ocamlfind query cil)

OCAMLOPT  = ocamlopt -I $(PATH_TO_CIL) -I $(PATH_TO_Z3A)
OCAMLYACC = ocamlyacc
OCAMLLEX  = ocamllex

PATHGEN_OBJS = \
	cilprinter.cmx \
	utils.cmx \
	paths.cmx \
	main.cmx 

PATHGEN_LIBS = \
	str.cmxa \
	nums.cmxa \
	unix.cmxa \
	cil.cmxa \
	z3.cmxa 

TRANSFORM_OBJS = \
	cilprinter.cmx \
	utils.cmx \
	transform.cmx 

TRANSFORM_LIBS = \
	str.cmxa \
	nums.cmxa \
	unix.cmxa \
	cil.cmxa 

all : pathgen transform

%.cmi: %.mli
	$(OCAMLOPT) -c $(XCOPT) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

%.ml %.mli: %.mly
	$(OCAMLYACC) $< 

%.ml: %.mll
	$(OCAMLLEX) $< 

pathgen: $(PATHGEN_OBJS)
	$(OCAMLOPT) -o pathgen $(PATHGEN_LIBS) $(PATHGEN_OBJS)


transform: $(TRANSFORM_OBJS)
	$(OCAMLOPT) -o transform $(TRANSFORM_LIBS) $(TRANSFORM_OBJS)

clean:
	$(RM) pathgen *.cmi *.cmx *.o
