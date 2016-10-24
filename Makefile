OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
OCAMLYACC=ocamlyacc
OCAMLLEX=ocamllex
OCAMLFIND=ocamlfind
INCLUDES=
OCAMLFLAGS=$(INCLUDES) extLib.cma unix.cma nums.cma str.cma cil.cma dynlink.cma zip.cma menhirLib.cmo why3.cma -g
OCAMLOPTFLAGS=$(INCLUDES) extLib.cmxa unix.cmxa nums.cmxa str.cmxa cil.cmxa dynlink.cmxa zip.cmxa menhirLib.cmx why3.cmxa #-p

INCLUDES+= -I $(shell $(OCAMLFIND) query cil)
INCLUDES+= -I $(shell $(OCAMLFIND) query extlib)
INCLUDES+= -I $(shell $(OCAMLFIND) query why3)
INCLUDES+= -I $(shell $(OCAMLFIND) query zip)
INCLUDES+= -I $(shell $(OCAMLFIND) query menhirLib)
INCLUDES+= -I $(shell $(OCAMLFIND) query extlib)
# INCLUDES+= -I $(shell pwd)/why3api

OBJS=ftree.cmo fparser.cmo flexer.cmo why3api.cmo utils.cmo	\
	polynomial.cmo formula.cmo why3util.cmo vc.cmo vcg.cmo	\
	vctrans.cmo print.cmo taskgen.cmo verifier.cmo		\
	interactive.cmo main.cmo

PROGNAME=a
TESTDIR=output/$(shell date +%y%m%d/%H%M%S)
PROGFLAGS= --warning --print-task-style short

DEPEND += flexer.ml fparser.ml

opt: $(PROGNAME).opt

byte: $(PROGNAME).byte

all: byte opt

$(PROGNAME).byte: $(DEPEND) $(OBJS)
	$(OCAMLC) $(OCAMLFLAGS) -o $@ $(OBJS)

$(PROGNAME).opt: $(DEPEND) $(subst .cmo,.cmx,$(OBJS))
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $@ $(subst .cmo,.cmx,$(OBJS))

run: $(PROGNAME)
#	mkdir -p $(TESTDIR)
	- ocamlrun -b $(PROGNAME) samples/count_up.cu count_up --output $(TESTDIR)/count_up.why
	- ocamlrun -b $(PROGNAME) samples/vectorAdd.cu vectorAdd --output $(TESTDIR)/vectorAdd.why
	- ocamlrun -b $(PROGNAME) samples/vectorAdd.cu vectorAdd1 --output $(TESTDIR)/vectorAdd1.why
#	- ocamlrun -b $(PROGNAME) samples/matrixMul.cu matrixMulCUDA > $(TESTDIR)/matrixMulCUDA.why

wc:
	ocamlwc ftree.ml fparser.mly flexer.mll why3api.ml utils.ml	\
		polynomial.ml formula.ml why3util.ml vc.ml vcg.ml	\
		vctrans.ml print.ml taskgen.ml verifier.ml		\
		interactive.ml main.ml

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

fparser.ml fparser.mli: fparser.mly
	@rm -f $@
	$(OCAMLYACC) -v $<
#	@chmod -w $@

flexer.ml: flexer.mll
	@rm -f $@
	$(OCAMLLEX) $<
	@chmod -w $@

# Clean up
clean:
	rm -f $(PROGNAME)
	rm -f *.cm[ioxt] *.cmti *.o *~ fparser.ml fparser.mli parser.output\
		flexer.ml .depend

# Dependencies
depend:: $(DEPEND)
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

-include .depend

-include Makefile.debug
