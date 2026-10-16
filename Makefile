.PHONY: all clean examples extraction FORCE
.SUFFIXES:

all: Makefile.rocq
	+$(MAKE) -f Makefile.rocq all

clean: Makefile.rocq clean_extraction clean_examples
	+$(MAKE) -f Makefile.rocq cleanall
	rm -rf Makefile.rocq Makefile.rocq.conf

deepclean: clean
	find -name '*.vo' -or -name '*.vos' -or -name '*.vok' -or -name '*.glob' -or -name 'lia.cache' -or -name '*.aux' | while read F; do rm "$$F"; done

examples: Makefile.examples.rocq all
	+$(MAKE) -f Makefile.examples.rocq all

clean_examples: Makefile.examples.rocq
	+$(MAKE) -f Makefile.examples.rocq cleanall
	rm -rf Makefile.examples.rocq Makefile.examples.rocq.conf src/*.cmi src/*.cmx src/*.o

clean_extraction:
	rm -rf ./extraction ./reversec ./reversec.depend ./vendor/CompCert-free/*.cmi ./vendor/CompCert-free/*.cmx ./vendor/CompCert-free/*.o ./vendor/CompCert-nonfree/*.cmi ./vendor/CompCert-nonfree/*.cmx ./vendor/CompCert-nonfree/*.o build/

Makefile.rocq Makefile.rocq.conf: _RocqProject
	coq_makefile -f _RocqProject -o Makefile.rocq

Makefile.examples.rocq Makefile.examples.rocq.conf: _RocqExamples
	coq_makefile -f $< -o Makefile.examples.rocq

extraction: extraction/STAMP

extraction/STAMP: Makefile.rocq Makefile.examples.rocq examples/Reverse/ReverseReify.vo examples/Reverse/ReverseExtraction.v
	rocq repl -R theories GallinaC -R examples GallinaC.Examples -batch -load-vernac-source examples/Reverse/ReverseExtraction.v
	touch extraction/STAMP

theories/%.vo: Makefile.rocq FORCE
	+$(MAKE) -f Makefile.rocq $@

examples/%.vo: Makefile.examples.rocq FORCE
	+$(MAKE) -f Makefile.examples.rocq $@

INCLUDE_EXTRACTION = $(addprefix -I , $(wildcard ./extraction))

%.cmi: %.mli
	ocamlopt -g -c $< $(INCLUDE_EXTRACTION) -I ./src -I ./vendor/CompCert-free -I ./vendor/CompCert-nonfree -o $@

%.cmx: %.ml
	ocamlopt -g -warn-error +58 -w -20 -c $< $(INCLUDE_EXTRACTION) -I ./src -I ./vendor/CompCert-free -I ./vendor/CompCert-nonfree -o $@

MLs = $(wildcard ./extraction/*.ml ./extraction)
CMIs = $(MLIs:.mli=.cmi)
CMXs = $(MLs:.ml=.cmx)

OCAMLDEP = ocamldep $(INCLUDE_EXTRACTION) \
	-I ./src -I ./vendor/CompCert-free -I ./vendor/CompCert-nonfree \
	$(wildcard ./src/*.ml) $(wildcard ./src/*.mli) \
	$(wildcard ./vendor/CompCert-free/*.ml) $(wildcard ./vendor/CompCert-free/*.mli) \
	$(wildcard ./vendor/CompCert-nonfree/*.ml) $(wildcard ./vendor/CompCert-nonfree/*.mli) \
	$(wildcard ./extraction/*.mli) $(wildcard ./extraction/*.ml)

REVERSEC_DEPS = $(shell $(OCAMLDEP) -sort | sed -e 's/[^ ]*.mli //g' | sed -e 's/\.ml/.cmx/g')

OCAML_LIB_PATH := $(shell opam var "ocaml:lib" )

OCAML_LIBS = -I $(OCAML_LIB_PATH) $(OCAML_LIB_PATH)/str.cmxa $(OCAML_LIB_PATH)/unix.cmxa

reversec: extraction reversec.depend $(REVERSEC_DEPS)
	ocamlopt -g $(OCAML_LIBS) $(REVERSEC_DEPS) $(INCLUDE_EXTRACTION) -o reversec

reverse: build/reverse.o build/reverselib.o
	ccomp -v $^ -o $@

build/%.o: src/%.c | build/
	ccomp -c $^ -o $@

build/%.o: build/%.S | build/
	ccomp -c $^ -o $@

build/%.S: %c | build/
	./$^

%/:
	mkdir --parents $@

FORCE:

.SECONDEXPANSION:
reversec.depend: $$(wildcard ./extraction/*.ml ./extraction/*.mli)
		$(OCAMLDEP) > reversec.depend

-include reversec.depend
