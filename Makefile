all: Makefile Makefile.rocq
	+$(MAKE) -f Makefile.rocq all

clean: Makefile.rocq
	+$(MAKE) -f Makefile.rocq cleanall
	rm -f Makefile.rocq Makefile.rocq.conf *~ */*~ */#*# */.*.aux */.*.cache */.*.d

Makefile.rocq: _RocqProject
	$(COQBIN)coq_makefile -f _RocqProject -o Makefile.rocq

.PHONY: all clean _CoqProject Makefile
