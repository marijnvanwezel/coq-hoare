# Derived from https://gitlab.mpi-sws.org/iris/stdpp/-/blob/477562788f8bed058324343c1bac77553cc50b1e/Makefile
# Default target
all: CoqMakefile
	+@$(MAKE) -f CoqMakefile all

clean: CoqMakefile
	+@$(MAKE) -f CoqMakefile clean
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq .lia.cache builddep/*

CoqMakefile: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o CoqMakefile

.PHONY: all clean

