.PHONY: build test clean

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

build: CoqMakefile
	$(MAKE) -f CoqMakefile

test: build

clean:
	$(MAKE) -f CoqMakefile clean 2>/dev/null || true
	rm -f CoqMakefile
