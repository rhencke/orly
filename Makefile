.PHONY: build test clean

build:
	coqc -R . Hello Hello.v

test: build

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
