.PHONY: build test clean

build:
	rocq compile -Q theories Hello theories/Hello.v

test: build

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux
