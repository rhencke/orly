.PHONY: build test clean

build:
	rocqc -R theories Hello theories/Hello.v

test: build

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux
