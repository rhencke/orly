.PHONY: build test clean serve

build:
	rocq compile -Q theories Hello theories/Hello.v

test: build

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux

serve:
	python3 -m http.server 8080 --directory docs
