.PHONY: testbin test clean clobber

export SYSTEMV_TEST_JUST
export SYSTEMV_TEST_INTERACTIVE
export SYSTEMV_BIN=../../build/exec/systemv


test:
	./build/exec/runtests $(SYSTEMV_BIN) --timing $(SYSTEMV_TEST_INTERACTIVE) --only $(SYSTEMV_TEST_JUST)

testbin:
	idris2 --build tests.ipkg

clean:
	idris2 --clean tests.ipkg

clobber: clean
	rm -rf build
