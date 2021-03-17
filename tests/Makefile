.PHONY: testbin test clean clobber

SYSTEMV_TEST_U ?= --interactive


test:
	./build/exec/runtests $(SYSTEMV_BIN) --timing $(SYSTEMV_TEST_U) --only $(SYSTEMV_TEST_O)

testbin:
	idris2 --build tests.ipkg

clean:
	idris2 --clean tests.ipkg

clobber: clean
	rm -rf build
