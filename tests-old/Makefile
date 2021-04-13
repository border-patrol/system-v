.PHONY: testbin test clean clobber

SYSTEMV_TEST_U ?= --interactive


test: testbin
	./build/exec/runtests $(SYSTEMV_BIN) --timing $(SYSTEMV_TEST_U) --only $(SYSTEMV_TEST_O)

testbin:
	${IDRIS2} --build tests.ipkg

clean:
	${IDRIS2} --clean tests.ipkg

clobber: clean
	${RM} -rf build
