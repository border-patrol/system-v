all: systemv test

systemv:
	idris2 --build systemv.ipkg

clobber: clean
	make -C tests clobber
	rm -rf build/

clean:
	idris2 --clean systemv.ipkg
	make -C tests clean


test: systemv
	make -C tests testbin
	make -C tests test SYSTEMV_BIN=../../build/exec/systemv SYSTEMV_TEST_U=$(SYSTEMV_TEST_U) SYSTEMV_TEST_O=$(SYSTEMV_TEST_O)

.PHONY: clobber clean test systemv
