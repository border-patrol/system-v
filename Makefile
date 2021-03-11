all: systemv test

systemv:
	idris2 --build systemv.ipkg

clobber: clean
	make -C tests clobber
	rm -rf build/

clean:
	idris2 --clean systemv.ipkg
	make -C tests clean


export SYSTEMV_TEST_JUST
export SYSTEMV_TEST_INTERACTIVE
export SYSTEMV_BIN=../../build/exec/unnamed

test:
	make -C tests testbin
	make -C tests test

.PHONY: clobber clean test systemv
