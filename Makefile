SYSTEMV=systemv
IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${SYSTEMV}

all: systemv test

systemv:
	$(IDRIS2) --build systemv.ipkg

systemv-timed:
	$(IDRIS2) --build systemv.ipkg --timing

clobber: clean
	${MAKE} -C tests clobber
	${RM} -rf build/
	${RM} -rf timing.txt

clean:
	$(IDRIS2) --clean systemv.ipkg
	${MAKE} -C tests clean IDRIS2=$(IDRIS2)


test:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 SYSTEMV_BIN=${TARGET} \
			 SYSTEMV_TEST_U=$(SYSTEMV_TEST_U) \
			 SYSTEMV_TEST_O=$(SYSTEMV_TEST_O)

bench: systemv
	${MAKE} -C tests testbin
	$(HYPERFINE) --warmup 10 '${MAKE} -C tests test SYSTEMV_BIN=$(TARGET) SYSTEMV_TEST_U=$(SYSTEMV_TEST_U) SYSTEMV_TEST_O=$(SYSTEMV_TEST_O)'

.PHONY: all clobber clean test systemv bench systemv-timed
