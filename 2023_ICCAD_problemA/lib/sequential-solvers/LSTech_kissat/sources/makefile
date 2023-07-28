all:
	$(MAKE) -C "/export/starexec/sandbox/solver/sources/build"
kissat:
	$(MAKE) -C "/export/starexec/sandbox/solver/sources/build" kissat
tissat:
	$(MAKE) -C "/export/starexec/sandbox/solver/sources/build" tissat
clean:
	rm -f "/export/starexec/sandbox/solver/sources"/makefile
	-$(MAKE) -C "/export/starexec/sandbox/solver/sources/build" clean
	rm -rf "/export/starexec/sandbox/solver/sources/build"
coverage:
	$(MAKE) -C "/export/starexec/sandbox/solver/sources/build" coverage
indent:
	$(MAKE) -C "/export/starexec/sandbox/solver/sources/build" indent
test:
	$(MAKE) -C "/export/starexec/sandbox/solver/sources/build" test
.PHONY: all clean coverage indent kissat test tissat
