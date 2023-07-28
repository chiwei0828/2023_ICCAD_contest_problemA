all:
	$(MAKE) -C "/export/starexec/sandbox/solver/build"
kissat:
	$(MAKE) -C "/export/starexec/sandbox/solver/build" kissat
tissat:
	$(MAKE) -C "/export/starexec/sandbox/solver/build" tissat
clean:
	rm -f "/export/starexec/sandbox/solver"/makefile
	-$(MAKE) -C "/export/starexec/sandbox/solver/build" clean
	rm -rf "/export/starexec/sandbox/solver/build"
coverage:
	$(MAKE) -C "/export/starexec/sandbox/solver/build" coverage
indent:
	$(MAKE) -C "/export/starexec/sandbox/solver/build" indent
test:
	$(MAKE) -C "/export/starexec/sandbox/solver/build" test
.PHONY: all clean coverage indent kissat test tissat
