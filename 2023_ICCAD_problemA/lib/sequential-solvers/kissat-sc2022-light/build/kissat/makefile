all:
	$(MAKE) -C "/export/starexec/sandbox2/solver/build/kissat/build"
kissat:
	$(MAKE) -C "/export/starexec/sandbox2/solver/build/kissat/build" kissat
tissat:
	$(MAKE) -C "/export/starexec/sandbox2/solver/build/kissat/build" tissat
clean:
	rm -f "/export/starexec/sandbox2/solver/build/kissat"/makefile
	-$(MAKE) -C "/export/starexec/sandbox2/solver/build/kissat/build" clean
	rm -rf "/export/starexec/sandbox2/solver/build/kissat/build"
coverage:
	$(MAKE) -C "/export/starexec/sandbox2/solver/build/kissat/build" coverage
indent:
	$(MAKE) -C "/export/starexec/sandbox2/solver/build/kissat/build" indent
test:
	$(MAKE) -C "/export/starexec/sandbox2/solver/build/kissat/build" test
.PHONY: all clean coverage indent kissat test tissat
