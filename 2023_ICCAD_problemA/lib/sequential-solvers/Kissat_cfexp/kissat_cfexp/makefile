all:
	$(MAKE) -C "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build"
kissat:
	$(MAKE) -C "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build" kissat
tissat:
	$(MAKE) -C "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build" tissat
clean:
	rm -f "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat"/makefile
	-$(MAKE) -C "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build" clean
	rm -rf "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build"
coverage:
	$(MAKE) -C "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build" coverage
indent:
	$(MAKE) -C "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build" indent
test:
	$(MAKE) -C "/mnt/e/bishe_code/kissat_sat+cf_with_pwd/kissat+cf+expscore/kissat/build" test
.PHONY: all clean coverage indent kissat test tissat
