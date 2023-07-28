all:
	$(MAKE) -C "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build"
kissat:
	$(MAKE) -C "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build" kissat
tissat:
	$(MAKE) -C "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build" tissat
clean:
	rm -f "//mnt/e/SATComp22/Kissat_MAB_ESA_Com"/makefile
	-$(MAKE) -C "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build" clean
	rm -rf "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build"
coverage:
	$(MAKE) -C "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build" coverage
indent:
	$(MAKE) -C "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build" indent
test:
	$(MAKE) -C "//mnt/e/SATComp22/Kissat_MAB_ESA_Com/build" test
.PHONY: all clean coverage indent kissat test tissat
