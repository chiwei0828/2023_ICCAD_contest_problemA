all:
	$(MAKE) -C "/home/zhangxd/solvers/rdpaper/kissat_mab/build"
kissat:
	$(MAKE) -C "/home/zhangxd/solvers/rdpaper/kissat_mab/build" kissat
tissat:
	$(MAKE) -C "/home/zhangxd/solvers/rdpaper/kissat_mab/build" tissat
clean:
	rm -f "/home/zhangxd/solvers/rdpaper/kissat_mab"/makefile
	-$(MAKE) -C "/home/zhangxd/solvers/rdpaper/kissat_mab/build" clean
	rm -rf "/home/zhangxd/solvers/rdpaper/kissat_mab/build"
coverage:
	$(MAKE) -C "/home/zhangxd/solvers/rdpaper/kissat_mab/build" coverage
indent:
	$(MAKE) -C "/home/zhangxd/solvers/rdpaper/kissat_mab/build" indent
test:
	$(MAKE) -C "/home/zhangxd/solvers/rdpaper/kissat_mab/build" test
.PHONY: all clean coverage indent kissat test tissat
