all:
	$(MAKE) -C "/home/zhangxd/solvers/kissat-LSinfo/build"
kissat:
	$(MAKE) -C "/home/zhangxd/solvers/kissat-LSinfo/build" kissat
tissat:
	$(MAKE) -C "/home/zhangxd/solvers/kissat-LSinfo/build" tissat
clean:
	rm -f "/home/zhangxd/solvers/kissat-LSinfo"/makefile
	-$(MAKE) -C "/home/zhangxd/solvers/kissat-LSinfo/build" clean
	rm -rf "/home/zhangxd/solvers/kissat-LSinfo/build"
coverage:
	$(MAKE) -C "/home/zhangxd/solvers/kissat-LSinfo/build" coverage
indent:
	$(MAKE) -C "/home/zhangxd/solvers/kissat-LSinfo/build" indent
test:
	$(MAKE) -C "/home/zhangxd/solvers/kissat-LSinfo/build" test
.PHONY: all clean coverage indent kissat test tissat
