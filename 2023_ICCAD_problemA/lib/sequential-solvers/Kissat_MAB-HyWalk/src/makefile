all:
	$(MAKE) -C "/home/zhengjz/SAT/kissat-hywalk-final/build"
kissat:
	$(MAKE) -C "/home/zhengjz/SAT/kissat-hywalk-final/build" kissat
tissat:
	$(MAKE) -C "/home/zhengjz/SAT/kissat-hywalk-final/build" tissat
clean:
	rm -f "/home/zhengjz/SAT/kissat-hywalk-final"/makefile
	-$(MAKE) -C "/home/zhengjz/SAT/kissat-hywalk-final/build" clean
	rm -rf "/home/zhengjz/SAT/kissat-hywalk-final/build"
coverage:
	$(MAKE) -C "/home/zhengjz/SAT/kissat-hywalk-final/build" coverage
indent:
	$(MAKE) -C "/home/zhengjz/SAT/kissat-hywalk-final/build" indent
test:
	$(MAKE) -C "/home/zhengjz/SAT/kissat-hywalk-final/build" test
.PHONY: all clean coverage indent kissat test tissat
