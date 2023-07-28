CADICALBUILD=/home/ktr/Desktop/D/SC2022/Solvers/hCaD-cadical-rel-1.4.1/build
all:
	$(MAKE) -C "$(CADICALBUILD)"
clean:
	@if [ -d "$(CADICALBUILD)" ]; \
	then \
	  if [ -f "$(CADICALBUILD)"/makefile ]; \
	  then \
	     touch "$(CADICALBUILD)"/build.hpp; \
	     $(MAKE) -C "$(CADICALBUILD)" clean; \
	  fi; \
	  rm -rf "$(CADICALBUILD)"; \
	fi
	rm -f "/home/ktr/Desktop/D/SC2022/Solvers/hCaD-cadical-rel-1.4.1/src/makefile"
	rm -f "/home/ktr/Desktop/D/SC2022/Solvers/hCaD-cadical-rel-1.4.1/makefile"
test:
	$(MAKE) -C "$(CADICALBUILD)" test
cadical:
	$(MAKE) -C "$(CADICALBUILD)" cadical
mobical:
	$(MAKE) -C "$(CADICALBUILD)" mobical
update:
	$(MAKE) -C "$(CADICALBUILD)" update
.PHONY: all cadical clean mobical test update
