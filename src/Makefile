all: satabs tan

.PHONY: satabs
.PHONY: tan
.PHONY: termination
.PHONY: clean

satabs:
	$(MAKE) -C satabs

termination:
	$(MAKE) -C termination

tan: satabs termination
	$(MAKE) -C tan

clean: 
	$(MAKE) clean -C satabs

