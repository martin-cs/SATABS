all: satabs tan boppo

.PHONY: satabs
.PHONY: tan
.PHONY: termination
.PHONY: clean
.PHONY: bplang
.PHONY: boppo

satabs:
	$(MAKE) -C satabs

termination:
	$(MAKE) -C termination

tan: satabs termination
	$(MAKE) -C tan

bplang:
	$(MAKE) -C bplang

boppo: bplang
	$(MAKE) -C boppo

clean: 
	$(MAKE) clean -C satabs
	$(MAKE) clean -C termination
	$(MAKE) clean -C tan
	$(MAKE) clean -C bplang
	$(MAKE) clean -C boppo

