default: tests.log

test:
	@../test.pl -c boppo

tests.log:
	@../test.pl -c boppo

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
