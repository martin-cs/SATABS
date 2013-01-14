default: tests.log

test:
	@../../test.pl -c satabs

tests.log: ../test.pl
	@../../test.pl -c satabs

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
