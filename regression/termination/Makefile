default: tests.log

test:
	@./test.pl

tests.log: test.pl
	@./test.pl

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/main.c" "$$dir/main.out"; \
		fi; \
	done;
