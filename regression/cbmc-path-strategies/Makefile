default: tests.log

test: gen-desc
	@../test.pl -p -c "../../../src/cbmc/cbmc --verbosity 10"

tests.log: ../test.pl gen-desc
	@../test.pl -p -c "../../../src/cbmc/cbmc --verbosity 10"

gen-desc:
	@../../scripts/make_descs.py

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.desc' -execdir $(RM) '{}' \;
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
