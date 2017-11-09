# This directory runs all of the CBMC tests, apart from those tests
# specified in the "exclude" file, using CBMC with the --paths flag.
# CBMC tests are copied into a "tmp" directory, which git ignores, and
# run from there. Any path-exploration-specific tests should also be
# copied into that directory when they are written.

default: tests.log

# CBMC test directories, not including files mentioned in the file "exclude"
REL_PATH_DIRS=$(shell (ls -1x ../cbmc             \
	                     && cat exclude             \
	                     && echo "Makefile"         \
	                     && echo "CMakeLists.txt"   \
	                     && echo "tests.log")       \
	                   | sort | uniq -u)
CBMC_PATH_DIRS=$(patsubst %,../cbmc/%,$(REL_PATH_DIRS))

CBMC ?=../../../../src/cbmc/cbmc

tests.log: ../test.pl
	@mkdir -p tmp
	@cp -r $(CBMC_PATH_DIRS) tmp
	@cd tmp && if ! ../../test.pl -c "$(CBMC) --paths --path-queue local-advance" ; then \
	  ../../failed-tests-printer.pl ; \
	  exit 1 ; \
	fi

show:
	@for dir in tmp/*; do \
	  if [ -d "$$dir" ]; then \
	    vim -o "$$dir/*.c" "$$dir/*.out"; \
	  fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
	$(RM) -r tmp
