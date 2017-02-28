CXXFLAGS=-std=c++11 -O3 -march=native -Wall -Wextra

.PHONY: all
all: td-validate

.PHONY: test
test: td-validate
	./test_td-validate.sh

.PHONY: clean
clean:
	rm -f td-validate
	rm -f td-validate.cpp.gcov td-validate.gcno td-validate.gcda

# Use this to determine code coverage for automated tests
.PHONY: coverage
coverage: CXXFLAGS += -O0 -fprofile-arcs -ftest-coverage
coverage: td-validate.cpp.gcov

td-validate.cpp.gcov: test
	gcov -r td-validate.cpp
