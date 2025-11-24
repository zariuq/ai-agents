.PHONY: bridge-test fuzz-corpus fixture-test

bridge-test: fixture-test
	@echo "Running Full Bridge Test Suite..."
	python3 tests/test_bridge_full.py --no-kernel

fixture-test:
	@echo "Running Fixture Tests..."
	python3 tests/test_bridge_full.py --no-kernel tests/fixtures/tactics/*.mg

fuzz-corpus:
	@echo "Generating Fuzz Corpus..."
	python3 tools/gen_mg.py tests/fuzz 20
	python3 tests/test_bridge_full.py --no-kernel tests/fuzz/*.mg