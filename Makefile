PYTHON ?= python3

.PHONY: verify test-tooling
verify:
	$(PYTHON) scripts/verify.py

test-tooling:
	$(PYTHON) -m unittest discover -s scripts -p 'test_*.py' -v
