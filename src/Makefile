
PYTHON = python3.6


difference_structures:
	$(PYTHON) -m unittest -v difference_structures_test.py

mclock:
	$(PYTHON) -m unittest -v mclock_test.py

muk:
	$(PYTHON) -m unittest -v microkanren_test.py

sexp:
	$(PYTHON) -m unittest -v sexp_test.py

reasoned_schemer:
	$(PYTHON) -m unittest -v reasonedschemer_test.py

suite: sexp muk reasoned_schemer mclock difference_structures
