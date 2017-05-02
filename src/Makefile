
PYTHON = python3.6

mclock:
	$(PYTHON) -m unittest -v mclock_test.py
	
sexp:
	$(PYTHON) -m unittest -v sexp_test.py

muk:
	$(PYTHON) -m unittest -v microkanren_test.py

reasoned_schemer:
	$(PYTHON) -m unittest -v reasonedschemer_test.py

tests: sexp muk reasoned_schemer mclock
