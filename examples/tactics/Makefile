FSTAR_HOME=../..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib
EXCLUDED_FSTAR_FILES=Launch.fst CanonCommSemiring.fst \
		     Test.Math.Lemmas.fst CanonDeep.fst Typeclasses.fst
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all #stringprintertest

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

launch: Launch.fst
	$(FSTAR) --unsafe_tactic_exec $^

ifdef KREMLIN_HOME
stringprintertest: $(CACHE_DIR)
	 [ ! -f $(KREMLIN_HOME)/krml ] || [ ! -x $(KREMLIN_HOME)/krml ] || $(KREMLIN_HOME)/krml -tmpdir stringprintertest -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
else
stringprintertest:
endif

canon-native:
	$(FSTAR) --cache_checked_modules --codegen Plugin --extract 'CanonCommMonoid CanonCommSwaps' CanonCommMonoid.fst
	rm -f ./CanonCommMonoid.cmxs
	echo "\nlet _ =\n  FStar_Tactics_Native.register_tactic \"CanonCommMonoid.canon_monoid_aux\"\n    (Prims.parse_int \"16\")\n    (fun psc  ->\n       fun args  ->\n         match args with\n         | (tv_0,_)::(tv_1,_)::args_tail ->\n             (FStar_Tactics_Interpreter.mk_tactic_interpretation_13 true\n                (FStar_Tactics_Native.from_tactic_13 canon_monoid_aux)\n                FStar_Reflection_Embeddings.e_term\n                (FStar_Tactics_Interpreter.e_tactic_1_alt\n                           FStar_Reflection_Embeddings.e_term\n                           FStar_Syntax_Embeddings.e_any)\n                (FStar_Tactics_Interpreter.e_tactic_1_alt\n                           FStar_Syntax_Embeddings.e_any\n                           FStar_Reflection_Embeddings.e_term)\n                FStar_Reflection_Embeddings.e_term\n                FStar_Reflection_Embeddings.e_term\n                FStar_Reflection_Embeddings.e_term\n                FStar_Syntax_Embeddings.e_any\n                FStar_Reflection_Embeddings.e_term\n                (FStar_Tactics_Interpreter.e_tactic_1_alt\n                           FStar_Syntax_Embeddings.e_any\n                           FStar_Reflection_Embeddings.e_term)\n                (FStar_Tactics_Interpreter.e_tactic_1_alt\n                           FStar_Reflection_Embeddings.e_term\n                           FStar_Syntax_Embeddings.e_any)\n                FStar_Syntax_Embeddings.e_any\n                FStar_Reflection_Embeddings.e_term\n                FStar_Reflection_Embeddings.e_term\n                FStar_Syntax_Embeddings.e_unit\n                (FStar_Ident.lid_of_str \"CanonCommMonoid.canon_monoid_aux\")\n                psc) args_tail\n         | _ -> failwith \"arity mismatch\")" >> CanonCommMonoid.ml
	env OCAMLPATH="../../bin/" ocamlfind ocamlopt -shared -I . -package fstar-tactics-lib -o ./CanonCommMonoid.cmxs ./CanonCommSwaps.ml ./CanonCommMonoid.ml
	$(FSTAR) --load CanonCommMonoid CanonCommMonoid.fst
