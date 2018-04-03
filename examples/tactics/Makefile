FSTAR_HOME=../..
include ../Makefile.include

.PHONY: neg stringprintertest-ver stringprintertest stringprinter

all:	Apply.uver		\
	ApplyLemma.uver		\
	Canon.uver		\
	CanonMonoid.uver	\
	CanonCommMonoid.uver	\
	CanonCommMonoidSimple.uver\
	EExists.uver		\
	Arith.uver		\
	Pruning.uver		\
	Cut.uver		\
	Fail.uver		\
	MApply.uver		\
	Clear.uver		\
	Cases.uver		\
	VC.uver			\
	Div.uver		\
	Change.uver		\
	Antiquote.uver		\
	Tutorial.uver		\
	Fresh.uver		\
	SolveThen.uver		\
	Splice.uver		\
	Syntax.uver		\
	NormBinderType.uver	\
	Normalization.uver	\
	GRewrite.uver		\
	VQuote.uver		\
	Rename.uver		\
	Imp.uver		\
	Inlining.uver		\
	UserTactics.uver	\
	Logic.uver		\
	DependentSynth.uver	\
	NatPos.uver		\
	Unfold.uver		\
	Trace.uver		\
	Bug1252.uver		\
	Bug1270.uver		\
	Bug1272.uver		\
	Bug1299.uver		\
	Admit.uver		\
	Nest.uver		\
	TestBV.uver		\
	Map.uver		\
	Map.OpaqueToSMT.uver	\
	Map.OpaqueToSMT.Test.uver	\
	Synthesis.uver		\
	Printers.uver		\
	Setopts.uver		\
	Simplifier.uver		\
	Neg.uver		\
	Sequences.uver		\
	Caller.uver		\
	Retype.uver		\
	Pose.uver		\
	Unify.uver		\
	UnitTests.uver		\
	MetaCoq.uver		\
	stringprinter \
	Tautology.uver		\
	Rewrite.Monoid.uver     \
	neg
	# launch			\

launch: Launch.fst
	$(FSTAR) --unsafe_tactic_exec $^

neg:
	$(MAKE) -C neg

ifdef KREMLIN_HOME
StringPrinter.RecC.uver StringPrinterTest.Aux.uver StringPrinterTest.uver: OTHERFLAGS+=--include $(KREMLIN_HOME)/kremlib
stringprintertest-ver: StringPrinter.RecC.uver StringPrinterTest.Aux.uver StringPrinterTest.uver
stringprintertest:
	 [ ! -f $(KREMLIN_HOME)/krml ] || [ ! -x $(KREMLIN_HOME)/krml ] || $(KREMLIN_HOME)/krml -tmpdir stringprintertest -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
else
stringprintertest-ver:
stringprintertest:
endif

stringprinter: \
	StringPrinter.Base.uver \
	StringPrinter.Rec.uver \
	stringprintertest-ver \
	stringprintertest

canon-native:
	$(FSTAR) --cache_checked_modules --codegen Plugin --extract 'CanonCommMonoid CanonCommSwaps' CanonCommMonoid.fst
	rm -f ./CanonCommMonoid.cmxs
	echo -e "\nlet _ =\n  FStar_Tactics_Native.register_tactic \"CanonCommMonoid.canon_monoid_aux\"\n    (Prims.parse_int \"16\")\n    (fun psc  ->\n       fun args  ->\n         match args with\n         | (tv_0,_)::(tv_1,_)::args_tail ->\n             (FStar_Tactics_Interpreter.mk_tactic_interpretation_13 true\n                (FStar_Tactics_Native.from_tactic_13 canon_monoid_aux)\n                FStar_Reflection_Embeddings.unembed_term\n                (fun t ->\n                  match (FStar_Tactics_Interpreter.unembed_tactic_1_alt\n                           FStar_Reflection_Embeddings.embed_term\n                           FStar_Syntax_Embeddings.unembed_any) t with\n                  | None -> None\n                  | Some f -> Some (fun x -> (f x).FStar_Tactics_Basic.tac_f))\n                (fun t ->\n                  match (FStar_Tactics_Interpreter.unembed_tactic_1_alt\n                           FStar_Syntax_Embeddings.embed_any\n                           FStar_Reflection_Embeddings.unembed_term) t with\n                  | None -> None\n                  | Some f -> Some (fun x -> (f x).FStar_Tactics_Basic.tac_f))\n                FStar_Reflection_Embeddings.unembed_term\n                FStar_Reflection_Embeddings.unembed_term\n                FStar_Reflection_Embeddings.unembed_term\n                FStar_Syntax_Embeddings.unembed_any\n                FStar_Reflection_Embeddings.unembed_term\n                (fun t ->\n                  match (FStar_Tactics_Interpreter.unembed_tactic_1_alt\n                           FStar_Syntax_Embeddings.embed_any\n                           FStar_Reflection_Embeddings.unembed_term) t with\n                  | None -> None\n                  | Some f -> Some (fun x -> (f x).FStar_Tactics_Basic.tac_f))\n                (fun t ->\n                  match (FStar_Tactics_Interpreter.unembed_tactic_1_alt\n                           FStar_Reflection_Embeddings.embed_term\n                           FStar_Syntax_Embeddings.unembed_any) t with\n                  | None -> None\n                  | Some f -> Some (fun x -> (f x).FStar_Tactics_Basic.tac_f))\n                FStar_Syntax_Embeddings.unembed_any\n                FStar_Reflection_Embeddings.unembed_term\n                FStar_Reflection_Embeddings.unembed_term\n                FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit\n                (FStar_Ident.lid_of_str \"CanonCommMonoid.canon_monoid_aux\")\n                psc) args_tail\n         | _ -> failwith \"arity mismatch\")\n" >> CanonCommMonoid.ml
	env OCAMLPATH="../../bin/" ocamlfind ocamlopt -shared -I . -package fstar-tactics-lib -o ./CanonCommMonoid.cmxs ./CanonCommSwaps.ml ./CanonCommMonoid.ml
	$(FSTAR) --load CanonCommMonoid CanonCommMonoid.fst
