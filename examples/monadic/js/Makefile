FSTAR=fstar --silent --skip_translation --dtencoding --odir log --z3exe --skip_logic_function_typing_triggers
LIBS=jsver.fst dom.fst

all: assign-test.ver HoverMagnifier.ver Typograf.ver Facepalm.ver

lib: 
	$(FSTAR) $(LIBS)

%.ver: %.js
	fstar --skip_logic_function_typing_triggers --silent --delay_monadic_unification --z3encode_binders --monadic_conv --skip_translation --dtencoding --odir log --z3exe --prims prims.fst jsver-labeled.fst dom.fst $^

%.annot.ver: %.annot.fst
	fstar --z3encode_binders --delay_monadic_unification --monadic_conv --skip_translation --dtencoding --odir log --z3exe --prims prims.fst jsver-labeled.fst dom.fst $^

# assign-test:
# 	$(FSTAR) $(LIBS) assign-test.js

# magnifier:
# 	$(FSTAR) $(LIBS) HoverMagnifier.js

# typograf:
# 	fstar --skip_translation --prims primsjs.fst --monadic Typograf.js

# facepalm:
# 	fstar --skip_translation --prims primsjs.fst --monadic Facepalm.js
