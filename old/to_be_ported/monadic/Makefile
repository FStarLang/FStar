
PASSING= \
    ex0-0.fst \
    ex0-1.fst \
    ex0-2.fst \
    ex0-3.fst \
    ex0-4.fst \
    ex1-0.fst \
    ex1-1.fst \
    ex1-2.fst \
    ex1-3.fst \
    ex1.fst \
    ex2.fst \
    ex3.fst \
    ex6.fst \
    ex9.fst \
    ex10.fst \
    ex11.fst \
    ex12.fst \
    ex15.fst \
    ex15-1.fst \
    ex15-2.fst \
    ex17.fst \
    sparseArray0.fst \
    sparseArray1.fst


SHOULD_BE_PASSING= 
    # ex16-2.fst
    # ex16.fst \
    # ex16-1.fst \
    testref.fst \

FAILING= 
ALWAYS_FAILING= \
    ex4.fst \
    ex5.fst \
    ex5.1.fst \
    ex7.fst \
    ex8.fst
REFINED=ex1-refined ex12-refined ex13-refined
INFERRED=ex12-inferred
#ex2.refined
OUT=out

# JS2ML
JS2ML=../js2ml/js-to-fsharp-examples
JS2ML_PASSING=block-test.js func-app-test.js function-recursive-test.js \
function-test.js if-test.js let-test.js object-method-test.js \
object-test.js ops-test.js return-test.js seq-test.js basic-loop-test.js \
break-test.js do-while-test.js for-test.js loop-in-function.js \
return-from-loop-test.js while-break-test.js

all: log ex pldi10

log:
	mkdir -p log

wcex: 
	wc -l $(PASSING) compose.fst twice.fst addtwo.fst 
wcall: 
	wc -l $(PASSING) compose.fst twice.fst addtwo.fst authac.fst iflow.fst automaton.fst

ex: 
	fstar --silent --skip_translation --z3encode_binders --generalize_monadic_types  --dtencoding --z3exe --odir log --prims prims-selupd.fst $(PASSING) compose.fst twice.fst addtwo.fst

passing: 
	cat $(PASSING) | wc -l
 # compose.fst addtwo.fst

should:
	cat $(SHOULD_BE_PASSING)

failing:
	cat $(FAILING)

refined: $(addsuffix .checked, $(REFINED))

inferred: $(addsuffix .checked, $(INFERRED))

test: $(OUT) clean
	@echo "PASSING:"
	@for f in $(addsuffix -inferred, $(basename $(PASSING))); do \
            echo -n "$$f "; \
            make $$f.checked > $(OUT)/$$f.out 2> $(OUT)/$$f.err; \
            if [ $$? -ne 0 ]; then echo "FAILED"; else echo "ok"; fi; \
        done
	make higherorder > $(OUT)/higherorder.out 2> $(OUT)/higherorder.err
	if [ $$? -ne 0 ]; then echo "FAILED"; else echo "ok"; fi
	@echo ""
	@echo "SHOULD BE PASSING:"
	@for f in $(addsuffix -inferred, $(basename $(SHOULD_BE_PASSING))); do \
            echo -n "$$f "; \
            make $$f.checked > $(OUT)/$$f.out 2> $(OUT)/$$f.err; \
            if [ $$? -ne 0 ]; then echo "FAILED"; else echo "PASSED"; fi; \
        done
	@echo ""
	@echo "FAILING:"
	@for f in $(addsuffix -inferred, $(basename $(FAILING))); do \
            echo -n "$$f "; \
            make $$f.checked > $(OUT)/$$f.out 2> $(OUT)/$$f.err; \
            if [ $$? -ne 0 ]; then echo "FAILED"; else echo "PASSED"; fi; \
        done

higherorder:
	fstar --skip_translation --z3encode_binders --generalize_monadic_types  --dtencoding --z3exe --odir log --prims prims-selupd.fst compose.fst twice.fst addtwo.fst

test-refined: $(OUT) clean
	@for f in $(REFINED); do \
            echo -n "$$f "; \
            make $$f.checked > $(OUT)/$$f.out 2> $(OUT)/$$f.err; \
            if [ $$? -ne 0 ]; then echo "FAILED"; else echo "PASSED"; fi; \
        done

list:
	@echo "PASSING:"
	@for f in $(basename $(PASSING)); do echo $$f; done
	@echo ""
	@echo "SHOULD BE PASSING:"
	@for f in $(basename $(SHOULD_BE_PASSING)); do echo $$f; done

js: $(OUT) clean
	@for f in $(JS2ML_PASSING); do \
            echo -n "$$f "; \
            make $$f.checked > $(OUT)/$$f.out 2> $(OUT)/$$f.err; \
            if [ $$? -ne 0 ]; then echo "FAILED"; else echo "PASSED"; fi; \
        done

pldi10:
	fstar --z3encode_binders --skip_translation --generalize_monadic_types  --dtencoding --z3exe --odir log authac.fst
	fstar --z3encode_binders --skip_translation --generalize_monadic_types  --dtencoding --z3exe --odir log iflow.fst
	fstar --z3encode_binders --skip_translation --generalize_monadic_types  --dtencoding --z3exe --odir log automaton.fst

out:
	@if [ ! -d $(OUT) ]; then mkdir $(OUT); fi
	@ls -d $(OUT)

clean:
	@rm -rf $(OUT)/*

%-refined.checked: %-refined.fst
	fstar --prims prims-selupd.fst $^

%-inferred.checked: %.fst
	cat $^
	fstar --generalize_monadic_types --skip_translation --dtencoding --z3exe --odir log --prims prims-selupd.fst $^

%.checked: %.fst
	fstar  --trace_err --monadic --prims prims-monadic.fst $^

%.js.checked: $(JS2ML)/%.js.fs
	fstar --monadic --trace_err --prims prims-monadic.fst JSBuiltIns-monadic_old.fst $^ 
	touch $@


.PHONY: out

