We have a proposal for something you could work on.  Right now, when people write "forall" and "exists" in F*, they can write a Z3 pattern (trigger) using the "{:pattern ...}" syntax ( https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns ).  However, if people don't write these patterns, then Z3 chooses the pattern, and Z3 does not have enough information to choose good patterns.  Dafny faced the same situation a few years ago, and Clement addressed this issue by extending Dafny to automatically choose good forall/exists triggers before sending queries to Z3.  You may be familiar with Dafny's trigger-generation code already; I was looking for commits related to it and I saw that you improved some of the code that Clement wrote:
 
https://github.com/Microsoft/dafny/commit/5eb855972c191ed6323253329fc50ebd1683fdd6
 
We'd like to have a similar automatic pattern generation for F* forall and exists.  It does not have to be as sophisticated as Dafny's, though, at least to start with.  For simplicity, I propose that (at least to start with), we not try to infer conjunctions of patterns {:pattern e1; ...; ek}.  I checked the haclstar repo, and:
•	about 2% of all user-supplied patterns use conjunctions ";".
•	about 20% of all user-supplied patterns use disjunctions "\/".
F* ulib is a little higher (10% with ";" and 30% with "\/"), but I don't think inferring conjunctions ";" is essential to start with.
 
Here's a simple proposal that would get us started.  Roughly, it's "find the smallest terms that contain all the quantifier variables".  In more detail:
•	If a user writes {:pattern ...} on a forall/exists, then F* uses the user-supplied pattern (no automated generation).
•	If a user writes {:nopattern} on a forall/exists, then F* generates no pattern and therefore lets Z3 choose the pattern.
•	Otherwise, F* attempts to automatically generate patterns for the forall/exist.
o	If the generation fails, then F* emits a warning asking the user to supply a {:pattern} or {:nopattern}, defaulting to the behavior of nopattern (i.e. letting Z3 choose the pattern).
o	(Eventually, I'd like to emit an error in this case.)
•	To automatically generate patterns for (forall (x1...xn). e) or (exists (x1...xn). e), F* searches inside e for a term t that contains all the variables x1...xn:
o	For simplicity, the search need not look inside other binders, such as nested foralls, exists, let, or lambdas inside e.
	(this could be improved, but it will prevent accidentally generating patterns that include out-of-scope variables)
o	The term t should contain only function applications, constants, and variables.  It should contain at least one function application (i.e. it can't just be a variable by itself).  It should not contain:
	any function with the "[@smt_theory_symbol]" attribute, like /\, ==, +, etc.
	"let", foralls, exists, and lambdas
o	F* should make t as small as possible while still covering x1...xn.  For example, it should choose f(x, y) instead of h(f(x, y)).
o	If there are no such t, automatic generation fails.
o	There may be more than one t.  In this case, F* would generate a disjunction of the terms {:pattern t1 \/ ... \/ tk}.
To avoid breaking old code, F* would only try to infer patterns if the --ext auto_patterns flag is set on the command line.
 
Examples:
•	(forall x. f(x) == h(g(x)))
o	generates {:pattern f(x) \/ g(x)}
•	(forall x. h(f(x), g(x)))
o	generates {:pattern f(x) \/ g(x)}
•	(forall x. f(x) == f(x + 1) /\ g(x))
o	generates {:pattern f(x) \/ g(x)}
o	(this is actually bad because f(x) leads to a matching loop, but we can try to improve this later)
•	(forall x y. h(f(x), g(y)))
o	generates {:pattern h(f(x), g(y))}
•	(forall x y. f(x) == f(y))
o	fails, because this requires a conjunctive pattern {:pattern f(x); f(y)}
•	(forall x. let y = x + 1 in f(x) == g(x, y))
o	fails, because f(x) and g(x, y) are inside a let-binding
 
In terms of implementation strategy, I would suggest adding it in TcTerm, in the
case of Tm_app. 

Note, the representation quantifiers like `forall x1 .. xn. e` in AST a nested
application of 
`Tm_app(Tm_fvar (forall), (fun x1 -> Tm_App(..., (fun xn -> e))))`, 
and the pattern has to go on the innermost application, so that it applies to all the variables x1...xn. 

So, to handle this, I would suggest adding some logic to the Tm_app case, which triggers in phase2 only:
- it detects if the head symbol is a quantifier (forall or exists)
- if so, it descends into the term, finding the innermost application of the quantifier, and then checking for the presence of a user-supplied pattern or nopattern. If neither is present, then it tries to generate a pattern as described above.
- then it returns the elaborated term with the inferred pattern, which it passes as
normal to the rest of the phase2 typechecking process. 

All of this logic should be guarded under the --ext auto_patterns flag.

Once you have it implemented, start enabling it in ulib files and benchmark carefully, first noting
- if you find files that regress with the new pattern generation, make a careful note of it add :nopattern annotations to the relevant quantifiers in those files, and make a log
of such changes


