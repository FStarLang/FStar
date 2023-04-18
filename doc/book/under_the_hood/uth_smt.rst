.. _UTH_smt:
              
Understanding how F* uses Z3
============================

As we have seen throughout, F* relies heavily on the Z3 SMT
(Satifiability Modulo Theories) solver for proof automation. Often, on
standalone examples at the scale covered in earlier chapters, the
automation just works out of the box, but as one builds larger
developments, proof automation can start becoming slower or
unpredictable---at that stage, it becomes important to understand how
F*'s encoding to SMT works to better control proofs.

At the most abstract level, one should realize that finding proofs in
the SMT logic F* uses (first-order logic with uninterpreted functions
and arithmetic) is an undecidable problem. As such, F* and the SMT
solver relies on various heuristics and partial decision procedures,
and a solver like Z3 does a remarkable job of being able to
effectively solve the very large problems that F* presents to it,
despite the theoretical undecidability. That said, the proof search
that Z3 uses is computationally expensive and can be quite sensitive
to the choice of heuristics and syntactic details of problem
instances. As such, if one doesn't chose the heuristics well, a small
change in a query presented to Z3 can cause it to take a different
search path, perhaps causing a proof to not be found at all, or to be
found after consuming a very different amount of resources.

Some background and resources:

  * F*'s SMT encoding uses the `SMT-LIB v2
    <http://smtlib.cs.uiowa.edu/language.shtml>`_ language. We refer
    to the "SMT-LIB v2" language as SMT2.
    
  * Alejandro Aguirre wrote a `tech report
    <https://catalin-hritcu.github.io/students/alejandro/report.pdf>`_
    describing work in progress towards formalizing F*'s SMT encoding.

  * Michal Moskal's `Programming with Triggers
    <https://moskal.me/pdf/prtrig.pdf>`_ describes how to pick
    triggers for quantifier instantiation and how to debug and profile
    the SMT solver, in the context of Vcc and the relation Hypervisor
    Verification project.

  * Leonardo de Moura and Nikolaj Bjorner `describe how E-matching is
    implemented in Z3
    <http://leodemoura.github.io/files/ematching.pdf>`_ (at least
    circa 2007).

A Primer on SMT2
----------------

SMT2 is a standardized input language supported by many SMT
solvers. Its syntax is based on `S-expressions
<https://en.wikipedia.org/wiki/S-expression>`_, inspired by languages
in the LISP family. We review some basic elements of its syntax here,
particularly the parts that are used by F*'s SMT encoding.

* Multi-sorted logic

  The logic provided by the SMT solver is multi-sorted: the sorts
  provide a simple type system for the logic, ensuring, e.g., that
  terms from two different sorts can never be equal. A user can define
  a new sort ``T``, as shown below:

  .. code-block:: smt2

    (declare-sort T)

  Every sort comes with a built-in notion of equality. Given two terms
  ``p`` and ``q`` of the same sort ``T``, ``(= p q)`` is a term of
  sort ``Bool`` expressing their equality.

    
* Declaring uninterpreted functions

  A new function symbol ``F``, with arguments in sorts
  ``sort_1 .. sort_n`` and returning a result in ``sort`` is declared
  as shown below,
  
  .. code-block:: smt2

     (declare-fun F (sort_1 ... sort_n) sort)                

  The function symbol ``F`` is *uninterpreted*, meaning that the only
  information the solver has about ``F`` is that it is a function,
  i.e., when applied to equal arguments ``F`` produces equal results.

* Theory symbols

   Z3 provides support for several *theories*, notably integer and
   real arithmetic. For example, on terms ``i`` and ``j`` of ``Int``
   sort, the sort of unbounded integers, the following terms define
   the expected arithmetic functions:

   .. code-block:: smt2

      (+ i j)       ; addition
      (- i j)       ; subtraction
      (* i j)       ; multiplication
      (div i j)     ; Euclidean division
      (mod i j)     ; Euclidean modulus

     
* Logical connectives

  SMT2 provides basic logical connectives as shown below, where ``p``
  and ``q`` are terms of sort ``Bool``

  .. code-block:: smt2

     (and p q)                ; conjunction
     (or p q)                 ; disjunction
     (not p)                  ; negation
     (implies p q)            ; implication
     (iff p q)                ; bi-implication


  SMT2 also provides support for quantifiers, where the terms below
  represent a term ``p`` with the variables ``x1 ... xn`` universally
  and existentially quantified, respectively.


  .. code-block:: smt2

     (forall ((x1 sort_1) ... (xn sort_n)) p)
     (exists ((x1 sort_1) ... (xn sort_n)) p)       

* Attribute annotations

  A term ``p`` can be decorated with attributes names ``a_1 .. a_n``
  with values ``v_1 .. v_n`` using the following syntax---the ``!`` is
  NOT to be confused with logical negation.

  .. code-block:: smt2

     (! p
        :a_1 v_1
        ...
        :a_n v_n)

  A common usage is with quantifiers, as we'll see below, e.g.,

  .. code-block:: smt2

     (forall ((x Int))
             (! (implies (>= x 0) (f x))
                :qid some_identifier))

* An SMT2 theory and check-sat

  An SMT2 theory is a collection of sort and function symbol
  declarations, and assertions of facts about them. For example,
  here's a simple theory declaring a function symbol ``f`` and an
  assumption that ``f x y`` is equivalent to ``(>= x y)``---note,
  unlike in F*, the ``assert`` keyword in SMT2 assumes that a fact is
  true, rather than checking that it is valid, i.e., ``assert`` in
  SMT2 is like ``assume`` in F*.


  .. code-block:: smt2

     (declare-fun f (Int Int) Bool)

     (assert (forall ((x Int) (y Int))
                     (iff (>= y x) (f x y))))


  In the context of this theory, one can ask whether some facts about
  ``f`` are valid. For example, to check if ``f`` is a transitive
  function, one asserts the *negation* of the transitivity
  property for ``f`` and then asks Z3 to check (using the
  ``(check-sat)`` directive) if the resulting theory is satisfiable.

  .. code-block:: smt2

     (assert (not (forall ((x Int) (y Int) (z Int))
                          (implies (and (f x y) (f y z))
                                   (f x z)))))
     (check-sat)
                  
  In this case, Z3 very quickly responds with ``unsat``, meaning that
  there are no models for the theory that contain an interpretation of
  ``f`` compatible with both assertions, or, equivalently, the
  transitivity of ``f`` is true in all models. That is, we expect
  successful queries to return ``unsat``.
  
    
A Brief Tour of F*'s SMT Encoding
---------------------------------

Consider the following simple F* code:

.. code-block:: fstar

   let id x = x
   let f (x:int) =
      if x < 0
      then assert (- (id x) >= 0)
      else assert (id x >= 0)

To encode the proof obligation of this program to SMT, F* generates an
SMT2 file with the following rough shape.

.. code-block:: smt2

   ;; Some basic scaffoling

   (declare-sort Term)
   ...
       
   ;; Encoding of some basic modules

   (declare-fun Prims.bool () Term)
   ...
    
   ;; Encoding of background facts about the current module

   (declare-fun id (Term) Term)
   (assert (forall ((x Term)) (= (id x) x)))

   ;; Encoding the query, i.e., negated proof obligation

   (assert (not (forall ((x Term))
                        (and (implies (lt x 0) (geq (minus (M.id x)) 0))
                             (implies (not (lt x 0)) (geq (M.id x) 0))))))

   (check-sat)

   ;; Followed by some instrumentation for error reporting
   ;; in case the check-sat call fails (i.e., does not return unsat)

That was just just to give you a rough idea---the details of F*'s
actual SMT encoding are a bit different, as we'll see below.

To inspect F*'s SMT encoding, we'll work through several small
examples and get F* to log the SMT2 theories that it generates. For
this, we'll use the file shown below as a skeleton, starting with the
``#push-options "--log_queries"`` directive, which instructs F* to
print out its encoding to ``.smt2`` file. The ``force_a_query``
definition at the end ensures that F* actually produces at least one
query---without it, F* sends nothing to the Z3 and so prints no output
in the .smt2 file. If you run ``fstar.exe SMTEncoding.fst`` on the
command line, you will find a file ``queries-SMTEncoding.smt2`` in the
current directory.

.. literalinclude:: ../code/SMTEncoding.fst
   :language: fstar

Even for a tiny module like this, you'll see that the .smt2 file is
very large. That's because, by default, F* always includes the modules
``prims.fst``, ``FStar.Pervasives.Native.fst``, and
``FStar.Pervasives.fsti`` as dependences of other modules. Encoding
these modules consumes about 150,000 lines of SMT2 definitions and
comments.

The encoding of each module is delimited in the .smt2 file by comments
of the following kind:

.. code-block:: smt2

   ;;; Start module Prims
   ...
   ;;; End module Prims (1334 decls; total size 431263)

   ;;; Start module FStar.Pervasives.Native
   ...
   ;;; End module FStar.Pervasives.Native (2643 decls; total size 2546449)

   ;;; Start interface FStar.Pervasives
   ...
   ;;; End interface FStar.Pervasives (2421 decls; total size 1123058)

where each `End` line also describes the number of declarations in
the module and its length in characters.

  
``Term`` sort
.............

Despite SMT2 being a multi-sorted logic, aside from the pervasive use
the SMT sort ``Bool``, F*'s encoding to SMT (mostly) uses just a
single sort: every pure (or ghost) F* term is encoded to the SMT
solver as an instance of an uninterpreted SMT sort called
``Term``. This allows the encoding to be very general, handling F*'s
much richer type system, rather than trying to map F*'s complex type
system into the much simpler type system of SMT sorts.


Booleans
........

One of the most primitive sorts in the SMT solver is ``Bool``, the
sort of Booleans. All the logical connectives in SMT are operations on
the ``Bool`` sort. To encode values of the F* type ``bool`` to SMT, we
use the ``Bool`` sort, but since all F* terms are encoded to the
``Term`` sort, we "box" the ``Bool`` sort to promote it to ``Term``,
using the SMT2 definitions below.

.. code-block:: smt2

   (declare-fun BoxBool (Bool) Term)
   (declare-fun BoxBool_proj_0 (Term) Bool)
   (assert (! (forall ((@u0 Bool))
                      (! (= (BoxBool_proj_0 (BoxBool @u0))
                             @u0)
                          :pattern ((BoxBool @u0))
                          :qid projection_inverse_BoxBool_proj_0))
               :named projection_inverse_BoxBool_proj_0))

This declares two uninterpreted functions ``BoxBool`` and
``BoxBool_proj_0`` that go back and forth between the sorts ``Bool``
and ``Term``.

The axiom named ``projection_inverse_BoxBool_proj_0`` states that
``BoxBool_proj_0`` is the inverse of ``BoxBool``, or, equivalently,
that ``BoxBool`` is an injective function from ``Bool`` to
``Term``. 


The ``qid`` is the quantifier identifier, usually equal to or derived
from the name of the assumption that includes it---qids come up when
we look at :ref:`profiling quantifier instantiation <Profiling_z3>`.

Patterns for quantifier instantiation
.....................................

The ``projection_inverse_BoxBool_proj_0`` axiom on booleans shows our
first use of a quantified formula with a pattern, i.e., the part that
says ``:pattern ((BoxBool @u0))``. These patterns are the main
heuristic used to control the SMT solver's proof search and will
feature repeatedly in the remainder of this chapter.

When exploring a theory, the SMT solver has a current partial model
which contains an assignment for some of the variables in a theory to
ground terms. All the terms that appear in this partial model are
called `active` terms and these active terms play a role in quantifier
instantiation.

Each universally quantified formula in scope is a term of the form below:

.. code-block:: smt2
                
    (forall ((x1 s1) ... (xn sn))
            (! (  body  )
             :pattern ((p1) ... (pm))))

This quantified formula is inert and only plays a role in the solver's
search once the bound variables ``x1 ... xn`` are instantiated. The
terms ``p1 ... pm`` are called patterns, and collectively, ``p1
... pm`` must mention *all* the bound variables. To instantiate the
quantifier, the solver aims to find active terms ``v1...vm`` that
match the patterns ``p1..pm``, where a match involves finding a
substitution ``S`` for the bound variables ``x1...xm``, such that the
substituted patterns ``S(p1...pm)`` are equal to the active terms
``v1..vm``. Given such a substitution, the substituted term
``S(body)`` becomes active and may refine the partial model further.

Existentially quantified formulas are dual to universally quantified
formulas. Whereas a universal formula in the *context* (i.e., in
negative position, or as a hypothesis) is inert until its pattern is
instantiated, an existential *goal* (or, in positive position) is
inert until its pattern is instantiated. Existential quantifiers can
be decorated with patterns that trigger instantiation when matched
with active terms, just like universal quantifiers

Returning to ``projection_inverse_BoxBool_proj_0``, what this means is
that once the solver has an active term ``BoxBool b``, it can
instantiate the quantified formula to obtain ``(= (BoxBool_proj_0
(BoxBool b)) b)``.

Integers
........

The encoding of the F* type ``int`` is similar to that of
``bool``---the primitive SMT sort ``Int`` (of unbounded mathematical
integers) are coerced to ``Term`` using the injective function
``BoxInt``.

.. code-block:: smt2

    (declare-fun BoxInt (Int) Term)
    (declare-fun BoxInt_proj_0 (Term) Int)
    (assert (! (forall ((@u0 Int))
                       (! (= (BoxInt_proj_0 (BoxInt @u0))
                             @u0)
                          :pattern ((BoxInt @u0))
                          :qid projection_inverse_BoxInt_proj_0))
               :named projection_inverse_BoxInt_proj_0))

The primitive operations on integers are encoded by unboxing the
arguments and boxing the result. For example, here's the encoding of
``Prims.(+)``, the addition operator on integers.
               
.. code-block:: smt2

    (declare-fun Prims.op_Addition (Term Term) Term)
    (assert (! (forall ((@x0 Term) (@x1 Term))
                       (! (= (Prims.op_Addition @x0
                                                @x1)
                             (BoxInt (+ (BoxInt_proj_0 @x0)
                                        (BoxInt_proj_0 @x1))))
                          :pattern ((Prims.op_Addition @x0
                                                       @x1))
                          :qid primitive_Prims.op_Addition))
             :named primitive_Prims.op_Addition))

This declares an uninterpreted function ``Prims.op_Addition``, a
binary function on ``Term``, and an assumption relating it to the SMT
primitive operator from the integer arithmetic theory ``(+)``. The
pattern allows the SMT solver to instantiate this quantifier for every
active application of the ``Prims.op_Addition``.

The additional boxing introduces some overhead, e.g., proving ``x + y
== y + x`` in F* amounts to proving ``Prims.op_Addition x y ==
Prims.op_Addition y x`` in SMT2. This in turn involves instantiation
quantifiers, then reasoning in the theory of linear arithmetic, and
finally using the injectivity of the ``BoxInt`` function to
conclude. However, this overhead is usually not perceptible, and the
uniformity of encoding everything to a single ``Term`` sort simplifies
many other things. Nevertheless, F* provides a few options to control
the way integers and boxed and unboxed, described :ref:`ahead
<z3_and_smtencoding_options>`.

   
Functions
.........

Consider the F* function below:

.. code-block:: fstar

   let add3 (x y z:int) : int = x + y + z


Its encoding to SMT has several elements.

First, we have have a declaration of an uninterpreted ternary function
on ``Term``.

.. code-block:: smt2

   (declare-fun SMTEncoding.add3 (Term Term Term) Term)

The semantics of ``add3`` is given using the assumption below, which
because of the pattern on the quantifier, can be interpreted as a
rewrite rule from left to right: every time the solver has
``SMTEncoding.add3 x y z`` as an active term, it can expand it to its
definition.

.. code-block:: smt2
                
   (assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
                      (! (= (SMTEncoding.add3 @x0
                                              @x1
                                              @x2)
                            (Prims.op_Addition (Prims.op_Addition @x0
                                                                  @x1)
                                               @x2))
                       :pattern ((SMTEncoding.add3 @x0
                                                @x1
                                                @x2))
                       :qid equation_SMTEncoding.add3))
    
            :named equation_SMTEncoding.add3))

In addition to its definition, F* encodes *the type of* ``add3`` to the
solver too, as seen by the assumption below. One of the key predicates
of F*'s SMT encoding is ``HasType``, which relates a term to its
type. The assumption ``typing_SMTEncoding.add3`` encodes the typing of
the application based on the typing hypotheses on the arguments.

.. code-block:: smt2

   (assert (! (forall ((@x0 Term) (@x1 Term) (@x2 Term))
                      (! (implies (and (HasType @x0
                                                Prims.int)
                                       (HasType @x1
                                                Prims.int)
                                       (HasType @x2
                                                Prims.int))
                                  (HasType (SMTEncoding.add3 @x0 @x1 @x2)
                                           Prims.int))
                         :pattern ((SMTEncoding.add3 @x0 @x1 @x2))
                    :qid typing_SMTEncoding.add3))
         :named typing_SMTEncoding.add3))

This is all we'd need to encode ``add3`` if it was never used at
higher order. However, F* treats functions values just like any other
value and allows them to be passed as arguments to, or returned as
results from, other functions. The SMT logic is, however, a
first-order logic and functions like ``add3`` are not first-class
values. So, F* introduces another layer in the encoding to model
higher-order functions, but we don't cover this here.


.. _UTH_SMT_fuel:

Recursive functions and fuel
............................

Non-recursive functions are similar to macro definitions---F* just
encodes encodes their semantics to the SMT solver as a rewrite
rule. However, recursive functions, since they could be unfolded
indefinitely, are not so simple. Let's look at the encoding of the
``factorial`` function shown below.

.. code-block:: fstar
                
   open FStar.Mul
   let rec factorial (n:nat) : nat =
     if n = 0 then 1
     else n * factorial (n - 1)


     
First, we have, as before, an uninterpreted function symbol on ``Term``
and an assumption about its typing.

.. code-block:: smt2
                
   (declare-fun SMTEncoding.factorial (Term) Term)

   (assert (! (forall ((@x0 Term))
                      (! (implies (HasType @x0 Prims.nat)
                                  (HasType (SMTEncoding.factorial @x0) Prims.nat))
                       :pattern ((SMTEncoding.factorial @x0))
                       :qid typing_SMTEncoding.factorial))
            :named typing_SMTEncoding.factorial))

            
However, to define the semantics of ``factorial`` we introduce a
second "fuel-instrumented" function symbol with an additional
parameter of ``Fuel`` sort.

.. code-block:: smt2
                
   (declare-fun SMTEncoding.factorial.fuel_instrumented (Fuel Term) Term)

The ``Fuel`` sort is declared at the very beginning of F*'s SMT
encoding and is a representation of unary integers, with two
constructors ``ZFuel`` (for zero) and ``SFuel f`` (for successor).

The main idea is to encode the definition of ``factorial`` guarded by
patterns that only allow unfolding the definition if the fuel argument
of ``factorial.fuel_instrumented`` is not zero, as shown below.
Further, the assumption defining the semantics of
``factorial.fuel_instrumented`` is guarded by a typing hypothesis on
the argument ``(HasType @x1 Prims.nat)``, since the recursive function
in F* is only well-founded on ``nat``, not on all terms. The
``:weight`` annotation is an SMT2 detail: setting it to zero ensures
that the SMT solver can instantiate this quantifier as often as
needed, so long as the the fuel instrumentation argument is non-zero.
Notice that the equation peels off one application of ``SFuel``, so
that the quantifier cannot be repeatedly instantiated infinitely.

.. code-block:: smt2

    (assert (! (forall ((@u0 Fuel) (@x1 Term))
                       (! (implies (HasType @x1 Prims.nat)
                                   (= (SMTEncoding.factorial.fuel_instrumented (SFuel @u0) @x1)
                                      (let ((@lb2 (Prims.op_Equality Prims.int @x1 (BoxInt 0))))
                                           (ite (= @lb2 (BoxBool true))
                                                (BoxInt 1)
                                                (Prims.op_Multiply
                                                       @x1
                                                       (SMTEncoding.factorial.fuel_instrumented
                                                            @u0
                                                            (Prims.op_Subtraction @x1 (BoxInt 1))))))))
                         :weight 0
                         :pattern ((SMTEncoding.factorial.fuel_instrumented (SFuel @u0) @x1))
                         :qid equation_with_fuel_SMTEncoding.factorial.fuel_instrumented))
             :named equation_with_fuel_SMTEncoding.factorial.fuel_instrumented))

We also need an assumption that tells the SMT solver that the fuel
argument, aside from controlling the number of unfoldings, is
semantically irrelevant.

.. code-block:: smt2
                
    (assert (! (forall ((@u0 Fuel) (@x1 Term))
                       (! (= (SMTEncoding.factorial.fuel_instrumented (SFuel @u0) @x1)
                             (SMTEncoding.factorial.fuel_instrumented ZFuel @x1))
                        :pattern ((SMTEncoding.factorial.fuel_instrumented (SFuel @u0) @x1))
                        :qid @fuel_irrelevance_SMTEncoding.factorial.fuel_instrumented))
             :named @fuel_irrelevance_SMTEncoding.factorial.fuel_instrumented))

And, finally, we relate the original function to its fuel-instrumented
counterpart.

.. code-block:: smt2
                
   (assert (! (forall ((@x0 Term))
                      (! (= (SMTEncoding.factorial @x0)
                            (SMTEncoding.factorial.fuel_instrumented MaxFuel @x0))
                       :pattern ((SMTEncoding.factorial @x0))
                       :qid @fuel_correspondence_SMTEncoding.factorial.fuel_instrumented))
            :named @fuel_correspondence_SMTEncoding.factorial.fuel_instrumented))

This definition uses the constant ``MaxFuel``. The value of this
constant is determined by the F* options ``--initial_fuel n`` and
``--max_fuel m``. When F* issues a query to Z3, it tries the query
repeatedly with different values of ``MaxFuel`` ranging between ``n``
and ``m``. Additionally, the option ``--fuel n`` sets both the initial
fuel and max fuel to ``n``.

This single value of ``MaxFuel`` controls the number of unfoldings of
`all` recursive functions in scope. Of course, the patterns are
arranged so that if you have a query involving, say, ``List.map``,
quantified assumptions about an unrelated recursive function like
``factorial`` should never trigger. Neverthless, large values of
``MaxFuel`` greatly increase the search space for the SMT solver. If
your proof requires a setting greater than ``--fuel 2``, and if it
takes the SMT solver a long time to find the proof, then you should
think about whether things could be done differently.

However, with a low value of ``fuel``, the SMT solver cannot reason
about recursive functions beyond that bound. For instance, the
following fails, since the solver can unroll the definition only once
to conclude that ``factorial 1 == 1 * factorial 0``, but being unable
to unfold ``factorial 0`` further, the proof fails.

.. code-block:: fstar

   #push-options "--fuel 1"
   let _ = assert (factorial 1 == 1) (* fails *)

As with regular functions, the rest of the encoding of recursive
functions has to do with handling higher-order uses.

Inductive datatypes and ifuel
.............................

Inductive datatypes in F* allow defining unbounded structures and,
just like with recursive functions, F* encodes them to SMT by
instrumenting them with fuel, to prevent infinite unfoldings. Let's
look at a very simple example, an F* type of unary natural numbers.

.. code-block:: fstar

   type unat = 
     | Z : unat
     | S : (prec:unat) -> unat

Although Z3 offers support for a built-in theory of datatypes, F* does
not use it (aside for ``Fuel``), since F* datatypes are more
complex. Instead, F* rolls its own datatype encoding using
uninterpreted functions and the encoding of ``unat`` begins by
declaring these functions.

.. code-block:: smt2

    (declare-fun SMTEncoding.unat () Term)
    (declare-fun SMTEncoding.Z () Term)
    (declare-fun SMTEncoding.S (Term) Term)
    (declare-fun SMTEncoding.S_prec (Term) Term)    

We have one function for the type ``unat``; one for each constructor
(``Z`` and ``S``); and one "projector" for each argument of each
constructor (here, only ``S_prec``, corresponding to the F* projector
``S?.prec``).

The type ``unat`` has its typing assumption, where ``Tm_type`` is the
SMT encoding of the F* type ``Type``---note F* does not encode the
universe levels to SMT.

.. code-block:: smt2

   (assert (! (HasType SMTEncoding.unat Tm_type)
            :named kinding_SMTEncoding.unat@tok))

The constructor ``S_prec`` is assumed to be an inverse of ``S``. If
there were more than one argument to the constructor, each projector
would project out only the corresponding argument, encoding that the
constructor is injective on each of its arguments.

.. code-block:: smt2

   (assert (! (forall ((@x0 Term))
                      (! (= (SMTEncoding.S_prec (SMTEncoding.S @x0)) @x0)
                       :pattern ((SMTEncoding.S @x0))
                       :qid projection_inverse_SMTEncoding.S_prec))
            :named projection_inverse_SMTEncoding.S_prec))                

The encoding defines two macros ``is-SMTEncoding.Z`` and
``is-SMTEncoding.S`` that define when the head-constructor of a term
is ``Z`` and ``S`` respectively. These two macros are used in the
definition of the inversion assumption of datatypes, namely that given
a term of type ``unat``, one can conclude that its head constructor
must be either ``Z`` or ``S``. However, since the type ``unat`` is
unbounded, we want to avoid applying this inversion indefinitely, so
it uses a quantifier with a pattern that requires non-zero fuel to
be triggered.

.. code-block:: smt2

   (assert (! (forall ((@u0 Fuel) (@x1 Term))
                 (! (implies (HasTypeFuel (SFuel @u0) @x1 SMTEncoding.unat)
                             (or (is-SMTEncoding.Z @x1)
                                 (is-SMTEncoding.S @x1)))
                    :pattern ((HasTypeFuel (SFuel @u0) @x1 SMTEncoding.unat))
                    :qid fuel_guarded_inversion_SMTEncoding.unat))
         :named fuel_guarded_inversion_SMTEncoding.unat))

Here, we see a use of ``HasTypeFuel``, a fuel-instrumented version of
the ``HasType`` we've seen earlier. In fact, ``(HasType x t)`` is just
a macro for ``(HasTypeFuel MaxIFuel x t)``, where much like for
recursive functions and fuel, the constant ``MaxIFuel`` is defined by
the current value of the F* options ``--initial_ifuel``,
``--max_ifuel``, and ``--ifuel`` (where ``ifuel`` stands for "inversion fuel").

The key bit in ensuring that the inversion assumption above is not
indefinitely applied is in the structure of the typing assumptions for
the data constructors. These typing assumptions come in two forms,
introduction and elimination.

The introduction form for the ``S`` constructor is shown below. This
allows deriving that ``S x`` has type ``unat`` from the fact that
``x`` itself has type ``unat``. The pattern on the quantifier makes
this goal-directed: if ``(HasTypeFuel @u0 (SMTEncoding.S @x1)
SMTEncoding.unat)`` is already an active term, then the quantifer
fires to make ``(HasTypeFuel @u0 @x1 SMTEncoding.unat)`` an active
term, peeling off one application of the ``S`` constructor.  If we
were to use ``(HasTypeFuel @u0 @x1 SMTEncoding.unat)`` as the pattern,
this would lead to an infinite quantifier instantiation loop, since
every each instantiation would lead a new, larger active term that
could instantiate the quantifier again.  Note, using the introduction
form does not vary the fuel parameter, since the the number of
applications of the constructor ``S`` decreases at each instantiation
anyway.

.. code-block:: smt2
                
   (assert (! (forall ((@u0 Fuel) (@x1 Term))
                 (! (implies (HasTypeFuel @u0 @x1 SMTEncoding.unat)
                             (HasTypeFuel @u0 (SMTEncoding.S @x1) SMTEncoding.unat))
                    :pattern ((HasTypeFuel @u0 (SMTEncoding.S @x1) SMTEncoding.unat))
                    :qid data_typing_intro_SMTEncoding.S@tok))
            :named data_typing_intro_SMTEncoding.S@tok))

The elimination form allows concluding that the sub-terms of a
well-typed application of a constructor are well-typed too. This time
note that the conclusion of the rule decreases the fuel parameter by
one. If that were not the case, then we would get a quantifier
matching loop between ``data_elim_SMTEncoding.S`` and
``fuel_guarded_inversion_SMTEncoding.unat``, since each application of
the latter would contribute an active term of the form ``(HasTypeFuel
(SFuel _) (S (S_prec x)) unat)``, allowing the former to be triggered
again.

.. code-block:: smt2

   (assert (! (forall ((@u0 Fuel) (@x1 Term))
                      (! (implies (HasTypeFuel (SFuel @u0) (SMTEncoding.S @x1) SMTEncoding.unat)
                                  (HasTypeFuel @u0 @x1 SMTEncoding.unat))
                       :pattern ((HasTypeFuel (SFuel @u0) (SMTEncoding.S @x1) SMTEncoding.unat))
                       :qid data_elim_SMTEncoding.S))
            :named data_elim_SMTEncoding.S))

A final important element in the encoding of datatypes has to do with
the well-founded ordering used in termination proofs. The following
states that if ``S x1`` is well-typed (with non-zero fuel) then ``x1``
precedes ``S x1`` in F*'s built-in sub-term ordering.

.. code-block:: smt2

   (assert (! (forall ((@u0 Fuel) (@x1 Term))
                      (! (implies (HasTypeFuel (SFuel @u0)
                                               (SMTEncoding.S @x1)
                                               SMTEncoding.unat)
                                  (Valid (Prims.precedes Prims.lex_t Prims.lex_t
                                                         @x1 (SMTEncoding.S @x1))))
                       :pattern ((HasTypeFuel (SFuel @u0) (SMTEncoding.S @x1) SMTEncoding.unat))
                       :qid subterm_ordering_SMTEncoding.S))
         :named subterm_ordering_SMTEncoding.S))

Once again, a lot of the rest of the datatype encoding has to do with
handling higher order uses of the constructors.

As with recursive functions, the single value of ``MaxIFuel`` controls
the number of inversions of all datatypes in scope. It's a good idea
to try to use an ``ifuel`` setting that is as low as possible for
your proofs, e.g., a value less than ``2``, or even ``0``, if
possible. However, as with fuel, a value of ifuel that is too low will
cause the solver to be unable to prove some facts. For example,
without any ``ifuel``, the solver cannot use the inversion assumption
to prove that the head of ``x`` must be either ``S`` or ``Z``, and F*
reports the error "Patterns are incomplete".

.. code-block:: fstar

   #push-options "--ifuel 0"                
   let rec as_nat (x:unat) : nat = 
      match x with (* fails exhaustiveness check *)
      | S x -> 1 + as_nat x (* fails termination check *)
      | Z -> 0

Sometimes it is useful to let the solver arbitrarily invert an
inductive type. The ``FStar.Pervasives.allow_inversion`` is a library
function that enables this, as shown below. Within that scope, the
ifuel guards on the ``unat`` type are no longer imposed and SMT can
invert ``unat`` freely---F* accepts the code below.

.. code-block:: fstar

   #push-options "--ifuel 0"                
   let rec as_nat (x:unat) : nat =
      allow_inversion unat;
      match x with
      | S x -> 1 + as_nat x
      | Z -> 0

This can be useful sometimes, e.g., one could set the ifuel to 0 and
allow inversion within a scope for only a few selected types, e.g.,
``option``. However, it is rarely a good idea to use
``allow_inversion`` on an unbounded type (e.g., ``list`` or even
``unat``).


Logical Connectives
....................

The :ref:`logical connectives <Part2_connectives>` that F* offers are all
derived forms. Given the encodings of datatypes and functions (and
arrow types, which we haven't shown), the encodings of all these
connectives just fall out naturally. However, all these connectives
also have built-in support in the SMT solver as part of its
propositional core and support for E-matching-based quantifier
instantiation. So, rather than leave them as derived forms, a vital
optimization in F*'s SMT encoding is to recognize these connectives
and to encode them directly to the corresponding forms in SMT.

The term ``p /\ q`` in F* is encoded to ``(and [[p]] [[q]]])`` where
``[[p]]`` and ``[[q]]`` are the *logical* encodings of ``p`` and ``q``
respectively. However, the SMT connective ``and`` is a binary function
on the SMT sort ``Bool``, whereas all we have been describing so far
is that every F* term ``p`` is encoded to the SMT sort ``Term``. To
bridge the gap, the logical encoding of a term ``p`` interprets the
``Term`` sort into ``Bool`` by using a function ``Valid p``, which
deems a ``p : Term`` to be valid if it is inhabited, as per the
definitions below.

.. code-block:: smt2

   (declare-fun Valid (Term) Bool)
   (assert (forall ((e Term) (t Term))
                (! (implies (HasType e t) (Valid t))
                   :pattern ((HasType e t) (Valid t))
                   :qid __prelude_valid_intro)))

The connectives ``p \/ q``, ``p ==> q``, ``p <==> q``, and ``~p`` are
similar.

The quantified forms ``forall`` and ``exists`` are mapped to the
corresponding quantifiers in SMT. For example,

.. code-block:: fstar

   let fact_positive = forall (x:nat). factorial x >= 1

is encoded to:

.. code-block:: smt2

   (forall ((@x1 Term))
           (implies (HasType @x1 Prims.nat)
                    (>= (BoxInt_proj_0 (SMTEncoding.factorial @x1))
                        (BoxInt_proj_0 (BoxInt 1)))))

Note, this quantifier does not have any explicitly annotated
patterns. In this case, Z3's syntactic trigger selection heuristics
pick a pattern: it is usually the smallest collection of sub-terms of
the body of the quantifier that collectively mention all the bound
variables. In this case, the choices for the pattern are
``(SMTEncoding.factorial @x1)`` and ``(HasType @x1 Prims.nat)``: Z3
picks both of these as patterns, allowing the quantifier to be
triggered if an active term matches either one of them.

For small developments, leaving the choice of pattern to Z3 is often
fine, but as your project scales up, you probably want to be more
careful about your choice of patterns. F* lets you write the pattern
explicitly on a quantifier and translates it down to SMT, as shown
below.

.. code-block:: fstar
                
   let fact_positive_2 = forall (x:nat).{:pattern (factorial x)} factorial x >= 1

This produces:

.. code-block:: smt2

    (forall ((@x1 Term))
            (! (implies (HasType @x1 Prims.nat)
                        (>= (BoxInt_proj_0 (SMTEncoding.factorial @x1))
                            (BoxInt_proj_0 (BoxInt 1))))
             :pattern ((SMTEncoding.factorial.fuel_instrumented ZFuel @x1))))


Note, since ``factorial`` is fuel instrumented, the pattern is
translated to an application that requires no fuel, so that the
property also applies to any partial unrolling of factorial also.

Existential formulas are similar. For example, one can write:

.. code-block:: fstar

   let fact_unbounded = forall (n:nat). exists (x:nat). factorial x >= n

And it gets translated to:

.. code-block:: smt2

   (forall ((@x1 Term))
           (implies (HasType @x1 Prims.nat)
                    (exists ((@x2 Term))
                            (and (HasType @x2 Prims.nat)
                                 (>= (BoxInt_proj_0 (SMTEncoding.factorial @x2))
                                     (BoxInt_proj_0 @x1))))))

.. _z3_and_smtencoding_options:

Options for Z3 and the SMT Encoding
...................................

F* provides two ways of passing options to Z3.

The option ``--z3cliopt <string>`` causes F* to pass the string as a
command-line option when starting the Z3 process. A typical usage
might be ``--z3cliopt 'smt.random_seed=17'``.

In contrast, ``--z3smtopt <string>`` causes F* to send the string to
Z3 as part of its SMT2 output and this option is also reflected in the
.smt2 file that F* emits with ``--log_queries``. As such, it can be
more convenient to use this option if you want to debug or profile a
run of Z3 on an .smt2 file generated by F*. A typical usage would be
``--z3smtopt '(set-option :smt.random_seed 17)'``. Note, it is
possible to abuse this option, e.g., one could use ``--z3smtopt
'(assert false)'`` and all SMT queries would trivially pass. So, use
it with care.

F*'s SMT encoding also offers a few options. 

* ``--smtencoding.l_arith_repr native``

This option requests F* to inline the definitions of the linear
arithmetic operators (``+`` and ``-``). For example, with this option
enabled, F* encodes the term ``x + 1 + 2`` as the SMT2 term below.

.. code-block:: smt2

    (BoxInt (+ (BoxInt_proj_0 (BoxInt (+ (BoxInt_proj_0 @x0)
                                         (BoxInt_proj_0 (BoxInt 1)))))
               (BoxInt_proj_0 (BoxInt 2))))

* ``--smtencoding.elim_box true``

This option is often useful in combination with
``smtencoding.l_arith_repr native``, enables an optimization to remove
redundant adjacent box/unbox pairs. So, adding this option to the
example above, the encoding of ``x + 1 + 2`` becomes:

.. code-block:: smt2

    (BoxInt (+ (+ (BoxInt_proj_0 @x0) 1) 2))


* ``--smtencoding.nl_arith_repr [native|wrapped|boxwrap]``
  
This option controls the representation of non-linear arithmetic
functions (``*, /, mod``) in the SMT encoding. The default is
``boxwrap`` which uses the encoding of ``Prims.op_Multiply,
Prims.op_Division, Prims.op_Modulus`` analogous to
``Prims.op_Addition``.

The ``native`` setting is similar to the ``smtencoding.l_arith_repr
native``. When used in conjuction with ``smtencoding.elim_box true``,
the F* term ``x * 1 * 2`` is encoded to:

.. code-block:: smt2

    (BoxInt (* (* (BoxInt_proj_0 @x0) 1) 2))

However, a third setting ``wrapped`` is also available with provides
an intermediate level of wrapping. With this setting enabled, the
encoding of ``x * 1 * 2`` becomes

.. code-block:: smt2

    (BoxInt (_mul (_mul (BoxInt_proj_0 @x0) 1) 2))

where ``_mul`` is declared as shown below:

.. code-block:: smt2

    (declare-fun _mul (Int Int) Int)
    (assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))

Now, you may wonder why all these settings are useful. Surely, one
would think, ``--smtencoding.l_arith_repr native
--smtencoding.nl_arith_repr native --smtencoding.elim_box true`` is
the best setting. However, it turns out that the additional layers of
wrapping and boxing actually enable some proofs to go through, and,
empirically, no setting strictly dominates all the others.

However, the following is a good rule of thumb if you are starting a
new project:

1. Consider using ``--z3smtopt '(set-option :smt.arith.nl
   false)'``. This entirely disables support for non-linear arithmetic
   theory reasoning in the SMT solver, since this can be very
   expensive and unpredictable. Instead, if you need to reason about
   non-linear arithmetic, consider using the lemmas from
   ``FStar.Math.Lemmas`` to do the non-linear steps in your proof
   manually. This will be more painstaking, but will lead to more
   stable proofs.

2. For linear arithmetic, the setting ``--smtencoding.l_arith_repr
   native --smtencoding.elim_box true`` is a good one to consider, and
   may yield some proof performance boosts over the default setting.

.. _UTH_smt_patterns:
   
Designing a Library with SMT Patterns
-------------------------------------

In this section, we look at the design of ``FStar.Set``, a module in
the standard library, examining, in particular, its use of SMT
patterns on lemmas for proof automation. The style used here is
representative of the style used in many proof-oriented
libraries---the interface of the module offers an abstract type, with
some constructors and some destructors, and lemmas that relate their
behavior.

To start with, for our interface, we set the fuel and ifuel both to
zero---we will not need to reason about recursive functions or invert
inductive types here.

.. literalinclude:: ../code/SimplifiedFStarSet.fsti
   :language: fstar
   :start-after: //SNIPPET_START: module$
   :end-before: //SNIPPET_END: module$

Next, we introduce the signature of the main abstract type of this
module, ``set``:

.. literalinclude:: ../code/SimplifiedFStarSet.fsti
   :language: fstar
   :start-after: //SNIPPET_START: set$
   :end-before: //SNIPPET_END: set$

Sets offer just a single operation called ``mem`` that allows testing
whether or not a given element is in the set.

.. literalinclude:: ../code/SimplifiedFStarSet.fsti
   :language: fstar
   :start-after: //SNIPPET_START: destructor$
   :end-before: //SNIPPET_END: destructor$

However, there are several ways to construct sets:

.. literalinclude:: ../code/SimplifiedFStarSet.fsti
   :language: fstar
   :start-after: //SNIPPET_START: constructors$
   :end-before: //SNIPPET_END: constructors$

Finally, sets are equipped with a custom equivalence relation:

.. literalinclude:: ../code/SimplifiedFStarSet.fsti
   :language: fstar
   :start-after: //SNIPPET_START: equal$
   :end-before: //SNIPPET_END: equal$

The rest of our module offers lemmas that describe the behavior of
``mem`` when applied to each of the constructors.

.. literalinclude:: ../code/SimplifiedFStarSet.fsti
   :language: fstar
   :start-after: //SNIPPET_START: core_properties$
   :end-before: //SNIPPET_END: core_properties$

Each of these lemmas should be intuitive and familiar. The extra bit
to pay attention to is the ``SMTPat`` annotations on each of the
lemmas. These annotations instruct F*'s SMT encoding to treat the
lemma like a universal quantifier guarded by the user-provided
pattern. For instance, the lemma ``mem_empty`` is encoded to the SMT
solver as shown below.

.. code-block:: smt2

   (assert (! (forall ((@x0 Term) (@x1 Term))
                      (! (implies (and (HasType @x0 Prims.eqtype)
                                       (HasType @x1 @x0))
                                  (not (BoxBool_proj_0
                                          (SimplifiedFStarSet.mem @x0
                                                                  @x1
                                                                 (SimplifiedFStarSet.empty @x0)))))
                       :pattern ((SimplifiedFStarSet.mem @x0
                                                         @x1
                                                         (SimplifiedFStarSet.empty @x0)))
                       :qid lemma_SimplifiedFStarSet.mem_empty))
           :named lemma_SimplifiedFStarSet.mem_empty))

That is, from the perspective of the SMT encoding, the statement of
the lemma ``mem_empty`` is analogous to the following assumption:

.. code-block:: fstar

   forall (a:eqtype) (x:a). {:pattern (mem x empty)} not (mem x empty)


As such, lemmas decorated with SMT patterns allow the user to inject
new, quantified hypotheses into the solver's context, where each of
those hypotheses is justified by a proof in F* of the corresponding
lemma. This allows users of the ``FStar.Set`` library to treat ``set``
almost like a new built-in type, with proof automation to reason about
its operations. However, making this work well requires some careful
design of the patterns.

Consider ``mem_union``: the pattern chosen above allows the solver to
decompose an active term ``mem x (union s1 s2)`` into ``mem x s1`` and
``mem x s2``, where both terms are smaller than the term we started
with. Suppose instead that we had written:

.. code-block:: fstar

   val mem_union (#a:eqtype) (x:a) (s1 s2:set a)
     : Lemma
       (ensures (mem x (union s1 s2) == (mem x s1 || mem x s2)))
       [SMTPat (mem x s1); SMTPat (mem x s2)]

This translates to an SMT quantifier whose patterns are the pair of
terms ``mem x s1`` and ``mem x s2``. This choice of pattern would
allow the solver to instantiate the quantifier with all pairs of
active terms of the form ``mem x s``, creating more active terms that
are themselves matching candidates. To be explicit, with a single
active term ``mem x s``, the solver would derive ``mem x (union s
s)``, ``mem x (union s (union s s))``, and so on.  This is called a
matching loop and can be disastrous for solver performance. So,
carefully chosing the patterns on quantifiers and lemmas with
``SMTPat`` annotations is important.

Finally, to complete our interface, we provide two lemmas to
characterize ``equal``, the equivalence relation on sets. The first
says that sets that agree on the ``mem`` function are ``equal``, and
the second says that ``equal`` sets are provably equal ``(==)``, and
the patterns allow the solver to convert reasoning about equality into
membership and provable equality.

.. literalinclude:: ../code/SimplifiedFStarSet.fsti
   :language: fstar
   :start-after: //SNIPPET_START: equal_intro_elim$
   :end-before: //SNIPPET_END: equal_intro_elim$

Of course, all these lemmas can be easily proven by F* under a
suitable representation of the abstract type ``set``, as shown in the
module implementation below.

.. literalinclude:: ../code/SimplifiedFStarSet.fst
   :language: fstar
   :start-after: //SNIPPET_START: SimplifiedFStarSet.Impl$
   :end-before: //SNIPPET_END: SimplifiedFStarSet.Impl$

Exercise
........

Extend the set library with another constructor with the signature
shown below:

.. code-block:: fstar

   val from_fun (#a:eqtype) (f: a -> bool) : Tot (set a)

and prove a lemma that shows that a an element ``x`` is in ``from_fun
f`` if and only if ``f x = true``, decorating the lemma with the
appropriate SMT pattern.

This `interface file <../code/SimplifiedFStarSet.fsti>`_ and its
`implementation <../code/SimplifiedFStarSet.fst>`_ provides the
definitions you need.

.. container:: toggle

    .. container:: header

       **Answer**

    Look at `FStar.Set.intension <https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Set.fsti>`_ if you get stuck

--------------------------------------------------------------------------------    

.. _Profiling_z3:
           
Profiling Z3 and Solving Proof Performance Issues
-------------------------------------------------

At some point, you will write F* programs where proofs start to take
much longer than you'd like: simple proofs fail to go through, or
proofs that were once working start to fail as you make small changes
to your program. Hopefully, you notice this early in your project and
can try to figure out how to make it better before slogging through
slow and unpredictable proofs. Contrary to the wisdom one often
receives in software engineering where early optimization is
discouraged, when developing proof-oriented libraries, it's wise to
pay attention to proof performance issues as soon as they come up,
otherwise you'll find that as you scale up further, proofs become so
slow or brittle that your productivity decreases rapidly.

Query Statistics
................

Your first tool to start diagnosing solver performance is F*'s
``--query_stats`` option. We'll start with some very simple artificial
examples.

With the options below, F* outputs the following statistics:


.. code-block:: fstar

   #push-options "--initial_fuel 0 --max_fuel 4 --ifuel 0 --query_stats" 
   let _ = assert (factorial 3 == 6)

   
.. code-block:: none

   (<input>(20,0-20,49))	Query-stats (SMTEncoding._test_query_stats, 1)	failed
      {reason-unknown=unknown because (incomplete quantifiers)} in 31 milliseconds
      with fuel 0 and ifuel 0 and rlimit 2723280
      statistics={mk-bool-var=7065 del-clause=242 num-checks=3 conflicts=5
                  binary-propagations=42 arith-fixed-eqs=4 arith-pseudo-nonlinear=1
                  propagations=10287 arith-assert-upper=21 arith-assert-lower=18
                  decisions=11 datatype-occurs-check=2 rlimit-count=2084689
                  arith-offset-eqs=2 quant-instantiations=208 mk-clause=3786
                  minimized-lits=3 memory=21.41 arith-pivots=6 max-generation=5
                  arith-conflicts=3 time=0.03 num-allocs=132027456 datatype-accessor-ax=3
                  max-memory=21.68 final-checks=2 arith-eq-adapter=15 added-eqs=711}
   
   (<input>(20,0-20,49))	Query-stats (SMTEncoding._test_query_stats, 1)	failed
      {reason-unknown=unknown because (incomplete quantifiers)} in 47 milliseconds
      with fuel 2 and ifuel 0 and rlimit 2723280
      statistics={mk-bool-var=7354 del-clause=350 arith-max-min=10 interface-eqs=3
                  num-checks=4 conflicts=8 binary-propagations=56 arith-fixed-eqs=17
                  arith-pseudo-nonlinear=3 arith-bound-prop=2 propagations=13767
                  arith-assert-upper=46 arith-assert-lower=40 decisions=25
                  datatype-occurs-check=5 rlimit-count=2107946 arith-offset-eqs=6
                  quant-instantiations=326 mk-clause=4005 minimized-lits=4
                  memory=21.51 arith-pivots=20 max-generation=5 arith-add-rows=34
                  arith-conflicts=4 time=0.05 num-allocs=143036410 datatype-accessor-ax=5
                  max-memory=21.78 final-checks=6 arith-eq-adapter=31 added-eqs=1053}
   
   (<input>(20,0-20,49))	Query-stats (SMTEncoding._test_query_stats, 1)	succeeded
       in 48 milliseconds with fuel 4 and ifuel 0 and rlimit 2723280
       statistics={arith-max-min=26 num-checks=5 binary-propagations=70 arith-fixed-eqs=47
                   arith-assert-upper=78 arith-assert-lower=71 decisions=40
                   rlimit-count=2130332 max-generation=5 arith-nonlinear-bounds=2
                   time=0.05 max-memory=21.78 arith-eq-adapter=53 added-eqs=1517
                   mk-bool-var=7805 del-clause=805 interface-eqs=3 conflicts=16
                   arith-pseudo-nonlinear=6 arith-bound-prop=4 propagations=17271
                   datatype-occurs-check=5 arith-offset-eqs=20 quant-instantiations=481
                   mk-clause=4286 minimized-lits=38 memory=21.23 arith-pivots=65
                   arith-add-rows=114 arith-conflicts=5 num-allocs=149004462
                   datatype-accessor-ax=9 final-checks=7}

There's a lot of information here:

* We see three lines of output, each tagged with a source location and
  an internal query identifer (``(SMTEncoding._test_query_stats, 1)``,
  the first query for verifying ``_test_query_stats``).

* The first two attempts at the query failed, with Z3 reporting the
  reason for failure as ``unknown because (incomplete
  quantifiers)``. This is a common response from Z3 when it fails to
  prove a query---since first-order logic is undecidable, when Z3
  fails to find a proof, it reports "unknown" rather than claiming
  that the theory is satisfiable. The third attempt succeeded.

* The attempts used ``0``, ``2``, and ``4`` units of fuel. Notice that
  our query was ``factorial 3 == 6`` and this clearly requires at
  least 4 units of fuel to succeed. In this case it didn't matter
  much, since the two failed attempts took only ``47`` and ``48``
  milliseconds. But, you may sometimes find that there are many
  attempts of a proof with low fuel settings and finally success with
  a higher fuel number. In such cases, you may try to find ways to
  rewrite your proof so that you are not relying on so many unrollings
  (if possible), or if you decide that you really need that much fuel,
  then setting the ``--fuel`` option to that value can help avoid
  several slow failures and retries.

* The rest of the statistics report internal Z3 statistics.

  - The ``rlimit`` value is a logical resource limit that F* sets when
    calling Z3. Sometimes, as we will see shortly, a proof can be
    "cancelled" in case Z3 runs past this resource limit. You can
    increase the ``rlimit`` in this case, as we'll see below.

  - Of the remaning statistics, perhaps the main one of interest is
    ``quant_instantiations``. This records a cumulative total of
    quantifiers instantiated by Z3 so far in the current
    session---here, each attempt seems to instantiate around 100--150
    quantifiers. This is a very low number, since the query is so
    simple. You may be wondering why it is even as many as that, since
    4 unfolding of factorial suffice, but remember that there are many
    other quantifiers involved in the encoding, e.g., those that prove
    that ``BoxBool`` is injective etc. A more typical query will see
    quantifier instantiations in the few thousands.


.. note::
   
   Note, since the ``quant-instantiations`` metric is cumulative, it
   is often useful to precede a query with something like the following:

   .. code-block:: fstar

      #push-options "--initial_fuel 0 --max_fuel 4 --ifuel 0 --query_stats" 
      #restart-solver
      let _dummy = assert (factorial 0 == 1)

      let _test_query_stats = assert (factorial 3 == 6)
                   
   The ``#restart-solver`` creates a fresh Z3 process and the
   ``dummy`` query "warms up" the process by feeding it a trivial
   query, which will run somewhat slow because of various
   initialization costs in the solver. Then, the query stats reported
   for the real test subject starts in this fresh session.

Working though a slow proof
...........................

Even a single poorly chosen quantified assumption in the prover's
context can make an otherwise simple proof take very long. To
illustrate, consider the following variation on our example above:

.. code-block:: fstar

   assume Factorial_unbounded: forall (x:nat). exists (y:nat). factorial y > x

   #push-options "--fuel 4 --ifuel 0 --query_stats" 
   #restart-solver
   let _test_query_stats = assert (factorial 3 == 6)

We've now introduced the assumption ``Factorial_unbounded`` into our
context. Recall from the SMT encoding of quantified formulas, from the
SMT solver's perspective, this looks like the following:

.. code-block:: smt2

    (assert (! (forall ((@x0 Term))
                       (! (implies (HasType @x0 Prims.nat)
                                   (exists ((@x1 Term))
                                           (! (and (HasType @x1 Prims.nat)
                                              (> (BoxInt_proj_0 (SMTEncoding.factorial @x1))
                                                 (BoxInt_proj_0 @x0)))
                                            :qid assumption_SMTEncoding.Factorial_unbounded.1)))
                    :qid assumption_SMTEncoding.Factorial_unbounded))
             :named assumption_SMTEncoding.Factorial_unbounded))


This quantifier has no explicit patterns, but Z3 picks the term
``(HasType @x0 Prims.nat)`` as the pattern for the ``forall``
quantifier. This means that it can instantiate the quantifier for
active terms of type ``nat``. But, a single instantiation of the
quantifier, yields the existentially quantified formula. Existentials
are immediately `skolemized
<https://en.wikipedia.org/wiki/Skolem_normal_form>`_ by Z3, i.e., the
existentially bound variable is replaced by a fresh function symbol
that depends on all the variables in scope. So, a fresh term ``a @x0``
corresponding ``@x1`` is introduced, and immediately, the conjunct
``HasType (a @x0) Prims.nat`` becomes an active term and can be used to
instantiate the outer universal quantifier again. This "matching loop"
sends the solver into a long, fruitless search and the simple proof
about ``factorial 3 == 6`` which previously succeeded in a few
milliseconds, now fails. Here's are the query stats:


.. code-block:: none

   (<input>(18,0-18,49))	Query-stats (SMTEncoding._test_query_stats, 1)	failed
     {reason-unknown=unknown because canceled} in 5647 milliseconds
     with fuel 4 and ifuel 0 and rlimit 2723280
     statistics={ ... quant-instantiations=57046 ... }

A few things to notice:

  * The failure reason is "unknown because canceled". That means the
    solver reached its resource limit and halted the proof
    search. Usually, when you see "canceled" as the reason, you could
    try raising the rlimit, as we'll see shortly.

  * The failure took 5.6 seconds.

  * There were 57k quantifier instantiations, as compared to just the
    100 or so we had earlier. We'll soon seen how to pinpoint which
    quantifiers were instantiated too much.

Increasing the rlimit
~~~~~~~~~~~~~~~~~~~~~

We can first retry the proof by giving Z3 more resources---the
directive below doubles the resource limit given to Z3.

.. code-block:: fstar

   #push-options "--z3rlimit_factor 2"

This time it took 14 seconds and failed. But if you try the same proof
a second time, it succeeds. That's not very satisfying.

Repeating Proofs with Quake
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Although this is an artificial example, unstable proofs that work and
then suddenly fail do happen. Z3 does guarantee that it is
deterministic in a very strict sense, but even the smallest change to
the input, e.g., a change in variable names, or even asking the same
query twice in a succession in the same Z3 session, can result in
different answers.

There is often a deeper root cause (in our case, it's the
``Factorial_unbounded`` assumption, of course), but a first attempt at
determining whether or not a proof is "flaky" is to use the F* option
``--quake``.

.. code-block:: fstar

   #push-options "--quake 5/k"
   let _test_query_stats = assert (factorial 3 == 6)

This tries the query 5 times and reports the number of successes and
failures.

In this case, F* reports the following:

.. code-block:: none

   Quake: query (SMTEncoding._test_query_stats, 1) succeeded 4/5 times (best fuel=4, best ifuel=0)

If you're working to stabilize a proof, a good criterion is to see if
you can get the proof to go through with the ``--quake`` option.

You can also try the proof by varying the Z3's random seed and
checking that it works with several choices of the seed.

.. code-block:: none

   #push-options "--z3smtopt '(set-option :smt.random_seed 1)'"


Profiling Quantifier Instantiation
..................................

We have a query that's taking much longer than we'd like and from the
query-stats we see that there are a lot of quantifier instances. Now,
let's see how to pin down which quantifier is to blame.


   1. Get F* to log an .smt2 file, by adding the ``--log_queries``
      option. It's important to also add a ``#restart-solver`` before
      just before the definition that you're interested in
      profiling.
      
      .. code-block:: fstar
   
          #push-options "--fuel 4 --ifuel 0 --query_stats --log_queries --z3rlimit_factor 2"
          #restart-solver
          let _test_query_stats = assert (factorial 3 == 6)

      F* reports the name of the file that it wrote as part of the
      query-stats. For example:

      .. code-block:: none

          (<input>(18,0-18,49)@queries-SMTEncoding-7.smt2)	Query-stats ...

   2. Now, from a terminal, you run Z3 on this generated .smt2 file,
      while passing it the following option and save the output in a
      file.

      .. code-block:: none

           z3 queries-SMTEncoding-7.smt2 smt.qi.profile=true > sample_qiprofile                        

   3. The output contains several lines that begin with
      ``[quantifier_instances]``, which is what we're interested in.


      .. code-block:: none

           grep quantifier_instances sample_qiprofile | sort -k 4 -n

      The last few lines of output look like this:

      .. code-block:: none

          [quantifier_instances] bool_inversion :    352 :  10 : 11
          [quantifier_instances] bool_typing :    720 :  10 : 11
          [quantifier_instances] constructor_distinct_BoxBool :    720 :  10 : 11
          [quantifier_instances] projection_inverse_BoxBool_proj_0 :   1772 :  10 : 11
          [quantifier_instances] primitive_Prims.op_Equality :   2873 :  10 : 11
          [quantifier_instances] int_typing :   3168 :  10 : 11
          [quantifier_instances] constructor_distinct_BoxInt :   3812 :  10 : 11
          [quantifier_instances] typing_SMTEncoding.factorial :   5490 :  10 : 11
          [quantifier_instances] int_inversion :   5506 :  11 : 12
          [quantifier_instances] @fuel_correspondence_SMTEncoding.factorial.fuel_instrumented :   5746 :  10 : 11
          [quantifier_instances] Prims_pretyping_ae567c2fb75be05905677af440075565 :   5835 :  11 : 12
          [quantifier_instances] projection_inverse_BoxInt_proj_0 :   6337 :  10 : 11
          [quantifier_instances] primitive_Prims.op_Multiply :   6394 :  10 : 11
          [quantifier_instances] primitive_Prims.op_Subtraction :   6394 :  10 : 11
          [quantifier_instances] token_correspondence_SMTEncoding.factorial.fuel_instrumented :   7629 :  10 : 11
          [quantifier_instances] @fuel_irrelevance_SMTEncoding.factorial.fuel_instrumented :   9249 :  10 : 11
          [quantifier_instances] equation_with_fuel_SMTEncoding.factorial.fuel_instrumented :  13185 :  10 : 10
          [quantifier_instances] refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2 :  15346 :  10 : 11
          [quantifier_instances] assumption_SMTEncoding.Factorial_unbounded :  15890 :  10 : 11
                       

      Each line mentions is of the form:

      .. code-block:: none

          qid : number of instances : max generation :  max cost

      where,

          * qid is the identifer of quantifier in the .smt2 file

          * the number of times it was instantiated, which is the
            number we're most interested in

          * the generation and cost are other internal measures, which
            Nikolaj Bjorner explains `here
            <https://github.com/Z3Prover/z3/issues/4522#issuecomment-644454562>`_

   4. Interpreting the results

      Clearly, as expected, ``assumption_SMTEncoding.Factorial_unbounded`` is
      instantiated the most.

      Next, if you search in the .smt2 file for ":qid
      refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2",
      you'll find the assumption that gives an interpretation to the
      ``HasType x Prims.nat`` predicate, where each instantiation of
      ``Factorial_unbounded`` yields another instance of this fact.

      Notice that
      ``equation_with_fuel_SMTEncoding.factorial.fuel_instrumented``
      is also instantiated a lot. This is because aside from the
      matching loop due to ``HasType x Prims.nat``, each
      instantiation of ``Factorial_unbounded`` also yields an
      occurrence of ``factorial`` as a new active term, which the
      solver then unrolls up to four times.

      We also see instantiations of quantifiers in ``Prims`` and other
      basic facts like ``int_inversion``, ``bool_typing`` etc.
      Sometimes, you may even find that these quantifiers fire the
      most. However, these quantifiers are inherent to F*'s SMT
      encoding: there's not much you can do about it as a user. They
      are usually also not to blame for a slow proof---they fire a lot
      when other terms are instantiated too much. You should try to
      identify other quantifiers in your code or libraries that fire
      a lot and try to understand the root cause of that.

Z3 Axiom Profiler
~~~~~~~~~~~~~~~~~

The `Z3 Axiom Profiler
<https://github.com/viperproject/axiom-profiler>`_ can also be used to
find more detailed information about quantifier instantiation,
including which terms we used for instantiation, dependence among the
quantifiers in the form of instantiation chains, etc.

However, there seem to be `some issues
<https://github.com/viperproject/axiom-profiler/issues/26>`_ with
using it at the moment with Z3 logs generated from F*.


.. _Splitting_queries:

Splitting Queries
.................

In the next two sections, we look at a small example that Alex Rozanov
reported, shown below. It exhibits similar proof problems to our
artificial example with factorial. Instead of just identifying the
problematic quantifier, we look at how to remedy the performance
problem by revising the proof to be less reliant on Z3 quantifier
instantiation.

.. literalinclude:: ../code/Alex.fst
   :language: fstar

The hypothesis is that ``unbounded f`` has exactly the same problem as
the our unbounded hypothesis on factorial---the ``forall/exists``
quantifier contains a matching loop. 

This proof of ``find_above_for_g`` succeeds, but it takes a while and
F* reports:

.. code-block:: none

    (Warning 349) The verification condition succeeded after splitting
    it to localize potential errors, although the original non-split
    verification condition failed. If you want to rely on splitting
    queries for verifying your program please use the '--split_queries
    always' option rather than relying on it implicitly.

By default, F* collects all the proof obligations in a top-level F*
definition and presents it to Z3 in a single query with several
conjuncts. Usually, this allows Z3 to efficiently solve all the
conjuncts together, e.g., the proof search for one conjunct may yield
clauses useful to complete the search for other clauses. However,
sometimes, the converse can be true: the proof search for separate
conjuncts can interfere with each other negatively, leading to the
entire proof to fail even when every conjunct may be provable if tried
separately. Additionally, when F* calls Z3, it applies the current
rlimit setting for every query. If a query contains N conjuncts,
splitting the conjuncts into N separate conjuncts is effectively a
rlimit multiplier, since each query can separately consume resources
as much as the current rlimit.

If the single query with several conjunct fails without Z3 reporting
any further information that F* can reconstruct into a localized error
message, F* splits the query into its conjuncts and tries each of
them in isolation, so as to isolate the failing conjunct it
any. However, sometimes, when tried in this mode, the proof of all
conjuncts can succeed.

One way to respond to Warning 349 is to follow what it says and enable
``--split_queries always`` explicitly, at least for the program fragment in
question. This can sometimes stabilize a previously unstable
proof. However, it may also end up deferring an underlying
proof-performance problem. Besides, even putting stability aside,
splitting queries into their conjuncts results in somewhat slower
proofs.

.. _UTH_opaque_to_smt:

Taking Control of Quantifier Instantiations with Opaque Definitions
...................................................................

Here is a revision of Alex's program that addresses the quantifier
instantiation problem. There are a few elements to the solution.

.. literalinclude:: ../code/AlexOpaque.fst
   :language: fstar
   :start-after: //SNIPPET_START: opaque$
   :end-before: //SNIPPET_END: opaque$

1. Marking definitions as opaque

     The attribute ``[@@"opaque_to_smt"]`` on the definition of
     ``unbounded`` instructs F* to not encode that definition to the SMT
     solver. So, the problematic alternating quantifier is no longer
     in the global scope.

2. Selectively revealing the definition within a scope

     Of course, we still want to reason about the unbounded
     predicate. So, we provide a lemma, ``instantiate_unbounded``, that
     allows the caller to explicity instantiate the assumption
     that ``f`` is unbounded on some lower bound ``m``.

     To prove the lemma, we use ``FStar.Pervasives.reveal_opaque``:
     its first argument is the name of a symbol that should be
     revealed; its second argument is a term in which that definition
     should be revealed. It this case, it proves that ``unbounded f``
     is equal to ``forall m. exists n. abs (f n) > m``.

     With this fact available in the local scope, Z3 can prove the
     lemma. You want to use ``reveal_opaque`` carefully, since with
     having revealed it, Z3 has the problematic alternating quantifier
     in scope and could go into a matching loop. But, here, since the
     conclusion of the lemma is exactly the body of the quantifier, Z3
     quickly completes the proof. If even this proves to be
     problematic, then you may have to resort to tactics.

3. Explicitly instantiate where needed

     Now, with our instantiation lemma in hand, we can precisly
     instantiate the unboundedness hypothesis on ``f`` as needed.

     In the proof, there are two instantiations, at ``m`` and ``m1``.

     Note, we are still relying on some non-trivial quantifier
     instantiation by Z3. Notably, the two assertions are important to
     instantiate the existential quantifier in the ``returns``
     clause. We'll look at that in more detail shortly.

     But, by making the problematic definition opaque and instantiating
     it explicitly, our performance problem is gone---here's what
     query-stats shows now.

     .. code-block:: none

        (<input>(18,2-31,5))	Query-stats (AlexOpaque.find_above_for_g, 1)
	             succeeded in 46 milliseconds

This `wiki page
<https://github.com/FStarLang/FStar/wiki/Code-pattern-for-hiding-definitions-from-Z3-and-selectively-revealing-them>`_
provides more information on selectively revealing opaque definitions.

Other Ways to Explicitly Trigger Quantifiers
............................................

For completeness, we look at some other ways in which quantifier
instantiation works.

.. _Artificial_triggers:

An Artificial Trigger
~~~~~~~~~~~~~~~~~~~~~

Instead of making the definition of ``unbounded`` opaque, we could
protect the universal quantifier with a pattern using some symbol
reserved for this purpose, as shown below.

.. literalinclude:: ../code/AlexOpaque.fst
   :language: fstar
   :start-after: //SNIPPET_START: trigger$
   :end-before: //SNIPPET_END: trigger$


1. We define a new function ``trigger x`` that is trivially true.

2. In ``unbounded_alt`` we decorate the universal quantifier with an
   explicit pattern, ``{:pattern (trigger x)}``. The pattern is not
   semantically relevant---it's only there to control how the
   quantifier is instantiated

3. In ``find_above_for_gg``, whenever we want to instantiate the
   quantifier with a particular lower bound ``k``, we assert ``trigger
   k``. That gives Z3 an active term that mentions ``trigger`` which
   it then uses to instantiate the quantifier with our choice of
   ``k``.

This style is not particularly pleasant, because it involves polluting
our definitions with semantically irrelevant triggers. The selectively
revealing opaque definitions style is much preferred. However,
artificial triggers can sometimes be useful.

Existential quantifiers
~~~~~~~~~~~~~~~~~~~~~~~

We have an existential formula in the goal ``exists (i:nat). abs(g i)
> m`` and Z3 will try to solve this by finding an active term to
instantiate ``i``. In this case, the patterns Z3 picks is ``(g i)`` as
well the predicate ``(HasType i Prims.nat)``, which the SMT encoding
introduces. Note, F* does not currently allow the existential
quantifier in a ``returns`` annoation to be decorated with a
pattern---that will likely change in the future.

Since ``g i`` is one of the patterns, by asserting ``abs (g (n - 1)) >
m`` in one branch, and ``abs (g (n1 - 1)) > m`` in the other, Z3 has
the terms it needs to instantiate the quantifier with ``n - 1`` in one
case, and ``n1 - 1`` in the other case.

In fact, any assertion that mentions the ``g (n - 1)`` and
``g (n1 - 1)`` will do, even trivial ones, as the example below shows.

.. literalinclude:: ../code/AlexOpaque.fst
   :language: fstar
   :start-after: //SNIPPET_START: trigger_exists$
   :end-before: //SNIPPET_END: trigger_exists$

We assert ``trigger (g (n - 1)))`` and ``trigger (g (n1 - 1))``, this
gives Z3 active terms for ``g (n - 1))`` and ``g (n1 - 1)``, which
suffices for the instantiation. Note, asserting ``trigger (n - 1)`` is
not enough, since that doesn't mention ``g``.

However, recall that there's a second pattern that's also applicable
``(HasType i Prims.nat)``--we can get Z3 to instantiate the quantifier
if we can inject the predicate ``(HasType (n - 1) nat)`` into Z3's
context. By using ``trigger_nat``, as shown below, does the trick,
since F* inserts a proof obligation to show that the argument ``x`` in
``trigger_nat x`` validates ``(HasType x Prims.nat)``.

.. literalinclude:: ../code/AlexOpaque.fst
   :language: fstar
   :start-after: //SNIPPET_START: trigger_nat$
   :end-before: //SNIPPET_END: trigger_nat$

Of course, rather than relying on implicitly chosen triggers for the
existentials, one can be explicit about it and provide the instance
directly, as shown below, where the ``introduce exists ...`` in each
branch directly provides the witness rather than relying on Z3 to find
it. This style is much preferred, if possible, than relying implicit
via various implicitly chosen patterns and artificial triggers.

.. literalinclude:: ../code/AlexOpaque.fst
   :language: fstar
   :start-after: //SNIPPET_START: explicit_exists$
   :end-before: //SNIPPET_END: explicit_exists$

Here is `a link to the the full file <../code/AlexOpaque.fst>`_ with
all the variations we have explored.

Overhead due to a Large Context
...............................

Consider the following program:

.. literalinclude:: ../code/ContextPollution.fst
   :language: fstar
   :start-after: //SNIPPET_START: context_test1$
   :end-before: //SNIPPET_END: context_test1$

The lemma ``test1`` is a simple property about ``FStar.Seq``, but the
lemma occurs in a module that also depends on a large number of other
modules---in this case, about 177 modules from the F* standard
library. All those modules are encoded to the SMT solver producing
about 11MB of SMT2 definitions with nearly 20,000 assertions for the
solver to process. This makes for a large search space for the solver
to explore to find a proof, however, most of those assertions are
quantified formulas guarded by patterns and they remain inert unless
some active term triggers them. Nevertheless, all these definitions
impose a noticeable overhead to the solver. If you turn
``--query_stats`` on (after a single warm-up query), it takes Z3 about
300 milliseconds (and about 3000 quantifier instantiations) to find a
proof for ``test1``.

You probably won't really notice the overhead of a proof that takes
300 milliseconds---the F* standard library doesn't have many
quantifiers in scope with things like bad quantifier alternation that
lead to matching loops. However, as your development starts to depend
on an ever larger stack of modules, there's the danger that at some
point, your proofs are impacted by some bad choice of quantifiers in
some module that you have forgotten about. In that case, you may find
that seemingly simple proofs take many seconds to go through. In this
section, we'll look at a few things you can do to diagnose such
problems.

Filtering the context
~~~~~~~~~~~~~~~~~~~~~

The first thing we'll look at is an F* option to remove facts from the
context.

.. literalinclude:: ../code/ContextPollution.fst
   :language: fstar
   :start-after: //SNIPPET_START: using_facts$
   :end-before: //SNIPPET_END: using_facts$

The ``--using_facts_from`` option retains only facts from modules that
match the namespace-selector string provided. In this case, the
selector shrinks the context from 11MB and 20,000 assertions to around
1MB and 2,000 assertions and the query stats reports that the proof
now goes through in just 15 milliseconds---a sizeable speedup even
though the absolute numbers are still small.

Of course, deciding which facts to filter from your context is not
easy. For example, if you had only retained ``FStar.Seq`` and forgot
to include ``Prims``, the proof would have failed. So, the
``--using_facts_from`` option isn't often very useful.

Unsat Core and Hints
~~~~~~~~~~~~~~~~~~~~

When Z3 finds a proof, it can report which facts from the context were
relevant to the proof. This collection of facts is called the unsat
core, because Z3 has proven that the facts from the context and the
negated goal are unsatisfiable. F* has an option to record and replay
the unsat core for each query and F* refers to the recorded unsat cores
as "hints".

Here's how to use hints:


1. Record hints

   .. code-block:: none

      fstar.exe --record_hints ContextPollution.fst

   This produces a file called ``ContextPollution.fst.hints``

   The format of a hints file is internal and subject to change,
   but it is a textual format and you can roughly see what it
   contains. Here's a fragment from it:

   .. code-block:: none
                   
      [
         "ContextPollution.test1",
         1,
         2,
         1,
         [
           "@MaxIFuel_assumption", "@query", "equation_Prims.nat",
           "int_inversion", "int_typing", "lemma_FStar.Seq.Base.lemma_eq_intro",
           "lemma_FStar.Seq.Base.lemma_index_app1",
           "lemma_FStar.Seq.Base.lemma_index_app2",
           "lemma_FStar.Seq.Base.lemma_len_append",
           "primitive_Prims.op_Addition", "primitive_Prims.op_Subtraction",
           "projection_inverse_BoxInt_proj_0",
           "refinement_interpretation_Tm_refine_542f9d4f129664613f2483a6c88bc7c2",
           "refinement_interpretation_Tm_refine_ac201cf927190d39c033967b63cb957b",
           "refinement_interpretation_Tm_refine_d83f8da8ef6c1cb9f71d1465c1bb1c55",
           "typing_FStar.Seq.Base.append", "typing_FStar.Seq.Base.length"
         ],
         0,
         "3f144f59e410fbaa970cffb0e20df75d"
       ]

   This is the hint entry for the query with whose id is
   ``(ContextPollution.test1, 1)``

   The next two fields are the fuel and ifuel used for the query,
   ``2`` and ``1`` in this case.
   
   Then, we have the names of all the facts in the unsat core for this
   query: you can see that it was only about 20 facts that were
   needed, out of the 20,000 that were originally present.

   The second to last field is not used---it is always 0.

   And the last field is a hash of the query that was issued.
   
2. Replaying hints

   The following command requests F* to search for
   ``ContextPollution.fst.hints`` in the include path and when
   attempting to prove a query with a given id, it looks for a hint
   for that query in the hints file, uses the fuel and ifuel settings
   present in the hints, and prunes the context to include only the
   facts present in the unsat core.
   
   .. code-block:: none

      fstar.exe --use_hints ContextPollution.fst

   Using the hints usually improves verification times substantially,
   but in this case, we see that the our proof now goes through in
   about 130 milliseconds, not nearly as fast as the 15 milliseconds
   we saw earlier. That's because when using a hint, each query to Z3
   spawns a new Z3 process initialized with just the facts in the
   unsat core, and that incurs some basic start-up time costs.

Many F* projects use hints as part of their build, including F*'s
standard library. The .hints files are checked in to the repository
and are periodically refreshed as proofs evolve. This helps improve
the stability of proofs: it may take a while for a proof to go
through, but once it does, you can record and replay the unsat core
and subsequent attempts of the same proof (or even small variations of
it) can go through quickly.

Other projects do not use hints: some people (perhaps rightfully) see
hints as a way of masking underlying proof performance problems and
prefer to make proofs work quickly and robustly without hints. If you
can get your project to this state, without relying on hints, then so
much the better for you!

Differential Profiling with qprofdiff
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you have a proof that takes very long without hints but goes
through quickly with hints, then the hints might help you diagnose why
the original proof was taking so long. This wiki page describes how to
`compare two Z3 quantifier instantiation profiles
<https://github.com/FStarLang/FStar/wiki/Profiling-Z3-queries#interpreting-the-results>`_
with a tool that comes with Z3 called qprofdiff.


Hints that fail to replay
^^^^^^^^^^^^^^^^^^^^^^^^^

Sometimes, Z3 will report an unsat core, but when F* uses it to try to
replay a proof, Z3 will be unable to find a proof of unsat, and F*
will fall back to trying the proof again in its original context. The
failure to find a proof of unsat from a previously reported unsat core
is not a Z3 unsoundness or bug---it's because although the report core
is really logically unsat, finding a proof of unsat may have relied on
quantifier instantiation hints from facts that are not otherwise
semantically relevant. The following example illustrates.

.. literalinclude:: ../code/HintReplay.fst
   :language: fstar


Say you run the following:

.. code-block:: none

   fstar --record_hints HintReplay.fst
   fstar --query_stats --use_hints HintReplay.fst

You will see the following output from the second run:

.. code-block:: none

   (HintReplay.fst(15,27-15,39))   Query-stats (HintReplay.test, 1)        failed
     {reason-unknown=unknown because (incomplete quantifiers)} (with hint)
     in 42 milliseconds ..
   
   (HintReplay.fst(15,27-15,39))   Query-stats (HintReplay.test, 1)        succeeded
     in 740 milliseconds ...

The first attempt at the query failed when using the hint, and the
second attempt at the query (without the hint) succeeded. 

To see why, notice that to prove the assertion ``r x`` from the
hypothesis ``q x``, logically, the assumption ``Q_R``
suffices. Indeed, if you look in the hints file, you will see that it
only mentions ``HintReplay.Q_R`` as part of the logical core. However,
``Q_R`` is guarded by a pattern ``p x`` and in the absence of the
assumption ``P_Q``, there is no way for the solver to derive an active
term ``p x`` to instantiate ``Q_R``---so, with just the unsat core, it
fails to complete the proof.

Failures for hint replay usually point to some unusual quantifier
triggering pattern in your proof. For instance, here we used ``p x``
as a pattern, even though ``p x`` doesn't appear anywhere in
``Q_R``---that's not usually a good choice, though sometimes, e.g.,
when using :ref:`artificial triggers <Artificial_triggers>` it can
come up.

This `wiki page on hints
<https://github.com/FStarLang/FStar/wiki/Robust,-replayable-proofs-using-unsat-cores,-(aka,-hints,-or-how-to-replay-verification-in-milliseconds-instead-of-minutes)>`_
provides more information about diagnosing hint-replay failures,
particularly in the context of the Low* libraries.


