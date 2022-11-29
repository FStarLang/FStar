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
    
  * Alejandro Aguirre wrote a `tech report:
    <https://catalin-hritcu.github.io/students/alejandro/report.pdf>`_
    describing work in progress towards formalizing F*'s SMT encoding.

  * Michal Moskal's `Programming with Triggers:
    <https://moskal.me/pdf/prtrig.pdf>`_ describes how to pick
    triggers for quantifier instantiation and how to debug and profile
    the SMT solver, in the context of Vcc and the relation Hypervisor
    Verification project.

  * Leonardo de Moura and Nikolaj Bjorner `describe how E-matching is
    implemented in Z3:
    <http://leodemoura.github.io/files/ematching.pdf>`_ (at least
    circa 2007).
    
A Brief Tour of F*'s SMT Encoding
---------------------------------

To inspect F*'s SMT encoding, we'll work through several small
examples and get F* to log the SMT-LIB theories that it generates. For
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

where each ``End`` line also describes the number of declarations in
the module and its length in characters.


              
``Term`` sort
.............

The logic provided by the SMT solver is multi-sorted: the sorts
provide a kind of simple type system for the logic, ensuring, e.g.,
that terms from two different sorts can never be equal. However, F*'s
encoding to SMT (mostly) uses just a single sort: every pure (or
ghost) F* term is encoded to the SMT solver as an instance of an
uninterpreted SMT sort called ``Term``. This allows the encoding to be
very general, handling F*'s much richer type system, rather than
trying to map F*'s complex type system into the much simpler type
system of SMT sorts.


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
and ``Term``. The axiom named ``projection_inverse_BoxBool_proj_0``
states that ``BoxBool_proj_0`` is the inverse of ``BoxBool``, or,
equivalently, that ``BoxBool`` is an injective function from ``Bool``
to ``Term``. Note, unlike in F*, the ``assert`` keyword in SMT2
assumes that a fact is true, rather than checking that it is valid,
i.e., ``assert`` in SMT2 is like ``assume`` in F*.

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
search once that bound variables ``x1 ... xn`` are instantiated. The
terms ``p1 ... pm`` are called patterns, and collectively, ``p1
... pm`` must mention all the bound variables. To instantiate the
quantifier, the solver aims to find active terms ``v1...vm`` that
match the patterns ``p1..pm``, where a match involves finding a
substitution ``S`` for the bound variables ``x1...xm``, such that the
substituted patterns are equal to the active terms ``v1..vm``. Given
such a substitution, the substituted term ``S(body)`` becomes active
and may refine the partial model further.

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
quantifiers, then reasoning the the theory of arithmetic, and finally
using the injectivity of the ``BoxInt`` function to conclude. However,
this overhead is usually not perceptible, and the uniformity of
encoding everything to a single ``Term`` sort simplifies many other
things. Nevertheless, F* provides a few options to control the way
integers and boxed and unboxed, described :ref:`ahead
<z3_and_smtencoding_options>`.

   
Functions
.........

Consider the F* function below:

.. code-block:: fstar

   let add3 (x y z:int) : int = x + y + z


Its encoding to SMT has several elements.

First, we have have a declaration of an uinterpreted ternary function
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

In addition to its definition, F* encoding the type of ``add3`` to the
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

   
Recursive functions and fuel
............................

Non-recursive functions are similar to macro definitions. F* simply
encodes encodes their semantics to the SMT solver as a rewrite
rule. However, recursive functions, since they could be unfolded
indefinitely, are not so simple. Let's look at the encoding of the
``factorial`` function shown below.

.. code-block:: fstar
                
   open FStar.Mul
   let rec factorial (n:nat) : nat =
     if n = 0 then 1
     else n * factorial (n - 1)


First, we have, as before an uninterpreted function symbol on ``Term``
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
`all` recursive functions in scope. Of coure, the patterns are
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
   let _ = assert (factorial 1 == 1)

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

The type ``unat`` has its typing assumption---note F* does not encode
the universe levels to SMT.

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
we it uses a quantifier with a pattern that requires non-zero fuel to
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
``--max_ifuel``, and ``--ifuel``.

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
could instantiate the quantifier again.  Note, using the introdution
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
to try to keep use an ``ifuel`` setting that is as low as possible for
your proofs, e.g., a value less than ``2``, or even zero if
possible. However, as with fuel, a value of ifuel that is too low will
cause the solver to be unable to prove some facts. For example,
without any ``ifuel``, the solver cannot use the inversion assumption
to prove that the head of ``x`` must be either ``S`` or ``Z``, and F*
reports the error "Patterns are incomplete".

.. code-block:: fstar

   #push-options "--ifuel 0"                
   let rec as_nat (x:unat) : nat = 
      match x with
      | S x -> 1 + as_nat x
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

The :ref`logical connectives <Part2_connectives>` that F* offers, all
derived forms. Given the encodings of datatypes and functions (and
arrow types), the encodings of all these connectives just fall out
naturally. However, all these connectives also have built-in support
in the SMT solver as part of its propositional core and support for
E-matching-based quantifier instantiation. So, rather than leave them
as derived forms, a vital optimization in F*'s SMT encoding is to
recognize these connectives and to encode them directly to the
corresponding forms in SMT.

The term ``p /\ q`` in F* encoded to ``(and [[p]] [[q]]])`` where
``[[p]]`` and ``[[q]]`` are the *logical* encodings of ``p`` and ``q``
respectively. However, the SMT connective ``and`` is a binary function
on the SMT sort ``Bool``, whereas all we have been describing so far
is that every F* term ``p`` is encoded to the SMT sort ``Term``. To
bridge the gap, the logical encoding of a term ``p`` interprets the
``Term`` sort into ``Bool`` by using a function ``Valid p``, which
deeps a ``p : Term`` to be valid if it is inhabited, as per the
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
variables. In this case, the likely choice for the pattern is
``(SMTEncoding.factorial @x1)``, though ``(HasType @x1 Prims.nat)`` is
also a candidate.

For small developments, leaving the choice of pattern to Z3 is often
fine, but as your project scales up, you probably want to be more
careful about your choice of patterns. F* lets you write the pattern
explicit on a quantifier and translates it down to SMT, as shown
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
wrapping are boxing actually enable some proofs to go, and,
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



