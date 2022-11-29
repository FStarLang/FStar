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

Passing options to Z3
......................

F* provides two ways of passing options to Z3.

The option ``--z3cliopt <string>`` causes F* to pass the string as a
command-line option when starting the Z3 process. A typical usage
might be ``--z3cliopt 'smt.random_seed=17'``.

In contrast, ``--z3smtopt <string>`` causes F* to send the string to
Z3 as part of its SMT2 output and this option is also reflected in the
.smt2 file that F* emits with ``--log_queries``. A typical usage would
be ``--z3smtopt '(set-option :smt.random_seed 17)'``. Note, it is
possible to abuse this option, e.g., one could use ``--z3smtopt
'(assert false)'`` and all SMT queries would trivially pass. So, use
it with care.

              
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

Each universally quantified axiom in scope is a term of the form below:

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
instantiate the axiom to obtain ``(= (BoxBool_proj_0 (BoxBool b))
b)``.

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
binary function on ``Term``, and an axiom relating it to the SMT
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
integers and boxed and unboxed.

Representing linear arithmetic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The option, ``--smtencoding.l_arith_repr native``, requests F* to,
effectively, inline the definitions of the linear arithmetic operators
(``+`` and ``-``). For example, with this option enabled, F* encodes
the term ``x + 1 + 2`` as the SMT2 term below.

.. code-block:: smt2

    (BoxInt (+ (BoxInt_proj_0 (BoxInt (+ (BoxInt_proj_0 @x0)
                                         (BoxInt_proj_0 (BoxInt 1)))))
               (BoxInt_proj_0 (BoxInt 2))))

Box elimination
~~~~~~~~~~~~~~~

The option ``--smtencoding.elim_box true`` is often useful in
combination with ``smtencoding.l_arith_repr native``, enables an
optimization to remove redundant adjacent box/unbox pairs. So, adding
this option to the example above, the encoding of ``x + 1 + 2``
becomes:

.. code-block:: smt2

    (BoxInt (+ (+ (BoxInt_proj_0 @x0) 1) 2))


Representing non-linear arithmetic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The option ``--smtencoding.nl_arith_repr [native|wrapped|boxwrap]``
controls the representation of non-linear arithmetic functions (``*,
/, mod``) in the SMT encoding. The default is ``boxwrap`` which uses
the encoding of ``Prims.op_Multiply, Prims.op_Division,
Prims.op_Modulus`` analogous to ``Prims.op_Addition``.

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

   
Functions
.........


Recursive functions and fuel
............................


Inductive datatypes and ifuel
.............................


Logical Formulas
................

