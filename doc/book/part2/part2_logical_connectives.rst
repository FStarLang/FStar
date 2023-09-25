.. _Part2_connectives:

Constructive & Classical Connectives
====================================

In :ref:`an earlier chapter <Part1_prop_connectives>`, we learned
about the propositional connectives :math:`\forall, \exists,
\Rightarrow, \iff, \wedge, \vee, \neg`, etc. Whereas in other logical
frameworks these connectives are primitive, in a type theory like F*
these connectives are defined notions, built from inductive type
definitions and function types. In this section, we take a closer look
at these logical connectives, show their definitions, and present some
utilities to manipulate them in proofs.

Every logical connective comes in two flavors. First, in its most
primitive form, it is defined as an inductive or arrow type, giving a
constructive interpretation to the connective. Second, and more
commonly used in F*, is a *squashed*, or proof-irrelevant, variant of
the same connective---the squashed variant is classical rather than
constructive and its proofs are typically derived by writing partial
proof terms with the SMT filling in the missing parts.

Each connective has an *introduction* principle (which describes how
to build proofs of that connective) and an *elimination* principle
(which describes how to use a proof of that connective to build other
proofs). Example uses of introduction and elimination principles for
all the connectives can be found in `ClassicalSugar.fst
<https://github.com/FStarLang/FStar/blob/master/tests/micro-benchmarks/ClassicalSugar.fst>`_

All these types are defined in ``Prims``, the very first module in all
F* programs.

Falsehood
.........

The ``empty`` inductive type is the proposition that has no
proofs. The logical consistency of F* depends on there being no closed
terms whose type is ``empty``.

.. code-block:: fstar

   type empty =

This definition might look odd at first: it defines an inductive type
with *zero* constructors. This is perfectly legal in F*, unlike in
languages like OCaml or F#.

The squashed variant of ``empty`` is called ``False`` and is defined
as shown below:

.. code-block:: fstar

   let False = squash empty

Introduction
++++++++++++

The ``False`` proposition has no introduction form, since it has no proofs.

Elimination
+++++++++++

From a (hypothetical) proof of ``False``, one can build a proof of any
other type.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: empty_elim$
   :end-before: //SNIPPET_END: empty_elim$

This body of ``elim_false`` is a ``match`` expression with no branches,
which suffices to match all the zero cases of the ``empty`` type.

``FStar.Pervasives.false_elim`` provides an analogous elimination rule
for ``False``, as shown below, where the termination check for the
recursive call succeeds trivially in a context with ``x:False``.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: false_elim$
   :end-before: //SNIPPET_END: false_elim$

Truth
.....

The ``trivial`` inductive type has just a single proof, ``T``.

.. code-block::

   type trivial = T

.. note::

   Although isomorphic to the ``unit`` type with its single element
   ``()``, for historic reasons, F* uses the ``trivial`` type to
   represent trivial proofs. In the future, it is likely that
   ``trivial`` will just be replaced by ``unit``.

The squashed form of ``trivial`` is written ``True`` and is defined as:

.. code-block::

   let True = squash trivial

Introduction
++++++++++++

The introduction forms for both the constructive and squashed variants
are trivial.

.. code-block::

   let _ : trivial = T
   let _ : True = ()

Elimination
+++++++++++

There is no elimination form, since proofs of ``trivial`` are vacuous
and cannot be used to derive any other proofs.


Conjunction
...........

A constructive proof of ``p`` and ``q`` is just a pair containing
proofs of ``p`` and ``q``, respectively.

.. code-block::

   type pair (p q:Type) = | Pair : _1:p -> _1:q -> pair p q

.. note::

   This type is isomorphic to the tuple type ``p & q`` that we
   encountered previously :ref:`here <Part1_tuples>`. F* currently
   uses a separate type for pairs used in proofs and those used to
   pair data, though there is no fundamental reason for this. In the
   future, it is likely that ``pair`` will just be replaced by the
   regular tuple type.

The squashed form of conjunction is written ``/\`` and is defined as
follows:

.. code-block::

   let ( /\ ) (p q:Type) = squash (pair p q)

Introduction
++++++++++++

Introducing a conjunction simply involves constructing a pair.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: and_intro$
   :end-before: //SNIPPET_END: and_intro$

To introduce the squashed version, there are two options. One can
either rely entirely on the SMT solver to discover a proof of ``p /\
q`` from proofs of ``p`` and ``q``, which it is usually very capable
of doing.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: conj_intro$
   :end-before: //SNIPPET_END: conj_intro$

Or, if one needs finer control, F* offers specialized syntax
(defined in ``FStar.Classical.Sugar``) to manipulate each of the
non-trivial logical connectives, as shown below.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: conj_intro_sugar$
   :end-before: //SNIPPET_END: conj_intro_sugar$

The sugared introduction form for conjunction is, in general, as
follows:

.. code-block:: fstar

   introduce p /\ q //Term whose top-level connective is /\
   with proof_of_p  //proof_of_p : squash p
   and  proof_of_q  //proof_of_q : squash q

Elimination
+++++++++++

Eliminating a conjunction comes in two forms, corresponding to
projecting each component of the pair.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: and_elim$
   :end-before: //SNIPPET_END: and_elim$

For the squashed version, we again have two styles, the first relying
on the SMT solver.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: conj_elim$
   :end-before: //SNIPPET_END: conj_elim$

And a style using syntactic sugar:

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: conj_elim_sugar$
   :end-before: //SNIPPET_END: conj_elim_sugar$

Disjunction
...........

A constructive proof of ``p`` or ``q`` is represented by the following
inductive type:

.. code-block:: fstar

   type sum (p q:Type) =
     | Left : p -> sum p q
     | Right : q -> sum p q

The constructors ``Left`` and ``Right`` inject proofs of ``p`` or
``q`` into a proof of ``sum p q``.

.. note::

   Just like before, this type is isomorphic to the type ``either p q``
   from ``FStar.Pervasives``.

The classical connective ``\/`` described previously is just a
squashed version of ``sum``.

.. code-block:: fstar

   let ( \/ ) (p q: Type) = squash (sum p q)

Introduction
++++++++++++

As with the other connectives, introducing a constructive disjunction
is just a matter of using the ``Left`` or ``Right`` constructor.

To introduce the squashed version ``\/``, one can either rely on the
SMT solver, as shown below.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: or_intro$
   :end-before: //SNIPPET_END: or_intro$

Or, using the following syntactic sugar, one can specifically provide
a proof for either the ``Left`` or ``Right`` disjunct.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: or_intro_sugar$
   :end-before: //SNIPPET_END: or_intro_sugar$

Elimination
+++++++++++

Eliminating a disjunction requires a *motive*, a goal proposition to
be derived from a proof of ``sum p q`` or ``p \/ q``.

In constructive style, eliminating ``sum p q`` amounts to just
pattern matching on the cases and constructing a proof of the goal
by applying a suitable goal-producing hypothesis.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: sum_elim$
   :end-before: //SNIPPET_END: sum_elim$

The squashed version is similar, except the case analysis can either
be automated by SMT or explicitly handled using the syntactic
sugar.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: or_elim$
   :end-before: //SNIPPET_END: or_elim$

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: or_elim_sugar$
   :end-before: //SNIPPET_END: or_elim_sugar$

Implication
...........

One of the elimination principles for disjunction used the implication
connective ``==>``. Its definition is shown below:

.. code-block:: fstar

   let ( ==> ) (p q : Type) = squash (p -> q)

That is, ``==>`` is just the squashed version of the non-dependent
arrow type ``->``.

.. note::

   In ``Prims``, the definition of ``p ==> q`` is actually ``squash (p
   -> GTot q)``, a **ghost** function from ``p`` to ``q``. We'll learn
   about this more when we encounter effects.

Introduction
++++++++++++

Introducing a constructive arrow ``p -> q`` just involves constructing
a :math:`\lambda`-literal of the appropriate type.

One can turn several kinds of arrows into implications, as shown below.

One option is to directly use a function from the ``FStar.Classical``
library, as shown below:

.. code-block:: fstar

   val impl_intro_tot (#p #q: Type) (f: (p -> q)) : (p ==> q)

However, this form is seldom used in F*. Instead, one often works with
functions between squashed propositions, or Lemmas, turning them into
implications when needed. We show a few styles below.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: implies_intro$
   :end-before: //SNIPPET_END: implies_intro$

Unlike the other connectives, there is no fully automated SMT-enabled
way to turn an arrow type into an implication. Of course, the form
shown above remains just sugar: it may be instructive to look at its
desugaring, shown below.

.. code-block:: fstar

   let implies_intro_1 (#p #q:Type) (pq: (squash p -> squash q))
     : squash (p ==> q)
     = FStar.Classical.Sugar.implies_intro
              p
              (fun (_: squash p) -> q)
              (fun (pf_p: squash p) -> pq pf_p)

``FStar.Squash`` and ``FStar.Classical`` provide the basic building
blocks and the sugar packages it into a more convenient form for use.

Elimination
+++++++++++

Of course, the elimination form for a constructive implication, i.e.,
``p -> q`` is just function application.

.. code-block:: fstar

   let arrow_elim #p #q (f:p -> q) (x:p) : q = f x

The elimination rule for the squashed form is the classical logical
rule *modus ponens*, which is usually very well automated by SMT, as
shown in ``implies_elim`` below. We also provide syntactic sugar for
it, for completeness, though it is seldom used in practice.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: implies_elim$
   :end-before: //SNIPPET_END: implies_elim$

Negation
........

Negation is just a special case of implication.

In its constructive form, it corresponds to ``p -> empty``.

In ``Prims``, we define ``~p`` as ``p ==> False``.

Being just an abbreviation for an implication to ``False``, negation
has no particular introduction or elimination forms of its
own. However, the following forms are easily derivable.

Introduction (Exercise)
+++++++++++++++++++++++

Prove the following introduction rule for negation:

`Exercise file <../code/exercises/Part2.Connectives.Negation.fst>`__

.. code-block:: fstar

   val neg_intro #p (f:squash p -> squash False)
     : squash (~p)

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Connectives.fst
       :language: fstar
       :start-after: //SNIPPET_START: neg_intro$
       :end-before: //SNIPPET_END: neg_intro$

--------------------------------------------------------------------------------


Elimination (Exercise)
+++++++++++++++++++++++

Prove the following elimination rule for negation using the sugar
rather than just SMT only.

.. code-block:: fstar

   val neg_elim #p #q (f:squash (~p)) (x:unit -> Lemma p)
     : squash (~q)

`Exercise file <../code/exercises/Part2.Connectives.Negation.fst>`__

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Connectives.fst
       :language: fstar
       :start-after: //SNIPPET_START: neg_elim$
       :end-before: //SNIPPET_END: neg_elim$

--------------------------------------------------------------------------------

Universal Quantification
........................

Whereas implication is represented by the non-dependent arrow ``p ->
q``, universal quantification corresponds to the dependent arrow ``x:t
-> q x``. Its classical form in ``forall (x:t). q x``, and is defined
in as shown below:

.. code-block:: fstar

   let ( forall ) #t (q:t -> Type) = squash (x:t -> q x)

.. note::

   As with ``==>``, in ``Prims`` uses ``x:t -> GTot (q x)``, a ghost
   arrow, though the difference is not yet significant.

Introduction
++++++++++++

Introducing a dependent function type ``x:t -> p x`` is just like
introducing a non-dependent one: use a lambda literal.

For the squashed form, F* provides sugar for use with several styles,
where names corresponding to each of the ``forall``-bound variables on
the ``introduce`` line are in scope for the proof term on the ``with``
line.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: forall_intro$
   :end-before: //SNIPPET_END: forall_intro$

Note, as ``forall_intro_3`` shows, the sugar also works for ``forall``
quantifiers of arities greater than 1.

Elimination
+++++++++++

Eliminating a dependent function corresponds to dependent function
application.

.. code-block:: fstar

   let dep_arrow_elim #t #q (f:(x:t -> q x)) (x:t) : q x = f x

For the squashed version, eliminating a ``forall`` quantifier amounts
to instantiating the quantifier for a given term. Automating proofs
that require quantifier instantiation is a large topic in its own
right, as we'll cover in a later section---this `wiki page
<https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns>`_
provides some hints.

Often, eliminating a universal quantifier is automated by the SMT
solver, as shown below, where the SMT solver easily instantiates the
quantified hypothesis ``f`` with ``a``.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: forall_elim_1$
   :end-before: //SNIPPET_END: forall_elim_1$

But, F* also provides syntactic sugar to explicitly trigger quantifier
insantiation (as shown below), where the terms provided on the
``with`` line are instantiations for each of the binders on the
``eliminate`` line.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: forall_elim_sugar$
   :end-before: //SNIPPET_END: forall_elim_sugar$

Its desugaring may be illuminating:

.. code-block:: fstar

   let forall_elim_2 (f: squash (forall (x0: t0) (x1: t1 x0). q x0 x1))
                     (v0: t0)
                     (v1: t1 v0)
     : squash (q v0 v1)
     = FStar.Classical.Sugar.forall_elim
           #(t1 v0)
           #(fun x1 -> q v0 x1)
           v1
           (FStar.Classical.Sugar.forall_elim
              #t0
              #(fun x0 -> forall (x1: t1 x0). q x0 x1)
              v0
              ())

.. _Part2_connectives_exists:

Existential Quantification
..........................

Finally, we come to existential quantification. Its constructive form
is a dependent pair, a dependent version of the pair used to represent
conjunctions. The following inductive type is defined in ``Prims``.

.. code-block:: fstar

   type dtuple2 (a:Type) (b: a -> Type) =
      | Mkdtuple2 : x:a -> y:b x -> dtuple2 a b

As with ``tuple2``, F* offers specialized syntax for ``dtuple2``:

   * Instead of ``dtuple2 a (fun (x:a) -> b x)``, one writes ``x:a & b x``.

   * Instead of writing ``Mkdtuple2 x y``, one writes ``(| x, y |)``.

The existential quantifier ``exists (x:t). p x`` is a squashed version
of the dependent pair:

.. code-block:: fstar

   let ( exists ) (#a:Type) (#b:a -> Type) = squash (x:a & b x)

Introduction
++++++++++++

Introducing a constructive proof of ``x:a & b x`` is just a question
of using the constructor---we show a concrete instance below.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: dtuple2_intro$
   :end-before: //SNIPPET_END: dtuple2_intro$

For the squashed version, introducing an ``exists (x:t). p x``
automatically using the SMT solver requires finding an instance ``a``
for the quantifier such that ``p a`` is derivable---this is the dual
problem of quantifier instantiation mentioned with universal

In the first example below, the SMT solver finds the instantiation and
proof automatically, while in the latter two, the user picks which
instantiation and proof to provide.

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: exists_intro$
   :end-before: //SNIPPET_END: exists_intro$

Elimination
+++++++++++

Just as with disjunction and conjunction, eliminating ``dtuple2`` or
``exists`` requires a motive, a goal proposition that *does not
mention* the bound variable of the quantifier.

For constructive proofs, this is just a pattern match:

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: dtuple2_elim$
   :end-before: //SNIPPET_END: dtuple2_elim$

For the ``exists``, the following sugar provides an elimination
principle:

.. literalinclude:: ../code/Connectives.fst
   :language: fstar
   :start-after: //SNIPPET_START: exists_elim$
   :end-before: //SNIPPET_END: exists_elim$

Names corresponding to the binders on the ``eliminate`` line are in
scope in the ``with`` line, which additionally binds a name for a
proof term corresponding to the body of the existential formula. That
is, in the examples above, ``x:t`` is implicitly in scope for the proof
term, while ``pf_p: squash p``.

Exercise
++++++++

In a :ref:`previous exercise <Part2_merkle_insert>`, we defined a
function to insert an element in a Merkle tree and had it return a new
root hash and an updated Merkle tree. Our solution had the following
signature:

.. literalinclude:: ../code/MerkleTree.fst
   :language: fstar
   :start-after: //SNIPPET_START: update_hint
   :end-before: //SNIPPET_END: update_hint

Revise the solution so that it instead returns a dependent
pair. ``dtuple2`` is already defined in ``Prims``, so you don't have
to define it again.

`Exercise file <../code/exercises/Part2.MerkleTreeUpdate.fst>`__

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/MerkleTree.fst
       :language: fstar
       :start-after: //SNIPPET_START: update
       :end-before: //SNIPPET_END: update
