.. _Part2_stlc:

Simply Typed Lambda Calculus
============================

In this chapter, we look at how inductively defined types can be used
to represent both raw data, inductively defined relations, and proofs
relating the two.

By way of illustration, we develop a case study in the simply typed
lambda calculus (STLC), a very simple programming language which is
often studied in introductory courses on the semantics of programming
languages. Its syntax, type system, and runtime behavior can be
described in just a few lines. The main result we're interested in
proving is the soundness of the type system, i.e., that if a program
type checks then it can be executed safely without a certain class of
runtime errors.

If you haven't seen the STLC before, there are several good resources
for it available on the web, including the `Software Foundations book
<https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html>`_,
though we'll try to keep the presentation here as self-contained as
possible. Thanks to Simon Forest, Catalin Hritcu, and Simon Schaffer
for contributing parts of this case study.

Syntax
++++++

The syntax of programs :math:`e` is defined by the context-free
grammar shown below.

.. math::

   e~::=~()~|~x~|~\lambda x:t. e_0~|~e_0~e_1

This can be read as follows: a program :math:`e` is either

  * the unit value :math:`()`;

  * a variable :math:`x`;

  * a lambda term :math:`\lambda x:t. e_0` associating a variable
    :math:`x` to a type :math:`t` and a some sub-program :math:`e_0`;

  * or, the application of the sub-program :math:`e_0` to another
    sub-program :math:`e_1`.

The syntax of the type annotation :math:`t` is also very simple:

.. math::

   t~::=~\mathsf{unit}~|~t_0 \rightarrow t_1

A type :math:`t` is either

  * the :math:`\mathsf{unit}` type constant;

  * or, arrow type :math:`t_0 \rightarrow t_1` formed from two smaller types
    :math:`t_0` and :math:`t_1`

This language is very minimalistic, but it can be easily extended with
some other forms, e.g., one could add a type of integers, integer
constants, and operators like addition and subtraction. We'll look at
that as part of some exercises.

We'll define the syntax of types and programs formally in F* as a pair
of simple inductive datatypes ``typ`` (for types) and ``exp`` (for
programs or expressions) with a constructor for each of the cases
above.

The main subtlety is in the representation of variables.  For example,
ignoring the type annotations, in the term
:math:`\lambda x. (\lambda x. x)` the inner lambda binds *a different*
:math:`x` than the outer one, i.e., the term is equivalent to
:math:`\lambda x. (\lambda y. y)` and our representation of programs
must respect this this convention. We'll use a technique called de
Bruijn indices, where the names of the variables are no longer
significant and instead each variable is represented by a natural
number describing the number of :math:`\lambda` binders that one must
cross when traversing a term from the occurrence of the variable to
that variable's :math:`\lambda` binder.

For example, the terms :math:`\lambda x. (\lambda x. x)` and
:math:`\lambda x. (\lambda y. y)` are both represented as
:math:`\lambda _. (\lambda _. 0)`, since the inner occurrence of
:math:`x` is associated with the inner :math:`\lambda`; while
:math:`\lambda x. (\lambda y. (\lambda z. x))` is represented as
:math:`\lambda _. (\lambda _. (\lambda _. 2)`, since from the inner
occurrence of :math:`x` one must skip past :math:`2` :math:`\lambda`s
to reach the :math:`\lambda` associated with :math:`x`. Note, the
variable names are no longer significant in de Bruijn's notation.

Representing types
------------------

The inductive type ``typ`` defined below is our representation of
types.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: typ$
   :end-before: //SNIPPET_END: typ$

This is entirely straightforward: a constructor for each case in our
type grammar, as described above.

Representing programs
---------------------

The representation of program expressions is shown below:

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: exp$
   :end-before: //SNIPPET_END: exp$

This too is straightforward: a constructor for each case in our
program grammar, as described above. We use a ``nat`` to represent
variables ``var`` and ``ELam`` represents an annotated lambda term of
the form :math:`\lambda _:t. e`, where the name of the binder is
omitted, since we're using de Bruijn's representation.

Runtime semantics
+++++++++++++++++

STLC has just one main computation rule to execute a program---the
function application rule or a :math:`\beta` reduction, as shown below:

.. math::

   (\lambda x:t. e_0)~e_1 \longrightarrow e_0 [x \mapsto e_1]

This says that when a :math:`\lambda` literal is applied to an
argument :math:`e_1` the program takes a single step of computation to
the body of the lambda literal :math:`e_0` with every occurrence of
the bound variable :math:`x` replaced by the argument :math:`e_1`. The
substituion has to be careful to avoid "name capture", i.e.,
substituting a term in a context that re-binds its free variables. For
example, when substituting :math:`y \mapsto x` in
:math:`\lambda x. y`, one must make sure that the resulting term is
**not** :math:`\lambda x. x`. Using de Bruijn notation will help us
make precise and avoid name capture.

The other computation rules in the language are inductively defined,
e.g., :math:`e_0~e_1` can take a step to :math:`e_0'~e_1` if
:math:`e_0 \longrightarrow e_0'`, and similarly for :math:`e_1`.

By choosing these other rules in different ways one obtains different
reduction strategies, e.g., call-by-value or call-by-name etc. We'll
leave the choice of reduction strategy non-deterministic and represent
the computation rules of the STLC as an indexed inductive type, ``step
e e'`` encoding one or more steps of computation.

Formalizing an Operational Semantics
------------------------------------

The inductive type ``step`` below describes a single step of
computation in what is known as a "small-step operational
semantics". The type ``step e e'`` is a relation between an initial
program ``e`` and a program ``e'`` that results after taking one step
of computation on some sub-term of ``e``.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: step$
   :end-before: //SNIPPET_END: step$

--------------------------------------------------------------------------------

  * The constructor ``Beta`` represents the rule for :math:`\beta`
    reduction. The most subtle part of the development is defining
    ``subst`` and ``sub_beta``---we'll return to that in detail
    shortly.

  * ``AppLeft`` and ``AppRight`` allow reducing either the left- or
    right-subterm of ``EApp e1 e2``.


Exercise
^^^^^^^^

Define an inductive relation ``steps : exp -> exp -> Type`` for the
transitive closure of ``step``, representing multiple steps of
computation.

Use this `exercise file <../code/exercises/Part2.STLC.fst>`_ for all
the exercises that follow.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.STLC.fst
       :language: fstar
       :start-after: //SNIPPET_START: steps$
       :end-before: //SNIPPET_END: steps$

--------------------------------------------------------------------------------

Substitution: Failed Attempt
----------------------------

Defining substitution is the trickiest part of the system. Our first
attempt will convey the main intuitions, but F* will refuse to accept
it as well-founded. We'll then enrich our definitions to prove that
substitution terminates.

We'll define a substitution as a total function from variables ``var``
to expressions ``exp``.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: sub0$
   :end-before: //SNIPPET_END: sub0$

These kind of substitutions are sometimes called "parallel
substitutions"---the each variable is substituted independently of the
others.

When doing a :math:`\beta` reduction, we want to substitute the
variable associated with de Bruijn index ``0`` in the body of the
function with the argument ``e`` and then remove the :math:`\lambda`
binder---``sub_beta0`` does just that, replacing variable ``0`` with
``e`` and shifting other variables down by ``1``, since the
:math:`\lambda` binder of the function is removed.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: sub_beta0$
   :end-before: //SNIPPET_END: sub_beta0$

The function ``subst s e`` applies the substitution ``s`` to ``e``:

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: subst0$
   :end-before: //SNIPPET_END: subst0$

* The ``EUnit`` case is trivial---there are no variables to substitute.

* In the variable case ``subst0 s (EVar x)`` just applies ``s`` to ``x``.

* In the ``EApp`` case, we apply the substitution to each sub-term.

* The ``ELam`` case is the most interesting. To apply the substitution
  ``s`` to the body ``e1``, we have to traverse a binder. The mutally
  recursive function ``sub_elam0 s`` adjusts ``s`` to account for this
  new binder, which has de Bruijn index ``0`` in the body ``e1`` (at
  least until another binder is encountered).

  - In ``sub_elam0``, if we are applying ``s`` to the newly bound
    variable at index ``0``, then we leave that variable unchanged,
    since ``s`` cannot affect it.

  - Otherwise, we have a variable with index at least ``1``,
    referencing a binder that is bound in an outer scope; so, we shift
    it down and apply ``s`` to it, and then increment all the
    variables in the resulting term (using ``sub_inc0``) to avoid capture.

This definition of substitution is correct, but F* refuses to accept
it since we have not convinced the typechecker that ``subst0`` and
``sub_elam0`` actually terminate. In fact, F* complains in two
locations about a failed termination check.

.. note::

   This definition is expected to fail, so the ``[@@expect_failure
   [19;19]]`` attribute on the definition asks F* to check that the
   definition raises Error 19 twice. We'll look in detail as to why it
   fails, next.

Substitution, Proven Total
--------------------------

Informally, let's try to convince ourselves why ``subst0`` and
``sub_elam0`` actually terminate.

* The recursive calls in the ``EApp`` case are applied to strictly
  smaller sub-terms (``e0`` and ``e1``) of the original term ``e``.

* In the ``ELam`` case, we apply ``subst0`` to a smaller sub-term
  ``e1``, but we make a mutally recursive call to ``sub_elam0 s``
  first---so we need to check that that call terminates. This is the
  first place where F* complains.

* When calling ``sub_elam0``, it calls back to ``subst0`` on a
  completely unrelated term ``s (y - 1)``, and F* complains that this
  may not terminate. But, thankfully, this call makes use only of the
  ``sub_inc0`` substitution, which is just a renaming substitution and
  which does not make any further recursive calls. Somehow, we have to
  convince F* that a recursive call with a renaming substitution is
  fine.

To distinguish renamings from general substitutions, we'll use an
indexed type ``sub r``, shown below.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: sub$
   :end-before: //SNIPPET_END: sub$

* ``sub true`` is the type of renamings, substitutions that map
  variables to variables.

* ``sub false`` are substitutions that map at least one variable to a
  non-variable.

It's easy to prove that ``sub_inc`` is a renaming:

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: sub_inc$
   :end-before: //SNIPPET_END: sub_inc$

The function ``sub_beta`` shown below is the analog of ``sub_beta0``,
but with a type that tracks whether it is a renaming or not.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: sub_beta$
   :end-before: //SNIPPET_END: sub_beta$

* The type says that ``sub_beta e`` is a renaming if and only if ``e``
  is itself a variable.

* Proving this type, particularly in the case where ``e`` is not a
  variable requires proving an existentially quantified formula, i.e.,
  ``exists x. ~(EVar (subst_beta e) x)``. As mentioned
  :ref:`previously <Part2_connectives_exists>`, the SMT solver cannot
  always automatically instantiate existential quantifiers in the
  goal. So, we introduce the existential quantifier explicitly,
  providing the witness ``0``, and then the SMT solver can easily
  prove ``~(EVar (subst_beta e) 0)``.

Finally, we show the definitions of ``subst`` and ``sub_elam``
below---identical to ``subst0`` and ``sub_elam0``, but enriched with
types that allow expressing a termination argument to F* using a
4-ary lexicographic ordering.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: subst$
   :end-before: //SNIPPET_END: subst$

Let's analyze the recursive calls of ``subst`` and ``subst_elam`` to
see why this order works.

* Cases of ``subst``:

  - The ``EUnit`` and ``EVar`` cases are trivial, as before.

  - In ``EApp``, ``e`` is definitely not a variable, so ``bool_order
    (EVar? e)`` is ``1``. if ``e1`` (respectively ``e2``) are
    variables, then this recursive call terminates, the lexicographic
    tuple ``(0, _, _, _) << (1, _, _, _)``, regardles of the other
    values. Otherwise, the last component of the tuple decreases
    (since ``e1`` and ``e2`` are proper sub-terms of ``e``), while
    none of the other components of the tuple change.

  - The call to ``sub_elam s`` in ``ELam`` terminates because the
    third component of the tuple decreases from ``1`` to ``0``, while
    the first two do not change.

  - The final recursive call to ``subst`` terminates for similar
    reasons to the recursive calls in the ``EApp`` case, since the
    type of ``sub_elam`` guarantees that ``sub_elam s`` is renaming if
    an only of ``s`` is (so the ``r`` bit does not change).

* Cases of ``sub_elam``, in the recursive call to ``subst sub_inc (s
  (y - 1))``, we have already proven that ``sub_inc`` is a
  renaming. So, we have two cases to consider:

  - If ``s (y - 1)`` is a variable, then ``bool_order (EVar? e)``, the
    first component of the decreases clause of ``subst`` is ``0``,
    which clearly precedes ``1``, the first component of the decreases
    clause of ``subst_elam``.

  - Otherwwise, ``s (y - 1)`` is not a variable, so ``s`` is
    definitely not a renaming while ``sub_inc`` is. So, the second
    second component of the decreases clause decreases while the first
    component is unchanged.

Finally, we need to prove that ``sub_elam s`` is a renaming if and
only if ``s`` is. For this, we need two things:

* First, strengthen the type of ``subst s`` to show that it maps
  variables to variables if and only if ``r`` is a renaming,

* Second, we need to instantiate an exisential quantifier in
  ``sub_elam``, to show that if ``s`` is not a renaming, then it must
  map some ``x`` to a non-variable and, hence, ``sub_elam s (x + 1)``
  is a non-variable too. One way to do this is by asserting this fact,
  which is a sufficient hint to the SMT solver to find the
  instantiation needed. Another way is to explicitly introduce the
  existential, as in the exercise below.

In summary, using indexed types combined with well-founded recursion
on lexicographic orderings, we were able to prove our definitions
total. That said, coming up with such orderings is non-trivial and
requires some ingenuity, but once you do, it allows for relatively
compact definitions that handle both substiutions and renamings.

Exercise
^^^^^^^^

Remove the first component of the decreases clause of both definitions
and revise the definitions to make F* accept it.

Your solution should have signature

.. code-block:: fstar

   let rec subst1 (#r:bool)
                  (s:sub r)
                  (e:exp)
     : Tot (e':exp { r ==> (EVar? e <==> EVar? e') })
           (decreases %[bool_order r;
                        1;
                        e])
   ...

   and sub_elam1 (#r:bool) (s:sub r)
     : Tot (sub r)
           (decreases %[bool_order r;
                        0;
                        EVar 0])


.. container:: toggle

    .. container:: header

       **Hint**

    Inline a case of ``subst`` in ``subst_elam``.
    The answer is included with the next problem below.

--------------------------------------------------------------------------------

Replace the assertion in ``subst_elam`` with a proof that explicitly
introduces the existential quantifier.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.STLC.fst
       :language: fstar
       :start-after: //SNIPPET_START: subst1$
       :end-before: //SNIPPET_END: subst1$

--------------------------------------------------------------------------------

Type system
+++++++++++

If when running a program, if one ends up with an term like
:math:`()~e` (i.e., some non-function term like :math:`()` being used
as if it were a function) then a runtime error has occurred and the
program crashes. A type system for the simply-typed lambda calculus is
designed to prevent this kind of runtime error.

The type system is an inductively defined relation ``typing g e t``
between a

  * typing environment ``g:env``, a partial map from variable indexes
    in a particular scope to their annotated types;

  * a program expression ``e:exp``;

  * and its type ``t:typ``.

Environments
------------

The code below shows our representation of typing environments
``env``, a total function from variable indexes ``var`` to ``Some t``
or ``None``.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: env$
   :end-before: //SNIPPET_END: env$

* The ``empty`` environment maps all variables to ``None``.

* Extending an an environment ``g`` associating a type ``t`` with a
  new variable at index ``0`` involves shifting up the indexes of all
  other variables in ``g`` by ``1``.

.. _Part2_stlc_typing:

Typing Relation
---------------

The type system of STLC is defined by the inductively defined relation
``typing g e t`` shown below. A value of ``typing g e t`` is a
derivation, or a proof, that ``e`` has type ``t`` in the environment
``g``.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: typing$
   :end-before: //SNIPPET_END: typing$

* The type does not support decidable equality, since all its
  constructors contain a field ``g:env``, a function-typed value
  without decidable equality. So, we mark the inductive with the
  ``noeq`` qualifier, :ref:`as described previously
  <Part2_equality_qualifiers>`.

* ``TyUnit`` says that the unit value ``EUnit`` has type ``TUnit`` in
  all environments.

* ``TyVar`` says that a variable ``x`` is well-typed only in an
  environment ``g`` that binds its type to ``Some t``, in which case,
  the program ``EVar x`` has type ``t``. This rule ensures that no
  out-of-scope variables can be used.

* ``TyLam`` says that a function literal ``ELam t e1`` has type ``TArr
  t t'`` in environment ``g``, when the body of the function ``e1``
  has type ``t'`` in an environment that extends ``g`` with a binding
  for the new variable at type ``t`` (while shifting and retaining all
  other ariables).

* Finally, ``TyApp`` allows applying ``e1`` to ``e2`` only when ``e1``
  has an arrow type and the argument ``e2`` has the type of the formal
  parameter of ``e1``---the entire term has the return type of ``e1``.

Progress
++++++++

It's relatively easy to prove that a well-typed non-unit or lambda
term with no free variables can take a single step of
computation. This property is known as *progress*.


Exercise
--------

State and prove progress.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.STLC.fst
       :language: fstar
       :start-after: //SNIPPET_START: progress$
       :end-before: //SNIPPET_END: progress$

--------------------------------------------------------------------------------

Preservation
++++++++++++

Given a well-typed term satisfying ``typing g e t`` and ``steps e e'``,
we would like to prove that ``e'`` has the same type as ``e``, i.e.,
``typing g e' t``. This property is known as *preservation* (or
sometimes *subject reduction*). When taken in combination with
*progress*, this allows us to show that a well-typed term can keep
taking a step until it reaches a value.

The proof below establishes preservation for a single step.

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: preservation_step$
   :end-before: //SNIPPET_END: preservation_step$

* Since we know the computation takes a step, the typing derivation
  ``ht`` must be an instance of ``TyApp``.

* In the ``AppLeft`` and ``AppRight`` case, we can easily use the
  induction hypothesis depending on which side actually stepped.

* The ``Beta`` case is the most interesting and requires a lemma about
  substitutions preserving typing.

The substitution lemma follows:

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: substitution$
   :end-before: //SNIPPET_END: substitution$

It starts with a notion of typability of substitutions, ``subst_typing
s g1 g2``, which that if a variable ``x`` has type ``g1 x``, then ``s
x`` must have that same type in ``g2``.

The substitution lemma lifts this notion to expressions, stating that
applying a well-typed substitution ``subst_typing s g1 g2`` to a term
well-typed in ``g1`` produces a term well-typed in ``g2`` with the
same type.

Exercise
--------

Use the substitution lemma to state and prove the
``substitution_beta`` lemma used in the proof of preservation.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.STLC.fst
       :language: fstar
       :start-after: //SNIPPET_START: substitution_beta$
       :end-before: //SNIPPET_END: substitution_beta$

--------------------------------------------------------------------------------

Exercise
--------

Prove a preservation lemma for multiple steps.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.STLC.fst
       :language: fstar
       :start-after: //SNIPPET_START: preservation$
       :end-before: //SNIPPET_END: preservation$

--------------------------------------------------------------------------------

Exercise
++++++++

Prove a type soundness lemma with the following statement:

.. literalinclude:: ../code/Part2.STLC.fst
   :language: fstar
   :start-after: //SNIPPET_START: soundness_stmt$
   :end-before: //SNIPPET_END: soundness_stmt$

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.STLC.fst
       :language: fstar
       :start-after: //SNIPPET_START: soundness_sol$
       :end-before: //SNIPPET_END: soundness_sol$

--------------------------------------------------------------------------------

Exercise
++++++++

Add a step for reduction underneath a binder and prove the system
sound.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part2.STLC.Strong.fst
       :language: fstar
