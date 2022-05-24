.. _Part2_universes:


Universes
=========

As mentioned :ref:`earlier <Part1_type_of_types>`, ``Type`` is the
type of types. So, one might ask the question, what is the type of
``Type``? Indeed, one can write the following and it may appear at
first that the type of ``Type`` is ``Type``.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: ty$
   :end-before: //SNIPPET_END: ty$

However, behind the scenes, F* actually has a countably infinite
hierarchy of types, ``Type u#0``, ``Type u#1``, ``Type u#2``, ..., and
the type of ``Type u#i`` is actually ``Type u#(i + 1)``.  The ``u#i``
suffixes are called *universe levels* and if you give F* the following
option, it will actually show you the universe levels it inferred when
it prints a term.

.. code-block:: fstar

   #push-options "--print_universes"                

With this option enabled, in fstar-mode.el, the F* emacs plugin,
hovering on the symbol ``ty`` prints ``Type u#(1 + _)``, i.e., the
type of ``ty`` is in a universe that is one greater than some universe
metavariable ``_``, i.e., ``ty`` is universe *polymorphic*. But, we're
getting a bit ahead of ourselves.

In this chapter, we'll look at universe levels in detail, including
why they're necessary to avoid paradoxes, and showing how to
manipulate definitions that involve universes. For the most part, F*
infers the universe levels of a term and you don't have to think too
much about it---in fact, in all that we've seen so far, F* inferred
universe levels behind the scenes and we haven't had to mention
them. Though, eventually, they do crop up and understanding what they
mean and how to work with them becomes necessary.

Other resources to learn about universes:

  * The Agda manual has a nice `chapter on universes
    <https://agda.readthedocs.io/en/latest/language/sort-system.html#sort-system>`_,
    including universe polymorphism.

  * This `chapter from Adam Chlipala's *Certified Programming with
    Dependent Types*
    <http://adam.chlipala.net/cpdt/html/Cpdt.Universes.html>`_
    describes universes in Coq. While it also provides useful
    background, F*'s universe system is more similar to Agda (and
    Lean) than Coq.


Universes: Basics
-----------------

A universe annotation on a term takes the form ``u#l``, where ``l`` is
a universe level. The universe levels are terms from the following
grammar:

.. code-block::

   k ::= 0 | 1 | 2 | ...    any natural number constant
   l ::= k                  universe constant
       | l + k | k + l      constant offset from level l
       | max l1 l2          maximum of two levels
       | a | b | c | ...    level variables


Let's revisit our first example, this time using explicit universe
annotations to make things clearer.

We've defined, below, instances of ``Type`` for universe levels ``0,
1, 2`` and we see that each of them has a type at the next level. The
constant ``Type u#0`` is common enough that F* allows you to write
``Type0`` instead.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: ty_constants$
   :end-before: //SNIPPET_END: ty_constants$

If you try to define ``ty_bad`` below, F* complains with the following
error:

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: ty_bad$
   :end-before: //SNIPPET_END: ty_bad$

.. code-block::

   Expected expression of type "Type0"; got expression "Type0" of type "Type u#1"

.. note::                

   That said, if we didn't turn on the option ``--print_universes``, the
   error message you get may be, sadly, bit baffling:

   .. code-block::

       Expected expression of type "Type"; got expression "Type" of type "Type"

   Turning on ``--print_universes`` and ``--print_implicits`` is a
   good way to make sense of type errors where the expected type and
   the type that was computed seem identical.

   The restriction that prevents a ``Type`` from being an inhabitant
   of itself if sometimes called *predicativity*. The opposite,
   *impredicativity*, if not suitably restricted, usually leads to
   logical inconsistency. F* provides a limited form of
   impredicativity through the use of ``squash`` types, which we'll
   see towards the end of this chapter.
   
Now, instead of defining several constants like ``ty0, ty1, ty2``
etc., F* can be *universe polymorphic*. Below, we define ``ty_poly``
as ``Type u#a``, for any universe variable ``a``, and so ``ty`` has
type ``Type u#(a + 1)``. 

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: ty_poly$
   :end-before: //SNIPPET_END: ty_poly$

One way to think of ``ty_poly`` is as a "definition template"
parameterized by the by the universe-variable ``a``. One can
instantiate ``ty_poly`` with a specific universe level ``l`` (by
writing ``ty_poly u#l``) and obtain a copy of its definition
specialized to level ``l``. F* can prove that instantiation of
``ty_poly`` are equal to the non-polymorphic definitions we had
earlier. As the last example shows, F* can usually infer the universe
instantiation, so you often don't need to write it.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: ty_poly_assert$
   :end-before: //SNIPPET_END: ty_poly_assert$

Universe computations for other types
-------------------------------------

Every type in F* lives in a particular universe. For example, here are
some common types in ``Type u#0``.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: some common types$
   :end-before: //SNIPPET_END: some common types$


**Universe of an arrow type**: In general, the universe of an arrow
type ``x:t -> t'`` is the the maximum of the universe of ``t`` and
``t'``.
      
This means that functions that are type-polymorphic live in higher
universes. For example, the polymorphic identity function that we saw
in an :ref:`earlier section <Part1_polymorphism_and_inference>`, is
actually also polymorphic in the universe level of its type argument.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: poly_id$
   :end-before: //SNIPPET_END: poly_id$

That is, the type of the identity function ``id`` is ``id_t`` or
``a:Type u#a -> a -> a`` or ``id_t``---meaning, for all types ``a`` in
universe ``Type u#i``, ``id a`` is function of type ``a -> a``.

Now, ``id_t`` is itself a type in universe ``Type u#(i + 1)``, and
since the ``id`` function can be applied to types in all universes, it
can be applied to ``id_t`` too. So, it may look like this allows one
to write functions that can be applied to themselves---which would be
bad, since that would allow one to create infinite loops and break
F*'s logic.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: seemingly_self_application$
   :end-before: //SNIPPET_END: seemingly_self_application$

However, if we write out the universe levels explicitly, we see that
actually we aren't really applying the ``id`` function to
itself. Things are actually stratified, so that we applying an
instance of ``id`` at universe ``u#(i + 1)`` to the instance of ``id``
at universes ``u#i``.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: stratified_application$
   :end-before: //SNIPPET_END: stratified_application$


One intuition for what's happening here is that there are really
infinitely many instances of the F* type system nested within each
other, with each instance forming a universe. Type-polymorphic
functions (like ``id``) live in some universe ``u#(a + 1)`` and are
parameterized over all the types in the immediately preceding universe
``u#a``. The universe levels ensure that an F* function within
universe level ``u#a`` cannot consume or produce terms that live in
some greater universe.

Universe level of an inductive type definition
..............................................

F* computes a universe level for inductive type definitions. To
describe the rules for this in full generality, consider again the
general form of an inductive type definition, shown first :ref:`here
<Part2_inductives>`, but this type with the universe level of each
type constructor made explicit, i.e., :math:`T_1` constructs a type in
universe :math:`\mathsf{Type~u\#l_1}`

.. math::

   \mathsf{type}~T_1~\overline{(x₁:p_i)} : \overline{y_1:q_1} → \mathsf{Type~u\#l_1} = \overline{| D_1 : t_1} \\
   \mathsf{and}~T_n~\overline{(x_n:p_n)} : \overline{y_n:q_n} → \mathsf{Type~u\#l_n} =  \overline{| D_n : t_n} \\

Recall that each type constructor :math:`T_i` has zero or more *data
constructors* :math:`\overline{D_i:t_i}` and for each data constructor
:math:`D_{ij}`, its type :math:`t_{ij}` must be of the form
:math:`\overline{z_{ij}:s_{ij}} → Tᵢ~\bar{x_i}~\bar{e}`

In addition to checking, as usual, that the each :math:`tᵢⱼ` is
well-typed, F* also checks the universe levels according to the
following rule:

  * Assuming that each :math:`T_i` has universe level :math:`l_i`

  * For every data constructor :math:`D_{ij}`, and for each of its
    arguments :math:`z_{ijk} : s_{ijk}`, check :math:`s_{ijk} : \mathsf{Type~u\#l_{ijk}}` and :math:`l_{ijk} ≤ l_i`.

In other words, the universe level of each type constructor must not
be less than less than the universe of any of the fields of data
constructors.

In practice, F* infers the universe levels :math:`l_1, …, l_n`, by
collecting level-inequality constraints and solving them using the
``max`` operator on universe levels, i.e., :math:`l_i` is set to
:math:`max_{jk} l_{ijk}`, the maximum of the universe levels of all
the fields of the constructors :math:`\overline{D_i : t_i}`. Let's
look at some examples.

The ``list`` type
+++++++++++++++++

The ``list`` type below is parameterized by ``a:Type u#a`` and
constructs a type in the same universe.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: list$
   :end-before: //SNIPPET_END: list$

* The ``Nil`` constructor has no fields, so it imposes no
  constraints on the universe level of ``list a``.

* The ``Cons`` constructor has two fields. Its first field ``hd``
  has type ``a: Type u#a``: we have a constraint that ``u#a ≤ u#a``; and
  the second field, by assumption, has type ``list a : Type u#a``,
  and again we have the constraint ``u#a ≤ u#a``.

F* infers the minimum satisfiable universe level assignment, by
default. But, there are many solutions to the inequalities, and if
needed, one can use annotations to pick another solution. For example,
one could write this, though it rarely makes sense to pick a universe
for a type higher that necessary (see :ref:`this section <Part2_Universes_raising>` for an exception).

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: list'$
   :end-before: //SNIPPET_END: list'$

.. note::

   Universe level variables are drawn from a different namespace than
   other variables. So, one often writes ``a:Type u#a``, where ``a``
   is a regular variable and ``u#a`` is the universe level of the type
   of ``a``.
                
The ``pair`` type
+++++++++++++++++
                
The ``pair`` type below is parameterized by ``a:Type u#a`` and
``b:Type u#b`` and constructs a type in ``u#(max a b)``.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: pair$
   :end-before: //SNIPPET_END: pair$

* The ``fst`` field is in ``u#a`` and so we have ``u#a ≤ u#(max a b)``.

* The ``snd`` field is in ``u#b`` and so we have ``u#b ≤ u#(max a b)``.    

The ``top`` type
+++++++++++++++++
                
The ``top`` type below packages a value at any type ``a:Type u#a``
with its type.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: top$
   :end-before: //SNIPPET_END: top$

* The ``a`` field of ``Top`` in ``u#(a + 1)`` while the ``v`` field
  is in ``u#a``. So, ``top`` itself is in ``u#(max (a + 1) a)``,
  which simplifies to ``u#(a + 1)``.

One intuition for why this is so is that from a value of type ``t :
top`` one can write a function that computes a value of type ``Type
u#a``, i.e., ``Top?.a t``. So, if, for instance we have ``top: Type
u#a`` and ``t:top``, then ``Top?.a : top -> Type u#a``, which would
break the stratification of universes. From a value ``top`` in
universe ``u#a``, we would be able to project out a value in
``Type u#(a + 1)``, which leads to a paradox, as we'll see next.

What follows is quite technical and you only need to know that the
universe system exists to avoid paradoxes, not how such paradoxes are
constructed.
    
Russell's Paradox
-----------------

Type theory has its roots in Bertrand Russell's work `The Principles
of Mathematics
<https://en.wikipedia.org/wiki/The_Principles_of_Mathematics>`_, which
explores the logical foundations of mathematics and set theory. In
this work, Russell proposed the paradoxical set :math:`\Delta` whose
elements are exactly all the sets that don't contain themselves and
considered whether or not :math:`\Delta` contained itself. This
self-referential construction is paradoxical since:

  * If :math:`\Delta \in \Delta`, then since the only sets in
    :math:`\Delta` are the sets that don't contain themselves, we can
    conclude that :math:`\Delta \not\in \Delta`.

  * On the other hand, if :math:`\Delta \not\in \Delta`, then since
    :math:`\Delta` contains all sets that don't contain themselves, we
    can conclude that :math:`\Delta \in \Delta`.

To avoid such paradoxes, Russell formulated a stratified system of
types to prevent nonsensical constructions that rely on
self-reference. The universe levels of modern type theories serve much
the same purpose.

In fact, as the construction below shows, if it were possible to break
the stratification of universes in F*, then one can code up Russell's
:math:`\Delta` set and prove ``False``. This construction is derived
from `Thorsten Altenkirch's Agda code
<http://www.cs.nott.ac.uk/~psztxa/g53cfr/l20.html/l20.html>`_. Liam
O'Connor also provides some useful context and comparison `here
<http://liamoc.net/posts/2015-09-10-girards-paradox.html>`_. Whereas
the Agda code uses a special compiler pragma to enable unsound
impredicativity, in F* we show how a user-introduced axiom can
simulate impredicativity and enable the same paradox.


Breaking the Universe System
.............................

Consider the following interface that intentionally breaks the
stratification of F*'s universe system. We'll need the following
ingredients:

1. A strictly positive type constructor ``lower`` that takes a type in
   any universe ``a:Type u#a``, and returns a type in ``u#0``. Note,
   we covered :ref:`strictly positive type functions, previously
   <Part2_strictly_positive_annotations>`. 

.. literalinclude:: ../code/UnsoundUniverseLowering.fst
   :language: fstar
   :start-after: //SNIPPET_START: lower$
   :end-before: //SNIPPET_END: lower$                 

2. Assume there is a function called ``inject``, which takes value of
   type ``x:a`` and returns value of type ``lower a``.

.. literalinclude:: ../code/UnsoundUniverseLowering.fst
   :language: fstar
   :start-after: //SNIPPET_START: inject$
   :end-before: //SNIPPET_END: inject$                 

3. ``lower`` and ``inject`` on their own are benign (e.g., ``let lower
   _ = unit`` and ``let inject _ = ()``). But, now if we assume we
   have a function ``project`` that is the inverse of ``inject``, then
   we've opened the door to paradoxes.

.. literalinclude:: ../code/UnsoundUniverseLowering.fst
   :language: fstar
   :start-after: //SNIPPET_START: project$
   :end-before: //SNIPPET_END: project$                 

Encoding Russell's Paradox
...........................

To show the paradox, we'll define a notion of ``set`` that can be
defined by a form of set comprehensions ``f: x -> set``, where
``x:Type u#0`` is an index to the comprehension, supposedly bounding
the cardinality of the set.  We'll subvert the universe system by
treating ``set`` as living in universe ``u#0``, even though they
contain a term ``x:Type u#0`` that has universe level ``u#1``

.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: set$
   :end-before: //SNIPPET_END: set$

This construction allows us to define many useful sets.

For example, the empty set ``zero`` as no elements; or the singleton
set ``one`` whose only element is the empty set; or the set ``two``
that contains the empty set ``zero`` and the singleton set ``one``.
                
.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: zero,one,two$
   :end-before: //SNIPPET_END: zero,one,two$

One can also define set membership: A set ``a`` is a member of a set
``b``, if one can exhibit an element ``v`` of the indexing type of
``b`` (i.e., ``(project b).x``), such that ``b``'s comprehension
``(project b).f`` applied to ``v`` is ``a``. For example, on can prove
``mem zero two`` by picking ``true`` for ``v`` and ``mem one two`` by
picking ``false`` for ``v``. Non-membership is just the negation of
membership.

.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: mem$
   :end-before: //SNIPPET_END: mem$

Now, we are ready to define Russell's paradoxical set
:math:`\Delta`. First, we define ``delta_big`` in a larger universe
and then use ``inject`` to turn it into a ``set : Type u#0``. The
encoding of ``delta_big`` is fairly direct: Its indexing type are sets
``s`` paired with proofs that ``s`` does not contain itself; and its
comprehension function just returns ``s`` itself.
      
.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: delta$
   :end-before: //SNIPPET_END: delta$

We can now prove both ``delta `mem` delta`` and ``delta `not_mem`
delta``, using the unsound ``inj_proj`` axiom that breaks the universe
system, and derive ``False``.

.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: proof$
   :end-before: //SNIPPET_END: proof$

Impredicativity, refinement types, and FStar.Squash
---------------------------------------------------

.. _Part2_Universes_raising:

Raising universes, or the lack of cumulativity
----------------------------------------------


Universe Inference: Annotations and conventions
-----------------------------------------------


