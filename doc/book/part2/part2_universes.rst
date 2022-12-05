.. _Part2_universes:


Universes
=========

As mentioned :ref:`earlier <Part1_type_of_types>`, ``Type`` is the
type of types. So, one might ask the question, what is the type of
``Type`` itself? Indeed, one can write the following and it may appear
at first that the type of ``Type`` is ``Type``.

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

  * This chapter from Adam Chlipala's `Certified Programming with
    Dependent Types
    <http://adam.chlipala.net/cpdt/html/Cpdt.Universes.html>`_
    describes universes in Coq. While it also provides useful
    background, F*'s universe system is more similar to Agda's and
    Lean's than Coq's.


Basics
------

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

The restriction that prevents a ``Type`` from being an inhabitant of
itself if sometimes called *predicativity*. The opposite,
*impredicativity*, if not suitably restricted, usually leads to
logical inconsistency. F* provides a limited form of impredicativity
through the use of ``squash`` types, which we'll see towards the end
of this chapter.
   
.. note::                

   That said, if we didn't turn on the option ``--print_universes``, the
   error message you get may be, sadly, bit baffling:

   .. code-block::

       Expected expression of type "Type"; got expression "Type" of type "Type"

   Turning on ``--print_universes`` and ``--print_implicits`` is a
   good way to make sense of type errors where the expected type and
   the type that was computed seem identical.

   
Now, instead of defining several constants like ``ty0, ty1, ty2``
etc., F* definitions can be *universe polymorphic*. Below, we define
``ty_poly`` as ``Type u#a``, for any universe variable ``a``, and so
``ty`` has type ``Type u#(a + 1)``.

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
``a:Type u#i -> a -> a``---meaning, for all types ``a`` in
universe ``Type u#i``, ``id a`` is function of type ``a -> a``.

Now, ``id_t`` is itself a type in universe ``Type u#(i + 1)``, and
since the ``id`` function can be applied to types in any universe, it
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
itself. Things are actually stratified, so that we are instead applying an
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
<Part2_inductives>`, but this time with the universe level of each
type constructor made explicit, i.e., :math:`T_i` constructs a type in
universe :math:`\mathsf{Type~u\#l_i}`

.. math::

   \mathsf{type}~T_1~\overline{(x_1:p_i)} : \overline{y_1:q_1} \rightarrow \mathsf{Type}~u\#l_1 = \overline{\bar D_1 : t_1} \\
   \mathsf{and}~T_n~\overline{(x_n:p_n)} : \overline{y_n:q_n} \rightarrow \mathsf{Type}~u\#l_n = \overline{\bar D_n : t_n} \\

Recall that each type constructor :math:`T_i` has zero or more *data
constructors* :math:`\overline{D_i:t_i}` and for each data constructor
:math:`D_{ij}`, its type :math:`t_{ij}` must be of the form
:math:`\overline{z_{ij}:s_{ij}} \rightarrow T_i~\bar{x_i}~\bar{e}`

In addition to checking, as usual, that the each :math:`t_{ij}` is
well-typed, F* also checks the universe levels according to the
following rule:

  * Assuming that each :math:`T_i` has universe level :math:`l_i`, for
    every data constructor :math:`D_{ij}`, and for each of its
    arguments :math:`z_{ijk} : s_{ijk}`, check :math:`s_{ijk} :
    \mathsf{Type}~u\#l_{ijk}` and :math:`l_{ijk} \leq l_i`.

In other words, the universe level of each type constructor must not
be less than the universe of any of the fields of data constructors.

In practice, F* infers the universe levels :math:`l_1, \ldots, l_n`, by
collecting level-inequality constraints and solving them using the
``max`` operator on universe levels, i.e., :math:`l_i` is set to
:math:`max_{jk}~l_{ijk}`, the maximum of the universe levels of all
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

* The ``Cons`` constructor has two fields. Its first field  ``hd``
  has type ``a: Type u#a``: we have a constraint that ``u#a`` :math:`\leq` ``u#a``; and
  the second field, by assumption, has type ``list a : Type u#a``,
  and again we have the constraint ``u#a`` :math:`\leq` ``u#a``.

F* infers the minimum satisfiable universe level assignment, by
default. But, there are many solutions to the inequalities, and if
needed, one can use annotations to pick another solution. For example,
one could write this, though it rarely makes sense to pick a universe
for a type higher than necessary (see :ref:`this section <Part2_Universes_raising>` for an exception).

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

* The ``fst`` field is in ``u#a`` and so we have ``u#a`` :math:`\leq` ``u#(max a b)``.

* The ``snd`` field is in ``u#b`` and so we have ``u#b`` :math:`\leq` ``u#(max a b)``.    

The ``top`` type
+++++++++++++++++
                
The ``top`` type below packages a value at any type ``a:Type u#a``
with its type.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: top$
   :end-before: //SNIPPET_END: top$

* The ``a`` field of ``Top`` is in ``u#(a + 1)`` while the ``v`` field
  is in ``u#a``. So, ``top`` itself is in ``u#(max (a + 1) a)``,
  which simplifies to ``u#(a + 1)``.

One intuition for why this is so is that from a value of type ``t :
top`` one can write a function that computes a value of type ``Type
u#a``, i.e., ``Top?.a t``. So, if instead we have ``top: Type u#a``
and ``t:top``, then ``Top?.a : top -> Type u#a``, which would break
the stratification of universes, since from a value ``top`` in
universe ``u#a``, we would be able to project out a value in
``Type u#(a + 1)``, which leads to a paradox, as we'll see next.

What follows is quite technical and you only need to know that the
universe system exists to avoid paradoxes, not how such paradoxes are
constructed.
    
Russell's Paradox
-----------------

Type theory has its roots in Bertrand Russell's `The Principles
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
O'Connor also provides `some useful context and comparison
<http://liamoc.net/posts/2015-09-10-girards-paradox.html>`_. Whereas
the Agda code uses a special compiler pragma to enable unsound
impredicativity, in F* we show how a user-introduced axiom can
simulate impredicativity and enable the same paradox.


Breaking the Universe System
.............................

Consider the following axioms that intentionally break the
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

To show the paradox, we'll define a notion of ``set`` in terms of a
form of set comprehensions ``f: x -> set``, where ``x:Type u#0`` is
the domain of the comprehension, supposedly bounding the cardinality
of the set.  We'll subvert the universe system by treating ``set`` as
living in universe ``u#0``, even though its constructor ``Set`` has a
field ``x:Type u#0`` that has universe level ``u#1``

.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: set$
   :end-before: //SNIPPET_END: set$

This construction allows us to define many useful sets. For example,
the empty set ``zero`` uses the empty type ``False`` as the domain of
its comprehension and so has no elements; or the singleton set ``one``
whose only element is the empty set; or the set ``two`` that contains
the empty set ``zero`` and the singleton set ``one``.
                
.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: zero,one,two$
   :end-before: //SNIPPET_END: zero,one,two$

One can also define set membership: A set ``a`` is a member of a set
``b``, if one can exhibit an element ``v`` of the domain type of
``b`` (i.e., ``(project b).x``), such that ``b``'s comprehension
``(project b).f`` applied to ``v`` is ``a``.

For example, one can prove ``mem zero two`` by picking ``true`` for
``v`` and ``mem one two`` by picking ``false`` for
``v``. Non-membership is just the negation of membership.

.. literalinclude:: ../code/Russell.fst
   :language: fstar
   :start-after: //SNIPPET_START: mem$
   :end-before: //SNIPPET_END: mem$

Now, we are ready to define Russell's paradoxical set
:math:`\Delta`. First, we define ``delta_big`` in a larger universe
and then use ``inject`` to turn it into a ``set : Type u#0``. The
encoding of ``delta_big`` is fairly direct: Its domain type is the
type of sets ``s`` paired with a proof that ``s`` does not contain
itself; and its comprehension function just returns ``s`` itself.
      
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

The proofs are more detailed than they need to be, and if you're
curious, maybe you can follow along by reading the comments.

The upshot, however, is that without the stratification of universes,
F* would be unsound.


Refinement types, FStar.Squash, ``prop``, and Impredicativity
-------------------------------------------------------------

We've seen how universes levels are computed for arrow types and
inductive type definitions. The other way in which types can be formed
in F* is with refinement types: ``x:t{p}``. As we've seen previously,
a value ``v`` of type ``x:t{p}`` is just a ``v:t`` where ``p[v/x]`` is
derivable in the current scope in F*'s SMT-assisted classical
logic—there is no way to extract a proof of ``p`` from a proof of
``x:t{p}``, i.e., refinement types are F*'s mechanism for proof
irrelevance.

**Universe of a refinement type**: The universe of a refinement type ``x:t{p}`` is the universe of ``t``.

Since the universe of a refinement type does not depend on ``p``, it
enables a limited form of impredicativity, and we can define the
following type (summarized here from the F* standard library
``FStar.Squash``):

.. code-block:: fstar

   let squash (p:Type u#p) : Type u#0 = _:unit { p }
   let return_squash (p:Type u#p) (x:p) : squash p = ()

This is a lot like the ``lower`` and ``inject`` assumptions that we
saw in the previous section, but, importantly, there is no ``project``
operation to invert an ``inject``. In fact, ``FStar.Squash`` proves
that ``squash p`` is proof irrelevant, meaning that all proofs of
``squash p`` are equal.

.. code-block:: fstar

   val proof_irrelevance (p: Type u#p) (x y: squash p) : squash (x == y)

``FStar.Squash`` does provide a limited way to manipulate a proof of
``p`` given a ``squash p``, using the combinator ``bind_squash`` shown
below, which states that if ``f`` can build a proof ``squash b`` from any
proof of ``a``, then it can do so from the one and only proof of ``a``
that is witnessed by ``x:squash a``. 

.. code-block:: fstar

   val bind_squash (#a: Type u#a) (#b: Type u#b) (x: squash a) (f: (a -> squash b)) : squash b
   
It is important that ``bind_squash`` return a ``squash b``,
maintaining the proof-irrelevance of the ``squash`` type. Otherwise,
if one could extract a proof of ``a`` from ``squash a``, we would be
perilously close to the unsound ``project`` axiom which enables
paradoxes.

This restriction is similar to Coq's restriction on its ``Prop`` type,
forbidding functions match on ``Prop`` to return results outside
``Prop``.

The F* type ``prop`` (which we saw first :ref:`here <Part1_prop>`) is
defined primitively as type of all squashed types, i.e., the only
types in ``prop`` are types of the form ``squash p``; or,
equivalently, every type ``t : prop``, is a subtype of ``unit``. Being
the type of a class of types, ``prop`` in F* lives in ``u#1``

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: prop$
   :end-before: //SNIPPET_END: prop$

However, ``prop`` still offers a form of impredicativity, e.g., you
can quantify over all ``prop`` while remaining in ``prop``.

.. literalinclude:: ../code/Universes.fst
   :language: fstar
   :start-after: //SNIPPET_START: prop impredicative$
   :end-before: //SNIPPET_END: prop impredicative$

* The first line above shows that, as usual, an arrow type is in a
  universe that is the maximum of the universes of its argument and
  result types. In this case, since it has an argument ``prop : Type
  u#1`` the arrow itself is in ``u#1``.

* The second line shows that by squashing the arrow type, we can bring
  it back to ``u#0``

* The third line shows the more customary way of doing this in F*,
  where ``forall (a:prop). a`` is just syntactic sugar for ``squash
  (a:prop -> a)``. Since this is a ``squash`` type, not only does it
  live in ``Type u#0``, it is itself a ``prop``.

* The fourth line shows that the same is true for ``exists``.

.. _Part2_Universes_raising:

Raising universes and the lack of cumulativity
----------------------------------------------

In some type theories, notably in Coq, the universe system is
*cumulative*, meaning that ``Type u#i : Type u#(max (i + i) j)``;
or, that ``Type u#i`` inhabits all universes greater than
``i``. In contrast, in F*, as in Agda and Lean, ``Type u#i : Type
u#(i + 1)``, i.e., a type resides only in the universe immediately
above it.

Cumulativity is a form of subtyping on universe levels, and it can be
quite useful, enabling definitions at higher universes to be re-used
for all lower universes. However, systems that mix universe
polymorphism with cumulativity are quite tricky, and indeed, it was
only recently that Coq offered both universe polymorphism and
cumulativity.

Lacking cumulativity, F* provides a library ``FStar.Universe`` that
enables lifting a term from one universe to a higher one. We summarize
it here:

.. code-block:: fstar

   val raise_t ([@@@ strictly_positive] t : Type u#a) : Type u#(max a b)

   val raise_val (#a:Type u#a) (x:a) : raise_t u#a u#b a

   val downgrade_val (#a:Type u#a) (x:raise_t u#a u#b a) : a

   val downgrade_val_raise_val (#a: Type u#a) (x: a)
     : Lemma (downgrade_val u#a u#b (raise_val x) == x)

   val raise_val_downgrade_val (#a: Type u#a) (x: raise_t u#a u#b a)
     : Lemma (raise_val (downgrade_val x) == x)

The type ``raise_t t`` is strictly positive in ``t`` and raises ``t``
from ``u#a`` to ``u#(max a b)``. ``raise_val`` and
``downgrade_val`` are mutually inverse functions between ``t`` and
``raise_t t``.

This signature is similar in structure to the unsound signature for
``lower, inject, project`` that we use to exhibit Russell's
paradox. However, crucially, the universe levels in ``raise_t`` ensure
that the universe levels *increase*, preventing any violation of
universe stratification.

In fact, this signature is readily implemented in F*, as shown below,
where the universe annotation on ``raise_t`` explicitly defines the
type in a higher universe ``u#(max a b)`` rather than in its minimum
universe ``u#a``.

.. code-block:: fstar

  noeq
  type raise_t (a : Type u#a) : Type u#(max a b) =
    | Ret : a -> raise_t a

  let raise_val #a x = Ret x
  let downgrade_val #a x = match x with Ret x0 -> x0
  let downgrade_val_raise_val #a x = ()
  let raise_val_downgrade_val #a x = ()

.. _Part2_tips_for_universes:  

Tips for working with universes
-------------------------------

Whenever you write ``Type`` in F*, you are implicitly writing ``Type
u#?x``, where ``?x`` is a universe *metavariable* left for F* to infer. When
left implicit, this means that F* may sometimes infer universes for
your definition that are not what you expect---they may be too general
or not general enough. We conclude this section with a few tips to
detect and fix such problems.

* If you see puzzling error messages, enable the following pragma:

  .. code-block:: fstar

     #push-options "--print_implicits --print_universes"

  This will cause F* to print larger terms in error messages, which
  you usually do not want, except when you are confronted with error
  messages of the form "expected type t; got type t".

* Aside from the built-in constants ``Type u#a``, the ``->`` type
  constructor, and the refinement type former, the only universe
  polymorphic F* terms are top-level definitions. That is, while you
  can define ``i`` at the top-level and use it polymorphically:

  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: id_top_level$
     :end-before: //SNIPPET_END: id_top_level$

  You cannot do the same in a non-top-level scope:
  
  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: no_local_poly$
     :end-before: //SNIPPET_END: no_local_poly$

  Of course, non-universe-polymorphic definitions work at all scopes,
  e.g., here, the ``i`` is polymorphic in all types at universe
  ``u#0``.

  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: type_poly$
     :end-before: //SNIPPET_END: type_poly$

* If you write a ``val f : t`` declaration for ``f``, F* will compute
  the most general universe for the type ``t`` independently of the
  ``let f = e`` or ``type f =`` definition.

  A simple example of this behavior is the following. Say, you declare
  ``tup2`` as below.

  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: val tup2$
     :end-before: //SNIPPET_END: val tup2$

  Seeing this declaration F* infers ``val tup2 (a:Type u#a) (b:Type u#b)
  : Type u#c``, computing the most general type for ``tup2``.

  If you now try to define ``tup2``, 

  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: let tup2$
     :end-before: //SNIPPET_END: let tup2$

  F* complains with the following error (with ``--print_universes`` on):

  .. code-block::

     Type u#(max uu___43588 uu___43589) is not a subtype of the expected type Type u#uu___43590
     
  Meaning that the inferred type for the definition of ``tup2 a b`` is
  ``Type u#(max a b)``, which is of course not the same a ``Type
  u#c``, and, sadly, the auto-generated fresh names in the error
  message don't make your life any easier.

  The reason for this is that one can write a ``val f : t`` in a
  context where a definition for ``f`` may never appear, in which case
  F* has to compute some universes for ``t``---it chooses the most
  general universe, though if you do try to implement ``f`` you may
  find that the most general universe is too general.

  A good rule of thumb is the following:

  - Do not write a ``val`` declaration for a term, unless you are
    writing an :ref:`interface <Part3_interfaces>`. Instead, directly
    write a ``let`` or ``type`` definition and annotate it with the
    type you expect it to have---this will lead to fewer
    surprises. For example, instead of separating the ``val tup2``
    from ``let tup2`` just write them together, as shown below, and F*
    infers the correct universes.

    .. literalinclude:: ../code/Universes.fst
       :language: fstar
       :start-after: //SNIPPET_START: tuple2$
       :end-before: //SNIPPET_END: tuple2$

  - If you must write a ``val f : t``, because, say, the type ``t`` is
    huge, or because you are writing an interface, it's a good idea to
    be explicit about universes, so that when defining ``f``, you know
    exactly how general you have to be in terms of universes; and,
    conversely, users of ``f`` know exactly how much universe
    polymorphism they are getting. For example:

    .. literalinclude:: ../code/Universes.fst
       :language: fstar
       :start-after: //SNIPPET_START: tup2_again$
       :end-before: //SNIPPET_END: tup2_again$

* When defining an inductive type, prefer using parameters over
  indexes, since usually type parameters lead to types in lower
  universes. For example, one might think to define lists this way:

  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: list_alt$
     :end-before: //SNIPPET_END: list_alt$

  Although semantically equivalent to the standard list        

  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: list$
     :end-before: //SNIPPET_END: list$

  ``list_alt`` produces a type in ``u#(a + 1)``, since both ``NilAlt``
  and ``ConsAlt`` have fields of type ``a:Type u#a``. So, unless the
  index of your type varies among the constructors, use a parameter
  instead of an index.
  
  That said, recall that it's the fields of the constructors of the
  inductive type that count. You can index your type by a type in any
  universe and it doesn't influence the result type. Here's an
  artificial example.

  .. literalinclude:: ../code/Universes.fst
     :language: fstar
     :start-after: //SNIPPET_START: crazy_index$
     :end-before: //SNIPPET_END: crazy_index$
