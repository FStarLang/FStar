.. _Part4_Ghost:

Erasure and the Ghost Effect
============================

When writing proof-oriented programs, inevitably, some parts of the
program serve only to state and prove properties about the code that
actually executes. Our first non-trivial effect separates the
computationally relevant parts of the program from the computationally
irrelevant (i.e., specificational or *ghost*) parts of a program. This
separation enables the F* compiler to guarantee that all the ghost
parts of a program are optimized away entirely.

For a glimpse of what all of this is about, let's take a look again at
length-indexed vectors---we saw them first :ref:`here <Part2_vectors>`.

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: vec
   :end-before: //SNIPPET_END: vec

and a function to concatenate two vectors:

.. literalinclude:: ../code/Vec.fst
   :language: fstar
   :start-after: //SNIPPET_START: append
   :end-before: //SNIPPET_END: append

Compare this with concatenating two lists:

.. code-block:: fstar

   let rec list_append #a (l1 l2:list a) =
       match l1 with
       | [] -> []
       | hd::tl -> hd :: list_append tl l2

Superficially, because of the implicit arguments, it may look like
concatenating vectors with ``append`` is just as efficient as a
concatenating lists---the length indexes seem to impose no
overhead. But, let's look at the code that F* extracts to OCaml for
length-indexed vectors.

First, in the definition of the ``vec`` type, since OCaml is not
dependently typed, the ``nat``-index of the F* ``vec`` is replaced by
a ``'dummy`` type argument---that's fine. But, notice that the
``Cons`` constructor contains three fields: a ``Prims.nat`` for the
length of the tail of the list, the head of the list, and then then
tail, i.e., the length of the tail of the list is stored at every
``Cons`` cell, so the ``vec`` type is actually less space efficient
than an ordinary ``list``.

.. literalinclude:: ../code/Vec.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: vec *)
   :end-before: (* SNIPPET_END: vec *)

Next, in the OCaml definition of ``append``, we see that it receives
additional arguments ``n`` and ``m`` for the lengths of the vectors,
and worse, in the last case, it incurs an addition to sum ``n' + m``
when building the result vector. So, ``append`` is also less
time-efficient than ``List.append``.

.. literalinclude:: ../code/Vec.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: append *)
   :end-before: (* SNIPPET_END: append *)

This is particularly unfortunate, since the computational behavior of
``append`` doesn't actually depend on the length indexes of the input
vectors. What we need is a principled way to indicate to the F\*
compiler that some parts of a computation are actually only there for
specification or proof purposes and that they can be removed when
compiling the code, without changing the observable result computed by
the program. This is what *erasure* is about---removing the
computationally irrelevant parts of a term for compilation. 

Here's a revised version of vectors, making use of the ``erased`` type
from the ``FStar.Ghost`` library to indicate to F* which parts must be
erased by the compiler.

.. literalinclude:: ../code/VecErased.fst
   :language: fstar

We'll look into this in much more detail in what follows, but notice
for now that:

  1. The first argument of ``Cons`` now has type ``erased nat``.

  2. The implicit arguments of ``append`` corresponding to the
     indexes of the input vectors have type ``erased nat``.

If we extract this code to OCaml, here's what we get:


.. literalinclude:: ../code/VecErased.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: vec *)
   :end-before: (* SNIPPET_END: vec *)

.. literalinclude:: ../code/VecErased.ml
   :language: ocaml
   :start-after: (* SNIPPET_START: append *)
   :end-before: (* SNIPPET_END: append *)

Notice that the erased arguments have all been turned into the unit
value ``()``, and the needless addition in ``append`` is gone too.

Of course, the code would be cleaner if F* were to have entirely
removed the argument instead of leaving behind a unit term, but we
leave it to the downstream compiler, e.g., OCaml itself, to remove
these needless units. Further, if we're compiling the ML code
extracted from F* to C, then KaRaMeL does remove these additional
units in the C code it produces.


Ghost: A Primitive Effect
-------------------------

The second, primitive effect in F*'s effect system is the effect of
*ghost* computations, i.e., computation types whose effect label is
``GTot``. [#]_ The label ``GTot`` is strictly above ``Tot`` in the
effect hierarchy, i.e., ``Tot < GTot``. This means that a term with
computation type ``GTot t`` cannot influence the behavior of a term
whose type is ``Tot s``. Conversely, every ``Tot`` computation can be
implicitly promoted to a ``GTot`` computation.

Ghost computations are just as well-behaved as pure, total
terms---they always terminate on all inputs and exhibit no observable
effects, except for the value they return. As such, F*'s logical core
really includes both ``Tot`` and ``GTot`` computations. The
distinction between ``Tot`` and ``GTot`` is only relevant when
considering how programs are compiled. Ghost computations are
guaranteed to be erased by the the compiler, while ``Tot``
computations are retained.

Since ``Tot`` terms are implicitly promoted to ``GTot``, it is easy to
designate that some piece of code should be erased just by annotating
it with a ``GTot`` effect label. For example, here is an ghost version
of the factorial function:

.. literalinclude:: ../code/FactorialTailRec.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial$
   :end-before: //SNIPPET_END: factorial$

Its definition is identical to the corresponding total function that
we saw earlier, except that we have annotated the return computation
type of the function as ``GTot nat``. This indicates to F* that
``factorial`` is to be erased during compilation, and the F*
type-and-effect checker ensures that ``Tot`` computation cannot depend
on an application of ``factorial n``.

.. [#] The name ``GTot`` is meant to stand for "Ghost and Total"
       computations, and is pronounced "gee tote". However, it's a
       poor name and is far from self-explanatory. We plan to change
       the name of this effect in the future (e.g., to something like
       ``Spec``, ``Ghost``, or ``Erased``), though this is a breaking
       change to a large amount of existing F* code.

Ghost Computations as Specifications
------------------------------------

A ghost function like ``factorial`` can be used in specifications,
e.g., in a proof that a tail recursion optimization ``factorial_tail``
is equivalent to ``factorial``.

.. literalinclude:: ../code/FactorialTailRec.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_tail$
   :end-before: //SNIPPET_END: factorial_tail$

This type allows a client to use the more efficient ``fact``, but for
reasoning purposes, one can use the more canonical ``factorial``,
proven equivalent to ``fact``.

In contrast, if we were to try to implement the same specification by
directly using the factorial ghost function, F* complains with a
effect incompatibility error.
      
.. literalinclude:: ../code/FactorialTailRec.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_bad$
   :end-before: //SNIPPET_END: factorial_bad$

The error is:

.. code-block:: none

   Computed type "r: nat{r == out * factorial n}" and
   effect "GTot" is not compatible with the annotated
   type "r: nat{r == out * factorial n}" effect "Tot"

So, while F* forbids using ghost computations in ``Tot`` contexts, it
seems to be fine with accepting a use of factorial in specifications,
e.g., in the type ``r:nat { r == out * factorial n }``. We'll see in a
moment why this is permitted.

Erasable and Non-informative Types
----------------------------------

In addition to using the ``GTot`` effect to classifies computations
that must be erased, F* also provides a way to mark certain *value
types* as erasable.

Consider introducing an inductive type definition that is meant to
describe a proof term only and for that proof term to introduce no
runtime overhead. In a system like Coq, the type of Coq propositions
``Prop`` serves this purpose, but ``prop`` in F* is quite
different. Instead, F* allows an inductive type definition to be
marked as ``erasable``.

For example, when we looked at the :ref:`simply typed lambda calculus
(STLC) <Part2_stlc_typing>`, we introduced the inductive type below,
to represent a typing derivation for an STLC term. One could define a
typechecker for STLC and give it the type shown below to prove it
correct:

.. code-block:: fstar

   val check (g:env) (e:exp) : (t : typ & typing g e t)                

However, this function returns both the type ``t:typ`` computed for
``e``, we well as the typing derivation. Although the typing
derivation may be useful in some cases, often returning the whole
derivation is unnecessary. By marking the definition of the ``typing``
inductive as shown below (and keeping the rest of the definition the
same), F* guarantees that the compiler will extract ``typing g e t``
to the ``unit`` type and correspondinly, all values of ``typing g e
t`` will be erased to the unit value ``()``

.. code-block:: fstar

   [@@erasable]
   noeq
   type typing : env -> exp -> typ -> Type = ... 

Marking a type with the ``erasable`` attribute and having it be erased
to ``unit`` is safe because F* restricts how ``erasable`` types can be
used. In particular, no ``Tot`` computations should be able to extract
information from a value of an erasable type.

Closely related to erasable types are a class of types that are called
*non-informative*, defined inductively as follows:

  1. The type ``Type`` is non-informative

  2. The type ``prop`` is non-informative (i.e., unit and all its
     subtypes)
     
  3. An erasable type is non-informative
     
  4. A function type ``x:t -> Tot s`` is non-informative, if ``s`` is
     non-informative
     
  5. A ghost function type ``x:t -> GTot s`` is non-informative
     
  6. A function type ``x:t -> C``, with user-defined computation type
     ``C``, is non-informative if the effect label of ``C`` has the
     erasable attribute.

Intuitively, a non-informative type is a type that cannot be
case-analyzed in a ``Tot`` context.

With this notion of non-informative types, we can now define the
restrictions on an ``erasable`` type:

   1. Any computation that pattern matches on an erasable type must
      return a non-informative type.

   2. Inductive types with the ``erasable`` attribute do not support
      built-in decidable equality and must also be marked ``noeq``.


The `erased` type, `reveal`, and `hide`
---------------------------------------

The ``erasable`` attribute can only be added to new inductive type
definitions and every instance of that type becomes erasable. If you
have a type like ``nat``, which is not erasable, but some occurrences
of it (e.g., in the arguments to ``Vector.append``) need to be erased,
the F* standard library ``FStar.Ghost.fsti`` offers the following:

.. code-block:: fstar
                
   (** [erased t] is the computationally irrelevant counterpart of [t] *)
   [@@ erasable]
   val erased (t:Type u#a) : Type u#a

``FStar.Ghost`` also offers a pair of functions, ``reveal`` and
``hide``, that form a bijection between ``a`` and ``erased a``.

.. code-block:: fstar

   val reveal (#a: Type u#a) (v:erased a) : GTot a

   val hide (#a: Type u#a) (v:a) : Tot (erased a)

   val hide_reveal (#a: Type) (x: erased a)
     : Lemma (ensures (hide (reveal x) == x))
             [SMTPat (reveal x)]
             
   val reveal_hide (#a: Type) (x: a)
     : Lemma (ensures (reveal (hide x) == x))
             [SMTPat (hide x)]                

Importantly, ``reveal v`` breaks the abstraction of ``v:erased a``
returning just an ``a``, but doing so incurs a ``GTot`` effect---so,
``reveal`` cannot be used in an arbitrary ``Tot`` contexts.

Dually, ``hide v`` can be used to erase ``v:a``, since a ``Tot``
context cannot depend on the value of an ``erased a``.

The SMT patterns on the two lemmas allow F* and Z3 to automatically
instantiate the lemmas to relate a value and its hidden
counterpart---:ref:`this chapter <UTH_smt>` provides more details on
how SMT patterns work.

**Implicit coercions**

``FStar.Ghost.erased``, ``reveal``, and ``hide`` are so commonly used
in F* that the compiler provides some special support for it. In
particular, when a term ``v:t`` is used in a context that expects an
``erased t``, F* implictly coerces ``v`` to ``hide v``. Likewise, when
the context expects a ``t`` where ``v:erased t`` is provided, F*
implicitly coerces ``v`` to ``reveal v``.

The following examples illustrates a few usages and limitations. You
can ask F* to print the code with implicits enabled by using
``--dump_module RevealHideCoercions --print_implicits``.

.. literalinclude:: ../code/RevealHideCoercions.fst
   :language: fstar

A few comments on these examples:
      
* The first two functions illustrate how a ``nat`` is coerced
  implicitly to ``erased nat``. Note, the effect of ``auto_reveal`` is
  ``GTot``

* ``auto_reveal_2`` fails, since the the annotation claims,
  incorrectly, that the effect label is ``Tot``

* ``incr`` is just a ``nat -> nat`` function.

* ``incr_e`` is interesting because it calls ``incr`` with an
  ``erased nat`` and the annotation expects an ``erased nat``
  too. The body of ``incr_e`` is implicitly coerced to ``hide (incr
  (reveal x))``

* ``incr'`` is interesting, since it calls ``incr_e``: its body
  is implicitly coerced to ``reveal (incr_e (hide x))``

* Finally, ``poly`` shows the limitations of implicit coercion: F*
  only inserts coercions when the expected type of the term in a
  context and the type of the term differ by an ``erased``
  constructor. In ``poly``, since ``==`` is polymorphic, the expected
  type of the context is just an unresolved unification variable and,
  so, no coercion is inserted. Instead, F* complains that ``y`` has
  type ``erased nat`` when the type ``nat`` was expected.
  

.. _Ghost_in_total_contexts:

Using Ghost Computations in Total Contexts
------------------------------------------

We have already noted that ``Tot < GTot``, enabling ``Tot``
computations to be re-used in ``GTot`` contexts. For erasure to be
sound, it is crucial that ``GTot`` terms cannot be used in ``Tot``
contexts, and indeed, F* forbids this in general.
However, there is one exception where
we can directly invoke a ``GTot`` computation in a ``Tot`` context
without wrapping the result in ``Ghost.erased``.


Effect Promotion for Non-informative Types
..........................................

Consider a term ``f`` with type ``GTot s``, where ``s`` is a
non-informative type. Since ``s`` is non-informative, no total context
can extract any information from ``f``. As such, F* allows implicitly
promoting ``GTot s`` to ``Tot s``, when ``s`` is a non-informative
type.

For instance, the following is derivable,
``hide (factorial 0) : Tot (erased nat)``: let's work through it in detail.

1. We know that that ``factorial n : GTot nat``
   
2. Recall from the discussion on :ref:`evaluation order
   <Part4_evaluation_order>` and the application of functions to
   effectful arguments, ``hide (factorial 0)`` is equivalent to ``let
   x = factorial 0 in hide x``, where ``x:nat`` and
   ``hide x : Tot (erased nat)``.
   
3. From the rule for sequential composition of effectful terms, the
   type of ``let x = factorial 0 in hide x`` should be ``GTot (erased
   nat)``, since ``GTot = lub GTot Tot``.

4. Since ``erased nat`` is a non-informative type, ``GTot (erased
   nat)`` is promoted to ``Tot (erased nat)``, which is then the type
   of ``hide (factorial 0)``.


Effect promotion for ghost functions returning non-informative types
is very useful. It allows one to mix ghost computations with total
computations, so long as the result of the ghost sub-computation is
hidden with an erased type. For instance, in the code below, we use
``hide (factorial (n - 1))`` and use the result ``f_n_1`` in an
assertion to or some other proof step, all within a function that is
in the ``Tot`` effect.

.. literalinclude:: ../code/FactorialTailRec.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_tail_alt$
   :end-before: //SNIPPET_END: factorial_tail_alt$


Revisiting Vector Concatenation
-------------------------------

We now have all the ingredients to understand how the vector append
example shown at the start of this chapter works. Here, below, is a
version of the same code with all the implicit arguments and
reveal/hide operations made explicit.

.. literalinclude:: ../code/VecErasedExplicit.fst
   :language: fstar

**Definition of vec**

In the definition of the inductive type ``vec a``, we have two
occurrences of ``reveal``. Consider ``vec a (reveal n)``, the type of
the ``tl`` of the vector. ``reveal n`` is a ghost computation of type
``GTot nat``, so ``vec a (reveal n) : GTot Type``. But, since ``Type``
is non-informative, ``GTot Type`` is promoted to ``Tot Type``. The
promotion from ``GTot Type`` to ``Tot Type`` is pervasive in F* and
enables ghost computations to be freely used in types and other
specifications.

The ``vec a (reveal n + 1)`` in the result type of ``Cons`` is
similar. Here ``reveal n + 1`` has type ``GTot nat``, but applying it
to ``vec a`` produces a ``GTot Type``, which is promoted to ``Tot
Type``.

**Type of append**

The type of ``append`` has four occurrences of ``reveal``. Three of
them, in the type of ``v0``, ``v1``, and the return type behave the
same as the typing the fields of ``Cons``: the ``GTot Type`` is
promoted to ``Tot Type``.

One additional wrinkle is in the decreases clause, where we have an
explicit ``reveal n``, since what decreases on each recursive call is
the ``nat`` that's in bijection with the parameter ``n``, rather than
``n`` itself. When F* infers a decreases clause for a function, any
erased terms in the clause are automatically revealed.

**Definition of append**

The recursive call instantiates the index parameters to ``n_tl`` and
``m``, which are both erased.

When constructing the ``Cons`` node, its index argument is
instantiated to ``hide (reveal n_tl + reveal m)``. The needless
addition is marked with a ``hide`` enabling that F* compiler to erase
it. As we saw before in ``factorial_tail_alt``, using ``hide`` allows
one to mingle ghost computations (like ``(reveal n - 1)``) with total
computations, as needed for specifications and proofs.

All of this is painfully explicit, but the implicit reveal/hide
coercions inserted by F* go a long way towards make things relatively
smooth.
