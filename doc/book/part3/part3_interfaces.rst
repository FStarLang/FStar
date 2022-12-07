.. _Part3_interfaces:

Interfaces
==========

Look through the F* standard libary (in the ``ulib`` folder) and
you'll find many files with ``.fsti`` extensions. Each of these is an
interface file that pairs with a module implementation in a
corresponding ``.fst`` file.

An interface (``.fsti``) is very similar to a module implementation
(``.fst``): it can contain all the elements that a module can,
including inductive ``type`` definitions; ``let`` and ``let rec``
definitions; ``val`` declarations; etc. However, unlike module
implementations, an interface is allowed to declare a symbol ``val f :
t`` without any corresponding definition of ``f``. This makes ``f``
abstract to the rest of the interface and all client modules, i.e.,
``f`` is simply assumed to have type ``t`` without any definition. The
definition of ``f`` is provided in the ``.fst`` file and checked to
have type ``t``, ensuring that a client module's assumption of ``f:t``
is backed by a suitable definition.

To see how interfaces work, we'll look at the design of the **bounded
integer** modules ``FStar.UInt32``, ``FStar.UInt64``, and the like,
building our own simplified versions by way of illustration.

Bounded Integers
^^^^^^^^^^^^^^^^

The F* primitive type ``int`` is an unbounded mathematical
integer. When compiling a program to, say, OCaml, ``int`` is compiled
to a "big integer", implemented by OCaml's `ZArith package
<https://opam.ocaml.org/packages/zarith/>`_. However, the ``int`` type
can be inefficient and in some scenarios (e.g., when compiling F*
to C) one may want to work with bounded integers that can always be
represented in machine word. ``FStar.UInt32.t`` and ``FStar.UInt64.t``
are types from the standard library whose values can always be
represented as 32- and 64-bit unsigned integers, respectively.

Arithmetic operations on 32-bit unsigned integers (like addition) are
interpreted modulo ``2^32``. However, for many applications, one wants
to program in a discipline that ensures that there is no unintentional
arithmetic overflow, i.e., we'd like to use bounded integers for
efficiency, and by proving that their operations don't overflow we can
reason bounded integer terms without using modular arithmetic.

.. note::

   Although we don't discuss them here, F*'s libraries also provide
   signed integer types that can be compiled to the corresponding
   signed integters in C. Avoiding overflow on signed integer
   arithmetic is not just a matter of ease of reasoning, since signed
   integer overflow is undefined behavior in C.

Interface: UInt32.fsti
----------------------

The interface ``UInt32`` begins like any module with the
module's name. Although this could be inferred from the name of the file
(``UInt32.fsti``, in this case), F* requires the name to be explicit.

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: t$
   :end-before: //SNIPPET_END: t$
                
``UInt32`` provides one abstract type ``val t : eqtype``, the type of
our bounded integer. Its type says that it supports decidable
equality, but no definition of ``t`` is revaled in the interface.

The operations on ``t`` are specified in terms of a logical model that
relates ``t`` to bounded mathematical integers, in particular
``u32_nat``, a natural number less than ``pow2 32``.

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: bounds$
   :end-before: //SNIPPET_END: bounds$

.. note::

   Unlike interfaces in languages like OCaml, interfaces in F* *can*
   include ``let`` and ``let rec`` definitions. As we see in
   ``UInt32``, these definitions are often useful for giving precise
   specifications to the other operations whose signatures appear in
   the interface.

To relate our abstract type ``t`` to ``u32_nat``, the interface
provides two coercions ``v`` and ``u`` that go back and forth between
``t`` and ``u32_nat``. The lemma signatures ``vu_inv`` and
``uv_inv`` require ``v`` and ``u`` to be mutually inverse, meaning
that ``t`` and ``u32_nat`` are in 1-1 correspondence.

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: vu$
   :end-before: //SNIPPET_END: vu$

Modular addition and subtraction
................................

Addition and subtraction on ``t`` values are defined modulo ``pow2
32``. This is specified by the signatures of ``add_mod`` and
``sub_mod`` below.

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: add_mod$
   :end-before: //SNIPPET_END: add_mod$

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: sub_mod$
   :end-before: //SNIPPET_END: sub_mod$

Bounds-checked addition and subtraction
.......................................

Although precise, the types of ``add_mod`` and ``sub_mod`` aren't
always easy to reason with. For example, proving that ``add_mod (u 2)
(u 3) == u 5`` requires reasoning about modular arithmetic---for
constants like ``2``, ``3``, and ``5`` this is easy enough, but proofs
about modular arithmetic over symbolic values will, in general, involve
reasoning about non-linear arithmetic, which is difficult to automate
even with an SMT solver. Besides, in many safety critical software
systems, one often prefers to avoid integer overflow altogether.

So, the ``UInt32`` interface also provides two additional operations,
``add`` and ``sub``, whose specification enables two ``t`` values to be added
(resp. subtracted) only if there is no overflow (or underflow).

First, we define an auxiliary predicate ``fits`` to state when an
operation does not overflow or underflow.

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: fits$
   :end-before: //SNIPPET_END: fits$

Then, we use ``fits`` to restrict the domain of ``add`` and ``sub``
and the type ensures that the result is the sum (resp. difference) of
the arguments, without need for any modular arithmetic.

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: add$
   :end-before: //SNIPPET_END: add$

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: sub$
   :end-before: //SNIPPET_END: sub$

.. note ::

   Although the addition operator can be used as a first-class
   function with the notation ``(+)``, the same does not work for
   subtraction, since ``(-)`` resolves to unary integer negation,
   rather than subtraction---so, we write ``fun x y -> x - y``.

Comparison
..........

Finally, the interface also provides a comparison operator ``lt``, as
specified below:

.. literalinclude:: ../code/UInt32.fsti
   :language: fstar
   :start-after: //SNIPPET_START: lt$
   :end-before: //SNIPPET_END: lt$

Implementation: UInt32.fst
--------------------------

An implementation of ``UInt32`` must provide definitions for
all the ``val`` declarations in the ``UInt32`` interface, starting
with a representation for the abstract type ``t``.

There are multiple possible representations for ``t``, however the
point of the interface is to isolate client modules from these
implementation choices.

Perhaps the easiest implementation is to represent ``t`` as a
``u32_nat`` itself. This makes proving the correspondence between
``t`` and its logical model almost trivial.

.. literalinclude:: ../code/UInt32.fst
   :language: fstar

Another choice may be to represent ``t`` as a 32-bit vector. This is a
bit harder and proving that it is correct with respect to the
interface requires handling some interactions between Z3's theory of
bit vectors and uninterpreted functions, which we handle with a
tactic. This is quite advanced, and we have yet to cover F*'s support
for tactics, but we show the code below for reference.

.. literalinclude:: ../code/UInt32BV.fst
   :language: fstar
   :start-after: //SNIPPET_START: UInt32BV$
   :end-before: //SNIPPET_END: UInt32BV$

Although both implementations correctly satisfy the ``UInt32``
interface, F* requires the user to pick one. Unlike module systems in some
other ML-like languages, where interfaces are first-class entities
which many modules can implement, in F* an interface can have at most
one implementation. For interfaces with multiple implementations, one
must use typeclasses.


Interleaving: A Quirk
---------------------

The current F* implementation views an interface and its
implementation as two partially implemented halves of a module. When
checking that an implementation is a correct implementation of an
interface, F* attempts to combine the two halves into a complete
module before typechecking it. It does this by trying to *interleave*
the top-level elements of the interface and implementation, preserving
their relative order.

This implementation strategy is far from optimal in various ways and a
relic from a time when F*'s implementation did not support separate
compilation. This implementation strategy is likely to change in the
future (see `this issue
<https://github.com/FStarLang/FStar/issues/1770>`_ for
details).

Meanwhile, the main thing to keep in mind when implementing interfaces
is the following:

  * The order of definitions in an implementation much match the order
    of ``val`` declarations in the interface. E.g., if the interface
    contains ``val f : tf`` followed by ``val g : tg``, then the
    implementation of ``f`` must precede the implementation of ``g``.

Also, remember that if you are writing ``val`` declarations in an
interface, it is a good idea to be explicit about universe levels. See
:ref:`here for more discussion <Part2_tips_for_universes>`.

Other issues with interleaving that may help in debugging compiler
errors with interfaces:

  * `Issue 2020 <https://github.com/FStarLang/FStar/issues/2020>`_
  * `Issue 1770 <https://github.com/FStarLang/FStar/issues/1770>`_
  * `Issue 959  <https://github.com/FStarLang/FStar/issues/959>`_

Comparison with machine integers in the F* library
--------------------------------------------------

F*'s standard library includes ``FStar.UInt32``, whose interface is
similar, though more extensive than the ``UInt32`` shown in this
chapter. For example, ``FStar.UInt32`` also includes multiplication,
division, modulus, bitwise logical operations, etc.

The implementation of ``FStar.UInt32`` chooses a representation for
``FStar.UInt32.t`` that is similar to ``u32_nat``, though the F*
compiler has special knowledge of this module and treats
``FStar.UInt32.t`` as a primitive type and compiles it and its
operations in a platform-specific way to machine integers. The
implementation of ``FStar.UInt32`` serves only to prove that its
interface is logically consistent by providing a model in terms of
bounded natural numbers.

The library also provides several other unsigned machine integer types
in addition to ``FStar.UInt32``, including ``FStar.UInt8``,
``FStar.UInt16``, and ``FStar.UInt64``.  F* also has several signed
machine integer types.

All of these modules are very similar, but not being first-class
entities in the language, there is no way to define a general
interface that is instantiated by all these modules. In fact, all
these variants are generated by a script from a common template.

Although interfaces are well-suited to simple patterns of information
hiding and modular structure, as we'll learn next, typeclasses are
more powerful and enable more generic solutions, though sometimes
requiring the use of higher-order code.
