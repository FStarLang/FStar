.. _Pulse_Existentials:

Existential Quantification
==========================

A very common specification style in Pulse involves the use of the
existential quantifier. Before we can start to write interesting
examples, let's take a brief look at how existential quantification
works.

As mentioned in the :ref:`introduction to Pulse <Pulse_Basics>`, one
of the connectives of Pulse's separation logic is the existential
quantifier. Its syntax is similar to F*'s existential quantifier,
except it is written ``exists*`` instead of just ``exists``, and its
body is a ``slprop``, as in the examples shown below.

.. code-block:: pulse

   exists* (v:nat). pts_to x v

   exists* v. pts_to x v

   exists* v1 v2. pts_to x v1 ** pts_to y v2

   ...


Some simple examples
....................

Looking back to the ``assign`` example from the previous chapter
(shown below), you may have wondered why we bothered to bind a logical
variable ``'v`` in precondition of the specification, since it is
never actually used in any other predicate.

.. literalinclude:: ../code/pulse/PulseTutorial.Ref.fst
   :language: pulse
   :start-after: //assign$
   :end-before: //end assign$

And indeed, another way to write the specification of ``assign``, without
the logical variable argument, is shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.Existentials.fst
   :language: pulse
   :start-after: //assign$
   :end-before: //end assign$

This time, in the precondition, we use an existential quantifier to
say that ``assign`` is callable in a context where ``x`` points to any
value ``w``.
   
Usually, however, the postcondition of a function *relates* the
initial state prior to the call to the state after the call and
existential variables are only in scope as far to the right as
possible of the enclosing ``slprop``. So, existential quantifiers in
the precondition of a function are not so common.

To illustrate, the following attempted specification of ``incr`` does
not work, since the existentially bound ``w0`` is not in scope for the
postcondition.

.. literalinclude:: ../code/pulse/PulseTutorial.Existentials.fst
   :language: pulse
   :start-after: //incr_fail$
   :end-before: //end incr_fail$

However, existential quantification often appears in postconditions,
e.g., in order to abstract the behavior of function by underspecifying
it. To illustrate, consider the function ``make_even`` below. It's
type states that it sets the contents of ``x`` to some even number
``w1``, without specifying ``w1`` exactly. It also uses an existential
quantification in its precondition, since its postcondition does not
depend on the initial value of ``x``.

.. literalinclude:: ../code/pulse/PulseTutorial.Existentials.fst
   :language: pulse
   :start-after: //make_even$
   :end-before: //end make_even$

Manipulating existentials
.........................

In a previous chapter on :ref:`handling classical connectives
<Part2_connectives>`, we saw how F* provides various constructs for
introducing and eliminating logical connectives, including the
existential quantifier. Pulse also provides constructs for working
explicitly with existential quantifiers, though, usually, Pulse
automation takes care of introducing and eliminating existentials
behind the scenes. However, the explicit operations are sometimes
useful, and we show a first example of how they work below

.. literalinclude:: ../code/pulse/PulseTutorial.Existentials.fst
   :language: pulse
   :start-after: //make_even_explicit$
   :end-before: //end make_even_explicit$

Eliminating existentials
++++++++++++++++++++++++

The form ``with w0...wn. assert p; rest`` is often used as an
eliminator for an existential. When the context contains ``exists*
x0...xn. p``, the ``with`` construct binds ``w0 ... wn`` to the
existentially bound variables in the remainder of the scope ``rest``.

A ``show_proof_state`` immediately after the ``with w0. assert (pts_to
x w0)`` prints the following:

.. code-block:: pulse
                
  - Current context:
      pts_to x (reveal w0) ** 
      emp
  - In typing environment:
      [w0#2 : erased int,
      x#1 : ref int]

That is, we have ``w0:erased int`` in scope, and ``pts_to x (reveal
w0)`` in context.

Here is another example usage of ``with``, this time with multiple
binders.

.. literalinclude:: ../code/pulse/PulseTutorial.Existentials.fst
   :language: pulse
   :start-after: //make_even_explicit_alt$
   :end-before: //end make_even_explicit_alt$

When there is a single existential formula in the context, one can
write ``with x1..xn. _`` to "open" the formula, binding its witnesses
in scope. A ``show_proof_state`` after the first line prints:

.. code-block:: pulse

  - Current context:
      pts_to x (reveal wx) ** 
      pts_to y (reveal wy) ** 
      pure (eq2 (op_Modulus (reveal wx) 2) (op_Modulus (reveal wy) 2)) ** 
      emp
  - In typing environment:
      [_#5 : squash (eq2 (op_Modulus (reveal wx) 2) (op_Modulus (reveal wy) 2)),
      wy#4 : erased int,
      wx#3 : erased int,
      y#2 : ref int,
      x#1 : ref int]


Introducing existentials
++++++++++++++++++++++++

The Pulse checker will automatically introduce existential formulas by
introduces new unification variables for each existentially bound
variable, and then trying to find solutions for those variables by
matching ``slprops`` in the goal with those in the context.

However, one can also introduce existential formulas explicitly, using
the ``introduce exists*`` syntax, as seen in the two examples
above. In general, one can write

.. code-block:: pulse

   introduce exists* x1 .. xn. p
   with w1...wn

explicitly providing witnesses ``w1..wn`` for each of the
existentially bound variables ``x1..xn``.
