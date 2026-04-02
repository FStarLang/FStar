.. _Pulse_Conditionals:

Conditionals
============

To start writing interesting programs, we need a few control
constructs. In this chapter, we'll write some programs with branches
of two kinds: ``if/else`` and ``match``.


A Simple Branching Program: Max
...............................

Here's a simple program that returns the maximum value stored in two
references.

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //max$
   :end-before: //end max$

This program illustrates a very common specification style.

  * We have a pure, F* function ``max_spec``

  * And a Pulse function working on mutable references, with a
    specification that relates it to the pure F* spec. In this case,
    we prove that ``max`` behaves like ``max_spec`` on the logical
    values that witness the contents of the two references.

The implementation of ``max`` uses a Pulse conditional statement. Its
syntax is different from the F* ``if-then-else`` expression: Pulse
uses a more imperative syntax with curly braces, which should be
familiar from languages like C.

Limitation: Non-tail Conditionals
+++++++++++++++++++++++++++++++++

Pulse's inference machinery does not yet support conditionals that
appear in non-tail position. For example, this variant of ``max``
fails, with the error message shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //max_alt_fail$
   :end-before: //end max_alt_fail$

.. code-block::                 

   Pulse cannot yet infer a postcondition for a non-tail conditional statement;
   Either annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional

Here's an annotated version of ``max_alt`` that succeeds.

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //max_alt$
   :end-before: //end max_alt$

We are working on adding inference for non-tail conditionals.

Pattern matching with nullable references
.........................................

To illustrate the use of pattern matching, consider the following
representation of a possibly null reference.

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: fstar
   :start-after: //nullable_ref$
   :end-before: //end nullable_ref$

Representation predicate
++++++++++++++++++++++++

We can represent a nullable ref as just an ``option (ref a)`` coupled
with a representation predicate, ``pts_to_or_null``. A few points to
note:

  * The notation ``(#[default_arg (\`1.0R)] p:perm)`` is F*
    syntax for an implicit argument which when omitted defaults to
    ``1.0R``---this is exactly how predicates like
    ``Pulse.Lib.Reference.pts_to`` are defined.

  * The definition is by cases: if the reference ``x`` is ``None``,
    then the logical witness is ``None`` too.

  * Otherwise, the underlying reference points to some value ``w`` and
    the logical witness ``v == Some w`` agrees with that value.

Note, one might consider defining it this way:

.. code-block:: fstar

   let pts_to_or_null #a
        (x:nullable_ref a) 
        (#[default_arg (`1.0R)] p:perm)
        (v:option a)
   : slprop
   = match x with
     | None -> pure (v == None)
     | Some x -> pure (Some? v) ** pts_to x #p (Some?.v v)

However, unlike F*'s conjunction ``p /\ q`` where the well-typedness
of ``q`` can rely on ``p``, the ``**`` operator is not left-biased; so
``(Some?.v v)`` cannot be proven in this context and the definition is
rejected.
                
Another style might be as follows:

.. code-block:: fstar

   let pts_to_or_null #a
        (x:nullable_ref a) 
        (#[default_arg (`1.0R)] p:perm)
        (v:option a)
   : slprop
   = match x, v with
     | None, None -> emp
     | Some x, Some w -> pts_to x #p w
     | _ -> pure False

This could also work, though it would require handling an additional
(impossible) case.

Reading a nullable ref
++++++++++++++++++++++

Let's try our first pattern match in Pulse:

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //read_nullable$
   :end-before: //end read_nullable$

The syntax of pattern matching in Pulse is more imperative and
Rust-like than what F* uses.

  * The entire body of match is enclosed within braces

  * Each branch is also enclosed within braces.

  * Pulse (for now) only supports simple patterns with a single top-level
    constructor applied to variables, or variable patterns: e.g., you
    cannot write ``Some (Some x)`` as a pattern.
                
The type of ``read_nullable`` promises to return a value equal to the
logical witness of its representation predicate.

The code is a little tedious---we'll see how to clean it up a bit
shortly.

A ``show_proof_state`` in the ``Some x`` branch prints the following:

.. code-block::
   
  - Current context:
      pts_to_or_null r (reveal 'v)
  - In typing environment:
      [branch equality#684 : squash (eq2 r (Some x)),
       ...

The interesting part is the ``branch equality`` hypothesis, meaning
that in this branch, we can assume that ``(r == Some x)``. So, the
first thing we do is to rewrite ``r``; then we ``unfold`` the
representation predicate; read the value ``o`` out of ``x``; fold the
predicate back; rewrite in the other direction; and return ``Some
o``. The ``None`` case is similar.

Another difference between Pulse and F* matches is that Pulse does not
provide any negated path conditions. For example, in the example
below, the assertion fails, since the pattern is only a wildcard and
the Pulse checker does not prove ``not (Some? x)`` as the path
condition hypothesis for the preceding branches not taken.

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //read_nullable_alt_fail$
   :end-before: //end read_nullable_alt_fail$

We plan to enhance the Pulse checker to also provide these negated
path conditions.

.. _Pulse_nullable_ref_helpers:

Helpers
+++++++

When a ``slprop`` is defined by cases (like ``pts_to_or_null``) it is
very common to have to reason according to those cases when pattern
matching. Instead of rewriting, unfolding, folding, and rewriting
every time, one can define helper functions to handle these cases.


.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //pts_to_or_null_helpers$
   :end-before: //end pts_to_or_null_helpers$

These functions are all marked ``ghost``, indicating that they are
purely for proof purposes only.

Writing these helpers is often quite mechanical: One could imagine
that the Pulse checker could automatically generate them from the
definition of ``pts_to_or_null``. Using F*'s metaprogramming support,
a user could also auto-generate them in a custom way. For now, we
write them by hand.

Using the helpers, case analyzing a nullable reference is somewhat
easier:

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //read_nullable_alt$
   :end-before: //end read_nullable_alt$


Writing a nullable reference
++++++++++++++++++++++++++++

Having defined our helpers, we can use them repeatedly. For example,
here is a  function to write a nullable reference.

.. literalinclude:: ../code/pulse/PulseTutorial.Conditionals.fst
   :language: pulse
   :start-after: //write_nullable$
   :end-before: //end write_nullable$



