.. _Pulse_DefinedVProps:

User-defined Predicates
=======================

In addition to the slprop predicates and connectives that the Pulse
libraries provide, users very commonly define their own ``slprops``. We
show a few simple examples here---subsequent examples will make heavy
use of user-defined predicates. For example, see this section for
:ref:`recursively defined predicates <Pulse_recursive_predicates>`.



Fold and Unfold with Diagonal Pairs
...................................

A simple example of a user-defined abstraction is show below.

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //pts_to_diag$
   :end-before: //end pts_to_diag$

``pts_to_diag r v`` is a ``slprop`` defined in F* representing a
reference to a pair whose components are equal.

We can use this abstraction in a Pulse program, though we have to be
explicit about folding and unfolding the predicate.

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //double$
   :end-before: //end double$

The ``unfold p`` command checks that ``p`` is provable in the current
context by some term ``q``, and then rewrites the context by replacing
that occurrence of ``q`` with the term that results from unfolding the
head symbol of ``p``. A ``show_proof_state`` after the ``unfold``
shows that we have a ``pts_to r (reveal 'v, reveal 'v)`` in the
context, exposing the abstraction of the ``pts_to_diag`` predicate.

At the end of function, we use the ``fold p`` command: this checks
that the unfolding of ``p`` is provable in the context by some term
``q`` and then replaces ``q`` in the context with ``p``.

``fold`` and ``unfold`` is currently very manual in Pulse. While in
the general case, including with recursively defined predicates,
automating the placement of folds and unfolds is challenging, many
common cases (such as the ones here) can be easily automated. We are
currently investigating adding support for this.

Some initial support for this is already available, inasmuch as Pulse
can sometimes figure out the arguments to the slprops that need to be
folded/unfolded. For instance, in the code below, we just mention the
name of the predicate to be unfolded/folded, without needing to
provide all the arguments.

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //double_alt$
   :end-before: //end double_alt$

Mutable Points
..............

As a second, perhaps more realistic example of a user-defined
abstraction, we look at defining a simple mutable data structure: a
structure with two mutable integer fields, representing a
2-dimensional point.

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: fstar
   :start-after: //point$
   :end-before: //end point$

A ``point`` is just an F* record containing two
references. Additionally, we define ``is_point``, a ``slprop``,
sometimes called a "representation predicate", for a
``point``. ``is_point p xy`` says that ``p`` is a representation of
the logical point ``xy``, where ``xy`` is pure, mathematical pair.

We can define a function ``move``, which translates a point by some
offset ``dx, dy``.

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //move$
   :end-before: //end move$

Implementing ``move`` is straightforward, but like before, we have to
``unfold`` the ``is_point`` predicate first, and then fold it back up
before returning.

Unfortunately, Pulse cannot infer the instantiation of ``is_point``
when folding it. A ``show_proof_state`` prior to the fold should help
us see why:

  * We have ``pts_to p.x (x + dx) ** pts_to p.y (y + dy)``

  * For ``fold (is_point p.x ?w)`` to succeed, we rely on F*'s type
    inference to find a solution for the unsolved witness ``?w`` such
    that ``fst ?w == (x + dx)`` and ``snd ?w == (y + dy)``. This
    requires an eta-expansion rule for pairs to solve ``?w := (x + dx,
    y + dy)``, but F*'s type inference does not support such a rule
    for pairs.

So, sadly, we have to provide the full instantiation ``is_point p (x +
dx, y + dy)`` to complete the proof.

This pattern is a common problem when working with representation
predicates that are indexed by complex values, e.g., pairs or
records. It's common enough that it is usually more convenient to
define a helper function to fold the predicate, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //fold_is_point$
   :end-before: //end fold_is_point$

.. note::

   We've marked this helper function ``ghost``. We'll look into
   ``ghost`` functions in much more detail in a later chapter.
   
This allows  type inference to work better, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //move_alt$
   :end-before: //end move_alt$

.. _Pulse_rewriting:

Rewriting
.........

In addition to ``fold`` and ``unfold``, one also often uses the
``rewrite`` command when working with defined predicates. Its general
form is:

.. code-block::

   with x1 ... xn. rewrite p as q;
   rest

Its behavior is to find a substitution ``subst`` that instantiates the
``x1 ... xn`` as ``v1 ... vn``, such that ``subst(p)`` is supported by
``c`` in the context, Pulse aims to prove that ``subst(p) ==
subst(q)`` and replaces ``c`` in the context by ``subst(q)`` and
proceeds to check ``subst(rest)``.

To illustrate this at work, consider the program below:

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //create_and_move$
   :end-before: //end create_and_move$

We allocate two references and put them in the structure ``p``. Now,
to call ``fold_is_point``, we need ``pts_to p.x _`` and ``pts_to p.y
_``, but the context only contains ``pts_to x _`` and ``pts_to y
_``. The ``rewrite`` command transforms the context as needed.

At the end of the function, we need to prove that ``pts_to x _`` and
``pts_to y _`` as we exit the scope of ``y`` and ``x``, so that they
can be reclaimed. Using ``rewrite`` in the other direction
accomplishes this.

This is quite verbose. As with ``fold`` and ``unfold``, fully
automated ``rewrite`` in the general case is hard, but many common
cases are easy and we expect to add support for that to the Pulse
checker.

In the meantime, Pulse provides a shorthand to make some common
rewrites easier.

The ``rewrite each`` command has the most general form:

.. code-block:: pulse

   with x1 ... xn. rewrite each e1 as e1', ..., en as en' in goal   

This is equivalent to:

.. code-block:: pulse

   with x1 ... xn. assert goal;
   rewrite each e1 as e1', ..., en as en' in goal

.. code-block:: pulse

   rewrite each e1 as e1', ..., en as en' in goal

is equivalent to

.. code-block:: pulse

   rewrite goal as goal'

where ``goal'`` is computed by rewriting, in parallel, every
occurrence of ``ei`` as ``ei'`` in ``goal``.

Finally, one can also write:

.. code-block:: pulse

   rewrite each e1 as e1', ..., en as en'

omitting the ``goal`` term. In this case, the ``goal`` is taken to be
the entire current ``slprop`` context.
  
Using ``rewrite each ...`` makes the code somewhat shorter:

.. literalinclude:: ../code/pulse/PulseTutorial.UserDefinedPredicates.fst
   :language: pulse
   :start-after: //create_and_move_alt$
   :end-before: //end create_and_move_alt$









