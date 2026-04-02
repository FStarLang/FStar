.. _PartPulse:

################################################################
Pulse: Proof-oriented Programming in Concurrent Separation Logic
################################################################

Many F* projects involve building domain-specific languages with
specialized programming and proving support. For example, `Vale
<https://github.com/project-everest/vale>`_ supports program proofs
for a structured assembly language; `Low*
<https://fstarlang.github.io/lowstar/html/>`_ provides effectful
programming in F* with a C-like memory model; `EverParse
<https://github.com/project-everest/everparse>`_ is a DSL for writing
low-level parsers and serializers. Recently, F* has gained new
features for building DSLs embedded in F* with customized syntax, type
checker plugins, extraction support, etc., with *Pulse* as a showcase
example of such a DSL.

Pulse is a new programming language embedded in F*, inheriting many of
its features (notably, it is higher order and has dependent types),
but with built-in support for programming with mutable state and
concurrency, with specifications and proofs in `Concurrent Separation
Logic <https://en.wikipedia.org/wiki/Separation_logic>`_.

As a first taste of Pulse, here's a function to increment a mutable
integer reference.

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: //incr
   :end-before: //end incr

And here's a function to increment two references in parallel.

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: //par_incr
   :end-before: //end par_incr

You may not have heard about separation logic before---but perhaps
these specifications already make intuitive sense to you. The type of
``incr`` says that if "x points to 'i" initially, then when ``incr``
returns, "x points to 'i + 1"; while ``par_incr`` increments the
contents of ``x`` and ``y`` in parallel by using the ``par``
combinator.

Concurrent separation logic is an active research area and there are many such
logics to use, all with different tradeoffs. The state of the art in concurrent
separation logic is `Iris <https://iris-project.org/>`_, a higher-order,
impredicative separation logic. Drawing inspiration from Iris, Pulse's logic is
similar in many ways to Iris, but is based on a logic called PulseCore,
formalized entirely within F*---you can find the formalization `here
<https://github.com/FStarLang/pulse/tree/main/lib/pulse/core>`_. Proofs of
programs in Pulse's surface language correspond to proofs of correctness in the
PulseCore program logic. But, you should not need to know much about how the
logic is formalized to use Pulse effectively. We'll start from the basics and
explain what you need to know about concurrent separation logic to start
programming and proving in Pulse. Additionally, Pulse is an extension of F*, so
all you've learned about F*, lemmas, dependent types, refinement types, etc.
will be of use again.


.. note::

   Why is it called Pulse? Because it grew from a prior logic called
   `Steel <https://fstar-lang.org/papers/steel/>`_, and one of the
   authors and his daughter are big fans of a classic reggae band
   called `Steel Pulse <https://steelpulse.com/>`_. We wanted a name
   that was softer than Steel, and, well, a bit playful. So, Pulse!
   

   
..   .. image:: pulse_arch.png

  
.. toctree::
   :maxdepth: 1
   :caption: Contents:

   pulse_getting_started
   pulse_ch1
   pulse_ch2
   pulse_existentials
   pulse_user_defined_predicates
   pulse_conditionals
   pulse_loops
   pulse_arrays
   pulse_ghost
   pulse_higher_order
   pulse_implication_and_forall
   pulse_linked_list
   pulse_atomics_and_invariants
   pulse_spin_lock
   pulse_parallel_increment
   pulse_extraction
