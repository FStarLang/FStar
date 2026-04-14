.. _Pulse_Basics:

Pulse Basics
============

A Pulse program is embedded in an F* program by including the
directive ``#lang-pulse`` in an F* file. The rest of the file can 
then use a mixture of Pulse and F* syntax, as shown below. 

.. literalinclude:: ../code/pulse/PulseByExample.fst
   :language: pulse
   :start-after: //SNIPPET_START: five
   :end-before: //SNIPPET_END

This program starts with a bit of regular F* defining ``fstar_five``
followed by an a Pulse function ``five`` that references that F*
definition and proves that it always returns the constant
``5``. Finally, we have a bit of regular F* referencing the ``five``
defined in Pulse. This is a really simple program, but it already
illustrates how Pulse and F* interact in both directions.

In what follows, unless we really want to emphasize that a fragment of code is
Pulse embedded in a larger F* context, we just assume that we're working in a
context where ``#lang-pulse`` is enabled.

A Separation Logic Primer
^^^^^^^^^^^^^^^^^^^^^^^^^

Separation Logic was invented by John Reynolds, Peter O'Hearn, and
others in the late 1990s as a way to reason about imperative programs
that use shared, mutable data structures, e.g., linked lists and
graphs---see this paper for `an introduction to separation logic
<https://www.cs.cmu.edu/~jcr/seplogic.pdf>`_. In the subsequent
decades, several innovations were added to separation logic by many
people, generalizing it beyond just sequential heap-manipulating
programs to distributed programs, concurrent programs, asynchronous
programs, etc. that manipulate abstract resources of various kinds,
including time and space, messages sent over communication channels,
etc.

Much like other Hoare Logics, which we reviewed in :ref:`an earlier
section <Part4_Floyd_Hoare>`, separation logic comes in two parts.

**Separation Logic Propositions** First, we have a language of propositions that
describe properties about program resources, e.g., the heap. These propositions
have the type ``slprop`` in Pulse, and, under the covers in the PulselCore
semantics of Pulse, a ``slprop = state -> prop``, where ``state`` represents the
state of a program, e.g., the contents of memory. It is useful (at least at
first) to think of a ``slprop`` as a memory property, though we will eventually
treat it more abstractly and use it to model many other kinds of resources.

.. I'm calling it a hmem to not confuse things with heap vs stack
   later.

**Separation Logic Hoare Triples** To connect ``slprop``'s to programs,
separation logics use Hoare triples to describe the action of a
program on its state. For example, the Hoare triple ``{ p } c { n. q
}`` describes a program ``c`` which when run in an initial state
``s0`` satisfying ``p s0`` (i.e., ``p`` is a precondition); ``c``
returns a value ``n`` while transforming the state to ``s1``
satisfying ``q n s1`` (i.e., ``q`` is a postcondition). Pulse's
program logic is a partial-correctness logic, meaning that ``c`` may
also loop forever, deadlock with other threads, etc.

**Some simple slprops and triples**: Here are two of the simplest
 ``slprops`` (defined in ``Pulse.Lib.Pervasives``):

  * ``emp``, the trivial proposition (equivalent to ``fun s -> True``).

  * ``pure p``, heap-independent predicate ``fun s -> p``. ``emp`` is
    equivalent to ``pure True``.

The type of the program ``five`` illustrates how these ``slprop``'s are
used in program specifications:

  * It is a function with a single unit argument---Pulse functions use
    the keyword ``fn``.

  * The precondition is just ``emp``, the trivial assertion in
    separation logic, i.e., ``five`` can be called in any initial
    state.

  * The return value is an integer ``n:int``

  * The postcondition may refer to the name of the return value (``n``
    in this case) and here claims that the final state satisfies the
    ``pure`` proposition, ``n == 5``.

In other words, the type signature in Pulse is a convenient way to
write the Hoare triple ``{ emp } five () { n:int. pure (n == 5) }``.

**Ownership** At this point you may wonder if the postcondition of
``five`` is actually strong enough. We've only said that the return
value ``n == 5`` but have not said anything about the state that
results from calling ``five ()``. Perhaps this specification allows
``five`` to arbitrarily change any memory location in the state, since ``pure
(5 == 5)`` is true of any state. [#]_ If you're familiar with Low*,
Dafny, or other languages based on Hoare logic for heaps, you may be
wondering about how come we haven't specified a ``modifies``-clause,
describing exactly which part of the state a function may have
changed. The nice thing in separation logic is that there is no need
to describe what parts of the state you may have modified. This is
because a central idea in logic is the concept of *ownership*. To a
first approximation, a computation can only access those resources
that it is explicitly granted access to in its precondition or those
that it creates itself. [#]_ In this case, with a precondition of
``emp``, the function ``five`` does not have permission to access
*any* resources, and so ``five`` simply cannot modify the state in any
observable way.


**Separating Conjunction and the Frame Rule** Let's go back to
``incr`` and ``par_incr`` that we saw in the previous section and look
at their types closely. We'll need to introduce two more common
``slprop``'s, starting with the "points-to" predicate:

  * ``pts_to x v`` asserts that the reference ``x`` points to a cell
    in the current state that holds the value ``v``.

``slprop``'s can also be combined in various ways, the most common one
being the "separating conjunction", written ``**`` in Pulse. [#]_
    
  * ``p ** q``, means that the state can be split into two *disjoint*
    fragments satisfying ``p`` and ``q``, respectively. Alternatively,
    one could read ``p ** q`` as meaning that one holds the
    permissions associated with both ``p`` and ``q`` separately in a
    given state. The ``**`` operator satisfies the following laws:

    - Commutativity: ``p ** q`` is equivalent to ``q ** p``

    - Associativity: ``p ** (q ** r)`` is equivalent to ``(p ** q) ** r``

    - Left and right unit: ``p ** emp`` is equivalent to ``p``. Since
      ``**`` is commutative, this also means that ``emp ** p`` is
      equivalent to ``p``
       
Now, perhaps the defining characteristic of separation logic is how
the ``**`` operator works in the program logic, via a key rule known
as the *frame* rule. The rule says that if you can prove the Hoare
triple ``{ p } c { n. q }``, then, for any other ``f : slprop``, you
can also prove ``{ p ** f } c { n. q ** f }``---``f`` is often called
the "frame". It might take some time to appreciate, but the frame rule
captures the essence of local, modular reasoning. Roughly, it states
that if a program is correct when it only has permission ``p`` on the
input state, then it remains correct when run in a larger state and is
guaranteed to preserve any property (``f``) on the part of the state
that it doesn't touch.

With this in mind, let's look again at the type of ``incr``, which
requires permission only to ``x`` and increments it:

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: //incr$
   :end-before: //end incr$

Because of the frame rule, we can also call ``incr`` in a context like
``incr_frame`` below, and we can prove without any additional work
that ``y`` is unchanged.
                                                          
.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: //incr_frame$
   :end-before: //end incr_frame$

In fact, Pulse lets us use the frame rule with any ``f:slprop``, and we
get, for free, that ``incr x`` does not disturb ``f``.

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: //incr_frame_any$
   :end-before: //end incr_frame_any$

A point about the notation: The variable ``'i`` is an implicitly bound
logical variable, representing the value held in the ref-cell ``x`` in
the initial state. In this case, ``'i`` has type ``FStar.Ghost.erased
int``---we learned about :ref:`erased types in a previous section
<Part4_Ghost>`. One can also bind logical variables explicitly, e.g.,
this is equivalent:

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: //incr_explicit_i$
   :end-before: //end incr_explicit_i$
   
**Other slprop connectives** In addition the separating conjunction,
Pulse, like other separation logics, provides other ways to combine
``slprops``. We'll look at these in detail in the subsequent chapters,
but we list the most common other connectives below just to give you a
taste of the logic.

  * ``exists* (x1:t1) ... (xn:tn). p``: Existential quantification is
    used extensively in the Pulse libraries, and the language provides
    many tools to make existentials convenient to use. ``exists x. p``
    is valid in a state ``s`` if there is a witness ``w`` such that
    ``p [w/x]`` is valid in ``s``. For experts, existential
    quantification is impredicative, in the sense that one can quantify
    over ``slprops`` themselves, i.e., ``exists* (p:slprop). q`` is
    allowed.

  * ``forall* (x1:t1) ... (xn:tn). p``: Universal quantification is
    also supported, though less commonly used. ``forall (x:t). p`` is
    valid in ``s`` if ``p[w/x]`` is valid for all values ``w:t``.
    Like existential quantification, it is also impredicative.
    
  * ``p @==> q`` is a form of separating implication similar to an
    operator called a *magic wand* or a *view shift* in other
    separation logics. 

Pulse does not yet provide libraries for conjunction or
disjunction. However, since Pulse is embedded in F*, new slprops can
also be defined by the user and it is common to do so, e.g.,
recursively defined predicates, or variants of the connectives
described above.

.. [#] For experts, Pulse's separation logic is *affine*.
   
.. [#] When we get to things like invariants and locks, we'll see how
       permissions can be acquired by other means.
   
.. [#] In the separation logic literature, separating conjunction is
       written ``p * q``, with just a single star. We use two stars
       ``**`` to avoid a clash with multiplication.
