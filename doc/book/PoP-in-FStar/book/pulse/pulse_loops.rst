.. _Pulse_Loops:

Loops & Recursion
#################

In this chapter, we'll see how various looping constructs work in
Pulse, starting with ``while`` and also recursive functions.

By default, Pulse's logic is designed for partial correctness. This
means that programs are allowed to loop forever. When we say that
program returns ``v:t`` satisfying a postcondition ``p``, this should
be understood to mean that the program could loop forever, but if it
does return, it is guaranteed to return a ``v:t`` where the state
satisfies ``p v``.


While loops: General form
.........................

The form of a while loop is:

.. code-block:: pulse

   while ( guard )
   invariant (b:bool). p
   { body }

Where

  * ``guard`` is a Pulse program that returns a ``b:bool``

  * ``body`` is a Pulse program that returns ``unit``
    
  * ``invariant (b:bool). p`` is an invariant where

    - ``exists* b. p`` must be provable before the loop is entered and as a postcondition of ``body``.

    - ``exists* b. p`` is the precondition of the guard, and ``p b``
      is its postcondition, i.e., the ``guard`` must satisfy:

      .. code-block:: pulse

           requires exists* b. p
           returns b:bool
           ensures p

    - the postcondition of the entire loop is ``invariant false``.

One way to understand the invariant is that it describes program
assertions at three different program points.

  * When ``b==true``, the invariant describes the program state at the
    start of the loop body;

  * when ``b==false``, the invariant describes the state at the end of
    the loop;

  * when ``b`` is undetermined, the invariant describes the property
    of the program state just before the guard is (re)executed, i.e.,
    at the entry to the loop and at the end of loop body.

Coming up with an invariant to describe a loop often requires some
careful thinking. We'll see many examples in the remaining chapters,
starting with some simple loops here.

Countdown
+++++++++

Here's our first Pulse program with a loop: ``count_down`` repeatedly
decrements a reference until it reaches ``0``.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: pulse
   :start-after: //count_down$
   :end-before: //end count_down$

While loops in Pulse are perhaps a bit more general than in other
languages. The ``guard`` is an arbitrary Pulse program, not just a
program that reads some local variables. For example, here's another
version of ``count_down`` where the ``guard`` does all the work and
the loop body is empty, and we don't need an auxiliary ``keep_going``
variable.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: pulse
   :start-after: //count_down3$
   :end-before: //end count_down3$
                

Partial correctness
+++++++++++++++++++

The partial correctness interpretation means that the following
infinitely looping variant of our program is also accepted:

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: pulse
   :start-after: //count_down_loopy$
   :end-before: //end count_down_loopy$

This program increments instead of decrement ``x``, but it still
satisfies the same invariant as before, since it always loops forever.

We do have a fragment of the Pulse logic, notably the logic of
``ghost`` and ``atomic`` computations that is guaranteed to always
terminate. We plan to also support a version of the Pulse logic for
general purpose sequential programs (i.e., no concurrency) that is
also terminating.

Multiply by repeated addition
+++++++++++++++++++++++++++++

Our next program with a loop multiplies two natural numbers ``x, y``
by repeatedly adding ``y`` to an accumulator ``x`` times.  This
program has a bit of history: A 1949 paper by Alan Turing titled
`"Checking a Large Routine"
<https://turingarchive.kings.cam.ac.uk/checking-large-routine>`_ is
often cited as the first paper about proving the correctness of a
computer program. The program that Turing describes is one that
implements multiplication by repeated addition.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: pulse
   :start-after: //multiply_by_repeated_addition$
   :end-before: //end multiply_by_repeated_addition$

A few noteworthy points:

  * Both the counter ``ctr`` and the accumulator ``acc`` are declared
    ``nat``, which implicitly, by refinement typing, provides an
    invariant that they are both always at least ``0``. This
    illustrates how Pulse provides a separation logic on top of F*'s
    existing dependent type system.

  * The invariant says that the counter never exceeds ``x``; the
    accumulator is always the product of counter and ``y``; and the
    loop continues so long as the counter is strictly less than ``x``.

Summing the first ``N`` numbers
+++++++++++++++++++++++++++++++

This next example shows a Pulse program that sums the first ``n``
natural numbers. It illustrates how Pulse programs can developed along
with pure F* specifications and lemmas.

We start with a specification of ``sum``, a simple recursive function
in F* along with a lemma that proves the well-known identity about
this sum.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: fstar
   :start-after: //sum$
   :end-before: //end sum$

Now, let's say we want to implement ``isum``, an iterative version of
``sum``, and prove that it satisfies the identity proven by
``sum_lemma``.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: pulse
   :start-after: //isum$
   :end-before: //end isum$

This program is quite similar to ``multiply_by_repeated_addition``,
but with a couple of differences:

  * The invariant says that the current value of the accumulator holds
    the sum of the the first ``c`` numbers, i.e., we prove that the
    loop refines the recursive implementation of ``sum``, without
    relying on any properties of non-linear arithmetic---notice, we
    have disabled non-linear arithmetic in Z3 with a pragma.
    
  * Finally, to prove the identity we're after, we just call the F*
    ``sum_lemma`` that has already been proven from within Pulse, and
    the proof is concluded.

The program is a bit artificial, but hopefully it illustrates how
Pulse programs can be shown to first refine a pure F* function, and
then to rely on mathematical reasoning on those pure functions to
conclude properties about the Pulse program itself.
    
Recursion
.........

Pulse also supports general recursion, i.e., recursive functions that
may not terminate. Here is a simple example---we'll see more examples
later.

Let's start with a standard F* (doubly) recursive definition that
computes the nth Fibonacci number.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: fstar
   :start-after: //fib$
   :end-before: //end fib$

One can also implement it in Pulse, as ``fib_rec`` while using an
out-parameter to hold that values of the last two Fibonacci numbers in
the sequence.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: pulse
   :start-after: //fib_rec$
   :end-before: //end fib_rec$

Some points to note here:

  * Recursive definitions in Pulse are introduced with ``fn rec``.

  * So that we can easily memoize the last two values of ``fib``, we
    expect the argument ``n`` to be a positive number, rather than
    also allowing ``0``.

  * A quirk shown in the comments: We need an additional type
    annotation to properly type ``(1, 1)`` as a pair of nats.
    
Of course, one can also define fibonacci iteratively, with a while
loop, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.Loops.fst
   :language: pulse
   :start-after: //fib_loop$
   :end-before: //end fib_loop$



