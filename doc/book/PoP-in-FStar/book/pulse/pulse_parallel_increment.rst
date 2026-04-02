.. _Pulse_parallel_increment:

Parallel Increment
==================

In this chapter, we look at an example first studied by Susan Owicki
and David Gries, in a classic paper titled `Verifying properties of
parallel programs: an axiomatic approach
<https://dl.acm.org/doi/10.1145/360051.360224>`_. The problem involves
proving that a program that atomically increments an integer reference
``r`` twice in parallel correctly adds 2 to ``r``. There are many ways
to do this---Owicki & Gries' approach, adapted to a modern separation
logic, involves the use of additional ghost state and offers a modular
way to structure the proof.

While this is a very simple program, it captures the essence of some
of the reasoning challenges posed by concurrency: two threads interact
with a shared resource, contributing to it in an undetermined order,
and one aims to reason about the overall behavior, ideally without
resorting to directly analyzing each of the possible interleavings.

Parallel Blocks
...............

Pulse provides a few primitives for creating new threads. The most
basic one is parallel composition, as shown below:

.. code-block:: pulse

   parallel
   requires p1 and p2
   ensures q1 and q2
   { e1 }
   { e2 }

The typing rule for this construct requires:

.. code-block:: pulse

   val e1 : stt a p1 q1
   val e2 : stt b p2 q2

and the ``parallel`` block then has the type:

.. code-block:: pulse

   stt (a & b) (p1 ** p2) (fun (x, y) -> q1 x ** q2 y)

In other words, if the current context can be split into separate
parts ``p1`` and ``p2`` satisfying the preconditions of ``e1`` and
``e2``, then the parallel block executes ``e1`` and ``e2`` in
parallel, waits for both of them to finish, and if they both do,
returns their results as a pair, with their postconditions on each
component.

Using ``parallel``, one can easily program the ``par`` combinator
below:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //par$
   :end-before: //end par$

As we saw in the :ref:`introduction to Pulse <PartPulse>`, it's easy
to increment two separate references in parallel:

.. literalinclude:: ../code/pulse/PulseTutorial.Intro.fst
   :language: pulse
   :start-after: //par_incr$
   :end-before: //end par_incr$

But, what if we wanted to increment the same reference in two separate
threads? That is, we wanted to program something like this:

.. code-block:: pulse

   fn add2 (x:ref int)
   requires pts_to x 'i
   ensures pts_to x ('i + 2)
   {
      par (fun _ -> incr x)
          (fun _ -> incr x)
   }

But, this program doesn't check. The problem is that we have only a
single ``pts_to x 'i``, and we can't split it to share among the
threads, since both threads require full permission to ``x`` to update
it.
   
Further, for the program to correctly add ``2`` to ``x``, each
increment operations must take place atomically, e.g., if the two
fragments below were executed in parallel, then they may both read the
initial value of ``x`` first, bind it to ```v``, and then both update
it to ``v + 1``.

.. code-block:: pulse
                
   let v = !x;      ||    let v = !x;
   x := v + 1;      ||    x := v + 1;

Worse, without any synchronization, on modern processors with weak
memory models, this program could exhibit a variety of other
behaviors.

To enforce synchronization, we could use a lock, e.g., shown below:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //attempt$
   :end-before: //end attempt$

This program is type correct and free from data races. But, since the
lock holds the entire permission on ``x``, there's no way to give this
function a precise postcondition.

.. note ::

   In this section, we use an implementation of spin locks from the
   Pulse library, Pulse.Lib.SpinLock. Unlike the version we developed
   in the previous chapter, these locks use a fraction-indexed
   permission, ``lock_alive l #f p``. The also provide a predicate,
   ``lock_acquired l``, that indicates when the lock has been
   taken. With full-permission to the lock, and ``lock_acquired l``,
   the lock can be freed---reclaiming the underlying
   memory. Additionally, the ``lock_acquired`` predicate ensures that
   locks cannot be double freed. As such, ``Pulse.Lib.SpinLock`` fixes
   the problems with the spin locks we introduced in the previous
   chapter and also provides a solution to the exercises given there.
   

A First Take, with Locks
........................

Owicki and Gries' idea was to augment the program with auxiliary
variables, or ghost state, that are purely for specification
purposes. Each thread gets its own piece of ghost state, and accounts
for how much that thread has contributed to the current value of
shared variable. Let's see how this works in Pulse.

The main idea is captured by ``lock_inv``, the type of the predicate
protected by the lock:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: fstar
   :start-after: //lock_inv$
   :end-before: //end lock_inv$

Our strawman ``lock`` in the ``attempt`` shown before had type ``lock
(exists* v. pts_to x v)``. This time, we add a conjunct that refines
the value ``v``, i.e., the predicate ``contributions l r init v`` says
that the current value of ``x`` protected by the lock (i.e., ``v``) is
equal to ``init + vl + vr``, where ``init`` is the initial value of
``x``; ``vl`` is the value of the ghost state owned by the "left"
thread; and ``vr`` is the value of the ghost state owned by the
"right" thread. In other words, the predicate ``contributions l r init
v`` shows that ``v`` always reflects the values of the contributions
made by each thread.

Note, however, the ``contributions`` predicate only holds
half-permission on the left and right ghost variables. The other half
permission is held outside the lock and allows us to keep track of
each threads contribution in our specifications.

Here's the code for the left thread, ``incr_left``:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //incr_left$
   :end-before: //end incr_left$

* Its arguments include ``x`` and the ``lock``, but also both pieces
  of ghost state, ``left`` and ``right``, and an erased value ``i``
  for the initial value of ``x``.

* Its precondition holds half permission on the ghost reference
  ``left``

* Its postcondition returns half-permission to ``left``, but proves
  that it was incremented, i.e., the contribution of the left thread
  to the value of ``x`` increased by ``1``.

Notice that even though we only had half permission to ``left``, the
specifications says we have updated ``left``---that's because we can
get the other half permission we need by acquiring the lock.

* We acquire the lock and update increment the value stored in ``x``.

* And then we follow the increment with several ghost steps:

  - Gain full permission on ``left`` by combining the half permission
    from the precondition with the half permission gained from the
    lock.

  - Increment ``left``.

  - Share it again, returning half permission to the lock when we
    release it.

* Finally, we ``GR.pts_to left #one_half (`vl + 1)`` left over to
  return to the caller in the postcondition.

The code of the right thread is symmetrical, but in this, our first
take, we have to essentially repeat the code---we'll see how to remedy
this shortly.

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //incr_right$
   :end-before: //end incr_right$

Finally, we can implement ``add2`` with the specification we want:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //add2$
   :end-before: //end add2$

* We allocate ``left`` and ``right`` ghost references, initializing
  them to ``0``.

* Then we split them, putting half permission to both in the lock,
  retaining the other half.

* Then spawn two threads for ``incr_left`` and ``incr_right``, and get
  as a postcondition that contributions of both threads and increased
  by one each.

* Finally, we acquire the lock, get ``pts_to x v``, for some ``v``,
  and ``contributions left right i v``. Once we gather up the
  permission on ``left`` and ``right``, and now the ``contributions
  left right i v`` tells us that ``v == i + 1 + 1``, which is what we
  need to conclude.

Modularity with higher-order ghost code
.......................................

Our next attempt aims to write a single function ``incr``, rather than
``incr_left`` and ``incr_right``, and to give ``incr`` a more
abstract, modular specification. The style we use here is based on an
idea proposed by Bart Jacobs and Frank Piessens in a paper titled
`Expressive modular fine-grained concurrency specification
<https://dl.acm.org/doi/10.1145/1926385.1926417>`_.

The main idea is to observe that ``incr_left`` and ``incr_right`` only
differ by the ghost code that they execute. But, Pulse is higher
order: so, why not parameterize a single function by ``incr`` and let
the caller instantiate ``incr`` twice, with different bits of ghost
code. Also, while we're at it, why not also generalize the
specification of ``incr`` so that it works with any user-chosen
abstract predicate, rather than ``contributions`` and ``left/right``
ghost state. Here's how:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //incr$
   :end-before: //end incr$

As before, ``incr`` requires ``x`` and the ``lock``, but, this time,
it is parameterized by:

* A predicate ``refine``, which generalizes the ``contributions``
  predicate from before, and refines the value that ``x`` points to.

* A predicate ``aspec``, an abstract specification chosen by the
  caller, and serves as the main specification for ``incr``, which
  transitions from ``aspec 'i`` to ``aspec ('i + 1)``.

* And, finally, the ghost function itself, ``ghost_steps``, now
  specified abstractly in terms of the relationship between ``refine``,
  ``aspec`` and ``pts_to x``---it says, effectively, that once ``x``
  has been updated, the abstract predicates ``refine`` and ``aspec``
  can be updated too.

Having generalized ``incr``, we've now shifted the work to the
caller. But, ``incr``, now verified once and for all, can be used with
many different callers just by instantiating it differently. For
example, if we wanted to do a three-way parallel increment, we could
reuse our ``incr`` as is. Whereas, our first take would have to be
completely revised, since ``incr_left`` and ``incr_right`` assume that
there are only two ghost references, not three.

Here's one way to instantiate ``incr``, proving the same specification
as ``add2``.

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //add2_v2$
   :end-before: //end add2_v2$

The code is just a rearrangement of what we had before, factoring the
ghost code in ``incr_left`` and ``incr_right`` into a ghost function
``step``. When we spawn our threads, we pass in the ghost code to
either update the left or the right contribution.

This code still has two issues:

* The ghost ``step`` function is a bloated: we have essentially the
  same code and proof twice, once in each branch of the
  conditional. We can improve this by defining a custom bit of ghost
  state using Pulse's support for partial commutative monoids---but
  that's for another chapter.
  
* We allocate and free memory for a lock, which is inefficient---could
  we instead do things with atomic operations? We'll remedy that next.

Exercise
++++++++

Instead of explicitly passing a ghost function, use a quantified trade.


A version with invariants
.........................

As a final example, in this section, we'll see how to program ``add2``
using invariants and atomic operations, rather than locks.

Doing this properly will require working with bounded, machine
integers, e.g., ``U32.t``, since these are the only types that support
atomic operations. However, to illustrate the main ideas, we'll assume
two atomic operations on unbounded integers---this will allow us to
not worry about possible integer overflow. We leave as an exercise the
problem of adapting this to ``U32.t``.

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: fstar
   :start-after: //atomic_primitives$
   :end-before: //end atomic_primitives$

Cancellable Invariants
++++++++++++++++++++++

The main idea of doing the ``add2`` proof is to use an invariant
instead of a lock. Just as in our previous code, ``add2`` starts with
allocating an invariant, putting ``exists* v. pts_to x v **
contribution left right i v`` in the invariant. Then call incr twice
in different threads. However, finally, to recover ``pts_to x (v +
2)``, where previously we would acquire the lock, with a regular
invariant, we're stuck, since the ``pts_to x v`` permission is inside
the invariant and we can't take it out to return to the caller.

An invariant ``inv i p`` guarantees that the property ``p`` is true
and remains true for the rest of a program's execution. But, what if
we wanted to only enforce ``p`` as an invariant for some finite
duration, and then to cancel it? This is what the library
``Pulse.Lib.CancellableInvariant`` provides. Here's the relevant part
of the API:

.. code-block:: pulse

   [@@ erasable]
   val cinv : Type0
   val iref_of (c:cinv) : GTot iref

The main type it offers is ``cinv``, the name of a cancellable
invariant.


.. code-block:: pulse
		
   ghost
   fn new_cancellable_invariant (v:boxable)
   requires v
   returns c:cinv
   ensures inv (iref_of c) (cinv_vp c v) ** active c 1.0R

Allocating a cancellable invariant is similar to allocating a regular
invariant, except one gets an invariant for an abstract predicate
``cinv_cp c v``, and a fraction-indexed predicate ``active c 1.0R``
which allows the cancellable invariant to be shared and gathered
between threads.

The ``cinv_cp c v`` predicate can be used in conjunction with
``active`` to recover the underlying predicate ``v``---but only when
the invariant has not been cancelled yet---this is what
``unpack_cinv_vp``, and its inverse, ``pack_cinv_vp``, allow one to
do.

.. code-block:: pulse
		
   ghost
   fn unpack_cinv_vp (#p:perm) (#v:slprop) (c:cinv)
   requires cinv_vp c v ** active c p
   ensures v ** unpacked c ** active c p

   ghost
   fn pack_cinv_vp (#v:slprop) (c:cinv)
   requires v ** unpacked c
   ensures cinv_vp c v

Finally, if one has full permission to the invariant (``active c
1.0R``) it can be cancelled and the underlying predicate ``v`` can be
obtained as postcondition.

.. code-block:: pulse

   ghost
   fn cancel (#v:slprop) (c:cinv)
   requires inv (iref_of c) (cinv_vp c v) ** active c 1.0R
   ensures v
   opens add_inv emp_inames (iref_of c)

An increment operation
++++++++++++++++++++++

Our first step is to build an increment operation from an
``atomic_read`` and a ``cas``. Here is its specification:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //incr_atomic_spec$
   :end-before: //end incr_atomic_spec$

The style of specification is similar to the generic style we used
with ``incr``, except now we use cancellable invariant instead of a
lock.

For its implementation, the main idea is to repeatedly read the
current value of ``x``, say ``v``; and then to ``cas`` in ``v+1`` if
the current value is still ``v``.

The ``read`` function is relatively easy:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //incr_atomic_body_read$
   :end-before: //end incr_atomic_body_read$

* We open the invariant ``l``; then, knowing that the invariant is
  still active, we can unpack` it; then read the value ``v``; pack it
  back; and return ``v``.

The main loop of ``incr_atomic`` is next, shown below:

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //incr_atomic_body_loop$
   :end-before: //end incr_atomic_body_loop$

The loop invariant says:

  * the invariant remains active

  * the local variable ``continue`` determines if the loop iteration
    continues

  * and, so long as the loop continues, we still have ``aspec 'i``,
    but when the loop ends we have ``aspec ('i + 1)``

The body of the loop is also interesting and consists of two atomic
operations. We first ``read`` the value of ``x`` into ``v``. Then we
open the invariant again try to ``cas`` in ``v+1``. If it succeeds, we
return ``false`` from the ``with_invariants`` block; otherwise
``true``. And, finally, outside the ``with_invariants`` block, we set
the ``continue`` variable accordingly. Recall that ``with_invariants``
allows at most a single atomic operation, so we having done a ``cas``,
we are not allowed to also set ``continue`` inside the
``with_invariants`` block.

``add2_v3``
+++++++++++

Finally, we implement our parallel increment again, ``add2_v3``, this
time using invariants, though it has the same specification as before.

.. literalinclude:: ../code/pulse/PulseTutorial.ParallelIncrement.fst
   :language: pulse
   :start-after: //add2_v3$
   :end-before: //end add2_v3$

The code too is very similar to ``add2_v2``, except instead of
allocating a lock, we allocate a cancellable invariant. And, at the
end, instead of acquiring, and leaking, the lock, we simply cancel the
invariant and we're done.

Exercise
........

Implement ``add2`` on a ``ref U32.t``. You'll need a precondition that
``'i + 2 < pow2 32`` and also to strengthen the invariant to prove
that each increment doesn't overflow.
