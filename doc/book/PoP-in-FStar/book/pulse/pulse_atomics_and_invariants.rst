.. _Pulse_atomics_and_invariants:

Atomic Operations and Invariants
================================

In this section, we finally come to some concurrency related
constructs.

Concurrency in Pulse is built around two concepts:

  * **Atomic operations**: operations that are guaranteed to be
    executed in a single-step of computation without interruption by
    other threads.

  * **Invariants**: named predicates that are enforced to be true at
    all times.  Atomic operations can make use of invariants, assuming
    they are true in the current state, and enforced to be true again
    once the atomic step concludes.

Based on this, and in conjunction with all the other separation logic
constructs that we've learned about so far, notably the use of ghost
state, Pulse enables proofs of concurrent programs.

Atomic Operations
.................

We've learned so far about :ref:`two kinds of Pulse computations
<Pulse_higher_order>`:

  * General purpose, partially correct computations, with the ``stt``
    computation type

  * Ghost computations, proven totally correct, and enforced to be
    computationally irrelevant with the ``stt_ghost`` computation
    type.

Pulse offers a third kind of computation, *atomic* computations, with
the ``stt_atomic`` computation type. Here is the signature of
``read_atomic`` and ``write_atomic`` from ``Pulse.Lib.Reference``:

.. code-block:: pulse

   atomic
   fn read_atomic (r:ref U32.t) (#n:erased U32.t) (#p:perm)
   requires pts_to r #p n
   returns x:U32.t
   ensures pts_to r #p n ** pure (reveal n == x)

.. code-block:: pulse   

   atomic
   fn write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
   requires pts_to r n
   ensures pts_to r x

The ``atomic`` annotation on these functions claims that reading and
writing 32-bit integers can be done in a single atomic step of
computation.

This is an assumption about the target architecture on which a Pulse
program is executed. It may be that on some machines, 32-bit values
cannot be read or written atomically. So, when using atomic
operations, you should be careful to check that it is safe to assume
that these operations truly are atomic.

Pulse also provides a way for you to declare that other operations are
atomic, e.g., maybe your machine supports 64-bit or 128-bit atomic
operations---you can program the semantics of these operations in F*
and add them to Pulse, marking them as atomic.

Sometimes, particularly at higher order, you will see atomic
computations described by the computation type below:

.. code-block:: fstar

   val stt_atomic (t:Type) (i:inames) (pre:slprop) (post:t -> slprop)
     : Type u#4

Like ``stt_ghost``, atomic computations are total and live in universe
``u#4``. As such, you cannot store an atomic function in the state,
i.e., ``ref (unit -> stt_atomic t i p q)`` is not a well-formed type.

Atomic computations and ghost computations are also indexed by
``i:inames``, where ``inames`` is a set of invariant names. We'll
learn about these next.

Invariants
..........

In ``Pulse.Lib.Core``, we have the following types:

.. code-block:: fstar

   [@@erasable]
   val iref : Type0
   val inv (i:iref) (p:slprop) : slprop

Think of ``inv i p`` as a predicate asserting that ``p`` is true in
the current state and all future states of the program. Every
invariant has a name, ``i:iref``, though, the name is only relevant in
specifications, i.e., it is erasable.

A closely related type is ``iname``:

.. code-block:: fstar

   val iname : eqtype
   let inames = erased (FStar.Set.set iname)

Every ``iref`` can be turned into an ``iname``, with the function
``iname_of (i:iref): GTot iname``.

Invariants are duplicable, i.e., from ``inv i p`` one can prove ``inv
i p ** inv i p``, as shown by the type of ``Pulse.Lib.Core.dup_inv``
below:

.. code-block:: pulse
		    
    ghost fn dup_inv (i:iref) (p:slprop)
    requires inv i p
    ensures inv i p ** inv i p

Creating an invariant 
+++++++++++++++++++++

Let's start by looking at how to create an invariant.

First, let's define a predicate ``owns x``, to mean that we hold
full-permission on ``x``.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: fstar
   :start-after: //owns$
   :end-before: //end owns$


Now, if we can currently prove ``pts_to r x`` then we can turn it into
an invariant ``inv i (owns r)``, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //create_invariant$
   :end-before: //end create_invariant$

Importantly, when we turn ``pts_to r x`` into ``inv i (owns r)``, **we
lose** ownership of ``pts_to r x``. Remember, once we have ``inv i
(owns r)``, Pulse's logic aims to prove that ``owns r`` remains true
always. If we were allowed to retain ``pts_to r x``, while also
creating an ``inv i (owns r)``, we can clearly break the invariant,
e.g., by freeing ``r``.

.. note::

   A tip: When using an ``inv i p``, it's a good idea to make sure
   that ``p`` is a user-defined predicate. For example, one might
   think to just write ``inv i (exists* v. pts_to x v)`` instead of
   defining an auxiliary predicate for ``inv i (owns r)``. However, the
   some of the proof obligations produced by the Pulse checker are
   harder for the SMT solver to prove if you don't use the auxiliary
   predicate and you may start to see odd failures. This is something
   we're working to improve. In the meantime, use an auxiliary
   predicate.

Impredicativity and the ``later`` modality
+++++++++++++++++++++++++++++++++++++++++++

Pulse allows *any* predicate ``p:slprop`` to be turned into an invariant ``inv i
p : slprop``. Importantly, ``inv i p`` is itself an ``slprop``, so one can even
turn an invariant into another invariant, ``inv i (inv j p)``, etc. This ability
to turn any predicate into an invariant, including invariants themselves, makes
Pulse an *impredicative* separation logic.

Impredicativity turns out to be useful for a number of reasons, e.g., one could
create a lock to protect access to a data structure that may itself contain
further locks. However, soundly implementing impredicativity in a separation
logic is challenging, since it involves resolving a kind of circularity in the
definitions of heaps and heap predicates. PulseCore resolves this circularity
using something called *indirection theory*, using it to provide a foundational
model for impredicative invariants, together with all the constructs of Pulse.
The details of this construction is out of scope here, but one doesn't really
need to know how the construction of the model works to use the resulting logic.

We provide a bit of intuition about the model below, but for now, just keep in
mind that Pulse includes the following abstract predicates:

.. code-block:: fstar

   val later (p:slprop) : slprop
   val later_credit (i:nat) : slprop

with the following forms to introduce and eliminate them:

.. code-block:: pulse

   ghost fn later_intro (p: slprop)
   requires p
   ensures later p

   ghost fn later_elim (p: slprop)
   requires later p ** later_credit 1
   ensures p

   fn later_credit_buy (amt:nat)
   requires emp
   ensures later_credit n

Opening Invariants
++++++++++++++++++++++++++++++++++++++++++++++

Once we've allocated an invariant, ``inv i (owns r)``, what can we do with it?
As we said earlier, one can make use of the ``owns r`` in an atomic computation,
so long as we restore it at the end of the atomic step.

The ``with_invariants`` construct gives us access to the invariant
within the scope of at most one atomic step, preceded or succeeded by
as many ghost or unobservable steps as needed.

The general form of ``with_invariants`` is as follows, to "open"
invariants ``i_1`` to ``i_k`` in the scope of ``e``.

.. code-block:: pulse

   with_invariants i_1 ... i_k
   returns x:t
   ensures post
   { e }

In many cases, the ``returns`` and ``ensures`` annotations are
omitted, since it can be inferred.
   
This is syntactic sugar for the following nest:

.. code-block:: pulse

   with_invariants i_1 {
    ...
     with_invariants i_k
     returns x:t
     ensures post
     { e }
    ...
   }

Here's the rule for opening a single invariant ``inv i p`` using
``with_invariant i { e }`` is as follows:

* ``i`` must have type ``iref`` and ``inv i p`` must be provable in
  the current context, for some ``p:slprop``
   
* ``e`` must have the type ``stt_atomic t j (later p ** r) (fun x -> later p **
  s x)``. [#]_ That is, ``e`` requires and restores ``later p``, while also
  transforming ``r`` to ``s x``, all in at most one atomic step. Further, the
  ``name_of_inv i`` must not be in the set ``j``.

* ``with_invariants i { e }`` has type ``stt_atomic t (add_inv i j)
  (inv i p ** r) (fun x -> inv i p ** s x)``. That is, ``e`` gets to
  use ``p`` for a step, and from the caller's perspective, the context
  was transformed from ``r`` to ``s``, while the use of ``p`` is
  hidden.

* Pay attention to the ``add_inv i j`` index on ``with_invariants``:
  ``stt_atomic`` (or ``stt_ghost``) computation is indexed by
  the names of all the invariants that it may open.


Let's look at a few examples to see how ``with_invariants`` works.

.. [#]

    Alternatively ``e`` may have type ``stt_ghost t j (later p ** r) (fun x ->
    later p ** s x)``, in which case the entire ``with_invariants i { e }``
    block has type ``stt_ghost t (add_inv i j) (inv i p ** r) (fun x -> inv i p
    ** s x)``, i.e., one can open an invariant and use it in either an atomic or
    ghost context.
    
    
Updating a reference
~~~~~~~~~~~~~~~~~~~~

Let's try do update a reference, given ``inv i (owns r)``. Our first attempt is
shown below:

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_atomic0$
   :end-before: //end update_ref_atomic0$

We use ``with_invariants i { ... }`` to open the invariant, and in the scope of
the block, we have ``later (owns r)``.  Now, we're stuck: we need ``later (owns
r)``, but we only have ``later (owns r)``. In order to eliminate the later, we
can use the ``later_elim`` combinator shown earlier, but to call it, we need to
also have a ``later_credit 1``.

So, let's try again:

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_atomic$
   :end-before: //end update_ref_atomic$

* The precondition of the function also includes a ``later_credit 1``.

* At the start of the ``with_invariants`` scope, we have ``later (owns r)`` in
  the context.

* The ghost step ``later_elim _`` uses up the later credit and eliminates
  ``later (owns r)`` into ``owns r``.

* The ghost step ``unfold owns`` unfolds it to its definition.

* Then, we do a single atomic action, ``write_atomic``. 

* And follow it up with a ``fold owns``, another ghost step.

* To finish the block, we need to restore ``later (owns r)``, but we have ``owns
  r``, so the ghost step ``later_intro`` does the job.

* The block within ``with_invariants i`` has type ``stt_atomic unit
  emp_inames (later (owns r) ** later_credit 1) (fun _ -> later (owns r) ** emp)``

* Since we opened the invariant ``i``, the type of ``update_ref_atomic`` records
  this in the ``opens (singleton i)`` annotation; equivalently, the type is
  ``stt_atomic unit (singleton i) (inv i (owns r) ** later_credit 1) (fun _ ->
  inv i (owns r))``. When the ``opens`` annotation is omitted, it defaults to
  ``emp_inames``, the empty set of invariant names.

Finally, to call ``update_ref_atomic``, we need to buy a later credit first.
This is easily done before we call the atomic computation, as shown below:


.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref$
   :end-before: //end update_ref$

The later modality and later credits
++++++++++++++++++++++++++++++++++++

Having seen an example with later modality at work, we provide a bit of
intuition for the underlying model.

The semantics of PulseCore is defined with respect to memory with an abstract
notion of a "ticker", a natural number counter, initialized at the start of a
program's execution. In other logics, this is sometimes called a "step index",
but in PulseCore, the ticker is unrelated to the number of actual steps a
computation takes. Instead, at specific points in the program, the programmer
can issue a specific *ghost* instruction to "tick" the ticker, decreasing its
value by one unit. The decreasing counter provides a way to define an
approximate fixed point between the otherwise-circular heaps and heap
predicates. The logic is defined in such a way that it is always possible to
pick a high enough initial value for the ticker so that any finite number of
programs steps can be executed before the ticker is exhausted. 

Now, rather than explicitly working with the ticker, PulseCore encapsulates all
reasoning about the ticker using two logical constructs: the *later* modality
and *later credits*, features found in Iris and other separation logics that
feature impredicativity.

The Later Modality and Later Credits
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The predicate ``later p`` states that the ``p:slprop`` is true after one tick.

.. code-block:: pulse

   val later (p: slprop) : slprop

All predicates ``p:slprop`` are "hereditary", meaning that if they are true in a
given memory, then they are also true after that memory is ticked. The ghost
function ``later_intro`` embodies this principle: from ``p`` one can prove
``later p``.

.. code-block:: pulse

   ghost fn later_intro (p: slprop)
   requires p
   ensures later p

Given a ``later p``, one can prove ``p`` by using ``later_elim``. This ghost
function effectively "ticks" the memory (since ``later p`` says that ``p`` is
true after a tick), but in order to do so, it needs a precondition that the
ticker has not already reached zero: ``later_credit 1`` says just that, i.e.,
that the memory can be ticked at least once.

.. code-block:: pulse

   ghost fn later_elim (p: slprop)
   requires later p ** later_credit 1
   ensures p

The only way to get a ``later_credit 1`` is to *buy* a credit with the operation
below---this is a concrete operation that ensures that the memory can be ticked
at least ``n`` times. 

.. code-block:: pulse

   fn later_credit_buy (amt:nat)
   requires emp
   ensures later_credit n

At an abstract level, if the ticker cannot be ticked further, the program loops
indefinitely---programs that use later credits (and more generally in step
indexed logics) are inherently proven only partially correct and are allowed to
loop infinitely. At a meta-level, we show that one can always set the initial
ticker value high enough that ``later_credit_buy`` will never actually loop
indefinitely. In fact, when compiling a program, Pulse extracts
``later_credit_buy n`` to a noop ``()``.

Note, later credits can also be split and combined additively:

.. code-block:: fstar

   val later_credit_zero ()
   : Lemma (later_credit 0 == emp)

   val later_credit_add (a b: nat)
   : Lemma (later_credit (a + b) == later_credit a ** later_credit b)

Timeless Predicates
~~~~~~~~~~~~~~~~~~~

All predicates ``p:slprop`` are hereditary, meaning that ``p`` implies ``later
p``. Some predicates, including many common predicates like ``pts_to`` are also
**timeless**, meaning that ``later p`` implies ``p``. Combining timeless
predicates with ``**`` or exisentially quantifying over timeless predicates
yields a timeless predicate.

All of the following are available in Pulse.Lib.Core:

.. code-block:: fstar

   val timeless (p: slprop) : prop
   let timeless_slprop = v:slprop { timeless v }
   val timeless_emp : squash (timeless emp)
   val timeless_pure  (p:prop) : Lemma (timeless (pure p))
   val timeless_star (p q : slprop) : Lemma
      (requires timeless p /\ timeless q)
      (ensures timeless (p ** q))
   val timeless_exists (#a:Type u#a) (p: a -> slprop) : Lemma
    (requires forall x. timeless (p x))
    (ensures timeless (op_exists_Star p))

And in Pulse.Lib.Reference, we have:

.. code-block:: fstar

   val pts_to_timeless (#a:Type) (r:ref a) (p:perm) (x:a) 
   : Lemma (timeless (pts_to r #p x))
           [SMTPat (timeless (pts_to r #p x))]

For timeless predicates, the ``later`` modality can be eliminated trivially
without requiring a credit.

.. code-block:: pulse

   ghost fn later_elim_timeless (p: timeless_slprop)
   requires later p
   ensures p

Updating a reference, with timeless predicates
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Since ``pts_to`` is timeless, we can actually eliminate ``later (owns r)``
without a later credit, as shown below.

First, we prove that ``owns`` is timeless:


.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //owns_timeless$
   :end-before: //end owns_timeless$

.. note::
   
   It's usually easier to prove a predicate timeless by just annotating its
   definition, rather than writing an explicit lemma. For example, 
   this would have worked:

   .. code-block:: fstar

      let owns (x:ref U32.t) : timeless_slprop = exists* v. pts_to x v

Next, we can revise ``update_ref_atomic`` to use ``later_elim_timeless``, rather
than requiring a later credit.

.. literalinclude::  ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_atomic_alt$
   :end-before: //end update_ref_atomic_alt$


Double opening is unsound
++++++++++++++++++++++++++

To see why we have to track the names of the opened invariants,
consider the example below. If we opened the same invariant twice
within the same scope, then it's easy to prove ``False``:

.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //double_open_bad$
   :end-before: //end double_open_bad$

Here, we open the invariants ``i`` twice and get ``owns r ** owns r``,
or more than full permission to ``r``---from this, it is easy to build
a contradiction.


Subsuming atomic computations
++++++++++++++++++++++++++++++

Atomic computations can be silently converted to regular, ``stt``
computations, while forgetting which invariants they opened. For
example, ``update_ref`` below is not marked atomic, so its type
doesn't record which invariants were opened internally.
  
.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref$
   :end-before: //end update_ref$

This is okay, since a non-atomic computation can never appear within a
``with_invariants`` block---so, there's no fear of an ``stt``
computation causing an unsound double opening. Attempting to use a
non-atomic computation in a ``with_invariants`` block produces an
error, as shown below.


.. literalinclude:: ../code/pulse/PulseTutorial.AtomicsAndInvariants.fst
   :language: pulse
   :start-after: //update_ref_fail$
   :end-before: //end update_ref_fail$

.. code-block::

   - This computation is not atomic nor ghost. `with_invariants`
     blocks can only contain atomic computations.