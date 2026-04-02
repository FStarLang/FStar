.. _Pulse_implication_and_forall:

Implication and Universal Quantification
========================================

In this chapter, we'll learn about two more separation logic
connectives, ``@==>`` and ``forall*``. We show a few very simple
examples using them, though these will be almost trivial. In the next
chapter, on linked lists, we'll see more significant uses of these
connectives.

Trades, or Separating Ghost Implication
........................................

The library ``module I = Pulse.Lib.Trade.Util`` defines the operator *trade*
``(@==>)`` and utilities for using it. In the literature, the operator ``p --*
q`` is pronounced "p magic-wand q"; ``p @==> q`` is similar, though there are
some important technical differences, as we'll see. We'll just pronounce it ``p
for q``, ``p trade q``, or ``p trades for q``. Here's an informal description of
what ``p @==> q`` means:

  ``p @==> q`` says that if you have ``p`` then you can *trade* it for
  ``q``. In other words, from ``p ** (p @==> q)``, you can derive
  ``q``. This step of reasoning is performed using a ghost function
  ``I.elim`` with the signature below:

  .. code-block:: pulse    
   
     ghost
     fn I.elim (p q:slprop)
     requires p ** (p @==> q)
     ensures q
   

Importantly, if you think of ``p`` as describing permission on a
resource, the ``I.elim`` makes you *give up* the permission ``p`` and
get ``q`` as a result. Note, during this step, you also lose
permission on the implication, i.e., ``p @==> q`` lets you trade ``p``
for ``q`` just once.

But, how do you create a ``p @==> q`` in the first place? That's its
introduction form, shown below:

  .. code-block:: pulse

     ghost
     fn I.intro (p q r:slprop)
                (elim: unit -> stt_ghost unit emp_inames (r ** p) (fun _ -> q))
     requires r
     ensures p @==> q
   
That is, to introduce ``p @==> q``, one has to show hold permission
``r``, such that a ghost function can transform ``r ** p`` into
``q``.

Share and Gather
++++++++++++++++

Here's a small example to see ``p @==> q`` at work.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: fstar
   :start-after: //regain_half$
   :end-before: //end regain_half$

The predicate ``regain_half`` says that you can trade a
half-permission ``pts_to x #one_half v`` for a full permission
``pts_to x v``. At first, this may seem counter-intuitive: how can you
gain a full permission from half-permission. The thing to remember is
that ``p @==> q`` itself holds permissions internally. In particular,
``regain_half x v`` holds ``exists* u. pts_to x #one_half u``
internally, such that if the context presents the other half, the
eliminator can combine the two to return the full permission.

Let's look at how to introduce ``regain_half``:

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //intro_regain_half$
   :end-before: //end intro_regain_half$

The specification says that if we start out with ``pts_to x 'v`` then
we can split it into ``pts_to x #one_half v`` and a ``regain_half x
'v``. The normal way of splitting a permission a reference would split
it into two halves---here, we just package the second half in a ghost
function that allows us to gather the permission back when we need it.

In the implementation, we define an auxiliary ghost function that
corresponds to the eliminator for ``pts_to x #one_half 'v @==> pts_to x
'v``---it's just a ``gather``. Then, we split ``pts_to x 'v`` into
halves, call ``I.intro`` passing the eliminator, and the fold it into
a ``regain_half``. All ``regain_half`` has done is to package the
ghost function ``aux``, together the half permission on ``x``, and put
it into a ``slprop``.

Later on, if want to use ``regain_half``, we can call its
eliminator---which, effectively, calls ``aux`` with the needed
permission, as shown below.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //use_regain_half$
   :end-before: //end use_regain_half$

At this point, you may be wondering why we bother to use a
``regain_half x 'v`` in the first place, since one might as well have
just used ``pts_to x #one_half 'v`` and ``gather``, and you'd be right
to wonder that! In this simple usage, the ``(@==>)`` hasn't bought us
much.

Universal Quantification
........................

Let's look at our ``regain_half`` predicate again:

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: fstar
   :start-after: //regain_half$
   :end-before: //end regain_half$

This predicate is not as general as it could be: to eliminate it, it
requires the caller to prove that they holds ``pts_to x #one_half v``,
for the same ``v`` as was used when the trade was introduced. 

One could try to generalize ``regain_half`` a bit by changing it to:

.. code-block:: fstar

   let regain_half #a (x:GR.ref a) (v:a) =
     (exists* u. pts_to x #one_half u) @==> pts_to x v

This is an improvement, but it still is not general enough, since it
does not relate ``v`` to the existentially bound ``u``. What we really
need is a universal quantifier.

Here's the right version of ``regain_half``:

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: fstar
   :start-after: //regain_half_q$
   :end-before: //end regain_half_q$

This says that no matter what ``pts_to x #one_half u`` the context
has, they can recover full permission to it, *with the same witness*
``u``.

The ``forall*`` quantifier and utilities to manipulate it are defined
in ``Pulse.Lib.Forall.Util``. The introduction and elimination forms
have a similar shape to what we saw earlier for ``@==>``:


  .. code-block:: pulse

     ghost
     fn FA.elim (#a:Type) (#p:a->slprop) (v:a)
     requires (forall* x. p x)
     ensures p v

The eliminator allows a *single* instantiation of the universally
bound ``x`` to ``v``.

  .. code-block:: pulse

     ghost
     fn FA.intro (#a:Type) (#p:a->slprop)
          (v:slprop)
          (f_elim : (x:a -> stt_ghost unit emp_inames v (fun _ -> p x)))
     requires v
     ensures (forall* x. p x)

The introduction form requires proving that one holds ``v``, and that
with ``v`` a ghost function can produce ``p x``, for any ``x``.

Note, it's very common to have universal quantifiers and trades
together, so the library also provides the following combined forms:

  .. code-block:: pulse

     ghost
     fn elim_forall_imp (#a:Type0) (p q: a -> slprop) (x:a)
     requires (forall* x. p x @==> q x) ** p x
     ensures q x
     
and

  .. code-block:: pulse
                  
     ghost
     fn intro_forall_imp (#a:Type0) (p q: a -> slprop) (r:slprop)
              (elim: (u:a -> stt_ghost unit emp_inames 
                               (r ** p u)
                               (fun _ -> q u)))
     requires r
     ensures forall* x. p x @==> q x

     
Share and Gather, Again
+++++++++++++++++++++++

Here's how one introduces ``regain_half_q``:

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //intro_regain_half_q$
   :end-before: //end intro_regain_half_q$

Now, when we want to use it, we can trade in any half-permission on
``pts_to x #one_half u``, for a full permission with the same ``u``.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //use_regain_half_q$
   :end-before: //end use_regain_half_q$

Note using the eliminator for ``FA.elim`` is quite verbose: we need to
specify the quantifier term again. The way Pulse uses F*'s unifier
currently does not allow it to properly find solutions to some
higher-order unification problems. We expect to fix this soon.


Trades and Ghost Steps
......................

As a final example in this section, we show that one can use package
any ghost computation into a trade, including steps that may modify
the ghost state. In full generality, this makes ``@==>`` behave more
like a view shift (in Iris terminology) than a wand.

Here's a predicate ``can_update`` which says that one can trade a half
permission to ``pts_to x #one_half u`` for a full permission to a
*different value* ``pts_to x v``.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: fstar
   :start-after: //can_update$
   :end-before: //end can_update$

In ``make_can_update``, we package a ghost-state update function into
a binary quantifier ``forall* u v. ...``.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //make_can_update$
   :end-before: //end make_can_update$

And in ``update``, below, we instantiate it to update the reference
``x`` from ``'u`` to ``k``, and also return back a ``can_update``
predicate to the caller, for further use.

.. literalinclude:: ../code/pulse/PulseTutorial.ImplicationAndForall.fst
   :language: pulse
   :start-after: //update$
   :end-before: //end update$
                
