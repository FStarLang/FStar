
.. _Pulse_linked_list:

Linked Lists
============

In this chapter, we develop a linked list library. Along the way,
we'll see uses of recursive predicates, trades, and universal
quantification.

Representing a Linked List
..........................

Let's start by defining the type of a singly linked list:

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: fstar
   :start-after: //llist$
   :end-before: //end llist$

A ``node t`` contains a ``head:t`` and a ``tail:llist t``, a nullable
reference pointing to the rest of the list. Nullable references are
represented by an option, as :ref:`we saw before
<Pulse_nullable_ref_helpers>`.

Next, we need a predicate to relate a linked list to a logical
representation of the list, for use in specifications. 

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: fstar
   :start-after: //is_list$
   :end-before: //end is_list$

The predicate ``is_list x l`` is a recursive predicate:

  * When ``l == []``, the reference ``x`` must be null.

  * Otherwise, ``l == head :: tl``, ``x`` must contains a valid
    reference ``p``, where ``p`` points to ``{ head; tail }`` and,
    recursively , we have ``is_list tail tl``.


Boilerplate: Introducing and Eliminating ``is_list``
....................................................

We've seen :ref:`recursive predicates in a previous chapter
<Pulse_recursive_predicates>`, and just as we did there, we need some
helper ghost functions to work with ``is_list``. We expect the Pulse
checker will automate these boilerplate ghost lemmas in the future,
but, for now, we are forced to write them by hand.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //boilerplate$
   :end-before: //end boilerplate$



Case analyzing a nullable pointer
.................................

When working with a linked list, the first thing we'll do, typically,
is to check whether a given ``x:llist t`` is null or not. However, the
``is_list x l`` predicate is defined by case analyzing ``l:list t``
rather than ``x:llist t``, since that is makes it possible to write
the predicate by recursing on the tail of ``l``. So, below, we have a
predicate ``is_list_cases x l`` that inverts ``is_list x l`` predicate
based on whether or not ``x`` is null.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: fstar
   :start-after: //is_list_cases$
   :end-before: //end is_list_cases$

Next, we define a ghost function to invert ``is_list`` into ``is_list_cases``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //cases_of_is_list$
   :end-before: //end cases_of_is_list$

We also define two more ghost functions that package up the call to
``cases_of_is_list``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //is_list_case_none$
   :end-before: //end is_list_case_none$

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //is_list_case_some$
   :end-before: //end is_list_case_some$

Length, Recursively
...................

With our helper functions in hand, let's get to writing some real
code, starting with a function to compute the length of an ``llist``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //length$
   :end-before: //end length$

The ``None`` case is simple.

Some points to note in the ``Some`` case:

  * We use ``with _node _tl. _`` to "get our hands on" the
    existentially bound witnesses.

  * After reading ``let node = !vl``, we need ``is_list node.tail
    _tl`` to make the recursive call. But the context contains
    ``is_list _node.tail _tl`` and ``node == _node``. So, we need a
    rewrite.

  * We re-introduce the ``is_list`` predicate, and return ``1 +
    n``. While the ``intro_is_list_cons x vl`` is a ghost step and
    will be erased before execution, the addition is not---so, this
    function is not tail recursive.

Exercise 1
..........

Write a tail-recursive version of ``length``.
    
Exercise 2
..........

Index the ``is_list`` predicate with a fractional permission.  Write
ghost functions to share and gather fractional ``is_list`` predicates.

Length, Iteratively, with Trades
................................

What if we wanted to implement ``length`` using a while loop, as is
more idiomatic in a language like C. It will take us a few steps to
get there, and we'll use the trade operator (``@==>``) to structure
our proof.

Trade Tails
+++++++++++

Our first step is to define ``tail_for_cons``, a lemma stating that with
permission on a node pointer (``pts_to v n``), we can build a trade
transforming a permission on the tail into a permission for a cons
cell starting at the given node.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //tail_for_cons$
   :end-before: //end tail_for_cons$


Tail of a list
++++++++++++++

Next, here's a basic operation on a linked list: given a pointer to a
cons cell, return a pointer to its tail. Here's a small diagram:


.. code-block::

   x             tl
   |             |
   v             v
   .---.---.     .---.---.
   |   | --|---> |   | --|--> ...
   .---.---.     .---.---.

We're given a pointer ``x`` to the cons cell at the head of a list,
and we want to return ``tl``, the pointer to the next cell (or
``None``, of x this is the end of the list). But, if we want to return
a pointer to ``tl``, we a permission accounting problem:

  * We cannot return permission to ``x`` to the caller, since then we
    would have two *aliases* pointing to the next cell in the list:
    the returned ``tl`` and ``x -> next``.

  * But, we cannot consume the permission to ``x`` either, since we
    would like to return permission to ``x`` once the return ``tl``
    goes out of scope.

The solution here is to use a trade. The type of ``tail`` below says
that if ``x`` is a non-null pointer satisfying ``is_list x 'l``, then
``tail`` returns a pointer ``y`` such that ``is_list y tl`` (where
``tl`` is the tail of ``'l``); and, one can trade ``is_list y tl`` to
recover permission to ``is_list x 'l``. The trade essentially says
that you cannot have permission to ``is_list x 'l`` and ``is_list y
tl`` at the same time, but once you give up permission on ``y``, you
can get back the original permission on ``x``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //tail$
   :end-before: //end tail$

``length_iter``
+++++++++++++++

The code below shows our iterative implementation of ``length``. The
basic idea is simple, though the proof takes a bit of doing. We
initialize a current pointer ``cur`` to the head of the list; and
``ctr`` to ``0``. Then, while ``cur`` is not null, we move ``cur`` to
the tail and increment ``ctr``. Finally, we return the ``!ctr``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //length_iter$
   :end-before: //end length_iter$

Now, for the proof. The main part is the loop invariant, which says:

  * the current value of the counter is ``n``;
    
  * ``cur`` holds a list pointer, ``ll`` where ``ll`` contains the
    list represented by ``suffix``;

  * ``n`` is the the length of the prefix of the list traversed so far;

  * the loop continues as long as ``b`` is true, i.e., the list
    pointer ``l`` is not ``None``;

  * and, the key bit: you can trade ownership on ``ll`` back for
    ownership on the original list ``x``.

Some parts of this could be simplified, e.g., to avoid some of the
rewrites.

One way to understand how trades have helped here is to compare
``length_iter`` to the recursive function ``length``. In ``length``,
after each recursive call returns, we called a ghost function to
repackage permission on the cons cell after taking out permission on
the tail. The recursive function call stack kept track of all these
pieces of ghost code that had to be executed. In the iterative
version, we use the trade to package up all the ghost functions that
need to be run, rather than using the call stack. When the loop
terminates, we use ``I.elim`` to run all that ghost code at once.

Of course, the recursive ``length`` is much simpler in this case, but
this pattern of using trades to package up ghost functions is quite
broadly useful.

Append, Recursively
...................

Here's another recursive function on linked lists: ``append``
concatenates ``y`` on to the end of ``x``.

It's fairly straightforward: we recurse until we reach the last node
of ``x`` (i.e., the ``tail`` field is ``None``; and we set that field
to point to ``y``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //append$
   :end-before: //end append$

The code is tail recursive in the ``Some _`` case, but notice that we
have a ghost function call *after* the recursive call. Like we did for
``length``, can we implement an iterative version of ``append``,
factoring this ghost code on the stack into a trade?

Append, Iteratively
...................

Let's start by defining a more general version of the ``tail``
function from before. In comparison, the postcondition of ``tail_alt``
uses a universal quantifier to say, roughly, that whatever list ``tl'``
the returns ``y`` points to, it can be traded for a pointer to ``x``
that cons's on to ``tl``. Our previous function ``tail`` can be easily
recovered by instantiating ``tl'`` to ``tl``.

.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //tail_alt$
   :end-before: //end tail_alt$

We'll use these quantified trades in our invariant of ``append_iter``,
shown below. The main idea of the implementation is to use a while
loop to traverse to the last element of the first list ``x``; and then
to set ``y`` as the ``next`` pointer of this last element.
      
.. literalinclude:: ../code/pulse/PulseTutorial.LinkedList.fst
   :language: pulse
   :start-after: //append_iter$
   :end-before: //end append_iter$

There are few interesting points to note.

  * The main part is the quantified trade in the invariant, which, as
    we traverse the list, encapsulates the ghost code that we need to
    run at the end to restore permission to the initial list pointer
    ``x``.

  * The library function, ``FA.trans_compose`` has the following
    signature:

    .. code-block:: pulse

      ghost
      fn trans_compose (#a #b #c:Type0)
                       (p: a -> slprop)
                       (q: b -> slprop)
                       (r: c -> slprop)
                       (f: a -> GTot b)
                       (g: b -> GTot c)
      requires
        (forall* x. p x @==> q (f x)) **
        (forall* x. q x @==> r (g x))
      ensures
        forall* x. p x @==> r (g (f x))
                  

    We use it in the key induction step as we move one step down the
    list---similar to what we had in ``length_iter``, but this time
    with a quantifier.

  * Illustrating again that Pulse is a superset of pure F*, we make
    use of a :ref:`bit of F* sugar <Part2_connectives>` in the
    ``introduce forall`` to prove a property needed for a Pulse
    rewrite.

  * Finally, at the end of the loop, we use ``FA.elim_forall_imp`` to
    restore permission on ``x``, now pointing to a concatenated list,
    effectively running all the ghost code we accumulated as we
    traversed the list.

Perhaps the lesson from all this is that recursive programs are much
easier to write and prove correct that iterative ones? That's one
takeaway. But, hopefully, you've seen how trades and quantifiers work
and can be useful in some proofs---of course, we'll use them not just
for rewriting recursive as iterative code.

Exercise 3
++++++++++

Write a function to insert an element in a list and a specific
position.


Exercise 4
++++++++++

Write a function to reverse a list.
