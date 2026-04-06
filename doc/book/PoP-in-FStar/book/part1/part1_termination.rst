.. _Part1_termination:

Proofs of termination
=====================

It's absolutely crucial to the soundness of F*'s core logic that all
functions terminate. Otherwise, one could write non-terminating 
functions like this::

  let rec loop (x:unit) : False = loop x

and show that ``loop () : False``, i.e., we'd have a proof term for
``False`` and the logic would collapse.

In the previous chapter, we just saw how to define recursive functions
to :ref:`compute the length of list <Part1_inductives_length>` and to
:ref:`append two lists <Part1_inductives_append>`. We also said
:ref:`earlier <Part1_ch1_arrows>` that all functions in F*'s core are
*total*, i.e., they always return in a finite amount of time. So, you
may be wondering, what is it that guarantees that recursive functions
like ``length`` and ``append`` actually terminate on all inputs?

The full details of how F* ensures termination of all functions in its
core involves several elements, including positivity restrictions on
datatype definitions and universe constraints. However, the main thing
that you'll need to understand at this stage is that F* includes a
termination check that applies to the recursive definitions of total
functions. The check is a semantic check, not a syntactic criterion,
like in some other dependently typed languages.

We quickly sketch the basic structure of the F\* termination check on
recursive functions---you'll need to understand a bit of this in order
to write more interesting programs.

A well-founded partial order on terms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In order to prove a function terminating in F\* one provides a
*measure*: a pure expression depending on the function's
arguments. F\* checks that this measure strictly decreases on each
recursive call.  The measure for the arguments of the call is compared
to the measure for the previous call according to a well-founded
partial order on F\* terms. We write `v1 << v2` when `v1` precedes
`v2` in this order.

.. note::

   A relation `R` is a well-founded partial order on a set `S` if, and
   only if, `R` is a partial order on `S` and there are no infinite
   descending chains in `S` related by `R`. For example, taking `S` to
   be `nat`, the set of natural numbers, the integer ordering `<` is a
   well-founded partial order (in fact, it is a total order).

Since the measure strictly decreases on each recursive call, and there
are no infinite descending chains, this guarantees that the function
eventually stops making recursive calls, i.e., it terminates.

.. _Part1_precedes_relation:

The precedes relation
.....................

Given two terms ``v1:t1`` and ``v2:t2``, we can prove ``v1 << v2``
if any of the following are true:

1. **The ordering on integers**:

   ``t1 = nat`` and ``t2 = nat`` and ``v1 < v2``

   Negative integers are not related by the `<<` relation, which is
   only a _partial_ order.

2. **The sub-term ordering on inductive types**

    If ``v2 = D u1 ... un``, where ``D`` is a constructor of an
    inductive type fully applied to arguments ``u1`` to ``un``, then
    ``v1 << v2`` if either

    * ``v1 = ui`` for some ``i``, i.e., ``v1`` is a sub-term of ``v2``

    * ``v1 = ui x`` for some ``i`` and ``x``, i.e., ``v1`` is the
      result of applying a sub-term of ``v2`` to some argument ``x``.


.. _Part1_why_length_terminates:


Why ``length`` terminates
^^^^^^^^^^^^^^^^^^^^^^^^^

Let's look again at the definition of ``length`` and see how F* checks
that it terminates, i.e.,

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: length
   :end-before: //SNIPPET_END: length

First off, the definition of ``length`` above makes use of various
syntactic shorthands to hide some details. If we were to write it out
fully, it would be as shown below:

.. code-block:: fstar

   let rec length #a (l:list a)
     : Tot nat (decreases l)
     = match l with
       | [] -> 0
       | _ :: tl -> 1 + length tl

The main difference is on the second line. As opposed to just writing
the result type of ``length``, in full detail, we write
``Tot nat (decreases l)``. This states two things

* The ``Tot nat`` part states that ``length`` is a total function
  returning a ``nat``, just as the ``nat`` did before.

* The additional ``(decreases l)`` specifying a *measure*, i.e., the
  quantity that decreases at each recursive call according to the
  well-founded relation ``<<``.

To check the definition, F* gives the recursively bound name
(``length`` in this case) a type that's guarded by the measure. I.e.,
for the body of the function, ``length`` has the following type:

.. code-block:: fstar

   #a:Type -> m:list a{ m << l } -> nat

This is to say that when using ``length`` to make a recursive call, we
can only apply it to an argument ``m << l``, i.e., the recursive call
can only be made on an argument ``m`` that precedes the current
argument ``l``. This is enough to ensure that the recursive calls will
eventually bottom out, since there are no infinite descending chains
related by ``<<``.

In the case of ``length``, we need to prove at the recursive call
``length tl`` that ``tl : (m : list a { m << l })``, or, equivalently
that ``tl << l`` is valid. But, from the sub-term ordering on
inductive types, ``l = Cons _ tl``, so ``tl << l`` is indeed provable
and everything checks out.

.. _Part1_lexicographic_orderings:

Lexicographic orderings
^^^^^^^^^^^^^^^^^^^^^^^

F* also provides a convenience to enhance the well-founded ordering
``<<`` to lexicographic combinations of ``<<``. That is, given two
lists of terms ``v1, ..., vn`` and ``u1, ..., un``, F* accepts that
the following lexicographic ordering::

   v1 << u1 ‌‌\/ (v1 == u1 /\ (v2 << u2 ‌‌\/ (v2 == u2 /\ ( ... vn << un))))

is also well-founded. In fact, it is possible to prove in F* that this
ordering is well-founded, provided ``<<`` is itself well-founded.

Lexicographic ordering are common enough that F* provides special
support to make it convenient to use them. In particular, the
notation::

   %[v1; v2; ...; vn] << %[u1; u2; ...; un]

is shorthand for::

   v1 << u1 ‌‌\/ (v1 == u1 /\ (v2 << u2 ‌‌\/ (v2 == u2 /\ ( ... vn << un))))

Let's have a look at lexicographic orderings at work in proving that
the classic ``ackermann`` function terminates on all inputs.

.. literalinclude:: ../code/Part1.Termination.fst
   :language: fstar
   :start-after: SNIPPET_START: ackermann
   :end-before: SNIPPET_END: ackermann

The ``decreases %[m;n]`` syntax tells F* to use the lexicographic
ordering on the pair of arguments ``m, n`` as the measure to prove
this function terminating.

When defining ``ackermann m n``, for each recursive call of the form
``ackermann m' n'``, F* checks that ``%[m';n'] << %[m;n]``, i.e., F*
checks that either

* ``m' << m``, or
* ``m' = m`` and ``n' << n``

There are three recursive calls to consider:

1. ``ackermann (m - 1) 1``: In this case, since we know that ``m >
   0``, we have ``m - 1 << m``, due to the ordering on natural
   numbers. Since the ordering is lexicographic, the second argument
   is irrelevant for termination.

2. ``ackermann m (n - 1)``: In this case, the first argument remained
   the same (i.e., it's still ``m``), but we know that ``n > 0`` so
   ``n - 1 << n`` by the natural number ordering.

3. ``ackermann (m - 1) (ackermann m (n - 1))``: Again, like in the
   first case, the first argument ``m - 1 << m``, and the second is
   irrelevant for termination.

.. _Part1_termination_default_measures:

Default measures
^^^^^^^^^^^^^^^^

As we saw earlier, F* allows you to write the following code, with no
``decreases`` clause, and it still accepts it.

.. literalinclude:: ../code/Part1.Inductives.fst
   :language: fstar
   :start-after: //SNIPPET_START: length
   :end-before: //SNIPPET_END: length

For that matter, you can leave out the ``decreases`` clause in
``ackermann`` and F* is okay with it.

.. code-block:: fstar

   let rec ackermann (m n:nat)
     : nat
     = if m=0 then n + 1
       else if n = 0 then ackermann (m - 1) 1
       else ackermann (m - 1) (ackermann m (n - 1))

This is because F* uses a simple heuristic to choose the decreases
clause, if the user didn't provide one.

The *default* decreases clause for a total, recursive function is the
lexicographic ordering of all the non-function-typed arguments, taken
in order from left to right.

That is, the default decreases clause for ``ackermann`` is exactly
``decreases %[m; n]``; and the default for ``length`` is just
``decreases %[a; l]`` (which is equivalent to ``decreases l``). So, you
needn't write it.

On the other hand, it you were to flip the order of arguments to
``ackermann``, then the default choice of the measure would not be
correct—so, you'll have to write it explicitly, as shown below.

.. literalinclude:: ../code/Part1.Termination.fst
   :language: fstar
   :start-after: SNIPPET_START: ackermann_flip
   :end-before: SNIPPET_END: ackermann_flip

.. _Part1_mutual_recursion:

Mutual recursion
^^^^^^^^^^^^^^^^

F* also supports mutual recursion and the same check of proving that a
measure of the arguments decreases on each (mutually) recursive call
applies.

For example, one can write the following code to define a binary
``tree`` that stores an integer at each internal node—the keyword
``and`` allows defining several types that depend mutually on each
other.

To increment all the integers in the tree, we can write the mutually
recursive functions, again using ``and`` to define ``incr_tree`` and
``incr_node`` to depend mutually on each other. F* is able to prove
that these functions terminate, just by using the default measure as
usual.

.. literalinclude:: ../code/Part1.Termination.fst
   :language: fstar
   :start-after: //SNIPPET_START: incr_tree
   :end-before: //SNIPPET_END: incr_tree

.. note::

   Sometimes, a little trick with lexicographic orderings can help
   prove mutually recursive functions correct. We include it here as a
   tip, you can probably skip it on a first read.

   .. literalinclude:: ../code/Part1.Termination.fst
      :language: fstar
      :start-after: SNIPPET_START: foo_bar
      :end-before: SNIPPET_END: foo_bar

   What's happening here is that when ``foo l`` calls ``bar``, the
   argument ``xs`` is legitimately a sub-term of ``l``. However, ``bar
   l`` simply calls back ``foo l``, without decreasing the
   argument. The reason this terminates, however, is that ``bar`` can
   freely call back ``foo``, since ``foo`` will only ever call ``bar``
   again with a smaller argument. You can convince F* of this by
   writing the decreases clauses shown, i.e., when ``bar`` calls
   ``foo``, ``l`` doesn't change, but the second component of the
   lexicographic ordering does decrease, i.e., ``0 << 1``.


The termination check, precisely
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Having seen a few examples at work, we can now describe how the
termination check works in general.


.. note::

   We use a slightly more mathematical notation here, so that we can
   be precise. If it feels unfamiliar, you needn't understand this
   completely at first. Continue with the examples and refer back to
   this section, if and when you feel like a precise description would
   be helpful.

When defining a recursive function

.. math::

   \mathsf{f~(\overline{x:t})~:~Tot~r~(decreases~m)~=~e}

i.e., :math:`\mathsf{f}` is a function with several arguments
:math:`\mathsf{x1:t1}, ..., \mathsf{x_n:t_n}`, returning
:math:`\mathsf{r}` with measure :math:`\mathsf{m}`, mutually
recursively with other functions of several arguments at type:

.. math::

   \mathsf{f_1~(\overline{x_1:t_1})~:~Tot~r_1~(decreases~m_1)} \\
   \ldots \\
   \mathsf{f_n~(\overline{x_n:t_n})~:~Tot~r_n~(decreases~m_n)} \\

we check the definition of the function body of :math:`\mathsf{f}`
(i.e., :math:`\mathsf{e}`) with all the mutually recursive functions
in scope, but at types that restrict their domain, in the following
sense:

.. math::

   \mathsf{f~:~(\overline{y:t}\{~m[\overline{y}/\overline{x}]~<<~m~\}~\rightarrow~r[\overline{y}/\overline{x}])} \\
   \mathsf{f_1~:~(\overline{x_1:t_1}\{~m_1~<<~m~\}~\rightarrow~r_1)} \\
   \ldots \\
   \mathsf{f_n~:~(\overline{x_n:t_n}\{~m_n~<<~m~\}~\rightarrow~r_n)} \\

That is, each function in the mutually recursive group can only be
applied to arguments that precede the current formal parameters of
:math:`\mathsf{f}` according to the annotated measures of each
function.

.. _Part1_termination_fibonacci:

Exercise: Fibonacci in linear time
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`Click here <../code/exercises/Part1.Termination.fst>`_ for the exercise file.

Here's a function to compute the :math:`n`-th Fibonacci number.

.. code-block:: fstar

   let rec fibonacci (n:nat)
     : nat
     = if n <= 1
       then 1
       else fibonacci (n - 1) + fibonacci (n - 2)

Here's a more efficient, tail-recursive, linear-time variant.

.. code-block:: fstar

   let rec fib a b n =
      match n with
      | 0 -> a
      | _ -> fib b (a+b) (n-1)

   let fibonacci n = fib 1 1 n

Add annotations to the functions to get F* to accept them, in
particular, proving that ``fib`` terminates.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Termination.fst
       :language: fstar
       :start-after: SNIPPET_START: fib
       :end-before: SNIPPET_END: fib


.. _Part1_termination_reverse:

Exercise: Tail-recursive reversal
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`Click here <../code/exercises/Part1.Termination.fst>`_ for the exercise file.

Here is a function to reverse a list:

.. code-block:: fstar

   let rec rev #a (l:list a)
     : list a
     = match l with
       | [] -> []
       | hd::tl -> append (rev tl) hd

But, it is not very efficient, since it is not tail recursive and,
worse, it is quadratic, it traverses the reversed tail of the list
each time to add the first element to the end of it.

This version is more efficient, because it is tail recursive and
linear.

.. code-block:: fstar

   let rec rev_aux l1 l2 =
     match l2 with
     | []     -> l1
     | hd :: tl -> rev_aux (hd :: l1) tl

   let rev l = rev_aux [] l

Add type annotations to ``rev_aux`` and ``rev``, proving, in
particular, that ``rev_aux`` terminates.

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: ../code/Part1.Termination.fst
       :language: fstar
       :start-after: SNIPPET_START: rev
       :end-before: SNIPPET_END: rev
