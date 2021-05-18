.. _Part1_ch2:

An SMT-assisted Classical Logic
===============================

As mentioned :ref:`at the start of this section <Part1>`, a type ``t``
represents a propostion and a term ``e : t`` is a proof of ``t``. In
many other dependently typed languages, exhibiting a term ``e : t`` is
the only way to prove that ``t`` is valid. In F*, while one can do
such proofs, it is not the only way to prove a theorem.

By way of illustration, let's think about :ref:`Boolean refinement
types <Part1_ch1_boolean_refinements>`. As we've seen already, it is
easy to prove in F* ```17 : x:int{x >= 0}``. Under the covers, F*
proves that ``(x >= 0) [17/x]`` reduces to ``true``, yet no explicit
term is given to prove this fact. Instead, F* encodes facts about a
program (including things like the semantics of arithmetic operators
like ``>=``) to the classical logic of an SMT solver and asks it (Z3
typically) to prove whether the formula ``17 >= 0`` is valid in
context including all encoded facts about a program. If Z3 is able to
prove it valid, F* accepts the formula as true, without ever
constructing a proof term for ``17 >= 0``.

This design has many important consequences, including, briefly:

* Trust: F* implicitly trusts its encoding to SMT logic and the
  correctess of the Z3 solver.
  
* Proof irrelevance: Since no proof term is constructed for proofs
  done by SMT, a program cannot distinguish between different proofs
  of a fact proven by SMT.

* Subtyping: Since no proof term is constructed, a term like ``17``
  can have many types, ``int``, ``nat``, ``x:int{x = 17}``, etc. As
  mentioned :ref:`earlier <Part1_ch1_boolean_refinements>`, F*
  leverages this to support refinement subtyping.

* Undecidability: Since Z3 can check the validity of formulas in the
  entirety of its logic, including things like quantifying universally
  and existentially over infinite ranges, F* does not restrict the the
  formulas checked for validity by Z3 to be boolean, or even
  decidable. Yes, typechecking in F* is undecidable.

In this chapter, we'll learn about the the classical logic parts of
F*, i.e., the parts that allow it to interface with an SMT solver.

.. note::

   The beginning of this chapter is a little technical, even though
   we're not telling the full story behind F*'s classical logic
   yet. If parts of it are hard to understand right now, here's what
   you need to know to before you :ref:`jump ahead
   <Part1_ch2_assertions>`.

   F* let's you write quantified formulas, called propositions, like
   so

   .. code-block:: fstar

     forall (x₁:t₁) ... (xₙ:tₙ). p
     exists (x₁:t₁) ... (xₙ:tₙ). p     

   You can build propositions from booleans and conjunctions (``/̀\``),
   disjunctions (``\/``), negations (``~``), implications (``==>``),
   and bi-implications (``<==>``) etc.

   For example, one can say (as shown below) that for all natural
   numbers ``x`` and ``y``, if the modulus ``x % y`` is ``0``, then
   there exists a natural number ``z`` such that ``x`` is ``z * y``.
   
   .. code-block:: fstar

     forall (x:nat) (y:nat). x % y = 0 ==> (exists (z:nat). x = z * y)

   F* also has a notion of propositional equality, written ``==``,
   that can be used to state that two terms of any type are equal. In
   contrast, the boolean equality ``=`` can only be used on types that
   support decidable equality. For instance, for ``f₁, f₂ : int ->
   int``, you can write ``f₁ == f₂`` but you cannot write ``f₁ = f₂``,
   since two functions cannot be decidably compared for equality.
                                 
     
Propositions
^^^^^^^^^^^^

The type ``prop`` defined in ``Prims`` is F*'s type of
proof-irrelevant propositions. More informally, ``prop`` is the type
given to facts that are provable using the SMT solver's classical
logic.

Propositions defined in ``prop`` need not be decidable. For example,
for a Turing machine ``tm``, the fact ``halts tm`` can be defined as a
``prop``, although it is impossible to decide for an arbitrary ``tm``
whether ``tm`` halts on all inputs. This is contrast with ``bool``,
the type of booleans ``{true, false}``. Clearly, one could not defined
``halts tm`` as a ``bool``, since one would be claiming that for
``halts`` is function that for any ``tm`` can decide (by returning
true or false) whether or not ``tm`` halts on all inputs.

F* will implicitly convert a ``bool`` to a ``prop`` when needed, since
a decidable fact can be turned into a fact that may be
undecidable. But, when using propositions, one can define things that
cannot be defined in ``bool``, including quantified formulae, as we'll
see next.

Propositional connectives
^^^^^^^^^^^^^^^^^^^^^^^^^

Consider stating that ``factorial n`` always returns a positive
number, when ``n:nat``. In the :ref:`previous section <Part1_ch1>` we
learned that one way to this is to give ``factorial`` a type like so.

.. code-block:: fstar

  val factorial (n:nat) : x:nat{x > 0}

Here's another way to state it:

.. code-block:: fstar
                
  forall (n:nat). factorial n > 0

What about stating that ``factorial n`` can sometimes return a value
that's greater than ``n²``?

.. code-block:: fstar
                
  exists (n:nat). factorial n > n * n
  
We've just seen our first use of universal and existential
quantifiers.

Quantifiers
...........

A universal quantifer is constructed using the ``forall`` keyword. Its
syntax has the following shape.

.. code-block:: fstar
                
  forall (x₁:t₁) ... (xₙ:tₙ) . p

The ``x₁ ... xₙ`` are bound variables and signify the domain over
which one the proposition ``p`` is quantified. That is, ``forall
(x:t). p`` is valid when for all ``v : t`` the proposition ``p[v/x]``
is valid.

And existential quantifier has similar syntax, using the ``exists``
keyword.

.. code-block:: fstar
                
   exists (x₁:t₁) ... (xₙ:tₙ) . p

In this case, ``exists (x:t). p`` is valid when for some ``v : t`` the
proposition ``p[v/x]`` is valid.

The scope of a quantifier extends as far to the right as possible.

As usual in F*, the types on the bound variables can be omitted and F*
will infer them. However, in the case of quantified formulas, it's a
good idea to write down the types, since the meaning of the quantifier
can change signicantly depending on the type of the variable. Consider
the two propositions below.

.. code-block:: fstar

   exists (x:int). x < 0
   exists (x:nat). x < 0

The first formula is valid by considering ``x = -1``, while the second
one is not—there is not natural number less than zero.

It is possible to quantify over any F* type. This makes the
quantifiers higher order and dependent. For example, one can write

.. code-block:: fstar

   forall (n:nat) (p: (x:nat{x >= n} -> prop)). p n 

.. note::

   The SMT solver uses a number of heuristics to determine if a
   quantified proposition is valid. As you start writing more
   substantial F* programs and proofs, it will become important to
   learn a bit about these heuristics. We'll cover this in a later
   chapter. If you're impatient, you can also read about in on the `F*
   wiki
   <https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns>`_.
   

Conjunction, Disjunction, Negation, Implication
...............................................

In addition to the quantifiers, you can build propositions by
combining them with other propositions, using the opertors below, in
decreasing order of precedence.

**Negation**

The proposition ``~p`` is valid if the negation of ``p`` is
valid. This is similar to the boolean operator ``not``, but applies to
propositions rather than just booleans.

**Conjunction**

The proposition ``p /\ q`` is valid if both ``p`` and ``q`` are
valid. This is similar to the boolean operator ``&&``, but applies to
propositions rather than just booleans.

**Disjunction**

The proposition ``p \/ q`` is valid if at least one of ``p`` and ``q``
are valid. This is similar to the boolean operator ``||``, but applies
to propositions rather than just booleans.

**Implication**

The proposition ``p ==> q`` is valid if whenever ``p`` is valid, ``q``
is also valid.

**Double Implication**

The proposition ``p <==> q`` is valid if ``p`` and ``q`` are
equivalent.

.. note::

   This may come as a surprise, but these precedence rules mean that
   ``p /\ q ==> r`` is parsed as ``(p /\ q) ==> r`` rather than
   ``p /\ (q ==> r)``. When in doubt, use parentheses.


Atomic propositions
^^^^^^^^^^^^^^^^^^^

We've shown you how to form new propositions by building them from
existing propositions using the connectives. But, what about the basic
propositions themselves?


Propositional equality
......................

We've implicitly used the equality operator ``=`` already. This is the
*boolean* equality operator. Given two terms ``e₁ : t`` and ``e₂ :
t``, so long as ``t`` supports a notion of decidable equality,
``(e₁ = e₂) : bool``.

But, what does it mean for a type ``t`` to support a decidable
equality? We'll answer this question in a later section, but, for now,
consider that not all types support equality. For example, what if
``t`` were a function type, like ``int -> int``. To decide if two
functions ``f₁, f₂ : int -> int`` are equal, we'd have to apply them
to all the infinitely many integers and compare their results—clearly,
this is not decidable.

F* offers another notion of equality, propositional equality, written
``==``. For *any type* ``t``, given terms ``e₁, e₂ : t``, the
proposition ``e₁ == e₂`` asserts the (possibly undecidable) equality
of ``e₁`` and ``e₂``.

**Turning a Boolean into a proposition**

Propositional equality provides a convenient way to turn a boolean
into a proposition. For any boolean ``b``, then term ``b == true`` is
a ``prop``. One seldom needs to do write this manually (although it
does come up occasionally), since F* will automatically insert a
``b==true`` if you're using a ``b:bool`` in a context where a ``prop``
was expected.

``Type`` vs. ``prop``
.....................

This next bit is quite technical. Don't worry if you didn't understand
it at first. It's enough to know at this stage that, just like
automatically converting a boolean to `prop`, F* automatically
converts any type to ``prop``, when neeeded. So, you can form new
atomic propositions out of types.

Every well-typed term in F* has a type. Even types have types, e.g.,
the type of ``int`` is ``Type``, i.e., ``int : Type``, ``bool :
Type``, and even ``prop : Type``. We'll have to leave a full
description of this to a later section, but, for now, we'll just
remark that another way to form an atomic proposition is to convert a
type to a proposition.

For any type ``t : Type``, the type ``_:unit { t } : prop``. We call
this "squashing" a type. This is so common, that F* provides two
mechanisms to support this:

1. All the propositonal connectives, like ``p /\ q`` are designed so
   that both ``p`` and ``q`` can be types (i.e., ``p,q : Type``),
   rather than propositions, and they implicitly squash their types.

2. The standard library, ``FStar.Squash``, provides several utilities
   for manipulating squashed types.

.. _Part1_ch2_assertions:

Assertions
^^^^^^^^^^

Now that we have a way to write down propositions, how can we ask F*
to check if those propositions are valid? There are several ways, the
most common of which is an *assertion*. Here's an example:

.. code-block:: fstar

   let sqr_is_nat (x:int) : unit = assert (x * x >= 0)

This defines a function ``sqr_is_nat : int -> unit``—meaning it takes
a ``nat`` and always returns ``()``. So, it's not very interesting as
a function.

However, it's body contains an assertion that ``x * x >= 0``. Now,
many programming languages support runtime assertions—code to check
some property of program when it executes. But, assertions in F* are
different—they are checked by the F* compiler *before* your program is
executed.

In this case, the ``assert`` instructs F* to encode the program to SMT
and to ask Z3 if ``x * x >= 0`` is valid for an arbitrary integer
``x:int``. If Z3 can confirm this fact (which it can), then F* accepts
the program and no trace of the assertion is left in your program when
it executes. Otherwise the program is rejected at compile time. For
example, if we were to write

.. code-block:: fstar

   let sqr_is_pos (x:int) : unit = assert (x * x > 0)

Then, F* complains with the following message::

  Ch2.fst(5,39-5,50): (Error 19) assertion failed; The SMT solver could not prove the query, try to spell your proof in more detail or increase fuel/ifuel

You can use an assertion with any proposition, as shown below.

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: //SNIPPET_START: max
   :end-before: //SNIPPET_END: max                              
   
Lemmas 
^^^^^^^

Let's say you wrote the ``factorial`` function and gave it the type
``nat -> nat``. Later, you care about some other property about
``factorial``, e.g., that if ``x > 2`` then ``factorial x > x``. One
option is to revise the type you wrote for ``factorial`` and get F\*
to reprove that it has this type. But this isn't always feasible. What
if you also wanted to prove that if ``x > 3`` then ``factorial x > 2 *
x``. Clearly, polluting the type of ``factorial`` with all these
properties that you may or may not care about is impractical.

You could write assertions to ask F* to check these properties, e.g.,

.. code-block:: fstar

   let _ = assert (forall (x:nat). x > 2 ==> factorial x > 2)

But, F* complains saying that it couldn't prove this fact. That's not
because the fact isn't true—recall, checking the validity of
assertions in F* is undecidable. So, there are facts that are true
that F* may not be able to prove, at least not without some help.

In this cae, proving this property about ``factorial`` requires a
proof by induction. F* and Z3 cannot do proofs by induction
automatically—you will have to help F* here by writing a *lemma*.

A lemma is a function in F* that always returns the ``():unit``
value. However, the type of lemma carries useful information about
which facts are provable.

Here's our first lemma:

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_is_positive
   :end-before: //SNIPPET_END: factorial_is_positive

There's a lot of information condensed in that definition. Let's spell
it out in detail:

* ``factorial_is_positive`` is a recursive function with a parameter ``x:nat``

* The return type of ``factorial_is_positive`` is a refinement of
  unit, namely ``u:unit{factorial x > 0}``.  That says that the
  function always returns ``()``, but, additionally, when
  ``factorial_is_postive x`` returns (which it always does, since it
  is a total function) it is safe to conclude that ``factorial x >
  0``.

* The next three lines prove the lemma using a proof by induction on
  ``x``. The basic concept here is that by programming total
  functions, we can write proofs about other pure expressions. We'll
  discuss such proofs in detail in the remainder of this section.

Some syntactic shorthands for Lemmas
....................................

Lemmas are so common in F* that it's convenient to have special syntax
for them. Here's another take at our proof by ``factorial x > 0``

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_is_pos
   :end-before: //SNIPPET_END: factorial_is_pos

The type ``x:t -> Lemma (requires pre) (ensures post)`` is the type of
a function

* that can be called with an argument ``v:t``
* the argument must satisfies the precondition ``pre[v/x]``
* the function always returns a ``unit``
* and ensures that the postcondition ``post[v/x]`` is valid

The type is equivalent to ``x:t{pre} -> u:unit{post}``.

A proof by induction, explained in detail
.........................................

Let's look at this lemma in detail again—why does it convince F* that
``factorial x > 0``?

.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: //SNIPPET_START: factorial_is_pos
   :end-before: //SNIPPET_END: factorial_is_pos

* It is a proof by induction on ``x``. Proofs by induction in F* are
  represented by total recursive functions. The fact that it is total
  is extremely important—it ensures that the inductive argument is
  well-founded, i.e., that the induction hypothesis is only applied
  correctly on strictly smaller arguments.

* The base case of the induction is when ``x=0``. In this case, F* +
  Z3 can easily prove that ``factorial 0 > 0``, since this just
  requires computing ``factorial 0`` to ``1`` and checking ``1 > 0``.

* What remains is the case where ``x > 0``.

* In the inductive case, the type of the recursively bound
  ``factorial_is_pos`` represents the induction hypothesis. In this
  case, its type is

  .. code-block:: fstar

     y:int {y < x} -> Lemma (requires y >= 0) (ensures factorial y > 0)

  In other words, the type of recursive function tells us that for all
  ``y`` that are smaller than that current argument ``x`` and
  non-negative , it is safe to assume that ``factorial y > 0``.

* By making a recursive call on ``x-1``, F* can conclude that
  ``factorial (x - 1) > 0``.

* Finally, to prove that ``factorial x > 0``, the solver figures out
  that ``factorial x = x * factorial (x - 1)``. From the recursive
  lemma invocation, we know that ``factorial (x - 1) > 0``, and since
  we're in the case where ``x > 0``, the solver can prove that the
  product of two positive numbers must be positive.

Exercises
^^^^^^^^^

Exercise 1
..........

Try proving the following lemmas about ``factorial``:

.. code-block:: fstar

   val factorial_is_greater_than_arg (x:int)
     : Lemma (requires x > 2)
             (ensures factorial x > x)

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: exercises/Ch2.fst
       :language: fstar
       :start-after: SNIPPET_START: factorial_is_greater_than_arg
       :end-before: SNIPPET_END: factorial_is_greater_than_arg

                    
Exercise 2
..........

Try proving the following lemmas about ``fibonacci``:
                    
.. literalinclude:: exercises/Ch2.fst
   :language: fstar
   :start-after: SNIPPET_START: fibonacci_question
   :end-before: SNIPPET_END: fibonacci_question

.. container:: toggle

    .. container:: header

       **Answer**

    .. literalinclude:: exercises/Ch2.fst
       :language: fstar
       :start-after: SNIPPET_START: fibonacci_answer
       :end-before: SNIPPET_END: fibonacci_answer
                    

    Let's have a look at that proof in some detail. It's much like the
    proof by induction we discussed in detail earlier, except now we
    have two uses of the induction hypothesis.

    * It's a proof by induction on ``n:nat{n >= 2}``, as you can tell from the
      ``let rec``.

    * The base cases are when ``n = 2`` and ``n = 3``. In both these
      cases, the solver can simply compute ``fibonacci n`` and check
      that it is greater than ``n``.

    * Otherwise, in the inductive case, we have ``n >= 4`` and the
      induction hypothesis is the type of the recursive function::

        m:nat{m >= 2 /\ m < n} -> Lemma (fibonacci m >= m)

    * We call the induction hypothesis twice and get::

        fibonacci (n - 1) >= n - 1
        fibonacci (n - 2) >= n - 2

    * To conclude, we show::

        fibonacci n = //by definition
        fibonacci (n - 1) + fibonacci (n - 2) >= //from the facts above
        (n - 1) + (n - 2) = //rearrange
        2*n - 3 >=  //when n >= 4
        n 

    As you can see, once you set up the induction, the SMT solver does
    a lot of the work.

    Sometimes, the SMT solver can even find proofs that you might not
    write yourself. Consider this alternative proof of ``fibonacci n
    >= n``.

    .. literalinclude:: exercises/Ch2.fst
       :language: fstar
       :start-after: SNIPPET_START: fibonacci_answer_alt
       :end-before: SNIPPET_END: fibonacci_answer_alt

    This proof works with just a single use of the induction
    hypothesis. How come? Let's look at it in detail.

    1. It's a proof by induction on ``n:nat{n >= 2}``.

    2. The base case is when ``n=2``. It's easy to compute ``fibonacci 2``
       and check that it's greater than or equal to 2.

    3. In the inductive case, we have::

        n >= 3

    4. The induction hypothesis is::
        
         m:nat{m >= 2 /\ m < n} -> Lemma (fibonacci m >= m)

    5. We apply the induction hypothesis to ``n - 1`` and get ::

        fibonacci (n - 1) >= n - 1

    6. We have::

        fibonacci n = //definition
        fibonacci (n - 1) + fibonacci (n - 2) >= //from 5
        (n - 1) + fibonacci (n - 2)

    7. So, our goal is now::

        (n - 1) + fibonacci (n - 2) >= n

    8. It suffices if we can show ``fibonacci (n - 2) >= 1``

    9. From (2) and the definition of ``fibonacci`` we have::

         fibonacci (n - 1) = //definition
         fibonacci (n - 2) + fibonacci (n - 3) >= //from 5
         n - 1 >= // from 3
         2

         
    10. Now, suppose for contradiction, that ``fibonacci (n - 2) = 0``.

        10.1. Then, from step 9, we have ``fibonacci (n-3) >= 2``

        10.2  If ``n=3``, then ``fibonacci 0 = 1``, so we have a contradiction.

        10.3  If ``n > 3``, then

           10.3.1. ``fibonacci (n-2) = fibonacci (n-3) + fibonacci (n-4)``, by definition

           10.3.2. ``fibonacci (n-3) + fibonacci (n-4) >= fibonacci (n-3)``, since ``fibonacci (n-4) : nat``.

           10.3.3. ``fibonacci (n-2) >= fibonacci (n-3)``, using 10.3.1 and 10.3.2

           10.3.4. ``fibonacci (n-2) >= 2``, using 10.1

           10.3.5. But, 10.3.4 contradicts 10; so the proof is complete.
    
    You probably wouldn't have come up with this proof yourself, and
    indeed, it took us some puzzling to figure out how the SMT solver
    was able to prove this lemma with just one use of the induction
    hypothesis. But, there you have it. All of which is to say that
    the SMT solver is quite powerful!
    
Assumptions
^^^^^^^^^^^

The dual of an assertion is an assumption. Rather than asking F* and
Z3 to prove a fact, an assumption allows one to tell F* and Z3 to
accept that some proposition is valid. You should use assumptions with
care—it's easy to make a mistake and assume a fact that isn't actually
true.

The syntax of an assumption is similar to an assertion. Here, below,
we write ``assume (x <> 0)`` to tell F* to assume ``x`` is non-zero in
the rest of the function. That allows F* to prove that the assertion
that follows is valid. 

.. code-block:: fstar

   let sqr_is_pos (x:int) = assume (x <> 0); assert (x * x > 0)                 

Of course, the assertion is not valid for all ``x``—it's only valid
for those ``x`` that also validate the preceding assumption. 

Just like an ``assert``, the type of ``assume p`` is ``unit``.

There's a more powerful form of assumption, called an ``admit``. The
term ``admit()`` can given any type you like. For example,

.. code-block:: fstar

   let sqr_is_pos (x:int) : y:nat{y > 0} = admit()

Both ``assume`` and ``admit`` can be helpful when you're working
through a proof, but a proof isn't done until it's free of them.
