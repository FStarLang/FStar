.. _Part1_prop_assertions:

Interfacing with an SMT solver
==============================

As mentioned :ref:`at the start of this section <Part1>`, a type ``t``
represents a proposition and a term ``e : t`` is a proof of ``t``. In
many other dependently typed languages, exhibiting a term ``e : t`` is
the only way to prove that ``t`` is valid. In F*, while one can do
such proofs, it is not the only way to prove a theorem.

By way of illustration, let's think about :ref:`Boolean refinement
types <Part1_ch1_boolean_refinements>`. As we've seen already, it is
easy to prove ``17 : x:int{x >= 0}`` in F*. Under the covers, F*
proves that ``(x >= 0) [17/x]`` reduces to ``true``, yet no explicit
term is given to prove this fact. Instead, F* encodes facts about a
program (including things like the semantics of arithmetic operators
like ``>=``) in the classical logic of an SMT solver and asks it (Z3
typically) to prove whether the formula ``17 >= 0`` is valid in a
context including all encoded facts about a program. If Z3 is able to
prove it valid, F* accepts the formula as true, without ever
constructing a term representing a proof of ``17 >= 0``.

This design has many important consequences, including, briefly:

* Trust: F* implicitly trusts its encoding to SMT logic and the
  correctness of the Z3 solver.
  
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

     forall (x1:t1) ... (xn:tn). p
     exists (x1:t1) ... (xn:tn). p     

   You can build propositions from booleans and conjunctions,
   disjunctions, negations, implications, and bi-implications:

   .. code-block:: fstar

      p /\ q   //conjunction
      p \/ q   //disjunction
      ~p       //negation
      p ==> q  //implication
      p <==> q //bi-implication

   For example, one can say (as shown below) that for all natural
   numbers ``x`` and ``y``, if the modulus ``x % y`` is ``0``, then
   there exists a natural number ``z`` such that ``x`` is ``z * y``.
   
   .. code-block:: fstar

     forall (x:nat) (y:nat). x % y = 0 ==> (exists (z:nat). x = z * y)

   F* also has a notion of propositional equality, written ``==``,
   that can be used to state that two terms of any type are equal. In
   contrast, the boolean equality ``=`` can only be used on types that
   support decidable equality. For instance, for ``f1, f2 : int ->
   int``, you can write ``f1 == f2`` but you cannot write ``f1 = f2``,
   since two functions cannot be decidably compared for equality.
                                 
.. _Part1_prop:

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
the type of booleans ``{true, false}``. Clearly, one could not define
``halts tm`` as a ``bool``, since one would be claiming that for
``halts`` is function that for any ``tm`` can decide (by returning
true or false) whether or not ``tm`` halts on all inputs.

F* will implicitly convert a ``bool`` to a ``prop`` when needed, since
a decidable fact can be turned into a fact that may be
undecidable. But, when using propositions, one can define things that
cannot be defined in ``bool``, including quantified formulae, as we'll
see next.

.. _Part1_prop_connectives:

Propositional connectives
^^^^^^^^^^^^^^^^^^^^^^^^^

Consider stating that ``factorial n`` always returns a positive
number, when ``n:nat``. In the :ref:`previous section <Part1_ch1>` we
learned that one way to do this is to give ``factorial`` a type like so.

.. code-block:: fstar

  val factorial (n:nat) : x:nat{x > 0}

Here's another way to state it:

.. code-block:: fstar
                
  forall (n:nat). factorial n > 0

What about stating that ``factorial n`` can sometimes return a value
that's greater than ``n * n``?

.. code-block:: fstar
                
  exists (n:nat). factorial n > n * n
  
We've just seen our first use of universal and existential
quantifiers.

Quantifiers
...........

A universal quantifier is constructed using the ``forall`` keyword. Its
syntax has the following shape.

.. code-block:: fstar
                
  forall (x1:t1) ... (xn:tn) . p

The ``x1 ... xn`` are bound variables and signify the domain over
which one the proposition ``p`` is quantified. That is, ``forall
(x:t). p`` is valid when for all ``v : t`` the proposition ``p[v/x]``
is valid.

And existential quantifier has similar syntax, using the ``exists``
keyword.

.. code-block:: fstar
                
   exists (x1:t1) ... (xn:tn) . p

In this case, ``exists (x:t). p`` is valid when for some ``v : t`` the
proposition ``p[v/x]`` is valid.

The scope of a quantifier extends as far to the right as possible.

As usual in F*, the types on the bound variables can be omitted and F*
will infer them. However, in the case of quantified formulas, it's a
good idea to write down the types, since the meaning of the quantifier
can change significantly depending on the type of the variable. Consider
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
combining them with other propositions, using the operators below, in
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


Falsehood
.........

The proposition ``False`` is always invalid.

Truth
.....

The proposition ``True`` is always valid.

.. _Part1_ch2_propositional_equality:

Propositional equality
......................

We learned in the previous chapter about the :ref:`two different forms
of equality <Part1_equality>`. The type of propositional equality is

.. code-block:: fstar

   val ( == ) (#a:Type) (x:a) (y:a) : prop

Unlike decidable equality ``(=)``, propositional equality is defined
for all types. The result type of ``(==)`` is ``prop``, the type of
propositions, meaning that ``x == y`` is a proof-irrelevant
proposition.

   
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
converts any type to ``prop``, when needed. So, you can form new
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

1. All the propositional connectives, like ``p /\ q`` are designed so
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

.. literalinclude:: ../code/Part1.Assertions.fst
   :language: fstar
   :start-after: //SNIPPET_START: max
   :end-before: //SNIPPET_END: max                              
    
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
