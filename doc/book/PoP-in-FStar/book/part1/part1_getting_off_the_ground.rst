.. _Part1_ch1:

Getting off the ground
======================

To start writing some F* programs, we'll need to learn some basics
about the syntax of the language and some core concepts of types and
functions.

.. _Part1_editors:

Text Editors
^^^^^^^^^^^^

F* can be used as a command line tool with any text editor. If you're
viewing this in the interactive online tutorial, you can use the
`Ace-based <https://ace.c9.io/>`_ text editor alongside, which
provides some basic conveniences like syntax highlighting. However,
beyond casual use, most users of F* rely on one of the following IDE
plugins.

  * `fstar-mode.el <https://github.com/FStarLang/fstar-mode.el>`_,
    which provides several utilities for interactively editing and
    checking F* files in emacs.

  * `fstar-vscode-assistant
    <https://github.com/FStarLang/fstar-vscode-assistant>`_, which
    also provides interactive editing and checking support in VS Code.

The main benefit to using these IDE plugins is that they allow you to
incrementally check just the changing suffix of an F* file, rather
than rechecking the entire file in batch mode. They also provide
standard things like jumping to definitions, type of a symbol etc.

Both these plugins rely on a generic but custom interaction protocol
implemented by the F* compiler. It should be possible to implement IDE
support similar to fstar-mode.el or fstar-vscode-assistant in your
favorite plugin-capable editor.


Basic syntactic structure
^^^^^^^^^^^^^^^^^^^^^^^^^

An F* program is a collection of modules, with each
module represented by a single file with the filename extension
``.fst``. Later, we'll see that a module's interface is in a separate
``.fsti`` file and allows hiding details of a module's implementation
from a client module.

A module begins with the module's name (which must match the name of
its file, i.e., ``module A`` is in ``A.fst``) and contains a sequence
of top-level signatures and definitions. Module names always begin
with a capital letter.

* Signatures ascribe a type to a definition, e.g., ``val f : t``.

Definitions come in several flavors: the two main forms we'll focus on
when programming with total functions are

* possibly recursive definitions (let bindings, ``let [rec] f = e``)
* and, inductive type definitions (datatypes, ``type t = | D1 : t1 | ... | Dn : tn``)

In later sections, we'll see two other kinds of definition:
user-defined indexed effects and sub-effects.

Comments
^^^^^^^^

Block comments are delimited by ``(*`` and ``*)``. Line comments begin
with ``//``.

.. code-block:: fstar

  (* this is a
     block comment *)


  //This is a line comment


Primitives
^^^^^^^^^^

Every F* program is checked in the context of some ambient primitive
definitions taken from the core F* module ``Prims``.

False
.....

The type ``False`` has no elements. Since there are no terms that
satisfy ``e : False``, the type ``False`` is the type of unprovable
propositions.

Unit
....

The type ``unit`` has a single element denoted ``()``, i.e., ``() :
unit``.

Booleans
........

The type ``bool`` has two elements, ``true`` and ``false``. Note, the
lowercase ``false`` is a boolean constant, distinct from the uppercase
``False`` type.

The following primitive boolean operators are available, in decreasing
order of precedence.

* ``not``: Boolean negation (unary, prefix)
* ``&&``: Boolean conjunction (binary, infix)
* ``||``: Boolean disjunction (binary, infix)

Conditionals
############

You can, of course, branch on a boolean with ``if/then/else``

.. code-block:: fstar

  if b then 1 else 0

  if b1 && b2 || b3
  then 17
  else 42


Integers
........

The type ``int`` represents unbounded, primitive mathematical
integers. Its elements are formed from the literals ``0, 1, 2, ...``,
and the following primitive operators, in decreasing order of
precedence.

* ``-``: Unary negation (prefix)
* ``-``: Subtraction (infix)
* ``+``: Addition (infix)
* ``/``: Euclidean division (infix)
* ``%``: Euclidean modulus (infix)
* ``op_Multiply``: Unfortunately, the traditional multiplication
  symbol ``*`` is reserved by default for the tuple type
  constructor. Use the module ``FStar.Mul`` to treat ``*`` as integer
  multiplication.
* ``<`` : Less than (infix)
* ``<=``: Less than or equal (infix)
* ``>`` : Greater than (infix)
* ``>=``: Greater than or equal (infix)

.. note::
   
    F* follows the OCaml style of no negative integer literals,
    instead negate a positive integer like ``(- 1)``.
    
.. _Part1_ch1_boolean_refinements:

Boolean refinement types
^^^^^^^^^^^^^^^^^^^^^^^^

The F* core library, ``Prims``, defines the type of
natural numbers as follows

.. code-block:: fstar

       let nat = x:int{x >= 0}

This is an instance of a boolean refinement type, whose general form
is ``x:t { e }`` where ``t`` is a type, and ``e`` is a ``bool``-typed term
that may refer to the ``t``-typed bound variable ``x``. The term ``e``
*refines* the type ``t``, in the sense that the set ``S`` denoted by ``t``
is restricted to those elements ``x`` :math:`\in` ``S``  for which ``e`` evaluates to
``true``.

That is, the type ``nat`` describes the set of terms that evaluate to an
element of the set ``{0, 1, 2, 3, ...}``.

But, there's nothing particularly special about ``nat``. You can define
arbitrary refinements of your choosing, e.g.,

.. code-block:: fstar

  let empty = x:int { false } //the empty set
  let zero = x:int{ x = 0 } //the type containing one element `0`
  let pos = x:int { x > 0 } //the positive numbers
  let neg = x:int { x < 0 } //the negative numbers
  let even = x:int { x % 2 = 0 } //the even numbers
  let odd = x:int { x % 2 = 1 } //the odd numbers

If you're coming from a language like C or Java where a type primarily
describes some properties about the representation of data in memory,
this view of types as describing arbitrary sets of values may feel a
bit alien. But, let it sink in a bit---types that carve out precise
sets of values will let you state and check invariants about your
programs that may otherwise have only been implicit in your code.

.. note::

   Refinement types in F* trace their lineage to `F7
   <https://www.microsoft.com/en-us/research/project/f7-refinement-types-for-f/>`_,
   a language developed at Microsoft Research c. 2007 -- 2011. `Liquid
   Haskell <https://ucsd-progsys.github.io/liquidhaskell-blog/>`_ is
   another language with refinement types. Those languages provide
   additional background and resources for learning about refinement
   types.

   Boolean refinements are a special case of a more powerful form of
   propositional refinement type in F*. Refinement types, in
   conjunction with dependent function types, are, in principle,
   sufficient to encode many kinds of logics for program
   correctness. However, refinement types are just one among several
   tools in F* for program specification and proof.


Refinement subtyping
....................

We have seen so far how to define a new refinement type, like ``nat`` or
``even``. However, to make use of refinement types we need rules that
allow us to:

1. check that a program term has a given refinement type, e.g., to
   check that ``0`` has type ``nat``. This is sometimes called
   *introducing* a refinement type.

2. make use of a term that has a refinement type, e.g., given ``x :
   even`` we would like to be able to write ``x + 1``, treating ``x`` as an
   ``int`` to add ``1`` to it. This is sometimes called *eliminating*
   a refinement type.

The technical mechanism in F* that supports both these features is
called *refinement subtyping*.

If you're used to a language like Java, C# or some other
object-oriented language, you're familiar with the idea of
subtyping. A type ``t`` is a subtype of ``s`` whenever a program term
of type ``t`` can be safely treated as an ``s``. For example, in Java,
all object types are subtypes of the type ``Object``, the base class
of all objects.

For boolean refinement types, the subtyping rules are as follows:

* The type ``x:t { p }`` is a subtype of ``t``. That is, given ``e :
  (x:t{p})``, it is always safe to *eliminate* the refinement and
  consider ``e`` to also have type ``t``.

* For a term ``e`` of type ``t`` (i.e., ``e : t``), ``t`` is a subtype
  of the boolean refinement type ``x:t { p }`` whenever ``p[e / x]``
  (``p[e/x]`` is notation for the term ``p`` with the variable ``x``
  replaced by ``e``), is provably equal to ``true``. In other words,
  to *introduce* ``e : t`` at the boolean refinement type ``x:t{ p
  }``, it suffices to prove that the term ``p`` with ``e`` substituted
  for bound variable ``x``, evaluates to ``true``.

The elimination rule for refinement types (i.e., the first part above)
is simple---with our intuition of types as sets, the refinement type
``x:t{ p }`` *refines* the set corresponding to ``t`` by the predicate
``p``, i.e., the ``x:t{ p }`` denotes a subset of ``t``, so, of course
``x:t{ p }`` is a subtype of ``t``.

The other direction is a bit more subtle: ``x:t{ p }`` is only a
subtype of ``p``, for those terms ``e`` that validate ``p``. You're
probably also wondering about how to prove that ``p[e/x]`` evaluates
to ``true``---we will look at this in detail later. But, the short
version is that F*, by default, uses an SMT solver to prove such fact,
though you can also use tactics and other techniques to do so.

An example
..........

Given ``x:even``, consider proving ``x + 1 : odd``; it takes a few
steps:

1. The operator ``+`` is defined in F*'s library. It expects both its
   arguments to have type ``int`` and returns an ``int``.

2. To prove that the first argument ``x:even`` is a valid argument for
   ``+``, we use refinement subtyping to eliminate the refinement and
   obtain ``x:int``. The second argument ``1:int`` already has the
   required type. Thus, ``x + 1 : int``.

3. To conclude that ``x + 1 : odd``, we need to introduce a refinement
   type, by proving that the refinement predicate of ``odd`` evaluates
   to true, i.e., ``x + 1 % 2 = 1``. This is provable by SMT, since we
   started with the knowledge that ``x`` is even.

As such, F* applies subtyping repeatedly to introduce and eliminate
refinement types, applying it multiple times even to check a simple
term like ``x + 1 : odd``.


Functions
^^^^^^^^^

We need a way to define functions to start writing interesting
programs. In the core of F*, functions behave like functions in
maths. In other words, they are defined on their entire domain (i.e.,
they are total functions and always return a result) and their only
observable behavior is the result they return (i.e., they don't have
any side effect, like looping forever, or printing a message etc.).

Functions are first-class values in F*, e.g., they can be passed as
arguments to other functions and returned as results. While F*
provides several ways to define functions, the most basic form is the
:math:`\lambda` term, also called a function literal, an anonymous function, or a
simply a *lambda*. The syntax is largely inherited from OCaml, and
this `OCaml tutorial
<https://ocaml.org/docs/tour-of-ocaml#functions>`_
provides more details for those unfamiliar with the language. We'll
assume a basic familiarity with OCaml-like syntax.

Lambda terms
............

The term ``fun (x:int) -> x + 1`` defines a function,
a lambda term, which adds 1 to its integer-typed parameter ``x``. You
can also let F* infer the type of the parameter and write ``fun x ->
x + 1`` instead.

.. _Part1_ch1_named_function:

Named functions
...............

Any term in F\* can be given a name using a ``let`` binding. We'll
want this to define a function once and to call it many times. For
example, all of the following are synonyms and bind the lambda term
``fun x -> x + 1`` to the name ``incr``

.. code-block:: fstar

  let incr = fun (x:int) -> x + 1
  let incr (x:int) = x + 1
  let incr x = x + 1

Functions can take several arguments and the result type of a function
can also be annotated, if desired

.. code-block:: fstar

  let incr (x:int) : int = x + 1
  let more_than_twice (x:int) (y:int) : bool = x > y + y

It's considered good practice to annotate all the parameters and
result type of a named function definition.

.. note::

   In addition to decorating the types of parameters and the results
   of function, F* allows annotating any term ``e`` with its expected
   type ``t`` by writing ``e <: t``. This is called a *type
   ascription*. An ascription instructs F* to check that the
   term ``e`` has the type ``t``. For example, we could have written

.. code-block:: fstar

     let incr = fun (x:int) -> (x + 1 <: int)


Recursive functions
...................

Recursive functions in F* are always named. To define them, one uses
the ``let rec`` syntax, as shown below.

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: factorial
   :end-before: SNIPPET_END: factorial

This syntax defines a function names ``factorial`` with a single
parameter ``n:nat``, returning a ``nat``. The definition of factorial
is allowed to use the ``factorial`` recursively—as we'll see in a
later chapter, ensuring that the recursion is well-founded (i.e., all
recursive calls terminate) is key to F*'s soundness. However, in this
case, the proof of termination is automatic.

.. note::

   Notice the use of `open FStar.Mul` in the example above. This
   brings the module `FStar.Mul` into scope and resolves the symbol
   ``*`` to integer multiplication.

F* also supports mutual recursion. We'll see that later.

.. _Part1_ch1_arrows:

Arrow types
^^^^^^^^^^^

Functions are the main abstraction facility of any functional language
and their types are pervasive in F*. In its most basic form, function
types, or arrows, have the shape::

  x:t0 -> t1

This is the type of a function that

1. receives an argument ``e`` of type ``t0``, and

2. always returns a value of type ``t1[e / x]``, i.e., the type of the
   returned value depends on the argument ``e``.

It's worth emphasizing how this differs from function types in other
languages.

* F*'s arrows are dependent---the type of the result depends on the
  argument. For example, we can write a function that returns a
  ``bool`` when applied to an even number and returns a ``string``
  when applied to an odd number. Or, more commonly, a function
  whose result is one greater than its argument.

* In F*'s core language, all functions are total, i.e., a function
  call always terminates after consuming a finite but unbounded amount
  of resources.

.. note::

   That said, on any given computer, it is possible for a function
   call to fail to return due to resource exhaustion, e.g., running
   out of memory. Later, as we look at :ref:`effects <effects>`, we
   will see that F* also supports writing non-terminating functions.


.. _Part1_ch1_arrow_notations:


Some examples and common notation
.................................

1. Functions are *curried*. Functions that take multiple arguments are
   written as functions that take the first argument and return a
   function that takes the next argument and so on. For instance, the
   type of integer addition is::

     val (+) : x:int -> y:int -> int

2. Not all functions are dependent and the name of the argument can be
   omitted when it is not needed. For example, here's a more concise
   way to write the type of ``(+)``::

     val (+) : int -> int -> int

3. Function types can be mixed with refinement types. For instance,
   here's the type of integer division---the refinement on the divisor
   forbids division-by-zero errors::

     val (/) : int -> (divisor:int { divisor <> 0 }) -> int

4. Dependence between the arguments and the result type can be used to
   state relationships among them. For instance, there are several
   types for the function ``let incr = (fun (x:int) -> x + 1)``::

     val incr : int -> int
     val incr : x:int -> y:int{y > x}
     val incr : x:int -> y:int{y = x + 1}

   The first type ``int -> int`` is its traditional type in languages
   like OCaml.

   The second type ``x:int -> y:int{y > x}`` states that the returned
   value ``y`` is greater than the argument ``x``.

   The third type is the most precise: ``x:int -> y:int{y = x + 1}``
   states that the result ``y`` is exactly the increment of the
   argument ``x``.

5. It's often convenient to add refinements on arguments in a
   dependent function type. For instance::

     val f : x:(x:int{ x >= 1 }) -> y:(y:int{ y > x }) -> z:int{ z > x + y }

   Since this style is so common, and it is inconvenient to have to
   bind two names for the parameters ``x`` and ``y``, F* allows (and
   encourages) you to write::

     val f : x:int{ x >= 1 } -> y:int{ y > x } -> z:int{ z > x + y }

6. To emphasize that functions in F*'s core are total functions (i.e.,
   they always return a result), we sometimes annotate the result type
   with the effect label "``Tot``". This label is optional, but
   especially as we learn about :ref:`effects <effects>`, emphasizing
   that some functions have no effects via the ``Tot`` label is
   useful. For example, one might sometimes write::

     val f : x:int{ x >= 1 } -> y:int{ y > x } -> Tot (z:int{ z > x + y })

   adding a ``Tot`` annotation on the last arrow, to indicate that the
   function has no side effects. One could also write::

     val f : x:int{ x >= 1 } -> Tot (y:int{ y > x } -> Tot (z:int{ z > x + y }))

   adding an annotation on the intermediate arrow, though this is not
   customary.

Exercises
^^^^^^^^^

This first example is just to show you how to run the tool and
interpret its output.

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: sample
   :end-before: SNIPPET_END: sample

Notice that the program begins with a ``module`` declaration. It
contains a single definition named ``incr``. Definitions that appear
at the scope of a module are called "top-level" definitions.

You have several options to try out these examples.

**F\* online**

To get started and for trying small exercises, the easiest way is via
the `online tutorial <http://fstar-lang.org/tutorial>`_. If that's
where you're reading this, you can just use the in-browser editor
alongside which communicates with an F* instance running in the
cloud. Just click `on this link
<../code/exercises/Part1.GettingOffTheGround.fst>`_ to load the
code of an exercise in the editor.

That said, the online mode can be a bit slow, depending on the load at
the server, and the editor is very minimalistic.

For anything more than small exercises, you should have a working
local installation of the F* toolchain, as described next.

**F\* in batch mode**

You can download pre-built F* binaries `from here
<https://github.com/FStarLang/FStar/releases>`_.

Once you have a local installation, to check a program you can run the
``fstar`` at the command line, like so::

  $ fstar Sample.fst

In response ``fstar`` should output::

  Verified module: Sample
  All verification conditions discharged successfully

This means that F* attempted to verify the module named ``Sample``. In
doing so, it generated some "verification conditions", or proof
obligations, necessary to prove that the module is type correct, and
it discharged, or proved, all of them successfully.

**F\* in emacs**

Rather than running ``fstar`` in batch mode from the command line, F*
programmers using the `emacs <https://www.gnu.org/software/emacs/>`_
editor often use `fstar-mode.el
<https://github.com/FStarLang/fstar-mode.el>`_, an editor plugin that
allows interactively checking an F* program. If you plan to use F* in
any serious way, this is strongly recommended.

Many types for ``incr``
.......................

Here are some types for ``incr``, including some types that are valid
and some others that are not.

This type claims that ``incr`` result is
greater than its argument and F* agrees—remember, the ``int`` type is
unbounded, so there's no danger of the addition overflowing.

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: ex1.1
   :end-before: SNIPPET_END: ex1.1

This type claims that ``incr`` always returns a natural number, but it
isn't true, since incrementing a negative number doesn't always
produce a non-negative number.

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: ex1.2
   :end-before: SNIPPET_END: ex1.2

F* produces the following error message::

  Sample.fst(11,26-11,31): (Error 19) Subtyping check failed; expected type
  Prims.nat; got type Prims.int; The SMT solver could not prove the query, try to
  spell your proof in more detail or increase fuel/ifuel (see also prims.fst(626,
  18-626,24))
  Verified module: Sample
  1 error was reported (see above)

**Source location**

The error message points to ``Sample.fst(11,26-11,31)``, a source
range mentioned the file name, a starting position (line, column), and
an ending position (line, column). In this case, it highlights the
``x + 1`` term.

**Severity and error code**

The ``(Error 19)`` mentions a severity (i.e., ``Error``, as opposed
to, say, ``Warning``), and an error code (``19``).

**Error message**

The first part of the message stated what you might expect::

  Subtyping check failed; expected type Prims.nat; got type Prims.int

The rest of the message provides more details, which we'll ignore for
now, until we've had a chance to explain more about how F* interacts
with the SMT solver. However, one part of the error message is worth
pointing out now::

  (see also prims.fst(626,18-626,24))

Error messages sometimes mention an auxiliary source location in a
"see also" parenthetical. This source location can provide some more
information about why F* rejected a program—in this case, it points to
the constraint ``x>=0`` in the definition of ``nat`` in ``prims.fst``,
i.e., this is the particular constraint that F* was not able to prove.

So, let's try again. Here's another type for ``incr``, claiming that
if its argument is a natural number then so is its result. This time
F* is happy.

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: ex1.3
   :end-before: SNIPPET_END: ex1.3

Sometimes, it is convenient to provide a type signature independently
of a definition. Below, the ``val incr4`` provides only the signature
and the subsequent ``let incr4`` provides the definition—F* checks
that the definition is compatible with the signature.

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: ex1.4
   :end-before: SNIPPET_END: ex1.4

Try writing some more types for ``incr``.
(`Load exercise <../code/exercises/Part1.GettingOffTheGround.fst>`_.)

.. container:: toggle

    .. container:: header

       **Some answers**

    .. literalinclude:: ../code/Part1.GettingOffTheGround.fst
       :language: fstar
       :start-after: SNIPPET_START: incr_types
       :end-before: SNIPPET_END: incr_types


Computing the maximum of two integers
.....................................

Provide an implementation of the following signature::

  val max (x:int) (y:int) : int

There are many possible implementations that satisfy this signature,
including trivial ones like::

  let max x y = 0

Provide an implementation of ``max`` coupled with a type that is
precise enough to rule out definitions that do not correctly return
the maximum of ``x`` and ``y``.

.. container:: toggle

    .. container:: header

       **Some answers**

    .. literalinclude:: ../code/Part1.GettingOffTheGround.fst
       :language: fstar
       :start-after: SNIPPET_START: max
       :end-before: SNIPPET_END: max


More types for factorial
........................

Recall the definition of ``factorial`` from earlier.

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: factorial
   :end-before: SNIPPET_END: factorial

Can you write down some more types for factorial?

.. container:: toggle

    .. container:: header

       **Some answers**

    .. literalinclude:: ../code/Part1.GettingOffTheGround.fst
       :language: fstar
       :start-after: SNIPPET_START: factorial_answers
       :end-before: SNIPPET_END: factorial_answers

Fibonacci
.........

Here's a doubly recursive function:

.. literalinclude:: ../code/Part1.GettingOffTheGround.fst
   :language: fstar
   :start-after: SNIPPET_START: fibonacci
   :end-before: SNIPPET_END: fibonacci

What other types can you give to it?

.. container:: toggle

    .. container:: header

       **Some answers**

    .. literalinclude:: ../code/Part1.GettingOffTheGround.fst
       :language: fstar
       :start-after: SNIPPET_START: fibonacci_answers
       :end-before: SNIPPET_END: fibonacci_answers
