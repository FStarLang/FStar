.. _Part4:

Computational Effects
=====================

All the programs we've considered so far have been *pure*, which is to
say that only thing that can be observed about a program by its
context is the value that the program returns---the inner workings of
the program (e.g., whether it multiplies two numbers by repeated
addition or by using a primitive operation for multiplication) cannot
influence the behavior of its context. That is, pure terms can be
reasoned about like pure mathematical functions. [#]_

However, many practical programs exhibit behaviors that are beyond
just their output. For example, they may mutate some global state, or
they may read and write files, or receive or send messages over the
network---such behaviors are often called *side effects*,
*computational effects*, or just *effects*.

In this section, we look at F*'s effect system which allows users to

  * Model the semantics of various kinds of effects, e.g., mutable
    state, input/output, concurrency, etc.

  * Develop reasoning principles that enable building proofs of
    various properties of effectful programs

  * Simplify effectful program construction by encapsulating the
    semantic model and reasoning principles within an abstraction that
    allows users to write programs in F*'s native syntax while behind
    the scenes, for reasoning and execution purposes, programs are
    elaborated into the semantic model

Aside from user-defined effects, F*'s also supports the following
*primitive* effects:

  * **Ghost**: An effect which describes which parts of a program have
    no observable behavior at all, and do not even influence the
    result returned by the program. This allows optimizing a program
    by erasing the parts of a program that are computationally
    irrelevant.

  * **Divergence**: An effect that encapsulates computations which may
    run forever. Potentially divergent computations cannot be used as
    proofs (see :ref:`termination<Part1_termination>`) and the effect
    system ensures that this is so.

  * **Partiality**: Partial functions are only defined over a subset
    of their domain. F* provides primitive support for partial
    functions as an effect. Although currently primitive, in the
    future, we hope to remove the special status of partial functions
    and make partial functions a user-defined notion too.

  
.. [#] Although pure F* programs are mathematical functions
       in the ideal sense, when executing these programs on a
       computer, they do exhibit various side effects, including
       consuming resources like time, power, and memory. Although
       these side effects are clearly observable to an external
       observer of a running F* program, the resourse-usage side
       effects of one component of a pure F* program are not visible
       to another component of the same program.

.. toctree::
   :maxdepth: 1
   :caption: Contents:

   part4_background
   part4_computation_types_and_tot
   part4_ghost
   part4_div
   part4_pure

