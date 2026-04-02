.. _Pulse_Extraction:

Extraction
===========

Pulse programs can be extracted to OCaml, C, and Rust. We illustrate the extraction capabilities
with the help of the `Boyer-Moore majority vote algorithm <https://apps.dtic.mil/sti/pdfs/ADA131702.pdf>`_
implemented in Pulse.

Boyer-Moore majority vote algorithm
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The algorithm finds majority vote in an array of votes in linear time
(2n comparisons, where n is the length of the array) and constant extra memory.

We implement the algorithm in Pulse with the following specification:

.. literalinclude:: ../code/pulse/PulseTutorial.Algorithms.fst
    :language: pulse
    :start-after: //majorityspec$
    :end-before: //majorityspecend$

The precondition ``SZ.fits (2 * SZ.v len)`` ensures safe arithmetic when counting
for majority.

The algorithm consists of two phases. The first phase, called the pairing phase,
pairs off disagreeing votes (cancels them) until the remaining votes are all same.
The main idea of the algorithm is to do this pairing with n comparisons. After the
pairing phase, the remaining vote must be the majority, *if the majority exists*.
The second phase, called the counting phase, checks if the remaining vote is indeed
in majority with n more comparisons.

For the first phase, the algorithm maintains three auxiliary variables, ``i`` for the
loop counter, ``cand`` the current majority candidate, and a count ``k``. It visits the
votes in a loop, where for the ``i-th``
element of the array, if ``k = 0``, the algorithm assigns the ``i-th`` vote as the new
majority candidate and assigns ``k = 1``. Otherwise, if the ``i-th`` vote is same as
``cand``, it increments ``k`` by one, otherwise it decrements ``k`` by one.

The second phase then is another while loop that counts the number of votes
for the majority candidate from the first phase.

.. literalinclude:: ../code/pulse/PulseTutorial.Algorithms.fst
    :language: pulse
    :start-after: //majorityphase1$
    :end-before: //majorityphase1end$

The loop invariant for the first phase specifies majority constraints *within* the
prefix of the array that the loop has visited so far. The second phase loop invariant
is a simple counting invariant.

Pulse automatically proves the program, with an hint for the behavior of the ``count``
function as we increment the loop counter, the following ``count_until_next`` lemma
captures the behavior, and we invoke the lemma in both the while loops:

.. literalinclude:: ../code/pulse/PulseTutorial.Algorithms.fst
    :language: pulse
    :start-after: //countlemma$
    :end-before: //countlemmaend$

Rust extraction
^^^^^^^^^^^^^^^^

Pulse toolchain is accompanied with a tool to extract Pulse programs to Rust.
The extraction pipeline maps the Pulse syntactic constructs such as ``let mut``,
``while``, ``if-then-else``, etc. to corresponding Rust constructs. Further,
Pulse libraries are mapped to their Rust counterparts, e.g. ``Pulse.Lib.Vec`` to
``std::vec``, ``Pulse.Lib.Array`` to Rust slices etc.

To extract a Pulse file to Rust, we first invoke the F* extraction pipeline with
the command line option ``--codegen Extension``. This emits a ``.ast`` file containing
an internal AST representation of the file. We then invoke the Rust extraction tool
that takes as input the ``.ast`` files and outputs the extracted Rust code (by-default
the output is written to ``stdout``, if an ``-o <file>`` option is provided to the tool,
the output is written to ``file``). For example, the first command produces the ``.ast``
file from ``PulseTutorial.Algorithms.fst`` (which contains the Boyer-Moore algorithm implementation),
and then the second command extracts the Rust code to ``voting.rs``. (These commands are run in the
``pulse`` root directory, change the location of main.exe according to your setup.)

.. code-block:: shell

  $ fstar.exe --include out/lib/pulse/
    --include share/pulse/examples/by-example/ --include share/pulse/examples/_cache/
    --cmi --load_cmxs pulse  --odir . PulseTutorial.Algorithms.fst
    --codegen Extension
  
  $ ./pulse2rust/main.exe PulseTutorial_Algorithms.ast -o voting.rs

The output Rust code is as shown below:

.. literalinclude:: ../code/pulse/voting.rs
    :language: pulse
    :start-after: //majorityrust$
    :end-before: //majorityrustend$

We can test it by adding the following in ``voting.rs`` and running the tests
(using ``cargo test``, it requires a ``Cargo.toml`` file, we provide an example file
in the repo that can be used):

.. literalinclude:: ../code/pulse/voting.rs
    :language: pulse
    :start-after: //majorityrusttest$
    :end-before: //majorityrusttestend$

A few notes about the extracted Rust code:

- The Pulse function and the Rust function are generic in the type of the votes. In Rust,
  the extracted code required the type argument to implement the ``Clone``, ``Copy``, and
  ``PartialEq`` traits. Currently we hardcode these traits. We plan to specify these traits
  in Pulse through attribute mechanism

- The ghost arguments ``p`` and ``s`` appear in the Rust code as ``unit`` arguments, we plan
  to make it so that these arguments are completely erased.

- Whereas ``majority`` needs only read permission for the ``votes`` array in the Pulse
  signature, the extracted Rust code specifies the argument as ``&mut``. The Rust extraction
  pipeline currently passes all the references as ``mut``, we plan to make
  it more precise by taking into account the permissions from the Pulse signature.

C extraction
^^^^^^^^^^^^^

Pulse programs can also be extracted to C. The extraction pipeline is based on the 
`Karamel <https://github.com/FStarLang/karamel>`_ tool. The process to extract Pulse
programs to C is similar to that of extracting Low* to C, described in
`this tutorial <https://fstarlang.github.io/lowstar/html/>`_. In summary, we first generate
``.krml`` files from using the F* extraction command line option ``--codegen krml``, and then
run the Karamel tool on those files.

One catch with extracting our Boyer-Moore implementation to C is that due to the lack
of support of polymorphism in C, Karamel monomorphizes polymorphic functions based on
their uses. So, we write a monomorphic version of the ``majority`` function for ``u32``,
that internally calls the polymorphic ``majority`` function:

.. literalinclude:: ../code/pulse/PulseTutorial.Algorithms.fst
    :language: pulse
    :start-after: //majoritymono$
    :end-before: //majoritymonoend$

Then we extract it to C as follows (the commands are run in the ``pulse`` root directory as before):

.. code-block:: shell

  $ fstar.exe --include out/lib/pulse/
    --include share/pulse/examples/by-example/ --include share/pulse/examples/_cache/
    --cmi --load_cmxs pulse  --odir . PulseTutorial.Algorithms.fst
    --extract 'FStar.Pervasives.Native PulseTutorial.Algorithms' --codegen krml

  $ ../karamel/krml -skip-compilation out.krml

This produces ``PulseTutorial_Algorithms.h`` and ``PulseTutorial_Algorithms.c`` files, with the following
implementation of ``majority``:

.. literalinclude:: ../code/pulse/PulseTutorial_Algorithms.c
    :language: C
    :start-after: //majorityc$
    :end-before: //majoritycend$

We can now test it with a client like:

.. literalinclude:: ../code/pulse/PulseTutorial_Algorithms_Client.c
    :language: C


.. code-block:: shell

  $ gcc PulseTutorial_Algorithms.c PulseTutorial_Algorithms_Client.c -I ../karamel/include/
    -I ../karamel/krmllib/c -I ../karamel/krmllib/dist/minimal/
  
  $ ./a.out
  Majority: 1

  $

OCaml extraction
^^^^^^^^^^^^^^^^^

As with all F* programs, Pulse programs can be extracted to OCaml. One caveat
with using the OCaml backend for Pulse programs is that the explicit memory
management from Pulse programs does not carry over to OCaml. For example, the
extracted OCaml programs rely on the OCaml garbage collector for reclaiming unused
heap memory, ``let mut`` variables are allocated on the heap, etc.

For the Boyer-Moore example, we can extract the program to OCaml as follows:

.. code-block:: shell

  $ fstar.exe --include out/lib/pulse/
    --include share/pulse/examples/by-example/ --include share/pulse/examples/_cache/
    --cmi --load_cmxs pulse  --odir . PulseTutorial.Algorithms.fst
    --codegen OCaml

and the extracted ``majority`` function looks like:

.. literalinclude:: ../code/pulse/PulseTutorial_Algorithms.ml
    :language: C
    :start-after: //majorityocaml$
    :end-before: //majorityocamlend$


.. Rust extraction
.. ^^^^^^^^^^^^^^^^

.. .. note::
..   The Rust extraction pipeline is under heavy development.

.. We illustrate Rust extraction with the
.. `Boyer-Moore majority vote algorithm <https://apps.dtic.mil/sti/pdfs/ADA131702.pdf>`_ implemented
.. in Pulse. The algorithm finds majority vote in an array of votes in linear time
.. (2n comparisons, where n is the length of the array) and constant extra memory.

.. The algorithm consists of two phases. The first phase, called the pairing phase,
.. pairs off disagreeing votes (cancels them) until the remaining votes are all same.
.. The main idea of the algorithm is to do this pairing with n comparisons. After the
.. pairing phase, the remaining vote must be the majority, *if the majority exists*.
.. The second phase, called the counting phase, checks if the remaining vote is indeed
.. in majority with n more comparisons.

.. We implement the algorithm in Pulse with the following specification:

.. .. literalinclude:: ../code/pulse/PulseTutorial.Algorithms.fst
..     :language: pulse
..     :start-after: //majorityspec$
..     :end-before: //majorityspecend$

.. The precondition ``SZ.fits (2 * SZ.v len)`` ensures safe arithmetic in the counting
.. phase of the algorithm. The implementation of the function contains two while loops
.. for the two phases.

.. For the first phase, the algorithm maintains three auxiliary variables, ``i`` for the
.. loop counter, ``cand`` the current majority candidate, and a count ``k``. For the ``i``-th
.. element of the array, if ``k = 0``, the algorithm assigns the ``i``-th vote as the new
.. majority candidate and assigns ``k = ``. Otherwise, if the ``i``-th vote is same as
.. ``cand``, it increments ``k`` by one, otherwise it decrements ``k`` by one.


.. .. literalinclude:: ../code/pulse/PulseTutorial.Algorithms.fst
..     :language: pulse
..     :start-after: //majorityphase1$
..     :end-before: //majorityphase1end$

.. The loop invariant specifies majority constraints *within* the prefix of the array
.. that the loop has visited so far. The second phase after this is a simple counting loop.
.. We refer the reader to the corresponding Pulse file for more details.

.. To extract ``majority`` to Rust, we first invoke F* extraction pipeline with option
.. ``--codegen Extension``. This emits a ``.ast`` file containing an internal AST
.. representation of the file. Pulse framework is accompanied with a rust extration tool
.. that takes as input the ``.ast`` files and outputs the extracted Rust code (by-default
.. the output is written to ``stdout``, if an ``-o <file>`` option is provided to the tool,
.. the output is written to ``file``). The output of the tool on this example is as shown
.. below:

.. .. literalinclude:: ../code/pulse/voting.rs
..     :language: pulse
..     :start-after: //majorityrust$
..     :end-before: //majorityrustend$

.. We can output this code in a file, and then test it as follows:

.. .. literalinclude:: ../code/pulse/voting.rs
..     :language: pulse
..     :start-after: //majorityrusttest$
..     :end-before: //majorityrusttestend$

.. A few notes about the extracted Rust code:

.. - The Pulse function and the Rust function are generic in the type of the votes. In Rust,
..   the extracted code required the type argument to implement the ``Clone``, ``Copy``, and
..   ``PartialEq`` traits. Currently we hardcode these traits. We plan to specify these traits
..   in Pulse through attribute mechanism

.. - The ghost arguments ``p`` and ``s`` appear in the Rust code as ``unit`` arguments, we plan
..   to make it so that these arguments are completely erased.

.. - Whereas ``majority`` needs only read permission for the ``votes`` array in the Pulse
..   signature, the extracted Rust code specifies the argument as ``&mut``. The Rust extraction
..   pipeline currently passes all the references as ``mut``, we plan to make
..   it more precise by taking into account the permissions from the Pulse signature.


.. .. Mutable Arrays
.. .. ===============

.. .. In this chapter, we will learn about mutable arrays in Pulse. An array
.. .. is a contiguous collection of values of the same type. Similar to ``ref``,
.. .. arrays in Pulse can be allocated in the stack frame of the current function
.. .. or in the heap---while the stack allocated arrays are reclaimed automatically
.. .. (e.g., when the function returns), heap allocated arrays are explicitly managed
.. .. by the programmer.

.. .. Pulse provides two array types: ``Pulse.Lib.Array.array t`` as the basic array type
.. .. and ``Pulse.Lib.Vec.vec t`` for heap allocated arrays. To provide code reuse, functions
.. .. that may operate over both stack and heap allocated arrays can be written using
.. .. ``Pulse.Lib.Array.array t``---the ``Pulse.Lib.Vec`` library provides back-and-forth coercions
.. .. between ``vec t`` and ``array t``.

.. .. ``array t``
.. .. ^^^^^^^^^^^^

.. .. We illustrate the basics of ``array t`` with the help of the following example
.. .. that reads an array:

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: ```pulse //readi$
.. ..    :end-before: ```

.. .. The library provides a points-to predicate ``pts_to arr #p s`` with
.. .. the interpretation that in the current memory, the contents of ``arr``
.. .. are same as the (functional) sequence ``s:FStar.Seq.seq t``. Like the
.. .. ``pts_to`` predicate on reference, it is also indexed by an implicit
.. .. fractional permission ``p``, which distinguished shared, read-only
.. .. access from exclusive read/write access.

.. .. In the arguments of ``read_i``, the argument ```s`` is erased, since
.. .. it is for specification only.

.. .. Arrays can be read and written-to using indexes of type
.. .. ``FStar.SizeT.t``, a model of C ``size_t`` [#]_ in F*, provided that
.. .. the index is within the array bounds---the refinement ``SZ.v i <
.. .. Seq.length s`` enforces that the index is in bounds, where ``module SZ
.. .. = FStar.SizeT``. The function returns the ``i``-th element of the
.. .. array, the asserted by the postcondition slprop ``pure (x == Seq.index
.. .. s (SZ.v i))``. The body of the function uses the array read operator
.. .. ``arr.(i)``.

.. .. As another example, let's write to the ``i``-th element of an array:

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: ```pulse //writei$
.. ..    :end-before: ```

.. .. The function uses the array write operator ``arr(i) <- x`` and the postcondition
.. .. asserts that in the state when the function returns, the contents of the array
.. .. are same as the sequence ``s`` updated at the index ``i``.

.. .. While any permission suffices for reading, writing requires
.. .. ``1.0R``.  For example, implementing ``write_i`` without
.. .. ``1.0R`` is rejected, as shown below.

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //writeipbegin$
.. ..    :end-before: //writeipend$

.. .. The library contains ``share`` and ``gather`` functions, similar to
.. .. those for references, to divide and combine permissions on arrays.

.. .. We now look at a couple of examples that use arrays with conditionals,
.. .. loops, existentials, and invariants, using many of the Pulse
.. .. constructs we have seen so far.

.. .. .. [#] ``size_t`` in C is an unsigned integer type that is at least
.. ..        ``16`` bits wide. The upper bound of ``size_t`` is platform
.. ..        dependent. ``FStar.SizeT.size_t`` models this type and is
.. ..        extracted to the primitive ``size_t`` type in C, similar to the
.. ..        other :ref:`bounded integer types <Machine_integers>` discussed
.. ..        previously.
       
.. .. Compare
.. .. ........

.. .. Let's implement a function that compares two arrays for equality:

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //comparesigbegin$
.. ..    :end-before: //comparesigend$

.. .. The function takes two arrays ``a1`` and ``a2`` as input, and returns a boolean.
.. .. The postcondition ``pure (res <==> Seq.equal 's1 's2)``
.. .. specifies that the boolean is true if and only if the sequence representations of the
.. .. two arrays are equal. Since the function only reads the arrays, it is parametric in the
.. .. permissions ``p1`` and ``p2`` on the two arrays. Note that the type parameter ``t`` has
.. .. type :ref:`eqtype<Part1_equality>`, requiring that values of type ``t`` support
.. .. decidable equality.

.. .. One way to implement ``compare`` is to use a ``while`` loop, reading the two arrays
.. .. using a mutable counter and checking that the corresponding elements are equal.

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //compareimplbegin$
.. ..    :end-before: //compareimplend$

.. .. The loop invariant states that (a) the arrays are pointwise equal up to the current value
.. .. of the counter, and (b) the boolean ``b`` is true if and only if the current value
.. .. of the counter is less than the length of the arrays and the arrays are equal at that index.
.. .. While (a) helps proving the final postcondition of ``compare``, (b) is required to maintain the
.. .. invariant after the counter is incremented in the loop body.

.. .. Copy
.. .. .....

.. .. As our next example, let's implement a ``copy`` function that copies the contents
.. .. of the array ``a2`` to ``a1``.

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //copy$
.. ..    :end-before: ```

.. .. The loop invariant existentially abstracts over the contents of ``a1``, and maintains
.. .. that upto the current loop counter, the contents of the two arrays are equal. Rest of
.. .. the code is straightforward, the loop conditional checks that the loop counter is less
.. .. than the array lengths and the loop body copies one element at a time.

.. .. The reader will notice that the postcondition of ``copy`` is a little convoluted.
.. .. A better signature would be the following, where we directly state that the
.. .. contents of ``a1`` are same as ``'s2``:

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //copy2sigbegin$
.. ..    :end-before: //copy2sigend$

.. .. We can implement this signature, but it requires one step of rewriting at the end
.. .. after the ``while`` loop to get the postcondition in this exact shape:

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //copy2rewriting$
.. ..    :end-before: //copy2rewritingend$

.. .. We could also rewrite the predicates explicitly, as we saw in a
.. .. :ref:`previous chapter <Pulse_rewriting>`.


.. .. Stack allocated arrays
.. .. ^^^^^^^^^^^^^^^^^^^^^^^

.. .. Stack arrays can be allocated using the expression ``[| v; n |]``. It
.. .. allocates an array of size ``n``, with all the array elements
.. .. initialized to ``v``. The size ``n`` must be compile-time constant.
.. .. It provides the postcondition that the newly create array points to a
.. .. length ``n`` sequence of ``v``. The following example allocates two
.. .. arrays on the stack and compares them using the ``compare`` function
.. .. above.

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: ```pulse //compare_stack_arrays$
.. ..    :end-before: ```

.. .. As with the stack references, stack arrays don't need to be deallocated or
.. .. dropped, they are reclaimed automatically when the function returns. As a result,
.. .. returning them from the function is not allowed:

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //ret_stack_array$
.. ..    :end-before: //ret_stack_array_end$

.. .. Heap allocated arrays
.. .. ^^^^^^^^^^^^^^^^^^^^^^

.. .. The library ``Pulse.Lib.Vec`` provides the type ``vec t``, for
.. .. heap-allocated arrays: ``vec`` is to ``array`` as ``box`` is to
.. .. ``ref``.

.. .. Similar to ``array``, ``vec`` is accompanied with a ``pts_to``
.. .. assertion with support for fractional permissions, ``share`` and
.. .. ``gather`` for dividing and combining permissions, and read and write
.. .. functions. However, unlike ``array``, the ``Vec`` library provides
.. .. allocation and free functions.

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: //heaparray$
.. ..    :end-before: //heaparrayend$

.. .. As with the heap references, heap allocated arrays can be coerced to ``array`` using the coercion
.. .. ``vec_to_array``. To use the coercion, it is often required to convert ``Vec.pts_to`` to ``Array.pts_to``
.. .. back-and-forth; the library provides ``to_array_pts_to`` and ``to_vec_pts_to`` lemmas for this purpose.

.. .. The following example illustrates the pattern. It copies the contents of a stack array into a heap array,
.. .. using the ``copy2`` function we wrote above.

.. .. .. literalinclude:: ../code/pulse/PulseTutorial.Array.fst
.. ..    :language: pulse
.. ..    :start-after: ```pulse //copyuse$
.. ..    :end-before: ```

.. .. Note how the assertion for ``v`` transforms from ``V.pts_to`` to ``pts_to`` (the points-to assertion
.. .. for arrays) and back. It means that array algorithms and routines can be implemented with the
.. .. ``array t`` type, and then can be reused for both stack- and heap-allocated arrays.

.. .. Finally, though the name ``vec a`` evokes the Rust ``std::Vec`` library, we don't yet support automatic
.. .. resizing.
