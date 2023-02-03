.. _Part1_execution:

Executing programs
==================

We've been through several chapters already, having learned many core
concepts of F*, but we have yet to see how to compile and execute a
program, since our focus so far has been on F*'s logic and how to
prove properties about programs.

F* offers several choices for executing a program, which we cover
briefly here, using `Quicksort <../code/Part1.Quicksort.Generic.fst>`_
as a running example.


Interpreting F* programs
^^^^^^^^^^^^^^^^^^^^^^^^

As mentioned in the :ref:`capsule summary
<Part1_symbolic_computation>`, F* includes an engine (called the
*normalizer*) that can symbolically reduce F* computations. We'll see
many more uses of F*'s normalizer as we go, but one basic usage of it
is to use it to interpret programs.

Invoking the interpreter is easy using :ref:`fstar-mode.el
<Part1_editors>` in emacs. In emacs, go to the F* menu, then to
*Interactive queries*, then choose *Evaluate an expression* (or type
C-c C-s C-e): this prompts you to enter an expression that you want to
evaluate: type ``sort ( <= ) [4;3;2;1]`` and then press "Enter". You
should see the following output: ``sort ( <= ) [4;3;2;1]``
:math:`\downarrow\beta\delta\iota\zeta` ``[1; 2; 3; 4] <: Prims.Tot
(list int)``, saying that the input term reduced to ``[1; 2; 3; 4]``
of type ``Tot (list int)``.

The :math:`\downarrow\beta\delta\iota\zeta` may seem a bit arcane, but
it describes the reduction strategy that F* used to interpret the term:

  * :math:`\beta` means that functions were applied
  * :math:`\delta` means that definitions were unfolded
  * :math:`\iota` means that patterns were matched
  * :math:`\zeta` means that recursive functions were unrolled

We'll revisit what these reduction steps mean in a later chapter,
including how to customize it for your needs.

Compiling to OCaml
^^^^^^^^^^^^^^^^^^

The main way to execute F* programs is by compiling, or *extracting*,
them to OCaml and then using OCaml's build system and runtime to
produce an executable and run it.

.. note:: 

   The method that we show here works for simple projects with just a few
   files. For larger projects, F* offers a dependence analysis that can
   produce dependences for use in a Makefile. F* also offers separate
   compilation which allows a project to be checked one file at a time,
   and for the results to be cached and reused. For documentation and
   examples of how to use these features and structure the build for
   larger projects see these resources:

     * `Dealing with dependences <https://github.com/FStarLang/FStar/wiki/Dealing-with-F%E2%98%85-dependencies>`_
     * `Caching verified modules <https://github.com/FStarLang/FStar/wiki/Caching-verified-modules>`_
     * `A multifile project <https://github.com/FStarLang/FStar/tree/master/examples/hello/multifile>`_
  

Producing an OCaml library
..........................

To extract OCaml code from a F* program use the command-line options,
as shown below:

.. code-block::

   fstar --codegen OCaml --extract Part1.Quicksort --odir out Part1.Quicksort.Generic.fst

* The ``--codegen`` option tells F* to produce OCaml code

* The ``--extract`` option tells F* to only extract all modules in the given namespace, i.e., in this case, all modules in ``Part1.Quicksort``

* The ``--odir`` option tells F* to put all the generated files into the specified directory; in this case ``out``
  
* The last argument is the source file to be checked and extracted

The resulting OCaml code is in the file
``Part1_Quicksort_Generic.ml``, where the F* ``dot``-separated name is
transformed to OCaml's naming convention for modules. The generated code is `here <../code/out/Part1_Quicksort_Generic.ml>`_

Some points to note about the extracted code:

* F* extracts only those definitions that correspond to executable
  code. Lemmas and other proof-only aspects are erased. We'll learn
  more about erasure in a later chapter.

* The F* types are translated to OCaml types. Since F* types are more
  precise than OCaml types, this translation process necessarily
  involves a loss in precision. For example, the type of total orders
  in ``Part1.Quicksort.Generic.fst`` is:

  .. code-block:: fstar

     let total_order_t (a:Type) = f:(a -> a -> bool) { total_order f }

  Whereas in OCaml it becomes

  .. code-block:: 

     type 'a total_order_t = 'a -> 'a -> Prims.bool
  

  This means that you need to be careful when calling your extracted
  F* program from unverified OCaml code, since the OCaml compiler will
  not complain if you pass in some function that is not a total order
  where the F* code expects a total order.

Compiling an OCaml library
..........................

Our extracted code provides several top-level functions (e.g.,
``sort``) but not ``main``. So, we can only compile it as a library.

For simple uses, one can compile the generated code into a OCaml
native code library (a cmxa file) with ``ocamlbuild``, as shown below

.. code-block::

   OCAMLPATH=$FSTAR_HOME/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Part1_Quicksort_Generic.cmxa

Some points to note:

  * You need to specify the variable ``OCAMLPATH`` which OCaml uses to
    find required libraries. For F* projects, the ``OCAMLPATH`` should
    include the ``bin`` directory of the FStar release bundle.

  * The ``-use-ocamlfind`` option enables a utility to find OCaml libraries.

  * Extracted F* programs rely on two libraries: ``batteries`` and
    ``fstar.lib``, which is what the ``-pkg`` options say.

  * Finally, ``Part1_Quicksort_Generic.cmxa`` references the name of
    the corresponding ``.ml`` file, but with the ``.cmxa`` extension
    to indicate that we want to compile it as a library.

Your can use the resulting .cmxa file in your other OCaml projects.


Adding a 'main'
...............

We have focused so far on programming and proving *total*
functions. Total functions have no side effects, e.g., they cannot
read or write state, they cannot print output etc. This makes total
functions suitable for use in libraries, but to write a top-level
driver program that can print some output (i.e., a ``main``), we need
to write functions that actually have some effects.

We'll learn a lot more about F*'s support for effectful program in a
later section, but for now we'll just provide a glimpse of it by
showing (below) a ```main`` program that calls into our Quicksort
library.

.. literalinclude:: ../code/Part1.Quicksort.Main.fst
       :language: fstar

There are few things to note here:

  * This time, rather than calling ``Q.sort`` from unverified OCaml
    code, we are calling it from F*, which requires us to prove all
    its preconditions, e.g., that the comparison function ``( <= )``
    that we are passing in really is a total order---F* does that
    automatically.
    
  * ``FStar.IO.print_string`` is a library function that prints a
    string to ``stdout``. Its type is ``string -> ML unit``, a type
    that we'll look at in detail when we learn more about effects.

  * The end of the file contains ``let _ = main ()``, a top-level term
    that has a side-effect (printing to ``stdout``) when executed. In
    a scenario where we have multiple modules, the runtime behavior of
    a program with such top-level side-effects depends on the order in
    which modules are loaded. When F* detects this, it raises the
    warning ``272``. In this case, we intend for this program to have
    a top-level effect, so we suppress the warning using the
    ``--warn_error -272`` option.

To compile this code to OCaml, along with its dependence on
``Part1.Quicksort.Generic``, one can invoke:

.. code-block::

   fstar --codegen OCaml --extract Part1.Quicksort --odir out Part1.Quicksort.Main.fst

This time, F* extracts both ``Part1.Quicksort.Generic.fst`` (as
before) and ``Part1.Quicksort.Main.fst`` to OCaml, producing
`Part1_Quicksort_Main.ml <../code/out/Part1_Quicksort_Main.ml>`_ to
OCaml.

You can compile this code in OCaml to a native executable by doing:

.. code-block::

   OCAMLPATH=$FSTAR_HOME/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Part1_Quicksort_Main.native

And, finally, you can execute Part1_Quicksort_Main.native to see the
following output:

.. code-block::

   $ ./Part1_Quicksort_Main.native
   Original list = [42; 17; 256; 94]
   Sorted list = [17; 42; 94; 256]

Compiling to other languages
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

F* also supports compiling programs to F# and, for a subset of the
language, supports compilation to C.

For the F# extraction, use the ``--codegen FSharp`` option. However,
it is more typical to structure an F* project for use with F# using
Visual Studio project and solution files. Here are some examples:

  * `A simple example <https://github.com/FStarLang/FStar/tree/master/examples/hello>`_

  * `A more advanced example mixing F* and F# code <https://github.com/FStarLang/FStar/tree/master/ulib/fs>`_

For extraction to C, please see the `tutorial on Low* <https://fstarlang.github.io/lowstar/html/>`_.

