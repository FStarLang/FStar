.. _Part1_modules:

More on modules
===============

The structure of an individual module has :ref:`already been explained
<Part1_basic_structure>`. E.g. in a file named ``SomeModule.fst``, we might
put:

.. code-block:: fstar

   module SomeModule

   let some_function = ...

Module-qualified names
----------------------

Signatures and definitions from other modules can be referred to by qualifying
them with the module name followed by a dot. E.g. in another file
``SomeOtherModule.fst``:

.. code-block:: fstar

   module SomeOtherModule

   let some_function_again = SomeModule.some_function

Module abbreviations
--------------------

To avoid repetition of long module names, it's possible to define module
abbreviations, e.g.:

.. code-block:: fstar

   module M = SomeModule

``SomeModule.some_function`` can then be used as simply ``M.some_function``.

open
----

It's also possible to bring another module's entire contents into the current
scope using ``open``:

.. code-block:: fstar

   open SomeModule

   let some_function_again = some_function

Overloading by type
-------------------

When several modules in scope define the same name, F* uses the types at the
use site to decide which one is meant. For instance, given two modules that both
define ``f``:

.. code-block:: fstar

   module IntOps
   let f (x:int) : int = x + 1

.. code-block:: fstar

   module BoolOps
   let f (x:bool) : bool = not x

both names are usable unqualified, and each occurrence resolves to the one whose
type fits:

.. code-block:: fstar

   module Client
   open IntOps
   open BoolOps

   let a : int  = f 0      // IntOps.f
   let b : bool = f true   // BoolOps.f
   let c : int -> int = f  // IntOps.f, from the expected type alone

Resolution looks at the number of explicit arguments, then at the type of each
explicit argument in turn, then at the expected type. It only ever *eliminates*
a candidate whose type definitely does not fit, and it compares types only by
their head symbol: ``list int`` and ``list bool`` are not distinguishable this
way, and neither is a candidate whose argument type is still unknown at that
point.

If more than one candidate survives, F* silently takes the innermost one — the
one that the last ``open`` brought into scope, which is the one it would have
picked before overloading existed. Overloading therefore never changes the
meaning of a program that already type-checks; it only lets programs that used
to be rejected, or that had to be written with a module qualifier, work as
written. A module-qualified name such as ``IntOps.f`` is never overloaded, and a
local variable always shadows everything.

Two options control this, both rarely needed:

* ``--ext fstar:overload=off`` restores the old behaviour, where a name resolves
  to the innermost binding and nothing else.
* ``--ext fstar:overload=strict`` reports an error (number 362) wherever more
  than one candidate survives, instead of quietly taking the innermost. This is
  a diagnostic aid rather than a mode to develop in: plenty of ambiguities are
  harmless, e.g. when two modules re-export the very same definition. Adding
  ``--warn_error +362`` turns those reports into warnings, so a whole
  development can be swept in one go.
