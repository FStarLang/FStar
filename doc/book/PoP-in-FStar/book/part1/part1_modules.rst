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

Whatever survives, F* takes the innermost of the survivors — the one brought
into scope by the latest ``open``. So when nothing has been eliminated the
answer is the innermost binding, exactly as it would be without overloading;
what overloading adds is that an inner binding which cannot possibly fit steps
aside and lets an outer one through. A module-qualified name such as
``IntOps.f`` is never overloaded, and a local variable always shadows
everything.

Operators participate on the same terms. An operator is an ordinary name
written in a special way — ``( + )`` is the name ``op_Plus`` — so a ``( + )``
of your own and the ``( + )`` on ``int`` that ``Prims`` defines are simply two
candidates for one name:

.. code-block:: fstar

   module Vec
   type vec = | V of int & int

   let ( + ) (a b : vec) : vec =
     let V (x1, y1) = a in
     let V (x2, y2) = b in
     V (x1 + x2, y1 + y2)

   let vsum = V (1, 2) + V (3, 4)   // Vec.( + )
   let isum : int = 1 + 2           // Prims.( + )

Overload resolution also allows for the conversions F* inserts on your behalf,
since a candidate whose type differs from yours only by one of those does fit. A
``bool`` may stand where a ``prop`` or a ``Type`` is wanted, and a ``prop``
where a ``bool`` is; a ``t`` may stand where an ``FStar.Ghost.erased t`` is
wanted, and the reverse; and any function you mark with the ``coercion``
attribute lets its argument type stand where its result type is wanted:

.. code-block:: fstar

   module Metres
   type metres = | Metres of int

   [@@coercion]
   let metres_to_int (m:metres) : int = Metres?._0 m

.. code-block:: fstar

   module Client
   open IntOps
   open BoolOps
   open Metres

   let d : int = f (Metres 3)   // IntOps.f, and the coercion is inserted

Neither ``f`` takes a ``metres``. But ``IntOps.f`` is the one whose argument a
``metres`` can be converted to, so ``BoolOps.f`` is the candidate that steps
aside, and ``metres_to_int`` is then applied as it would be anywhere else.
Resolution and coercion are decided together in this way: a candidate is set
aside only when no conversion in scope could bridge the difference. Should a
name nevertheless resolve somewhere you did not intend, qualifying it is always
available, as is turning the feature off.

Three modes are selectable, and the default rarely wants changing:

* ``--ext fstar:overload=compat`` is the default described above.
* ``--ext fstar:overload=off`` turns off overload resolution and a name resolves
  to the innermost binding and nothing else.
* ``--ext fstar:overload=strict`` reports an error (number 362) wherever more
  than one candidate survives, instead of quietly taking the innermost. This is
  a diagnostic aid rather than a mode to develop in: plenty of ambiguities are
  harmless, e.g. when two modules re-export the very same definition. Adding
  ``--warn_error +362`` turns those reports into warnings, so a whole
  development can be swept in one go.