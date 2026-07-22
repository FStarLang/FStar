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
