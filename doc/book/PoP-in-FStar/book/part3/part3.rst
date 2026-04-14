.. _Part3:

##########################################
Modularity With Interfaces and Typeclasses
##########################################

In this section, we'll learn about two abstraction techniques used to
structure larger F* developments: *interfaces* and *typeclasses*.

**Interfaces**: An F* module ``M`` (in a file ``M.fst``) can be paired
with an interface (in a file ``M.fsti``). A module's interface is a
subset of the module's declarations and definitions. Another module
``Client`` that uses ``M`` can only make use of the part of ``M``
revealed in its interface---the rest of ``M`` is invisible to
``Client``. As such, interfaces provide an abstraction mechanism,
enabling the development of ``Client`` to be independent of any
interface-respecting implementation of ``M``.

Unlike module systems in other ML-like languages (which provide more
advanced features like signatures, functors, and first-class modules),
F*'s module system is relatively simple.

* A module can have at most one interface.

* An interface can have at most one implementation.

* A module lacking an interface reveals all its details to clients.

* An interface lacking an implementation can be seen as an assumption or an axiom.

**Typeclasses**: Typeclasses cater to more complex abstraction
patterns, e.g., where an interface may have several
implementations. Many other languages, ranging from Haskell to Rust,
support typeclasses that are similar in spirit to what F* also
provides.

Typeclasses in F* are actually defined mostly by a "user-space"
metaprogam (relying on general support for metaprogramming in `Meta-F*
<http://fstar-lang.org/papers/metafstar/>`_), making them very
flexible (e.g., multi-parameter classes, overlapping instances,
etc. are easily supported).

That said, typeclasses are a relatively recent addition to the
language and most of F*'s standard library does not yet use
typeclasses. As such, they are somewhat less mature than interfaces
and some features require encodings (e.g., typeclass inheritance),
rather than being supported with built-in syntax.

Thanks especially to Guido Martinez, who designed and implemented
most of F*'s typeclass system.

.. toctree::
   :maxdepth: 1
   :caption: Contents:

   part3_interfaces
   part3_typeclasses
   part3_alacarte
