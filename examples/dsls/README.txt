This directory contains some domain-specific languages and their custom typecheckers.
The typecheckers implement custom typing rules and elaborate the programs and typing
derivations in the DSL to F* syntax and an F* typing judgment, establishing well-typedness
of the elaborated programs in the F* type system.

It is enabled by a (partial) specification of the F* type system defined in
ulib/experimental/FStar.Reflection.Typing.fsti. So far it only covers parts of
Tot fragments of F*.

The elaborated terms can be added as top-level F* definitions using a new
`splice_t` meta-F* primitive. These definitions are not re-typechecked, since
they are accompanied with a typing proof.