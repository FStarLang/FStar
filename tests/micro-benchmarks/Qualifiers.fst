module Qualifiers

(* 'new' and 'inline_for_extraction' are compatible.
They may both appear in an interface, in order to declare
the type as new and also make it inline with --cmi. *)
inline_for_extraction noextract
new
val foo : Type0

type foo = | Foo
