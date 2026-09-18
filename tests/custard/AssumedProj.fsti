module AssumedProj

(* Section 8.5: a type's projectors and discriminators are *declaration-only*,
   so an extractor that waits for a [Sig_let] never sees one.  A record update
   compiles to a projector application, so leaving these as externals produced
   an unresolved symbol at link time -- which is what this test pins, via the
   NOGREP on [u___proj].

   This used to need [@@no_auto_projectors] to arrange, and Pulse's [st_term]
   carried the attribute for that reason.  F* now declares projectors this way
   unconditionally and the attribute is a deprecated no-op, so the test simply
   drops it: the shape under test is now the default rather than something
   that has to be asked for. *)
noeq
type tree (a:Type0) =
  | Leaf
  | Node of node a
and node (a:Type0) = { left : tree a; here : a; right : tree a }

val relabel (n : node int) : node int
