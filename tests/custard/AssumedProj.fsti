module AssumedProj

(* Section 8.5: [@@no_auto_projectors] makes F* declare a type's projectors
   and discriminators without defining them, so an extractor that waits for a
   [Sig_let] never sees one.  Pulse's [st_term] carries the attribute, and a
   record update compiles to a projector application, so leaving these as
   externals produced an unresolved symbol at link time. *)
[@@ no_auto_projectors]
noeq
type tree (a:Type0) =
  | Leaf
  | Node of node a
and node (a:Type0) = { left : tree a; here : a; right : tree a }

val relabel (n : node int) : node int
