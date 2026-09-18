module ExnName

open FStar.All
open FStar.Exception { string_of_exn }

module L = ExnNameLib

(* Section 125.7.  [FStar.Exception.string_of_exn] is [Printexc.to_string],
   which prints the constructor, so the OCaml name Custard picks for an
   exception is the one thing about the mangling a program can observe.  It is
   applied where there is a collision and not otherwise, and the three cases
   are all here. *)

(* Unambiguous: emitted as [B], so [Printexc] says [ExnName.B]. *)
exception B

(* Ambiguous with [ExnNameLib.A]: both stay mangled, and *both* do, because
   handing the short name to whichever was declared first would make which of
   them is readable depend on declaration order. *)
exception A

(* Unambiguous among the program's own exceptions, and still mangled: it is
   one of OCaml's, and shadowing [Stdlib.Not_found] for the rest of the file
   would be a collision with the language. *)
exception Not_found

let show (e:exn) : ML unit =
  FStar.IO.print_string (string_of_exn e); FStar.IO.print_string "\n"

let main () : ML unit =
  (try raise B with e -> show e);
  (try raise A with e -> show e);
  (try raise L.A with e -> show e);
  (try raise Not_found with e -> show e)
