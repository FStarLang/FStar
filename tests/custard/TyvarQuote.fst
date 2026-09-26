module TyvarQuote
open FStar.All

(* Section 122.3.1.  A type variable whose F* name ends in a quote.  [t']
   printed as ['t'], which OCaml lexes as a character literal, so the test is
   that the output compiles at all; the greps pin the escape itself, which is
   the same one on both backends and has to be injective -- [t'] and [t_] must
   not meet. *)

noeq type box (t':Type) (t_:Type) = | Box : t' -> t_ -> box t' t_

let first (#t':Type) (#t_:Type) (b : box t' t_) : t' =
  match b with | Box x _ -> x

let main () : ML unit =
  FStar.IO.print_string (first (Box "ok" 0) ^ "\n")
