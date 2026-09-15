module ExternOpt

open FStar.All
open FStar.Attributes
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* Section 100.  A C boundary that speaks in an F* type constructor.

   [listener] is the target's, so nothing here knows its shape; but [option]
   is Custard's, and a specialization of it is an ordinary struct Custard is
   perfectly able to emit.  Until section 100 the mere fact that [listen]'s
   signature mentioned [option] froze the type -- section 5.0.1 rule 4, which
   exists so that a hand-written OCaml realization keeps the representation
   it was written against -- and the program was rejected for a reason that
   only holds on the OCaml path.

   The realization is written against the generated header, in the same way
   PolyExtern's is: the name and the layout are Custard's, which is what
   makes the boundary describable at all. *)

[@@custard_extern "externopt_listener_t"; custard_c_header "ExternOpt_stubs.h"]
assume val listener : Type0

[@@custard_extern "externopt_port"; custard_c_header "ExternOpt_stubs.h"]
assume val port (l:listener) : U32.t

(* The reported shape: an external *returning* a specialization. *)
assume val listen (n:U32.t) : ML (option listener)

(* And one *taking* it, which goes through the same signature walk. *)
assume val close (o:option listener) : ML U32.t

let main () : ML I32.t =
  match listen 443ul with
  | None -> 1l
  | Some l ->
    if U32.eq (port l) 443ul && U32.eq (close (Some l)) 443ul
       && U32.eq (close None) 0ul
       && None? (listen 0ul)
    then 0l else 1l
