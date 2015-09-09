(*--build-config
    options:--z3timeout 10 --verify_module Bug --codegen OCaml --admit_fsi FStar.IO;
    other-files:
            ext.fst classical.fst
            set.fsi set.fst
            heap.fst st.fst all.fst
            string.fst list.fst
            io.fsti
  --*)

module Bug

open FStar.All
open FStar.String
open FStar.IO

(* two events, recording genuine requests and responses *)

logic type lnat = nat


val escape : lnat -> Tot nat
let escape l = l


(* logic *) type Request : string -> Type
(* logic *) type Response : string -> string -> Type

(* the meaning of MACs, as used in RPC *)

(* opaque logic *) type reqresp (msg:string) =
    (exists s.    Request s)
(* \/ (exists s t.  Response s t) *)

(*
let keygen (p: (string -> Type)) =
  ()


let k = print_string "generating shared key...\n";
  keygen reqresp*)
