(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module Bug --codegen OCaml-experimental;
    variables:LIB=../../lib;
    other-files:
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst $LIB/all.fst
            $LIB/string.fst $LIB/list.fst
            $LIB/io.fst
  --*)

module Bug

open All
open String
open IO

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
