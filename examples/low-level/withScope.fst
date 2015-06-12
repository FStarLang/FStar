(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst stack.fst listset.fst st3.fst
  --*)
module Example2
open StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet



val withNewScope3 : a:Type ->
   body:(unit -> SST a
     (requires mStackNonEmpty)
     (ensures (fun m0 _ m1 -> mStackNonEmpty m1))
     )
      -> SST a (requires (fun m -> True))
                (ensures (fun m0 a m1 -> True))

let withNewScope3 (a:Type)
  (body:(unit -> SST a
          (requires mStackNonEmpty)
          (ensures (fun _ _ m1 -> mStackNonEmpty m1)))
          )
          =
(* omitting the types in above let expression results in a wierd error*)
    pushStackFrame ();
    let v = body () in
    popStackFrame (); v

val identity  : n:nat
  -> SST nat (fun m -> True)
              (fun _ n' _ ->  n'==n)
let identity n = n


val identity2  : n:nat -> unit ->
   SST nat (fun m -> True /\ mStackNonEmpty m)
              (fun _ n' m1 ->  n'=n /\ mStackNonEmpty m1)
let identity2 n u = n


val scopedID : n:nat
  -> SST nat (fun m -> True)
              (fun _ n' _ -> n'==n)

(* This does not typecheck *)
(*let scopedID (n:nat) =
  withNewScope3
    nat
    (fun () ->  n)*)

(* The part below also does not typecheck. The error is uninformative:
Subtyping check failed; expected type (unit -> SST (nat)); got type (unit -> SST (nat))
Perhaps some implicit argument is different

let scopedID (n:nat) =
  withNewScope3
    nat
     (identity2 n)*)



let scopedID (n:nat) =
 withNewScope
   nat
   (fun m -> True)
   (fun _ n' _ -> n'==n)
   (fun () ->  n)


(* Leaving the pre/post conditions out makes the above fail.
   Having to put those everytime when callling withNewScope will be very tedious

let scopedID (n:nat) =
 withNewScope
   nat
   _
   _
   (fun () ->  n)*)


val scopedID2 : n:nat
  -> SST nat (fun m -> True)
              (fun _ n' _ -> True)

let scopedID2 (n:nat) =
  withNewScope3
    nat
    (fun () ->  n)


(*Just being able to define an abbreviation like below should be good, but it fails*)
(*let withNewScope4
  body
          =
    pushStackFrame ();
    let v = body () in
    popStackFrame (); v*)

(*effect ALL and StSTATE cannot be combined*)
