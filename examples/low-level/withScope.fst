(*--build-config
    options:--admit_fsi Set --logQueries --debug Test --debug_level High --debug_level Rel;
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

let scopedID (n:nat) =
  withNewScope (fun () -> n)

val withNewScope3 : #a:Type ->
      body:(unit -> SST a mStackNonEmpty
                          (fun m0 _ m1 -> mStackNonEmpty m1))
      -> SST a (requires (fun m -> True))
               (ensures (fun m0 a m1 -> True))

let withNewScope3 body =
    pushStackFrame ();
    let v = body () in
    popStackFrame (); v

val identity  : n:nat
  -> SST nat (fun m -> True)
              (fun _ n' _ ->  n'==n)
let identity n = n


val identity2  : n:nat -> unit ->
   SST nat (fun m -> mStackNonEmpty m)
           (fun _ n' m1 ->  n'=n /\ mStackNonEmpty m1)
let identity2 n u = n


val scopedID : n:nat
  -> SST nat (requires (fun m -> True))
             (ensures (fun _ n' _ -> True)) // n'==n))
(* This does not typecheck *)
(* NS: Why do you expect it to type-check? The post-condition of withNewScope3 is just True.
       So, there's no way to prove that n=n' from that.
       It does check if you remove that post-condition from scopedID *)
let scopedID (n:nat) =
  withNewScope3 #nat
    (fun () ->  n)

(* NS: Here's how I would write it *)
val withNewScope4 : #a:Type -> #req:(smem -> Type) -> #ens:(smem -> a -> smem -> Type)
      -> =body:(unit -> SST a req ens) //=body is an equality constraint for type inference
      -> SST a (requires (fun m ->
                            (forall m'. mtail m' = m
                                    /\ isNonEmpty (st m')
                                    /\ topstb m' = emp
                                    ==> req m')
                         /\ (forall m0 x m1. ens m0 x m1 ==> sids m0 = sids m1)))
               (ensures (fun m0 x m1 ->
                         sids m0 = sids m1
                         /\ (exists m0' m1'. mtail m0'=m0
                                          /\ isNonEmpty (st m0')
                                          /\ topstb m0'=emp
                                          /\ ens m0' x m1')))
let withNewScope4 body =
   pushStackFrame ();
   let v = body () in
   popStackFrame (); v

val scopedID4 : n:nat
 -> SST nat (requires (fun m -> True))
            (ensures (fun _ n' _ -> n'==n))
let scopedID4 (n:nat) =
  //One option is to annotate the
  let id : unit -> SST nat (fun s -> True) (fun s0 x s1 -> s0=s1 /\ x=n) =
    fun () -> n in
  withNewScope4 id

assume val as_SST: #a:Type -> #b:Type
         -> #wp:(a -> (b -> smem -> Type) -> smem -> Type)
         -> #wlp:(a -> (b -> smem -> Type) -> smem -> Type)
         -> =f:(x:a -> StSTATE b (wp x) (wlp x))
         -> Tot (x:a -> SST b
                            (wp x (fun y s -> True))
                            (fun s0 y s1 -> wlp x (fun y' s1' -> y=y' /\ s1=s1') s0))


val test: unit -> SST int (requires (fun n -> True))
                          (ensures (fun s0 x s1 -> s0=s1 /\ x=17))
let test () = as_SST (fun () -> 17) ()

val scopedID5 : n:nat
             -> SST nat (requires (fun m -> True))
                        (ensures (fun _ n' _ -> n'==n))
let scopedID5 (n:nat) =
  withNewScope4 (as_SST (fun () -> n))
