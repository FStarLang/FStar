(*--build-config
    options:--admit_fsi Set --logQueries --debug Test --debug_level High --debug_level Rel;
    other-files:ext.fst set.fsi heap.fst st.fst list.fst stack.fst listset.fst st3.fst
  --*)
module Example2
open StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet

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
