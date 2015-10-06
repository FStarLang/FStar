(*--build-config
    options:--admit_fsi Set;
    other-files:ext.fst set.fsi heap.fst st.fst list.fst stack.fst listset.fst st3.fst example1.fst
  --*)
module ScopedWhile3
open StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet
open Example1






effect whileGuard3 (pre :(smem -> Type))
  (lct : (smem -> Type))
  (lcf : (smem -> Type))
  = RST bool  (pre) ((fun m0 b m1 -> m0 = m1 /\  (b = true ==> lct m0) /\ (b = false ==> lcf m0)))
(* the guard of a while loop is not supposed to change the memory*)

effect whileBody3 (loopInv:smem -> Type) (truePre:smem  -> Type)
  =
  (*WNSC unit ((fun m -> loopInv m  /\ (truePre m)))
             ((fun m0 _ m1 -> loopInv m1))*)

  RST unit ((fun m -> loopInv (mtail m) /\ (truePre (mtail m))))
             ((fun m0 _ m1 -> loopInv (mtail m1) /\ sids m0 = sids m1))

(*#set-options "--initial_fuel 9000 --max_fuel 900000 --initial_ifuel 9000 --max_ifuel 900000"*)

val scopedWhile3 : loopInv:(smem -> Type)
  -> wglct:(smem -> Type)
  -> wglcf:(smem -> Type)
  -> wg:(unit -> whileGuard3 loopInv wglct wglcf)
  -> bd:(unit -> whileBody3 loopInv wglct)
  -> RST unit ((fun m -> loopInv m))
              ((fun m0 _ m1 -> loopInv m1 /\ wglcf m1 /\ sids m0 = sids m1))
let rec scopedWhile3 (loopInv:(smem -> Type))
  (wglct:(smem -> Type))
  (wglcf:(smem -> Type))
  (wg:(unit -> whileGuard3 loopInv wglct wglcf))
  (bd:(unit -> whileBody3 loopInv wglct)) =
   if (wg ())
      then
        ((withNewScope unit
          (fun m -> loopInv m /\ (wglct m)) (fun _ _ m1 -> loopInv m1) bd);
        (scopedWhile3 loopInv wglct wglcf wg bd))
      else ()



val loopyFactorial3 : n:nat
  -> RST nat (fun m -> True)
              (fun _ rv _ -> rv == (factorial n))
let loopyFactorial3 n =
  pushRegion ();
  let li = ralloc 0 in
  let res = ralloc 1 in
  (scopedWhile3
    (loopInv li res)
    (fun m -> (refIsLive li m) /\ ~ ((lookupRef li m) = n))
    (fun m -> (refIsLive li m) /\  ((lookupRef li m) = n))
    (fun u -> not (memread li = n))
    (fun u ->
      let liv = memread li in
      let resv = memread res in
      memwrite li (liv + 1);
      memwrite res ((liv+1) * resv)));
  let v=memread res in
  popRegion ();
  v
