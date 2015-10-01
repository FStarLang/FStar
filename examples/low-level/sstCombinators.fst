(*--build-config
    variables:MATHS=../maths;
    other-files:ext.fst set.fsi set.fst  heap.fst st.fst all.fst   list.fst stack.fst listset.fst ghost.fst located.fst lref.fst regions.fst rst.fst
  --*)

module RSTCombinators

open RST
open Heap
open Lref  open Located
open Stack
open Regions
open Set
open Prims
open List
open ListSet

open Ghost

(*Sane RST*)


(** withNewStackFrame combinator *)
(*adding requires/ensures here causes the definition of scopedWhile below to not typecheck.
Hope this is not a concert w.r.t. soundness*)
effect WNSC (a:Type) (pre:(smem -> Type))  (post: (smem -> RSTPost a)) (mod:modset) =
  Mem a
      ( (*requires *) (fun m -> isNonEmpty (st m) /\ topRegion m = emp /\ pre (tail m)))
      ( (* ensures *) (fun m0 a m1 -> post (tail m0) a (tail m1)))
      mod

val withNewScope : #a:Type -> #pre:(smem -> Type) -> #post:(smem -> RSTPost a)
  -> #mods:modset
  -> body:(unit -> WNSC a pre post mods)
      -> Mem a pre post mods
let withNewScope 'a 'pre 'post #mods body =
    pushRegion ();
    let v = body () in
    popRegion (); v


(*a combinator for writing while loops*)

(*Mem restriction is not needed, because there is a even stronger condition here that the memory is unchanged*)
effect whileGuard (pre :(smem -> Type))
  (lc : (smem -> Type))
  = PureMem bool  pre (fun m0 b  ->   (lc m0 <==> b = true))
(* the guard of a while loop is not supposed to change the memory*)


effect whileBody (loopInv:smem -> Type) (lc:smem  -> Type) (mod:modset)
  = WNSC unit (fun m -> loopInv m /\ lc m)
              (fun m0 _ m1 -> (* (loopInv m0 /\ canModify m0 m1 mod) ==> *) loopInv m1)
              mod


val scopedWhile : loopInv:(smem -> Type)
  -> wglc:(smem -> Type)
  -> wg:(unit -> whileGuard loopInv wglc)
  -> mods:(modset)
  -> bd:(unit -> whileBody loopInv wglc mods)
  -> Mem unit (requires (fun m -> loopInv m))
              (ensures (fun _ _ m1 -> loopInv m1 /\ (~(wglc m1))))
              mods
let rec scopedWhile
   'loopInv 'wglc wg mods bd =
   if (wg ())
      then
        ((let _ = pushRegion () in
          let _ = bd  () in popRegion());
         (scopedWhile 'loopInv 'wglc wg mods bd))
      else ()

val scopedWhile1 :
  #a:Type
  -> r:(lref a)
  -> lc : (a -> Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:(modset)
  -> bd:(unit -> whileBody
                      (fun m -> loopInv m /\ liveRef r m)
                      (fun m -> liveRef r m /\ lc (lookupRef r m))  mods)
  -> Mem unit ((fun m -> loopInv m /\ liveRef r m))
              ((fun m0 _ m1 -> loopInv m1 /\ liveRef r m1 /\ ~(lc (lookupRef r m1))))
              mods
let scopedWhile1 'a r lc 'loopInv mods bd =
(*loop invariant includes the precondition for evaluating the guard*)
  scopedWhile
    (fun m -> 'loopInv m /\ liveRef r m)
    (fun m -> liveRef r m /\ (lc (lookupRef r m)))
    (fun u -> lc (memread r))
    mods
    bd

val scopedWhile2 :
  #a:Type
  -> #b:Type
  -> ra:(lref a)
  -> rb:(lref b)
  -> lc : (a -> b ->  Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:(modset)
  -> bd:(unit -> whileBody
                      (fun m -> loopInv m /\ liveRef ra m /\ liveRef rb m)
                      (fun m -> liveRef ra m /\ liveRef rb m /\ lc (lookupRef ra m) (lookupRef rb m))
                      mods)
  -> Mem unit (requires (fun m -> loopInv m /\ liveRef ra m /\ liveRef rb m))
              (ensures (fun m0 _ m1 -> loopInv m1 /\ liveRef ra m1 /\ liveRef rb m1 /\ ~(lc (lookupRef ra m1) (lookupRef rb m1)) ))
              mods
let scopedWhile2 'a ra rb lc 'loopInv mods bd =
  scopedWhile
    (fun m -> 'loopInv m /\ liveRef ra m /\ liveRef rb m)
    (fun m -> liveRef ra m /\ liveRef rb m /\ (lc (lookupRef ra m) (lookupRef rb m))  )
    (fun u -> lc (memread ra) (memread rb))
    mods
    bd


(*unscoped while. push/pops are costly because of FFI and possibly malloc overheads.
So if the programmer knows that nothing is being allocated, they should used the
unscoped versions below*)

effect whileBodyUnscoped (loopInv:smem -> Type) (lc:smem  -> Type) (mod:modset)
  = Mem unit (fun m -> loopInv m /\ lc m)
              (fun m0 _ m1 -> (* (loopInv m0 /\ canModify m0 m1 mod) ==> *) loopInv m1)
              mod



val unscopedWhile : loopInv:(smem -> Type)
  -> wglc:(smem -> Type)
  -> wg:(unit -> whileGuard loopInv wglc)
  -> mods:(modset)
  -> bd:(unit -> whileBodyUnscoped loopInv wglc mods)
  -> Mem unit (requires (fun m -> loopInv m))
              (ensures (fun _ _ m1 -> loopInv m1 /\ (~(wglc m1))))
              mods
let rec unscopedWhile
   'loopInv 'wglc wg mods bd =
   if (wg ())
      then (let _ = bd () in (unscopedWhile 'loopInv 'wglc wg mods bd))
      else ()

val unscopedWhile1 :
  #a:Type
  -> r:(lref a)
  -> lc : (a -> Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:(modset)
  -> bd:(unit -> whileBodyUnscoped
                      (fun m -> loopInv m /\ liveRef r m)
                      (fun m -> liveRef r m /\ lc (lookupRef r m))  mods)
  -> Mem unit ((fun m -> loopInv m /\ liveRef r m))
              ((fun m0 _ m1 -> loopInv m1 /\ liveRef r m1 /\ ~(lc (lookupRef r m1))))
              mods
let unscopedWhile1 'a r lc 'loopInv mods bd =
  unscopedWhile
    (fun m -> 'loopInv m /\ liveRef r m)
    (fun m -> liveRef r m /\ (lc (lookupRef r m)))
    (fun u -> lc (memread r))
    mods
    bd
