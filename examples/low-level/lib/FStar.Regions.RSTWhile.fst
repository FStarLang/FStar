(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst stack.fst
      listset.fst ghost.fst located.fst lref.fst regions.fst rst.fst
  --*)

module FStar.Regions.RSTWhile

open FStar.Regions.RST
open FStar.Regions.Heap
open FStar.Regions.Located
open FStar.Regions.Regions

(* The effect of a computation that takes places within a fresh, new region
   freshly pushed on the stack. *)
(* AA: adding requires/ensures here causes the definition of scopedWhile below
   to not typecheck. Hope this is not a concern w.r.t. soundness. *)
effect WNSC (a:Type) (pre:smem -> Type) (post: smem -> Post a) (mod:modset) =
  Mem a
      ( (* requires *) (fun m -> Stack.isNonEmpty (st m) /\ topRegion m = emp /\ pre (tail m)))
      ( (* ensures *) (fun m0 a m1 -> post (tail m0) a (tail m1)))
      mod

(* Run in a new scope a computation that returns an [a]; the [Mem] return type
   indicates that, from the point of view of the caller, this function leaves
   the stack of regions unchanged (because it cleans up after it's done). In a
   sense, this combinator is hiding a local effect. As far as I can tell, this
   is sound (see “Three comments on the anti-frame rule” by Pottier). *)
val withNewScope : #a:Type -> #pre:(smem -> Type) -> #post:(smem -> Post a)
  -> #mods:modset
  -> body:(unit -> WNSC a pre post mods)
      -> Mem a pre post mods
let withNewScope 'a 'pre 'post #mods body =
    pushRegion ();
    let v = body () in
    popRegion ();
    v


(* A guard for a while statement is a computation that can only *read* from the
   memory (this is [PureMem]). The [whileGuard] is parameterized by [lc], a
   logical condition that the guard entails (JP: is the equivalence strictly
   needed?). *)
effect whileGuard (pre: smem -> Type) (lc: smem -> Type)
  = PureMem bool pre (fun m0 b -> (lc m0 <==> b = true))

(* The guard body, conversely, may read anything, and may write references in
   [modset]: it is a computation in [WNSC], that is, in [Mem]. [Mem] also
   conveys the restriction that the [whileBody] may not change the stack of
   regions; we obviously want this (no region-stack overflow or underflow). *)
effect whileBody (loopInv:smem -> Type) (lc:smem  -> Type) (mod:modset)
  = WNSC unit (fun m -> loopInv m /\ lc m)
              (fun m0 _ m1 -> (* (loopInv m0 /\ canModify m0 m1 mod) ==> *) loopInv m1)
              mod


(* Putting it all together: a while combinator that
   - allocates a new region for each iteration;
   - has distinct guards and logical conditions. *)
val scopedWhile : loopInv:(smem -> Type)
  -> wglc:(smem -> Type)
  -> wg:(unit -> whileGuard loopInv wglc)
  -> mods:modset
  -> bd:(unit -> whileBody loopInv wglc mods)
  -> Mem unit (requires (fun m -> loopInv m))
              (ensures (fun _ _ m1 -> loopInv m1 /\ (~(wglc m1))))
              mods
let rec scopedWhile
   'loopInv 'wglc wg mods bd =
   if wg () then begin
     pushRegion ();
     ignore (bd ());
     popRegion();
     scopedWhile 'loopInv 'wglc wg mods bd
   end else
     ()


(* A simplified version of the combinator where:
   - the guard and its logical condition are combined into one total boolean
     predicate (which we lift to [Type])
   - the guard only depends on the current value of a single (located) reference
   - the loop invariant is automatically augmented with the hypothesis that the
     reference remains live. *)
val scopedWhile1 :
  #a:Type
  -> r:lref a
  -> lc : (a -> Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:modset
  -> bd:(unit -> whileBody
                      (fun m -> loopInv m /\ refIsLive r m)
                      (fun m -> refIsLive r m /\ lc (lookupRef r m))  mods)
  -> Mem unit (fun m -> loopInv m /\ refIsLive r m)
              (fun m0 _ m1 -> loopInv m1 /\ refIsLive r m1 /\ ~(lc (lookupRef r m1)))
              mods
let scopedWhile1 'a r lc 'loopInv mods bd =
  scopedWhile
    (fun m -> 'loopInv m /\ refIsLive r m)
    (fun m -> refIsLive r m /\ lc (lookupRef r m))
    (fun _ -> lc (memread r))
    mods
    bd

(* Same thing with two references. *)
val scopedWhile2 :
  #a:Type
  -> #b:Type
  -> ra:lref a
  -> rb:lref b
  -> lc : (a -> b ->  Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:modset
  -> bd:(unit -> whileBody
                      (fun m -> loopInv m /\ refIsLive ra m /\ refIsLive rb m)
                      (fun m -> refIsLive ra m /\ refIsLive rb m /\ lc (lookupRef ra m) (lookupRef rb m))
                      mods)
  -> Mem unit (requires (fun m -> loopInv m /\ refIsLive ra m /\ refIsLive rb m))
              (ensures (fun m0 _ m1 -> loopInv m1 /\ refIsLive ra m1 /\ refIsLive rb m1 /\ ~(lc (lookupRef ra m1) (lookupRef rb m1)) ))
              mods
let scopedWhile2 'a ra rb lc 'loopInv mods bd =
  scopedWhile
    (fun m -> 'loopInv m /\ refIsLive ra m /\ refIsLive rb m)
    (fun m -> refIsLive ra m /\ refIsLive rb m /\ (lc (lookupRef ra m) (lookupRef rb m))  )
    (fun u -> lc (memread ra) (memread rb))
    mods
    bd


(* Pushing and popping regions is costly (especially in a tight loop), mostly
   due to the FFI and possibly malloc overheads. In the case that the programmer
   knows that no allocation takes place, the simplified versions below are more
   efficient. *)
effect whileBodyUnscoped (loopInv:smem -> Type) (lc:smem -> Type) (mod:modset)
  = Mem unit (fun m -> loopInv m /\ lc m)
             (fun m0 _ m1 -> (* (loopInv m0 /\ canModify m0 m1 mod) ==> *) loopInv m1)
             mod

(* JP: is there a way to limit the code / specification duplication? *)
val unscopedWhile : loopInv:(smem -> Type)
  -> wglc:(smem -> Type)
  -> wg:(unit -> whileGuard loopInv wglc)
  -> mods:modset
  -> bd:(unit -> whileBodyUnscoped loopInv wglc mods)
  -> Mem unit (requires (fun m -> loopInv m))
              (ensures (fun _ _ m1 -> loopInv m1 /\ (~(wglc m1))))
              mods
let rec unscopedWhile 'loopInv 'wglc wg mods bd =
   if wg () then
     let _ = bd () in
     unscopedWhile 'loopInv 'wglc wg mods bd
   else
     ()

val unscopedWhile1 :
  #a:Type
  -> r:lref a
  -> lc : (a -> Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:modset
  -> bd:(unit -> whileBodyUnscoped
                      (fun m -> loopInv m /\ refIsLive r m)
                      (fun m -> refIsLive r m /\ lc (lookupRef r m))  mods)
  -> Mem unit (fun m -> loopInv m /\ refIsLive r m)
              (fun m0 _ m1 -> loopInv m1 /\ refIsLive r m1 /\ ~(lc (lookupRef r m1)))
              mods
let unscopedWhile1 'a r lc 'loopInv mods bd =
  unscopedWhile
    (fun m -> 'loopInv m /\ refIsLive r m)
    (fun m -> refIsLive r m /\ (lc (lookupRef r m)))
    (fun u -> lc (memread r))
    mods
    bd
