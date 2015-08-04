(*--build-config
    options: --codegen OCaml-experimental --trace_error --debug yes;
    variables:LIB=../../lib;
    variables:MATHS=../maths;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst  $LIB/list.fst stack.fst listset.fst $LIB/ghost.fst stackAndHeap.fst sst.fst
  --*)

module SSTCombinators
open StackAndHeap
open SST
open Heap
open Stack
open Set
open Prims
open List
open ListSet


(*Sane SST*)
effect Mem (a:Type) (pre: smem -> Type) (post: (smem -> SSTPost a)) (mod:set aref) =
        SST a pre (fun m0 a m1 -> post m0 a m1 /\ sids m0 = sids m1 /\ canModify m0 m1 mod)

effect PureMem (a:Type) (pre:smem -> Type) (post: (smem -> Post a)) =
        SST a pre (fun m0 a m1 -> post m0 a m1 /\ m0=m1)


(** withNewStackFrame combinator *)
(*adding requires/ensures here causes the definition of scopedWhile below to not typecheck.
Hope this is not a concert w.r.t. soundness*)
effect WNSC (a:Type) (pre:(smem -> Type))  (post: (smem -> SSTPost a)) (mod:set aref) =
  Mem a
      ( (*requires *) (fun m -> isNonEmpty (st m) /\ topstb m = emp /\ pre (mtail m)))
      ( (* ensures *) (fun m0 a m1 -> post (mtail m0) a (mtail m1)))
      mod

val withNewScope : #a:Type -> #pre:(smem -> Type) -> #post:(smem -> SSTPost a)
  -> #mods:set aref
  -> body:(unit -> WNSC a pre post mods)
      -> Mem a pre post mods
let withNewScope 'a 'pre 'post #mods body =
    pushStackFrame ();
    let v = body () in
    popStackFrame (); v

(*SMTPat could be used to implement something similar to Coq's type-class mechanism.
Coq's typeclass resolution is based on proof search using Hint databases, which is similar to SMTPat.
Can implicit arguments be inferred automatically by the SMT solver using proof seach with SMTPat hints?
*)


(*a combinator for writing while loops*)

(*Mem restriction is not needed, because there is a even stronger condition here that the memory is unchanges*)
effect whileGuard (pre :(smem -> Type))
  (lc : (smem -> Type))
  = PureMem bool  pre (fun m0 b _ ->   (lc m0 <==> b = true))
(* the guard of a while loop is not supposed to change the memory*)

effect whileBody (loopInv:smem -> Type) (lc:smem  -> Type) (mod:set aref)
  = WNSC unit (fun m -> loopInv m /\ lc m)
              (fun m0 _ m1 -> (* (loopInv m0 /\ canModify m0 m1 mod) ==> *) loopInv m1)
              mod



val scopedWhile : loopInv:(smem -> Type)
  -> wglc:(smem -> Type)
  -> wg:(unit -> whileGuard loopInv wglc)
  -> mods:(set aref)
  -> bd:(unit -> whileBody loopInv wglc mods)
  -> Mem unit (requires (fun m -> loopInv m))
              (ensures (fun m0 _ m1 -> loopInv m1 /\ (~(wglc m1))))
              mods
let rec scopedWhile
   'loopInv 'wglc wg mods bd =
   if (wg ())
      then
        ((withNewScope #unit
            #(fun m -> 'loopInv m /\ ('wglc m)) #(fun _ _ m1 -> 'loopInv m1) #mods bd);
        (scopedWhile 'loopInv 'wglc wg mods bd))
      else ()

(*The 2 definitions below do not extract properly. 'loopInv is a type var and
OCaml complains "operator expected" . Removing 'loopInv manually in the extract
fixes the problem. 'loopInv is not used anyway in the extract. *)

val scopedWhile1 :
  #a:Type
  -> r:(ref a)
  -> lc : (a -> Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:(set aref)
  -> bd:(unit -> whileBody
                      (fun m -> loopInv m /\ refExistsInMem r m)
                      (fun m -> refExistsInMem r m /\ lc (loopkupRef r m))  mods)
  -> Mem unit ((fun m -> loopInv m /\ refExistsInMem r m))
              ((fun m0 _ m1 -> loopInv m1 /\ refExistsInMem r m1 /\ ~(lc (loopkupRef r m1))))
              mods
let scopedWhile1 'a r lc 'loopInv mods bd =
  scopedWhile
  (*augment the loop invariant to include the precondition for evaluating the guard*)
    (fun m -> 'loopInv m /\ refExistsInMem r m)
    (fun m -> refExistsInMem r m /\ (lc (loopkupRef r m)))
    (fun u -> lc (memread r))
    mods
    bd

val scopedWhile2 :
  #a:Type
  -> #b:Type
  -> ra:(ref a)
  -> rb:(ref b)
  -> lc : (a -> b ->  Tot bool)
  -> loopInv:(smem -> Type)
  -> mods:(set aref)
  -> bd:(unit -> whileBody
                      (fun m -> loopInv m /\ refExistsInMem ra m /\ refExistsInMem rb m)
                      (fun m -> refExistsInMem ra m /\ refExistsInMem rb m /\ lc (loopkupRef ra m) (loopkupRef rb m))
                      mods)
  -> Mem unit (requires (fun m -> loopInv m /\ refExistsInMem ra m /\ refExistsInMem rb m))
              (ensures (fun m0 _ m1 -> loopInv m1 /\ refExistsInMem ra m1 /\ refExistsInMem rb m1 /\ ~(lc (loopkupRef ra m1) (loopkupRef rb m1)) ))
              mods
let scopedWhile2 'a ra rb lc 'loopInv mods bd =
  scopedWhile
  (*augment the loop invariant to include the precondition for evaluating the guard*)
    (fun m -> 'loopInv m /\ refExistsInMem ra m /\ refExistsInMem rb m)
    (fun m -> refExistsInMem ra m /\ refExistsInMem rb m /\ (lc (loopkupRef ra m) (loopkupRef rb m))  )
    (fun u -> lc (memread ra) (memread rb))
    mods
    bd
