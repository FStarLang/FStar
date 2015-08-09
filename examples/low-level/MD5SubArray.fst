(*--build-config
    options:--admit_fsi Set --z3timeout 50;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst  stack.fst listset.fst
    $LIB/ghost.fst $LIB/seq.fst stackAndHeap.fst sst.fst sstCombinators.fst  $LIB/constr.fst word.fst mvector.fsi mvector.fst MD5Common.fst
  --*)

(*this file is not being maintained anymore*)
module MD5SubArray
open SSTCombinators
open StackAndHeap
open SST
open MVector
open Heap
open Set
open MachineWord
open MD5Common
open Stack

type array (a:Type) (n:nat)= vector (ref a) n

val flattenRefsUpto : #a:Type -> #n:nat -> upto:(m:nat{m<=n}) -> (array a n) -> Tot (set aref)
let rec flattenRefsUpto 'a #n upto v  =
  match upto with
  | 0 -> empty
  | _ -> union (singleton (Ref (atIndex v (upto-1)))) (flattenRefsUpto (upto -1) v)

val flattenRefs : #a:Type -> #n:nat -> (array a n) -> Tot (set aref)
let flattenRefs 'a #n v  = flattenRefsUpto n v

assume val memFlattenIndex :
  #a:Type ->  #n:nat
  -> v:(vector (ref  a) n)
  -> ind:(m:nat{m<n})
  -> m:smem
  ->
  Lemma
    (requires True)
    (ensures (mem (Ref (atIndex v ind)) (flattenRefs v)))
      [SMTPat (ind < n)]

(*define this using flatten refs?*)
type arrayExixtsInMem (#a:Type) (#n:nat) (v: vector (ref  a) n) (m:smem) =
 forall (r:(r:(ref a){mem (Ref r) (flattenRefs v)})).
 {:pattern (mem (Ref r) (flattenRefs v))}refExistsInMem r m


 type allocateVectorInBlock (#a:Type) (#n:nat) (rv: vector (ref a) n)
  (h0 : memblock)
  (h1 : memblock) (init : a)  (rl: refLocType) =
  (forall (r:(r:(ref a){mem (Ref r) (flattenRefs rv)})).
        {:pattern (mem (Ref r) (flattenRefs rv))}
           refLoc r = rl
          /\ not (Heap.contains h0 r)
          /\ Heap.contains h1 r
          /\  init = sel h0 r)
/\ Heap.equal h1 (concat h0 (restrict h1 (flattenRefs rv)))

(*tj*)
assume val sallocateVector :  a:Type -> n:nat
 -> init:a
 -> Mem (vector (ref a) n)
    (requires (fun m -> isNonEmpty (st m)))
    (ensures (fun m0 rv m1->
        (isNonEmpty (st m0)) /\ (isNonEmpty (st m1))
        /\ (topstid m0 = topstid m1)
        /\ mtail m0 = mtail m1
        /\  allocateVectorInBlock rv (topstb m0) (topstb m1) init (InStack (topstid m0))
    ))
      (empty)

type chunk512 = array word 16

val arrayExistsMod :
    #a:Type
    -> #n:nat
    -> s:(set aref)
    -> v:(array a n)
    -> m0:smem
    -> m1:smem
    -> Lemma
        (requires (arrayExixtsInMem v m0 /\ canModify m0 m1 s))
        (ensures (arrayExixtsInMem v m1))
let s v m0 m1 = ()


val processChunkSubArray :
 ch:chunk512
-> acc:(array word 4)
-> WNSC unit
    (requires (fun m -> arrayExixtsInMem ch m
              /\ arrayExixtsInMem acc m
                (*/\ ch =!= acc : why was this not needed?*)
                ))
    (ensures (fun _ _ m1 -> arrayExixtsInMem ch m1
              /\ arrayExixtsInMem acc m1
              (*/\ ch =!= acc*)
              ))
    ((flattenRefs acc))
    (*(Set.complement Set.empty)*)

(* Surprisingly, any anti-aliasing condition between ch and acc was not required.
    even though and acc might have some refs in common,
    anything in ch-acc is not modified. Hence the modifies clause checks.
*)

(*had to increase timeout to get this to typecheck.
  The switch from "ref vector" to "vector ref" cost atleast 10 times more time
*)

let processChunkSubArray ch acc =
  let li = salloc #nat 0 in
  scopedWhile1
    li
    (fun liv -> liv < 64)
    (fun m -> True
              /\ arrayExixtsInMem ch m
              /\ arrayExixtsInMem acc m
              /\ refExistsInMem li m /\ loopkupRef li m < 65
              )
    (union (singleton (Ref li)) (flattenRefs acc))
    (*(Set.complement Set.empty)*)
    (fun u ->
      let liv = memread li in
      let vA = memread (atIndex acc iA) in
      let vB = memread (atIndex acc iB) in
      let vC = memread (atIndex acc iC) in
      let vD = memread (atIndex acc iD) in
      let fF:word = funFGHI liv vB vC vD in
      let g:(n:nat{n<16}) = idx liv liv in
      memwrite (atIndex acc iD) vC;
      memwrite (atIndex acc iA) vD;
      let mg = memread  (atIndex ch g) in
      let vBr = wmodAdd vA  (wmodAdd fF ( wmodAdd(consts liv)  mg)) in
      memwrite (atIndex acc iB) (wmodAdd vB (leftrotate (rots liv) vBr));
      memwrite li (liv+1)
      )

val subArrayExists :
#a:Type
-> #n:nat
-> ch:((array a n))
-> offset:nat
-> len:(k:nat{offset+k <= n})
-> m:smem
-> Lemma
    (requires (arrayExixtsInMem ch m))
    (ensures (arrayExixtsInMem (subVector offset len ch) m))
    [SMTPat (subVector #(ref a) #n offset len ch); SMTPatT (arrayExixtsInMem #a #n ch m)]

let subArrayExists 'a #n ch offset len m = (admit ())
(*Note that subVector is opaque and Fstar doesnot know anything about it*)

(*because SMTPat does not work above, this is a nop to get the logic right*)
val subArrayExists2 :
#a:Type
-> #n:nat
-> ch:((array a n))
-> offset:nat
-> len:(k:nat{offset+k <= n})
-> PureMem unit
    (requires (fun m -> arrayExixtsInMem ch m))
    (ensures (fun _ _ m1 -> arrayExixtsInMem (subVector offset len ch) m1))
let subArrayExists2 'a #n ch offset len = (admit ())


val mainLoopSubArrayAux :
  n : nat{divides 16 n}
 -> ch:((array word n))
 -> acc : (array word 4)
 -> un:unit
 -> WNSC (vector word 4)
    (requires (fun m -> True /\ arrayExixtsInMem ch m /\ arrayExixtsInMem acc m))
    (ensures (fun m0 _ m1 -> True
      /\ arrayExixtsInMem acc m1 /\ arrayExixtsInMem ch m1))
    (
      (*union *)
      (flattenRefs acc)
      (*(flattenRefs ch)*)
      )


let mainLoopSubArrayAux n ch acc u =
  let offset = salloc #nat 0 in
  (*let acc =  sallocateVector word 4 w0 in*)
  scopedWhile1
    offset
    (fun offsetv -> offsetv +16 <= n)
    (fun m -> True
              /\ arrayExixtsInMem ch m
              /\ arrayExixtsInMem acc m
              /\ refExistsInMem offset m
              )
    (
      (*union*)
        (union
          (singleton (Ref offset))
          (flattenRefs acc))
          (*(flattenRefs ch)*)
    )
    (fun u ->

        let offsetv = memread offset in
        subArrayExists2 ch offsetv 16;
        processChunkSubArray (subVector offsetv 16 ch) acc;
        memwrite offset (offsetv + 16)
        );
  initAcc

  val memAssert : p:(smem->Type) ->
    PureMem unit (requires p) (ensures (fun _ _ _ -> True))
  let memAssert 'p = ()

val arrayExistsInMemTailSids : #a:Type -> #n:nat -> r:(vector (ref a) n)
  -> m0:smem -> m1:smem -> Lemma
  (requires (sids m0 = sids m1 /\ arrayExixtsInMem r (mtail m0) /\ arrayExixtsInMem r m1))
  (ensures arrayExixtsInMem r (mtail m1))
  [SMTPat (sids m0 = sids m1)]
let arrayExistsInMemTailSids 'a #n r m0 m1 = (admit ())



val mainLoopSubArray :
  n : nat{divides 16 n}
 -> ch:((array word n))
 -> un:unit
 -> WNSC (vector word 4)
    (fun m -> True /\ arrayExixtsInMem ch m)
    (fun m0 _ m1 -> True)
    (*this computation does not modify anything, but F* needs more convincing *)
     (*(Set.empty)*)
    (*allRefs*)
    (Set.complement (Set.empty))

let mainLoopSubArray n ch u =
  let acc =  sallocateVector word 4 w0 in
  let dummy : ref nat = salloc 0 in
  (*assert (b2t (not (Set.mem (Ref dummy) (flattenRefs acc)))) ;*)
  memAssert (fun m -> ~ (refExistsInMem dummy (mtail m)));
  memAssert (fun m -> ~ (arrayExixtsInMem acc (mtail m)));
  memAssert (fun m -> forall (r:(r:(ref word){Set.mem (Ref r) (flattenRefs acc)})). ~ (refExistsInMem r (mtail m)) );
  memAssert (fun m -> True /\ arrayExixtsInMem ch (m));
  pushStackFrame ();
  memAssert (fun m -> True /\ arrayExixtsInMem ch (m));
  memAssert (fun m -> True /\ arrayExixtsInMem acc (m));
  let x = (mainLoopSubArrayAux n ch acc ()) in
  popStackFrame ();
  memAssert (fun m -> True /\ arrayExixtsInMem acc (m));
  memAssert (fun m -> True /\ arrayExixtsInMem ch (m));
  memAssert (fun m -> True /\ arrayExixtsInMem ch (mtail m));
  (* The assertion below typechecked above. sids have not changed since because we pushed once and then popped once.

   *)
    (*memAssert (fun m -> ~ (arrayExixtsInMem acc (mtail m)));*)
  (*memAssert (fun m -> forall (r:(r:(ref word){Set.mem (Ref r) (flattenRefs acc)})). ~ (refExistsInMem r (mtail m)) );*)
  memAssert (fun m -> ~ (refExistsInMem dummy (mtail m)));
  x
