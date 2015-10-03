(*--build-config
    options:--admit_fsi Set;
    other-files:ext.fst set.fsi heap.fst st.fst list.fst stack.fst listset.fst st3.fst
  --*)
module Example1
open StructuredMem
open Heap
open Stack
open Set
open Prims
open List
open ListSet


(*a good aspect of the current formulation is that the heap/stack difference
only matters at the time of allocation. Functions like increment can be
defined without without bothering about that distinction*)

(*ideally, the refIsLive clauses should not be needed in the postcondition*)
val incrementRef : r:(lref int) -> RST unit
  (requires (fun m -> (refIsLive r m)==true))
  (ensures (fun m0 a m1 -> (refIsLive r m0) /\ (refIsLive r m1) /\ (lookupRef r m1 = (lookupRef r m0) + 1)))
let incrementRef r =
  let oldv = memread r in
  memwrite r (oldv + 1)

val pushPopNoChage : unit ->  RST unit  (fun _ -> True) (fun m0 vo m1 -> m0 == m1)
let pushPopNoChage () =
  pushRegion (); (* As expected, removing this line results in an error, even for the trivial postcondition*)
  popRegion ()


val incrementUsingStack : vi:int -> RST int  (fun _ -> True)
    (fun m0 vo m1 -> m0 = m1 /\ vo=vi+1)
let incrementUsingStack vi =
  pushRegion ();
    let r = ralloc vi in
    let oldv = memread r in
    memwrite r (oldv + 1);
    let v = (memread r) in
  popRegion ();
  v


val incrementRef2 : r:(lref int) -> RST unit
(fun m -> (refIsLive r m)
              /\ (isNonEmpty (st m))
              /\ (regionOf r = InStack (topRegionId m)))
(fun m0 a m1 -> (refIsLive r m0) /\ (refIsLive r m1)
    /\ (mtail m0 = mtail m1)
    /\ (lookupRef r m1 = (lookupRef r m0) + 1))
let incrementRef2 r =
  let oldv = memread r in
  memwrite r (oldv + 1)

(* an example illustrating a typical C idiom :
  caller allocates memory and passes the lref to callee to get some work done *)
val incrementUsingStack2 : vi:int -> RST int  (fun _ -> True)
    (fun m0 vo m1 -> m0 = m1 /\ vo=vi+1)
let incrementUsingStack2 vi =
  pushRegion ();
    let r = ralloc vi in
    incrementRef2 r; (*why doesn't incrementRef work here?*)
    let v = (memread r) in
  popRegion ();
  v

val incrementUsingStack3 : vi:int -> RST int  (fun _ -> True)
    (fun m0 vo m1 ->  m0 =  m1 /\ vo=vi+1)
let incrementUsingStack3 vi =
  pushRegion ();
    let r = ralloc vi in
    let r2 = ralloc 0 in
    let oldv = memread r in
    memwrite r (oldv + 1);
    memwrite r2 2; (*a dummy operation bwteen write r and read r*)
    let v = (memread r) in
  popRegion ();
  v

(* Why am I able to write this if then else with effectful computations in the brances?
   What is going on under the hood?
   Is this because of the ite_wp in the definition of an effect? *)
val incrementIfNot2 : r:(lref int) -> RST int  (fun m -> (refIsLive r m)==true)
(fun m0 a m1 -> (refIsLive r m0) /\ (refIsLive r m1))
let incrementIfNot2 r =
  let oldv = memread r in
  (if (oldv=2)
    then memwrite r 2
    else memwrite r (oldv + 1));oldv



(*What are the advantage (if any) of writing low-level programs this way,
  as opposed to writihg it as constructs in a deep embedding of C, e.g. VST.
  Hopefully, most of the code will not need the low-level style.
  Beautiful functional programs will also be translated to C?
  *)


val testAliasing : n:nat -> ((k:nat{k<n}) -> Tot bool) -> RST unit (fun  _  -> True) (fun _ _ _ -> True)
let testAliasing n initv =
  pushRegion ();
  let li: lref nat = ralloc 1 in
  let res : lref ((k:nat{k<n}) -> Tot bool) = ralloc initv in
  let resv=memread res in
    memwrite li 2;
    let resv2=memread res in
      assert (resv ==  resv2);
      popRegion ()

val testAliasing2 : n:nat
 -> li : lref nat
 -> res : lref ((k:nat{k<n}) -> Tot bool)
 -> RST unit
          (requires (fun  m  -> refIsLive res m /\ refIsLive li m /\ (li=!=res)))
          (ensures (fun _ _ _ -> True))
let testAliasing2 n li res =
  let resv=memread res in
    memwrite li 2;
    let resv2=memread res in
      assert (resv =  resv2)


val testSalloc1 : unit -> RST unit (fun _ -> True) (fun _ _ _ -> True)
let testSalloc1 () =
  pushRegion ();
  let xi=ralloc 0 in
  memwrite xi 1;
  pushRegion ();
  memwrite xi 1

val testSalloc2 : xi:lref int -> RST unit (fun m -> b2t (refIsLive xi m)) (fun _ _ m1 -> b2t (refIsLive xi m1))
let testSalloc2 xi =
  pushRegion ();
  memwrite xi 1;
  popRegion ();
  memwrite xi 1
