(*--build-config
    options:--admit_fsi Set --z3timeout 50;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/list.fst  stack.fst listset.fst
    st3.fst $LIB/constr.fst word.fst mvector.fsi mvector.fst MD5.fst
  --*)

(*Why is MD5 so? Why did its designer(s) think
  it was a good way to convolute bits?
  Is there a principle behind its design? or just random convolutery?
  *)
module MD5SubArray
open StructuredMem
open MVector
open Heap
open Set
open MachineWord
open MD5
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

assume val sallocateVector :  a:Type -> n:nat
 -> init:a
 ->
Mem (vector (ref a) n)
  (requires (fun m -> isNonEmpty (st m)))
   (ensures (fun m0 r m1-> (arrayExixtsInMem r m1) /\ mtail m0 = mtail m1))
   (empty)

type chunk512 = array word 16

assume val w0 : word

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

(* Surprisingly, any anti-aliasing condition between ch and acc was not required.
    even though and acc might have some refs in common,
    anything in ch -acc is not modified. Hence the modified clause works
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
    (*allRefs ; why does this not work?*)
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
(*redefine arrayExixtsInMem in terms of flattenRefs.
  then characterize subVector in terms of flatten.
  Note that subVector is opaque and Fstar doesnot know anything about it*)

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




val mainLoopSubArray :
  n : nat{divides 16 n}
 -> ch:((array word n))
 -> un:unit
 -> WNSC (vector word 4)
    (fun m -> True /\ arrayExixtsInMem ch m)
    (fun m0 _ m1 -> True)
    empty


val memAssert : p:(smem->Type) ->
  PureMem unit (requires p) (ensures (fun _ _ _ -> True))
let memAssert 'p = ()


let mainLoopSubArray n ch u =
  let acc =  sallocateVector word 4 w0 in
  memAssert (fun m -> True /\ arrayExixtsInMem ch (m));
  pushStackFrame ();
  memAssert (fun m -> True /\ arrayExixtsInMem ch (m));
  memAssert (fun m -> True /\ arrayExixtsInMem acc (m));
  popStackFrame (); initAcc

(*perhaps the can modify set is causing issues*)

    let x = (mainLoopSubArrayAux n ch acc ()) in
  popStackFrame (); x
