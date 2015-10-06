(*--build-config
    other-files:ext.fst set.fsi set.fst heap.fst st.fst all.fst list.fst ../stack.fst ../listset.fst
    ghost.fst ../located.fst ../lref.fst ../stackAndHeap.fst ../sst.fst ../sstCombinators.fst constr.fst ../word.fst seq.fsi seq.fst ../array.fsi
     ../array.fst ../arrayAlgos.fst
  --*)

module Huffman

open RST
open RSTArray
open ArrayAlgos

open StackAndHeap
open Stack

open Lref
open Located

open FStar.Ghost

assume val symbol_value_bound: nat

type symbol_t = n:nat{n < symbol_value_bound}

type node =
  {
    frequency: lref int;
    zero_child: located node;
    one_child: located node;
    symbol: symbol_t;
    code: lref string
  }

val live_located: #a:Type -> located a -> smem -> Tot bool
let live_located x sm = match regionOf x with
  | InHeap     -> true
  | InStack id -> List.mem id (ssids (snd sm))

assume val greveal_precedence_axiom: #a:Type -> l:located a
                                     -> Lemma (requires (True)) (ensures (greveal l << l))
                                                           
val live_node: n:located node -> sm:smem -> GTot bool
let rec live_node n sm =
  greveal_precedence_axiom n;

  let n' = greveal n in
  live_located n sm && refIsLive n'.frequency sm && live_node n'.zero_child sm &&
  live_node n'.one_child sm && refIsLive n'.code sm

val live_node_after_write: #a:Type ->  rw:(lref a) -> v:a
                           -> n:located node -> m:smem{live_node n m}
                           -> GTot (u:unit{live_node n (writeMemAux rw m v)})
                              (decreases n)
let rec live_node_after_write rw v n m =
  greveal_precedence_axiom n;
  let n' = greveal n in
  live_node_after_write rw v n'.zero_child m;
  live_node_after_write rw v n'.one_child m

val live_node_after_ralloc: #a:Type -> r:(lref a) -> v:a -> n:located node
                            -> m:smem{isNonEmpty (st m) /\ not (contains (topRegion m) r) /\ live_node n m}
                            -> GTot (u:unit{live_node n (allocateInTopR r v m)})
                               (decreases n)
let rec live_node_after_ralloc r v n m =
  greveal_precedence_axiom n;
  let n' = greveal n in
  live_node_after_ralloc r v n'.zero_child m;
  live_node_after_ralloc r v n'.one_child m

(* TODO: FIXME: Can't write ghost code in lemmas *)
val live_node_after_write_lemma: #a:Type -> rw:(lref a) -> v:a
                                 -> n:located node -> m:smem{live_node n m}
                                 -> Lemma (requires (True))
                                          (ensures (live_node n (writeMemAux rw m v)))
                                    [SMTPat (writeMemAux rw m v); SMTPat (live_node n m)]
let live_node_after_write_lemma rw v n m = admit ()

val live_node_after_ralloc_lemma: #a:Type -> r:(lref a) -> v:a -> n:located node
                            -> m:smem{isNonEmpty (st m) /\ not (contains (topRegion m) r) /\ live_node n m}
                            -> Lemma (requires (True))
                                     (ensures (live_node n (allocateInTopR r v m)))
                               [SMTPat (allocateInTopR r v m); SMTPat (live_node n m)]
let live_node_after_ralloc_lemma r v n m = admit ()

(* projectors *)
assume val read_frequency: n:located node -> PureMem (lref int)
                                             (fun sm0 -> b2t (live_located n sm0))
                                             (fun sm0 r -> b2t (r = (greveal n).frequency))
assume val read_zero_child: n:located node -> PureMem (located node)
                                              (fun sm0 -> b2t (live_located n sm0))
                                              (fun sm0 r -> b2t (r = (greveal n).zero_child))
assume val read_one_child: n:located node -> PureMem (located node)
                                             (fun sm0 -> b2t (live_located n sm0))
                                             (fun sm0 r -> b2t (r = (greveal n).one_child))
assume val read_symbol: n:located node -> PureMem symbol_t
                                          (fun sm0 -> b2t (live_located n sm0))
                                          (fun sm0 r -> b2t (r = (greveal n).symbol))
assume val read_code: n:located node -> PureMem (lref string)
                                        (fun sm0 -> b2t (live_located n sm0))
                                        (fun sm0 r -> b2t (r = (greveal n).code))

(* mk *)
assume val mk_node: f:lref int -> z:located node -> o:located node -> s:symbol_t -> c:lref string
                    -> PureMem (located node)
                       (fun sm0 -> isNonEmpty (st sm0) /\
                                   refIsLive f sm0 /\ live_node z sm0 /\ live_node o sm0 /\ refIsLive c sm0)
                       (fun sm0 r -> isNonEmpty (st sm0) /\ regionOf r = InStack (topRegionId sm0) /\
                                     (greveal r).frequency = f  /\
                                     (greveal r).zero_child = z /\
                                     (greveal r).one_child = o  /\
                                     (greveal r).symbol = s     /\
                                     (greveal r).code = c       /\
                                     live_node r sm0)

assume val mk_null_node: unit -> PureMem (located node)
                                 (fun sm0 -> b2t (isNonEmpty (st sm0)))
                                 (fun sm0 r -> isNonEmpty (st sm0) /\ regionOf r = InStack (topRegionId sm0) /\
                                               live_node r sm0 /\
                                               lookupRef (greveal r).frequency sm0 = -1)

val is_null: n:located node -> PureMem bool
                               (fun sm0 -> b2t (live_node n sm0))
                               (fun sm0 r -> live_node n sm0 /\
                                             (r = (lookupRef (greveal n).frequency sm0 = -1)))
let is_null n = memread (read_frequency n) = -1

(**********)

(* NodeList module *)

type node_list = lref (list (located node))  // list is on heap

val live_list: l:list (located node) -> sm:smem -> GTot bool
let rec live_list l sm = match l with
  | []     -> true
  | hd::tl -> live_node hd sm && live_list tl sm

val live_list_after_write_lemma: #a:Type -> rw:(lref a) -> v:a
                                 -> l:list (located node) -> m:smem{live_list l m}
                                 -> Lemma (requires (True))
                                          (ensures (live_list l (writeMemAux rw m v)))
                                    [SMTPat (writeMemAux rw m v); SMTPat (live_list l m)]
let rec live_list_after_write_lemma rw v l m = match l with
  | []     -> ()
  | hd::tl -> live_list_after_write_lemma rw v tl m

val live_list_after_ralloc_lemma: #a:Type -> r:(lref a) -> v:a -> l:list (located node)
                            -> m:smem{isNonEmpty (st m) /\ not (contains (topRegion m) r) /\ live_list l m}
                            -> Lemma (requires (True))
                                     (ensures (live_list l (allocateInTopR r v m)))
                               [SMTPat (allocateInTopR r v m); SMTPat (live_list l m)]
let rec live_list_after_ralloc_lemma r v l m = match l with
  | []     -> ()
  | hd::tl -> live_list_after_ralloc_lemma r v tl m

val live_node_list: l:node_list -> sm:smem -> GTot bool
let live_node_list l sm = refIsLive l sm && live_list (lookupRef l sm) sm

val new_list: unit -> Mem node_list (fun m0 -> True) (fun m0 r m1 -> b2t (live_node_list r m1)) (hide (Set.empty))
let new_list _ = halloc []

val is_empty: l:node_list -> PureMem bool
                             (fun m0 -> b2t (live_node_list l m0))
                             (fun m0 r -> live_node_list l m0 /\ r = (lookupRef l m0 =  []))
let is_empty l = (memread l = [])

val is_singleton: l:node_list -> PureMem bool
                                 (fun m0 -> b2t (live_node_list l m0))
                                 (fun m0 r -> live_node_list l m0 /\ r = (is_Cons (lookupRef l m0) &&
                                                                          Cons.tl (lookupRef l m0) = []))
let is_singleton l = match (memread l) with
  | _::[] -> true
  | _     -> false

val pop_two: l:node_list -> Mem (located node * located node)
                            (fun m0 -> live_node_list l m0 /\
                                       is_Cons (lookupRef l m0) /\
                                       is_Cons (Cons.tl (lookupRef l m0)))
                            (fun m0 r m1 -> live_node_list l m0                 /\
                                            is_Cons (lookupRef l m0)           /\
                                            is_Cons (Cons.tl (lookupRef l m0)) /\
                                            live_node (fst r) m1                /\
                                            live_node (snd r) m1                /\
                                            live_node_list l m1                 /\
                                            lookupRef l m1 = (Cons.tl (Cons.tl (lookupRef l m0))))
                            (hide (Set.singleton (Ref l)))
let pop_two l = match (memread l) with
  | hd::hd'::tl ->
    memwrite l tl;
    hd, hd'

val contents: l:node_list -> PureMem (list (located node)) (fun m0 -> b2t (live_node_list l m0))
                                                           (fun m0 r -> live_node_list l m0 /\
                                                                        r = lookupRef l m0)
let contents l = memread l                                                                        

val insert_in_ordered_list: n:located node -> l:list (located node)
                            -> PureMem (list (located node))
                               (fun m0 -> live_node n m0 /\ live_list l m0)
                               (fun m0 r -> live_node n m0                    /\
                                            live_list l m0                    /\
                                            live_list r m0                    /\
                                            List.mem n r                      /\
                                            (forall n'. List.mem n' l ==> List.mem n' r))
let rec insert_in_ordered_list n l = match l with
  | []     -> [n]
  | hd::tl ->
    let f = memread (read_frequency n) in
    let f' = memread (read_frequency hd) in
    if f <= f' then
      n::hd::tl
    else    
      let tl' = insert_in_ordered_list n tl in
      hd::tl'

val insert_in_ordered_node_list:
  n:located node -> l:node_list
  -> Mem unit (fun m0 -> live_node n m0 /\ live_node_list l m0)
              (fun m0 _ m1 -> live_node n m0               /\
                              live_node_list l m0          /\
                              live_node_list l m1          /\
                              List.mem n (lookupRef l m1) /\
                              (forall n'. List.mem n' (lookupRef l m0) ==> List.mem n' (lookupRef l m1)))
              (hide (Set.singleton (Ref l)))
let insert_in_ordered_node_list n l =
  let r = insert_in_ordered_list n (memread l) in
  memwrite l r

(**********)

type data = sstarray symbol_t

type histogram = sstarray (located node)

val live_histogram_arr: h:sstarray (located node) -> sm:smem{liveArr sm h}
                        -> i:nat{i <= glength h sm}
                        -> GTot (r:bool{r ==> (forall (j:nat). (j >= i /\ j < glength h sm) ==> live_node (gindex h sm j) sm)})
                           (decreases (glength h sm - i))
let rec live_histogram_arr h sm i =
  if i = glength h sm then true
  else
    live_node (gindex h sm i) sm && live_histogram_arr h sm (i + 1)

val live_hist_arr_after_write: #a:Type -> rw:(lref a) -> v:a
                           -> h:histogram{reveal (asRef h) =!= rw} -> i:nat
                           -> m:smem{liveArr m h /\ i <= glength h m /\ live_histogram_arr h m i}
                           -> m':smem{m' = writeMemAux rw m v}
                           -> GTot (u:unit{liveArr m' h /\ i <= glength h m' /\ live_histogram_arr h m' i})
                              (decreases (glength h m - i))
let rec live_hist_arr_after_write rw v h i m m' =
  if i = glength h m then ()
  else live_hist_arr_after_write rw v h (i + 1) m m'

val live_hist_arr_after_ralloc: #a:Type -> r:(lref a) -> v:a -> h:histogram{reveal (asRef h) =!= r} -> i:nat
                            -> m:smem{isNonEmpty (st m) /\ not (contains (topRegion m) r) /\
                                      liveArr m h /\ i <= glength h m /\ live_histogram_arr h m i}
                            -> m':smem{m' = allocateInTopR r v m}
                            -> GTot (u:unit{liveArr m' h /\ i <= glength h m' /\ live_histogram_arr h m' i})
                               (decreases (glength h m - i))
let rec live_hist_arr_after_ralloc r v h i m m' =
  if i = glength h m then ()
  else live_hist_arr_after_ralloc r v h (i + 1) m m'

val live_hist_arr_after_write_lemma: #a:Type -> rw:(lref a) -> v:a
                           -> h:histogram{reveal (asRef h) =!= rw} -> i:nat
                           -> m:smem{liveArr m h /\ i <= glength h m /\ live_histogram_arr h m i}
                           -> m':smem{m' = writeMemAux rw m v}
                           -> Lemma (requires (True))
                              (ensures (liveArr m' h /\ i <= glength h m' /\ live_histogram_arr h m' i))
                              [SMTPat (live_histogram_arr h m i); SMTPat (live_histogram_arr h m' i); SMTPat (writeMemAux rw m v)]
let live_hist_arr_after_write_lemma rw v h i m m' = admit ()

val live_hist_arr_after_ralloc_lemma: #a:Type -> r:(lref a) -> v:a -> h:histogram{reveal (asRef h) =!= r} -> i:nat
                            -> m:smem{isNonEmpty (st m) /\ not (contains (topRegion m) r) /\
                                      liveArr m h /\ i <= glength h m /\ live_histogram_arr h m i}
                            -> m':smem{m' = allocateInTopR r v m}
                            -> Lemma (requires (True))
                               (ensures (liveArr m' h /\ i <= glength h m' /\ live_histogram_arr h m' i))
                               [SMTPat (live_histogram_arr h m i); SMTPat (live_histogram_arr h m' i); SMTPat (allocateInTopR r v m)]
let live_hist_arr_after_ralloc_lemma r v h i m m' = admit ()

val live_histogram: h:histogram -> sm:smem -> GTot (r:bool{r ==> (liveArr sm h /\
                                                                  (forall i. (i >= 0 /\ i < glength h sm) ==>
                                                                              live_node (gindex h sm i) sm))})
let live_histogram h sm = liveArr sm h && live_histogram_arr h sm 0

val live_hist_after_write_lemma: #a:Type -> rw:(lref a) -> v:a
                           -> h:histogram{reveal (asRef h) =!= rw}
                           -> m:smem{live_histogram h m}
                           -> m':smem{m' = writeMemAux rw m v}
                           -> Lemma (requires (True))
                              (ensures (live_histogram h m'))
                              [SMTPat (live_histogram h m); SMTPat (live_histogram h m'); SMTPat (writeMemAux rw m v)]                              
let live_hist_after_write_lemma rw v h m m' = ()

val live_hist_after_ralloc_lemma: #a:Type -> r:(lref a) -> v:a -> h:histogram{reveal (asRef h) =!= r}
                            -> m:smem{isNonEmpty (st m) /\ not (contains (topRegion m) r) /\
                                      live_histogram h m}
                            -> m':smem{m' = allocateInTopR r v m}
                            -> Lemma (requires (True))
                               (ensures (live_histogram h m'))
                               [SMTPat (live_histogram h m); SMTPat (live_histogram h m'); SMTPat (allocateInTopR r v m)]
let live_hist_after_ralloc_lemma r v h m m' = ()

val compute_histogram: d:data -> h:histogram -> i:nat
                       -> RST unit
                          (fun m0 -> isNonEmpty (st m0)                        /\
                                     liveArr m0 d /\ live_histogram h m0       /\
                                     glength h m0 = symbol_value_bound /\
                                     i <= glength d m0)
                          (fun m0 r m1 -> isNonEmpty (st m0)                        /\
                                          liveArr m0 d /\ live_histogram h m0       /\
                                          glength h m0 = symbol_value_bound /\
                                          i <= glength d m0 /\ isNonEmpty (st m1))
                                                                   (*/\
                                          isNonEmpty (st m1))*)
                                                                 (*/\
                                          liveArr m1 d ) /\ live_histogram h m1)*)
let compute_histogram d h i =
  if i = RSTArray.length d then ()
  else
    let sym = RSTArray.readIndex d i in    
    let the_leaf = RSTArray.readIndex h sym in
    if is_null the_leaf then
      let the_leaf' = mk_node (ralloc 1) (mk_null_node ()) (mk_null_node ()) sym (ralloc "") in
      RSTArray.writeIndex h sym the_leaf'
    else admit ()
      //memwrite (the_leaf.frequency) ((memread the_leaf.frequency) + 1)



(*val insert_in_ordered_list: n:located node -> l:node_list
                            -> RST unit
                               (fun sm0 -> live_ghost_list n sm0 /\ live_node n sm0 /\ live_node_list l sm0)
                               (fun sm0 _ sm1 -> live_ghost_list n sm0 /\ live_node n sm0 /\ live_node_list l sm0 /\
                                                 live_ghost_list n sm1) ///\ live_node n sm1 /\ live_node_list l sm1)
                                (*/\ live_node n sm1 /\ live_node_list l sm1 /\
                                                 sids sm0 = sids sm1 /\ canModify sm0 sm1 (get_modset_for_list_insert l sm0 (hide Set.empty)))*)
                               (*(fun sm0 _ sm1 -> live_node n sm0 /\ live_node_list l sm0 /\ live_node n sm1 /\ live_node_list l sm1 /\
                                                 sids sm0 = sids sm1 /\ canModify sm0 sm1 (get_modset_for_list_insert l sm0 (hide Set.empty)))*)
let rec insert_in_ordered_list n l =
  let n = memread l in
  if is_null n then
    let _ = memwrite l n in
    admit () // TODO: FIXME: at this point writeMemAuxPreservesExists should fire, but it doesn't
  else admit ()
    (*let f1 = memread (read_frequency n) in
    let f2 = memread (read_frequency (memread l)) in
    if f1 <= f2 then
      let n = memread l in    // located node
      let _ = memwrite (read_next n) (memread l) in
      let _ = memwrite l n in
      admit ()    // need to set the ghost list field
    else
      admit ()*)

(* check_marker *)
(*
(*
 * Nodes are not yet allocated on stack, would really like the located t and
 * regionOf change (on-going discussion with Abhishek) before attempting that.
 * When that happens, how do we write predicate on top most region before and after
 * all refs point to same value after a pair is allocated on top most region ?
 *)
assume val mk_node: f:lref int -> n:lref node -> z:node -> o:node -> s:symbol_t -> c:lref string
                    -> PureMem node
                       (fun sm0 -> refIsLive f sm0 /\ refIsLive n sm0 /\ refIsLive c sm0)
                       (fun sm0 r -> live_node r sm0)

type live_histogram (h:sstarray node) (sm:smem) =
  liveArr sm h /\
  (forall (i:nat). i < glength h sm ==> live_node (gindex h sm i) sm)

(*
 * Thus far only ensure that non empty regions in sm1, so that pop succeeds in caller
 *)
val compute_histogram: sstream: sstarray symbol_t -> histogram: sstarray node
                       -> i:nat
                       -> RST unit
                          (fun sm0 -> isNonEmpty (st sm0)                                    /\
                                      liveArr sm0 sstream /\ live_histogram histogram sm0    /\
                                      glength histogram sm0 = symbol_value_bound             /\
                                      i <= glength sstream sm0)
                          (fun sm0 r sm1 -> b2t (isNonEmpty (st sm1)))
let rec compute_histogram sstream histogram i =
  if i = RSTArray.length sstream then ()
  else
    let sym = RSTArray.readIndex sstream i in
    let the_leaf = RSTArray.readIndex histogram sym in
    if is_null the_leaf then
      let the_leaf' = mk_node (ralloc 1) (ralloc (null_node ())) (null_node ()) (null_node ()) sym (ralloc "") in
      RSTArray.writeIndex histogram sym the_leaf'
    else
      memwrite (the_leaf.frequency) ((memread the_leaf.frequency) + 1)

val build_huffman_tree: histogram: sstarray node
                        -> RST node
                           (fun sm0 -> isNonEmpty (st sm0) /\ live_histogram histogram sm0)
                           (fun sm0 r sm1 -> b2t (isNonEmpty (st sm1)))
let build_huffman_tree histogram =
  admit ()
                                   

val huffman_encode: sstream:sstarray symbol_t -> estream:sstarray byte
                    -> RST (sstarray byte * nat * nat)
                       (fun sm0 -> liveArr sm0 sstream /\ liveArr sm0 estream /\
                                   glength sstream sm0 = glength estream sm0)
                       (fun sm0 r sm1 -> True)
let huffman_encode sstream estream =
  pushRegion ();
  let histogram = screate symbol_value_bound (null_node ()) in
  compute_histogram sstream histogram 0;
  let tree = build_huffman_tree histogram in
  popRegion ();
  admit ()
  *)*)
