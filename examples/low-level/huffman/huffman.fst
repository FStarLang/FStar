(*--build-config
    variables:LIB=../../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/set.fst $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst ../stack.fst ../listset.fst
    $LIB/ghost.fst ../located.fst ../lref.fst ../stackAndHeap.fst ../sst.fst ../sstCombinators.fst $LIB/constr.fst ../word.fst $LIB/seq.fsi $LIB/seq.fst ../array.fsi
     ../array.fst ../MD5Common.fst ../arrayAlgos.fst
  --*)

module Huffman

open SST
open SSTArray
open ArrayAlgos

open StackAndHeap
open Stack

open Lref
open Located

open Ghost

assume val symbol_value_bound: nat

type symbol_t = n:nat{n < symbol_value_bound}

type erased_heap_list (a:Type) = erased (r:lref (list a){regionOf r = InHeap})

type node =
  { frequency: lref int;
    next: lref (located node);
    zero_child: located node;
    one_child: located node;
    symbol: symbol_t;
    code: lref string;
    
    ghost_list: erased_heap_list (located node)    // ghost list to keep elements of linked list
  }

val contains_region: sidt -> memStack -> Tot bool
let contains_region id st = List.mem id (ssids st)

val live_located: #a:Type -> located a -> smem -> Tot bool
let live_located x sm = match regionOf x with
  | InHeap     -> true
  | InStack id -> contains_region id (snd sm)

assume val ghost_lreveal: #a:Type -> x:located a -> GTot (r:a{regionOf x = InHeap ==> r = unlocate x})

val live_ghost_list: n:located node -> sm:smem -> GTot bool
let live_ghost_list n sm = liveRef (reveal (ghost_lreveal n).ghost_list) sm

(* live_node also ensures that the linked list is live  *)
val live_node: n:located node -> sm:smem{live_ghost_list n sm}
               -> GTot bool (decreases (List.length (loopkupRef (reveal ((ghost_lreveal n).ghost_list)) sm)))
let rec live_node n sm =
  if live_located n sm then
    let n = ghost_lreveal n in
    if liveRef n.frequency sm && liveRef n.next sm && liveRef n.code sm &&
       live_located n.zero_child sm && live_located n.one_child sm then
      let l = loopkupRef (reveal n.ghost_list) sm in
      match l with
        | []     -> loopkupRef n.frequency sm = -1    // meaning that the node is also null_node defined below
        | hd::tl ->
          loopkupRef n.frequency sm <> -1 &&
          hd = loopkupRef n.next sm && live_ghost_list hd sm &&
          tl = loopkupRef (reveal (ghost_lreveal hd).ghost_list) sm && live_node hd sm
    else
      false
  else
    false

(* projectors *)
assume val read_frequency: n:located node -> PureMem (lref int)
                                             (fun sm0 -> b2t (live_located n sm0))
                                             (fun sm0 r -> b2t (r = (ghost_lreveal n).frequency))
assume val read_next: n:located node -> PureMem (lref (located node))
                                        (fun sm0 -> b2t (live_located n sm0))
                                        (fun sm0 r -> b2t (r = (ghost_lreveal n).next))
assume val read_zero_child: n:located node -> PureMem (located node)
                                              (fun sm0 -> b2t (live_located n sm0))
                                              (fun sm0 r -> b2t (r = (ghost_lreveal n).zero_child))
assume val read_one_child: n:located node -> PureMem (located node)
                                             (fun sm0 -> b2t (live_located n sm0))
                                             (fun sm0 r -> b2t (r = (ghost_lreveal n).one_child))
assume val read_symbol: n:located node -> PureMem symbol_t
                                          (fun sm0 -> b2t (live_located n sm0))
                                          (fun sm0 r -> b2t (r = (ghost_lreveal n).symbol))
assume val read_code: n:located node -> PureMem (lref string)
                                        (fun sm0 -> b2t (live_located n sm0))
                                        (fun sm0 r -> b2t (r = (ghost_lreveal n).code))
assume val read_ghost_list: n:located node -> PureMem (erased_heap_list (located node))
                                                      (fun sm0 -> b2t (live_located n sm0))
                                                      (fun sm0 r -> b2t (r = (ghost_lreveal n).ghost_list))
(* mk *)
assume val mk_node: f:lref int -> n:lref (located node) -> z:located node -> o:located node
                    -> s:symbol_t -> c:lref string
                    -> PureMem (located node)
                       (fun sm0 -> isNonEmpty (st sm0) /\
                                   liveRef f sm0 /\ liveRef n sm0 /\ live_located z sm0 /\
                                   live_located o sm0 /\ liveRef c sm0)
                       (fun sm0 r -> isNonEmpty (st sm0) /\ regionOf r = InStack (topstid sm0) /\
                                     (ghost_lreveal r).frequency = f  /\
                                     (ghost_lreveal r).next = n       /\
                                     (ghost_lreveal r).zero_child = z /\
                                     (ghost_lreveal r).one_child = o  /\
                                     (ghost_lreveal r).symbol = s     /\
                                     (ghost_lreveal r).code = c       /\
                                     live_ghost_list r sm0            /\
                                     live_node r sm0)

assume val mk_null_node: unit -> PureMem (located node)
                                 (fun sm0 -> b2t (isNonEmpty (st sm0)))
                                 (fun sm0 r -> isNonEmpty (st sm0) /\ regionOf r = InStack (topstid sm0) /\
                                               live_ghost_list r sm0 /\
                                               live_node r sm0 /\
                                               loopkupRef (ghost_lreveal r).frequency sm0 = -1 /\
                                               loopkupRef (reveal (ghost_lreveal r).ghost_list) sm0 = [])

val is_null: n:located node -> PureMem bool
                       (fun sm0 -> live_ghost_list n sm0 /\ live_node n sm0)
                       (fun sm0 r -> live_ghost_list n sm0 /\ live_node n sm0 /\
                                     (r <==> (loopkupRef (ghost_lreveal n).frequency sm0 = -1)))
                                              //TODO: loopkupRef (reveal (ghost_lreveal n).ghost_list) sm0 = [])))
let is_null n = memread (read_frequency n) = -1

val is_nullT: n:located node -> sm:smem{live_ghost_list n sm /\ live_node n sm}
              -> GTot (r:bool{r <==> (loopkupRef (ghost_lreveal n).frequency sm = -1)})
                                      //TODO: reveal (ghost_lreveal n).ghost_list = [])})
let is_nullT n sm = loopkupRef (ghost_lreveal n).frequency sm = -1

type node_list = lref (located node)

val live_node_list: l:node_list -> sm:smem -> GTot bool
let live_node_list l sm = liveRef l sm && live_ghost_list (loopkupRef l sm) sm && live_node (loopkupRef l sm) sm

(*val get_modset_for_list_insert: l:node_list -> sm:smem{live_node_list l sm} -> s:modset
                                -> GTot modset
                                   (decreases (List.length (reveal (ghost_lreveal (loopkupRef l sm)).ghost_list)))
let rec get_modset_for_list_insert l sm s =
  let n = loopkupRef l sm in
  if is_nullT n sm then eunion s (only l)
  else
    let s' = get_modset_for_list_insert (ghost_lreveal n).next sm s in
    eunion s' (only l)*)
    
val insert_in_ordered_list: n:located node -> l:node_list
                            -> SST unit
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
                       (fun sm0 -> liveRef f sm0 /\ liveRef n sm0 /\ liveRef c sm0)
                       (fun sm0 r -> live_node r sm0)

type live_histogram (h:sstarray node) (sm:smem) =
  liveArr sm h /\
  (forall (i:nat). i < glength h sm ==> live_node (gindex h sm i) sm)

(*
 * Thus far only ensure that non empty regions in sm1, so that pop succeeds in caller
 *)
val compute_histogram: sstream: sstarray symbol_t -> histogram: sstarray node
                       -> i:nat
                       -> SST unit
                          (fun sm0 -> isNonEmpty (st sm0)                                    /\
                                      liveArr sm0 sstream /\ live_histogram histogram sm0    /\
                                      glength histogram sm0 = symbol_value_bound             /\
                                      i <= glength sstream sm0)
                          (fun sm0 r sm1 -> b2t (isNonEmpty (st sm1)))
let rec compute_histogram sstream histogram i =
  if i = SSTArray.length sstream then ()
  else
    let sym = SSTArray.readIndex sstream i in
    let the_leaf = SSTArray.readIndex histogram sym in
    if is_null the_leaf then
      let the_leaf' = mk_node (salloc 1) (salloc (null_node ())) (null_node ()) (null_node ()) sym (salloc "") in
      SSTArray.writeIndex histogram sym the_leaf'
    else
      memwrite (the_leaf.frequency) ((memread the_leaf.frequency) + 1)

val build_huffman_tree: histogram: sstarray node
                        -> SST node
                           (fun sm0 -> isNonEmpty (st sm0) /\ live_histogram histogram sm0)
                           (fun sm0 r sm1 -> b2t (isNonEmpty (st sm1)))
let build_huffman_tree histogram =
  admit ()
                                   

val huffman_encode: sstream:sstarray symbol_t -> estream:sstarray byte
                    -> SST (sstarray byte * nat * nat)
                       (fun sm0 -> liveArr sm0 sstream /\ liveArr sm0 estream /\
                                   glength sstream sm0 = glength estream sm0)
                       (fun sm0 r sm1 -> True)
let huffman_encode sstream estream =
  pushStackFrame ();
  let histogram = screate symbol_value_bound (null_node ()) in
  compute_histogram sstream histogram 0;
  let tree = build_huffman_tree histogram in
  popStackFrame ();
  admit ()
  *)