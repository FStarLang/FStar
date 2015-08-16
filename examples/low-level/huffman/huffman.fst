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

assume val symbol_value_bound: nat

type symbol_t = n:nat{n < symbol_value_bound}

type node =
  { frequency: lref int;
    next: lref node;
    zero_child: node;
    one_child: node;
    symbol: symbol_t;
    code: lref string
  }

val live_node: n:node -> sm:smem -> GTot bool
let live_node n sm =
  liveRef n.frequency sm && liveRef n.next sm && liveRef n.code sm

assume val null_node: unit -> PureMem node (fun sm0 -> True) (fun sm0 r -> b2t (live_node r sm0))

val is_null: n:node -> PureMem bool (fun sm -> b2t (live_node n sm)) (fun sm r -> True)
let is_null n = memread n.frequency = -1

val g_is_null: n:node -> sm:smem{live_node n sm} -> GTot bool
let g_is_null n sm = loopkupRef (n.frequency) sm = -1

type node_list = lref node

val live_node_list: l:node_list -> sm:smem{liveRef l sm} -> GTot bool
let rec live_node_list l sm =
  let n = loopkupRef l sm in
  if not (live_node n sm) then false
  else
    if g_is_null n sm then true
    else
      live_node_list n.next sm

val is_empty: l:node_list -> PureMem bool (fun sm0 -> )

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
  