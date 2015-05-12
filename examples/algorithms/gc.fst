(*--build-config
    options:--max_ifuel 1 --initial_ifuel 1 --max_fuel 1 --initial_fuel 1;
    other-files:
  --*)
module GC

(* invariants *)
type color =
 | Unalloc
 | White
 | Gray
 | Black

assume val mem_lo : x:int{0 < x}
assume val mem_hi : x:int{mem_lo < x}
let is_mem_addr i = mem_lo <= i && i < mem_hi

type field =
  | F1
  | F2

assume type abs_node
assume val no_abs : abs_node
let valid a = a <> no_abs
type valid_node = a:abs_node{valid a}

type mem_addr  = i:int{is_mem_addr i}
type color_map = mem_addr -> Tot color
type abs_map   = mem_addr -> Tot abs_node

type field_map     = mem_addr -> field -> Tot mem_addr
type abs_field_map = abs_node -> field -> Tot abs_node

(* Invariant: to_abs is injective *)
type to_abs_inj (to_abs:abs_map) =
  forall (i1:mem_addr) (i2:mem_addr).
    valid (to_abs i1)
    /\ valid (to_abs i2)
    /\ i1 <> i2
    ==> to_abs i1 <> to_abs i2

(*
Note: the default inferred type infers ('a -> 'b) to to_abs
      which includes an unwanted effect
*)
type gc_state = {
  to_abs: abs_map;
  color: color_map;
  abs_fields: abs_field_map;
  fields: field_map
}

opaque type ptr_lifts gc_state (ptr:mem_addr) : Type =
  b2t (valid (gc_state.to_abs ptr))

opaque type ptr_lifts_to gc_state (ptr:mem_addr) (abs:abs_node) : Type =
  valid abs
  /\ gc_state.to_abs ptr = abs

opaque type obj_inv gc_state (i:mem_addr) =
  valid (gc_state.to_abs i)
  ==> (ptr_lifts_to gc_state (gc_state.fields i F1) (gc_state.abs_fields (gc_state.to_abs i) F1)
   /\  ptr_lifts_to gc_state (gc_state.fields i F2) (gc_state.abs_fields (gc_state.to_abs i) F2))

(* Maybe derive gc_inv from mutator_inv? via some higher-orderness *)
opaque type gc_inv gc_state =
  to_abs_inj gc_state.to_abs
  /\ (forall (i:mem_addr).
        obj_inv gc_state i
        /\ (gc_state.color i = Black ==> (gc_state.color (gc_state.fields i F1) <> White
                                       /\ gc_state.color (gc_state.fields i F2) <> White))
        /\ (not (valid (gc_state.to_abs i)) <==> gc_state.color i = Unalloc))

opaque logic type trigger (i:int) = True
opaque type mutator_inv gc_state =
  to_abs_inj gc_state.to_abs
  /\ (forall (i:mem_addr).{:pattern (trigger i)}
        obj_inv gc_state i /\
        (gc_state.color i = Unalloc \/ gc_state.color i = White) /\
        (not (valid (gc_state.to_abs i)) <==> gc_state.color i = Unalloc))

new_effect GC_STATE = STATE_h gc_state
kind GCPost (a:Type) = a -> gc_state -> Type
sub_effect
  DIV   ~> GC_STATE = fun (a:Type) (wp:PureWP a) (p:GCPost a) (gc:gc_state) -> wp (fun a -> p a gc)

effect GC (a:Type) (pre:gc_state -> Type) (post: gc_state -> GCPost a) =
       GC_STATE a
             (fun (p:GCPost a) (gc:gc_state) ->
                  pre gc /\ (forall a gc'. (pre gc /\ post gc a gc') ==> p a gc')) (* WP *)
             (fun (p:GCPost a) (gc:gc_state) ->
                  (forall a gc'. (pre gc /\ post gc a gc') ==> p a gc'))           (* WLP *)

effect GCMut (res:Type) (req:gc_state -> Type) (ens:gc_state -> GCPost res) =
       GC res (fun gc -> req gc /\ mutator_inv gc)
              (fun gc res gc' -> ens gc res gc' /\ mutator_inv gc')

assume val get : unit -> GC gc_state (fun gc -> True) (fun gc res gc' -> gc=gc' /\ res=gc')
assume val set : g:gc_state -> GC unit (fun gc -> True) (fun _ _ gc' -> b2t(g=gc'))

type init_invariant (ptr:mem_addr) (gc:gc_state) =
  forall i. mem_lo <= i /\ i < ptr
        ==> not(valid (gc.to_abs i))
         /\ gc.color i = Unalloc

val upd_map: #a:Type -> #b:Type -> (a -> Tot b) -> a -> b -> a -> Tot b
let upd_map f i v = fun j -> if i=j then v else f j

val aux_init : ptr:mem_addr -> GC unit
                            (requires (init_invariant ptr))
                            (ensures (fun gc _ gc' -> mutator_inv gc'))
let rec aux_init ptr =
  let gc = get () in
  let gc' = {gc with
      color=upd_map gc.color ptr Unalloc;
      to_abs=upd_map gc.to_abs ptr no_abs
    } in
  set gc';
  if ptr + 1 < mem_hi then aux_init (ptr + 1)

val initialize: unit -> GC unit
    (requires (fun g -> True))
    (ensures (fun g _ g' -> mutator_inv g'))
let initialize () = aux_init mem_lo  (* TODO: hoisting aux is super ugly ... fix! *)

val read_field : ptr:mem_addr -> f:field -> GCMut mem_addr
  (requires (fun gc -> ptr_lifts_to gc ptr (gc.to_abs ptr)))
  (ensures (fun gc i gc' -> gc=gc'
            /\ ptr_lifts_to gc' i (gc.abs_fields (gc.to_abs ptr) f)))
let read_field ptr f =
  cut (trigger ptr);
  let gc = get () in
  gc.fields ptr f

val upd_field: field_map
            -> mem_addr
            -> field
            -> mem_addr
            -> Tot field_map
let upd_field m i f v =
  fun j g -> if (i, f) = (j, g) then v else m j g

val upd_abs_field: abs_field_map
            -> abs_node
            -> field
            -> abs_node
            -> Tot abs_field_map
let upd_abs_field m i f v =
  fun j g -> if (i, f) = (j, g) then v else m j g

opaque type obj_inv' gc_state (i:mem_addr) =
    valid (gc_state.to_abs i)
    ==> (ptr_lifts_to gc_state (gc_state.fields i F1) (gc_state.abs_fields (gc_state.to_abs i) F1)
     /\  ptr_lifts_to gc_state (gc_state.fields i F2) (gc_state.abs_fields (gc_state.to_abs i) F2))

opaque type mutator_inv' gc_state =
    to_abs_inj gc_state.to_abs
    /\ (forall (i:mem_addr).//{:pattern (trigger i)}
          obj_inv' gc_state i /\
          (gc_state.color i = Unalloc \/ gc_state.color i = White) /\
          (not (valid (gc_state.to_abs i)) <==> gc_state.color i = Unalloc) /\
          True
          )
module VerifyThis
open GC
(*val write_field: ptr:mem_addr -> f:field -> v:mem_addr -> GC unit
  (requires (fun gc -> ptr_lifts gc ptr /\ ptr_lifts gc v /\ mutator_inv' gc))
  (ensures (fun gc _ gc' ->
              to_abs_inj gc'.to_abs
                /\ obj_inv gc' ptr
                /\ obj_inv gc' v /\
                (*/\ mutator_inv gc' /\*)
                (*/\ (forall (i:mem_addr).{:pattern (trigger i)}
                      obj_inv gc' i /\
                      (*(gc'.color i = Unalloc \/ gc'.color i = White) /\*)
                      (*(not (valid (gc'.to_abs i)) <==> gc'.color i = Unalloc)*)
                      True
                      )) /\*)
              gc'.color=gc.color /\
              gc'.to_abs = gc.to_abs /\
              gc'.abs_fields
               = upd_map #(abs_node * field) #abs_node gc.abs_fields (gc.to_abs ptr, f) (gc.to_abs v)))*)
val write_field: ptr:mem_addr -> f:field -> v:mem_addr -> GC unit
 (requires (fun gc -> ptr_lifts_to gc ptr (gc.to_abs ptr)
                   /\ ptr_lifts_to gc v (gc.to_abs v)
                   /\ mutator_inv' gc))
 (ensures (fun gc _ gc' -> True))
let write_field ptr f v =
  let gc = get () in
  (*assert (obj_inv gc v);*)
  let gc' = {gc with
    (*color=upd_map gc.color ptr (gc.color ptr)*)
    fields=upd_field gc.fields ptr f v;//(gc.fields ptr f);
    abs_fields=upd_abs_field gc.abs_fields (gc.to_abs ptr) f (gc.to_abs v);//(gc.fields ptr f));//v)
    } in
  (*assert (valid (gc'.to_abs v));
  assert (v<>ptr ==> gc'.abs_fields (gc'.to_abs v, f) = gc.abs_fields (gc.to_abs v, f));
  assert (v<>ptr ==> gc'.fields (v, f) = gc.fields (v, f));
  assert (ptr_lifts_to gc' (gc'.fields (v, f)) (gc'.abs_fields (gc'.to_abs v, f)));
  assert (obj_inv gc' v);
  assert (obj_inv gc' ptr);
  assert (mutator_inv gc);*)
  assert (mutator_inv' gc');
  admit();
  set gc'
