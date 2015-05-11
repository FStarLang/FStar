module GC

(* invariants *)
type color =
 | Unalloc
 | White
 | Gray
 | Black

assume val mem_lo : x:int{0 < x}
assume val mem_hi : x:int{mem_lo <= x}
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
type ptr_lifts_to (to_abs:abs_map) (ptr:mem_addr) (abs:abs_node) : Type =
  valid abs
  /\ to_abs ptr = abs

type obj_inv (i:mem_addr) (to_abs:abs_map) (abs_fields:abs_field_map) (fields:field_map) =
  valid (to_abs i)
  /\ ptr_lifts_to to_abs (fields i F1) (abs_fields (to_abs i) F1)
  /\ ptr_lifts_to to_abs (fields i F2) (abs_fields (to_abs i) F2)

type gc_inv (color:color_map) (to_abs:abs_map) (abs_fields:abs_field_map) (fields:field_map) =
  to_abs_inj to_abs
  /\ (forall (i:mem_addr).
        obj_inv i to_abs abs_fields fields
        /\ (color i = Black ==> color (fields i F1) <> White
                             /\ color (fields i F2) <> White)
        /\ not (valid (to_abs i)) <==> color i = Unalloc)

type mutator_inv (color:color_map) (to_abs:abs_map) (abs_fields:abs_field_map) (fields:field_map) =
  to_abs_inj to_abs
  /\ (forall (i:mem_addr).
        obj_inv i to_abs abs_fields fields
        /\ (color i = Unalloc \/ color i = White)
        /\ not (valid (to_abs i)) <==> color i = Unalloc)
