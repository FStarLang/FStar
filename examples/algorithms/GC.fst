(* Copyright Microsoft Research 2015

   This module is an adaptation of Chris Hawblitzel and Erez Petrank's
   simplified mark-sweep collector from the POPL 2009 paper
   "Automated Verification of Practical Garbage Collectors"

   While this module states and proves the same properties as the paper,
   its implementation is currently still quite high-level, e.g, it
   uses lots of recursive functions instead of while loops with mutable
   local variables. Going lower level with this module is work in progress.
*)
module GC

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

assume type abs_node : a:Type0{hasEq a}
assume val no_abs : abs_node
let valid a = a <> no_abs
type valid_node = a:abs_node{valid a}

type mem_addr  = i:int{is_mem_addr i}
type color_map = mem_addr -> Tot color
type abs_map   = mem_addr -> Tot abs_node

type field_map     = mem_addr * field -> Tot mem_addr
type abs_field_map = abs_node * field -> Tot abs_node

type trigger (i:int) = True

type to_abs_inj (to_abs:abs_map) =
  forall (i1:mem_addr) (i2:mem_addr).{:pattern (trigger i1); (trigger i2)}
    trigger i1 /\
    trigger i2 /\
       valid (to_abs i1)
    /\ valid (to_abs i2)
    /\ i1 <> i2
    ==> to_abs i1 <> to_abs i2

noeq type gc_state = { 
  to_abs: abs_map;
  color: color_map;
  abs_fields: abs_field_map;
  fields: field_map
}

type ptr_lifts gc_state (ptr:mem_addr) : Type =
  b2t (valid (gc_state.to_abs ptr))

type ptr_lifts_to gc_state (ptr:mem_addr) (abs:abs_node) : Type =
  valid abs
  /\ gc_state.to_abs ptr = abs

type obj_inv gc_state (i:mem_addr) =
  valid (gc_state.to_abs i)
  ==> (forall f. ptr_lifts_to gc_state (gc_state.fields (i, f)) (gc_state.abs_fields (gc_state.to_abs i, f)))

unfold type inv gc_state (color_invariant:mem_addr -> Type) =
    to_abs_inj gc_state.to_abs
    /\ (forall (i:mem_addr).{:pattern (trigger i)}
	trigger i ==>
          obj_inv gc_state i /\
          color_invariant i /\
          (not (valid (gc_state.to_abs i)) <==> gc_state.color i = Unalloc))

type gc_inv gc_state =
  inv gc_state (fun i ->
      (gc_state.color i = Black
        ==> (forall f. gc_state.color (gc_state.fields (i, f)) <> White)))

type mutator_inv gc_state =
  inv gc_state (fun i -> gc_state.color i = Unalloc \/ gc_state.color i = White)

new_effect GC_STATE = STATE_h gc_state
let gc_post (a:Type) = a -> gc_state -> Type0
sub_effect
  DIV   ~> GC_STATE = fun (a:Type) (wp:pure_wp a) (p:gc_post a) (gc:gc_state) -> wp (fun a -> p a gc)

effect GC (a:Type) (pre:gc_state -> Type0) (post: gc_state -> Tot (gc_post a)) =
       GC_STATE a
             (fun (p:gc_post a) (gc:gc_state) ->
                  pre gc /\ (forall a gc'. (pre gc /\ post gc a gc') ==> p a gc')) (* WP *)

effect GCMut (res:Type) (req:gc_state -> Type0) (ens:gc_state -> Tot (gc_post res)) =
       GC res (fun gc -> req gc /\ mutator_inv gc)
              (fun gc res gc' -> ens gc res gc' /\ mutator_inv gc')
	      
assume val get : unit -> GC gc_state (fun gc -> True) (fun gc res gc' -> gc==gc' /\ res==gc')
assume val set : g:gc_state -> GC unit (fun gc -> True) (fun _ _ gc' -> g==gc')

type init_invariant (ptr:mem_addr) (gc:gc_state) =
  forall i. mem_lo <= i /\ i < ptr
        ==> not(valid (gc.to_abs i))
         /\ gc.color i = Unalloc

val upd_map: #a:eqtype -> #b:Type -> (a -> Tot b) -> a -> b -> a -> Tot b
let upd_map #a #b f i v = fun j -> if i=j then v else f j

val upd_map2: #a:eqtype -> #b:eqtype -> #c:Type -> (a -> b -> Tot c) -> a -> b -> c -> a -> b -> Tot c
let upd_map2 #a #b #c m i f v = fun j g -> if (i,f)=(j,g) then v else m j g

val initialize: unit -> GC unit
    (requires (fun g -> True))
    (ensures (fun g _ g' -> mutator_inv g'))
let initialize () =
  let rec aux_init : ptr:mem_addr -> GC unit
                              (requires (init_invariant ptr))
                              (ensures (fun gc _ gc' -> mutator_inv gc'))
     = fun ptr ->
          let gc = get () in
          let gc' = {gc with
              color=upd_map gc.color ptr Unalloc;
              to_abs=upd_map gc.to_abs ptr no_abs
            } in
          set gc';
          if ptr + 1 < mem_hi then aux_init (ptr + 1) in
  aux_init mem_lo

val read_field : ptr:mem_addr -> f:field -> GCMut mem_addr
  (requires (fun gc -> ptr_lifts_to gc ptr (gc.to_abs ptr)))
  (ensures (fun gc i gc' -> gc==gc'
            /\ ptr_lifts_to gc' i (gc.abs_fields (gc.to_abs ptr, f))))
let read_field ptr f =
  cut (trigger ptr);
  let gc = get () in
  gc.fields (ptr, f)

val write_field: ptr:mem_addr -> f:field -> v:mem_addr -> GCMut unit
  (requires (fun gc -> ptr_lifts gc ptr /\ ptr_lifts gc v))
  (ensures (fun gc _ gc' -> gc'.color==gc.color))
let write_field ptr f v =
  cut (trigger ptr /\ trigger v);
  let gc = get () in
  let gc' = {gc with
    fields=upd_map gc.fields (ptr, f) v;
    abs_fields=upd_map gc.abs_fields (gc.to_abs ptr, f) (gc.to_abs v);
    } in
  set gc'

val mark : ptr:mem_addr -> GC unit
  (requires (fun gc -> gc_inv gc /\ trigger ptr /\ ptr_lifts gc ptr))
  (ensures (fun gc _ gc' -> gc_inv gc'
                        /\  (forall (i:mem_addr).{:pattern (trigger i)}
                                   trigger i ==>
                                   (gc'.color i <> Black
                                 ==> gc.color i = gc'.color i))
                        /\ gc'.color ptr <> White
                        /\ (exists c. gc' == {gc with color=c})))
let rec mark ptr =
  let st = get () in
  if st.color ptr = White
  then begin
    let st' = {st with color=upd_map st.color ptr Gray} in
    set st';
    mark (st'.fields (ptr, F1));
    mark (st'.fields (ptr, F2));
    let st'' = get () in
    set ({st'' with color = upd_map st''.color ptr Black})
  end


 type sweep_aux_inv (old:gc_state) (ptr:int) (st:gc_state) =
  gc_inv old
  /\ (st.fields == old.fields /\ st.abs_fields == old.abs_fields)
  /\ to_abs_inj st.to_abs
  /\ (forall (i:mem_addr). {:pattern (trigger i)}
           trigger i
       ==> st.color i <> Gray
       /\ (old.color i = Black
           ==> (ptr_lifts st i
               /\ obj_inv st i
               /\ (forall f. st.fields (i, f) >= ptr ==> st.color (st.fields (i, f)) <> White)))
       /\ (~(ptr_lifts st i) <==> st.color i=Unalloc)
       /\ (ptr_lifts st i ==> old.to_abs i = st.to_abs i)
       /\ (ptr <= i ==> old.color i = st.color i)
       /\ (i < ptr ==> (st.color i = Unalloc \/ st.color i = White))
       /\ (i < ptr /\ st.color i = White ==> old.color i = Black)
     )

let test1 old n = assert (sweep_aux_inv old mem_hi n
                           ==> mutator_inv n)

let test2 old = assert (gc_inv old /\ (forall i. old.color i <> Gray) ==> sweep_aux_inv old mem_lo old)

val sweep: unit -> GC unit
  (requires (fun gc -> gc_inv gc
                    /\ (forall (i:mem_addr). {:pattern (trigger i)}
                             trigger i
                          ==> gc.color i <> Gray)))
  (ensures (fun gc _ gc' -> (exists c a. gc' == {gc with color=c; to_abs=a}
                        /\ mutator_inv gc'
                        /\ (forall (i:mem_addr).{:pattern (trigger i)}
                                 trigger i
                              ==> (gc.color i=Black ==> ptr_lifts gc' i)
                                  /\ (ptr_lifts gc' i ==> gc.to_abs i = gc'.to_abs i)))))
let sweep () =
  let old = get () in
  let rec sweep_aux : ptr:mem_addr -> GC unit
      (requires (fun gc -> sweep_aux_inv old ptr gc))
      (ensures (fun _ _ st ->
                      (st.abs_fields == old.abs_fields
                       /\ st.fields == old.fields
                       /\ mutator_inv st
                       /\ (forall (i:mem_addr).{:pattern (trigger i)}
                               trigger i
                            ==> (old.color i=Black ==> ptr_lifts st i)
                                /\ (ptr_lifts st i ==> old.to_abs i = st.to_abs i)))))
     = fun ptr ->
          cut (trigger ptr);
          let st = get () in
          if st.color ptr = White //deallocate
          then (let st' = {st with
                              color=upd_map st.color ptr Unalloc;
                              to_abs=upd_map st.to_abs ptr no_abs} in
                set st')
          else if st.color ptr = Black
          then
          begin let st' = {st with color=upd_map st.color ptr White} in
                set st'
          end;
          if ptr + 1 < mem_hi
          then sweep_aux (ptr + 1) in
  sweep_aux mem_lo

val gc: root:mem_addr -> GCMut unit
  (requires (fun gc -> root<>0 ==> ptr_lifts gc root))
  (ensures (fun gc _ gc' -> (exists c a. gc' == {gc with color=c; to_abs=a})
                    /\ (root<>0 ==> ptr_lifts gc' root)
                    /\ (forall (i:mem_addr). {:pattern (trigger i)}
                                trigger i ==> (ptr_lifts gc' i ==> gc.to_abs i = gc'.to_abs i))
                    /\ (root <> 0 ==> gc.to_abs root = gc'.to_abs root)))
let gc root =
  cut (trigger root);
  if (root <> 0)
  then mark root;
  sweep ()

type try_alloc_invariant (root:mem_addr) (abs:abs_node) (gc:gc_state) (gc':gc_state) =
     (root <> 0 ==> ptr_lifts_to gc' root (gc.to_abs root))
  /\ gc'.abs_fields (abs, F1) = abs
  /\ gc'.abs_fields (abs, F2) = abs
  /\ (forall (i:mem_addr).{:pattern (trigger i)}
                         trigger i
                      ==> (ptr_lifts gc i
                      ==> gc'.to_abs i <> abs))

val alloc: root:mem_addr -> abs:abs_node -> GCMut mem_addr
  (requires (fun gc ->
              try_alloc_invariant root abs gc gc
              /\ abs <> no_abs
              /\ (forall (i:mem_addr). trigger i /\ ptr_lifts gc i ==> gc.to_abs i <> abs)))
  (ensures (fun gc ptr gc' -> (root <> 0 ==> ptr_lifts_to gc' root (gc.to_abs root))
                            /\ ptr_lifts gc' ptr
                            /\ gc'.abs_fields == gc.abs_fields))
let rec alloc root abs =
    let rec try_alloc_at_ptr : ptr:mem_addr -> abs:abs_node -> GCMut int
      (requires (fun gc ->
                  abs <> no_abs /\
                  trigger ptr /\
                  (forall (i:mem_addr). trigger i /\ ptr_lifts gc i ==> gc.to_abs i <> abs) /\
                  gc.abs_fields (abs, F1) = abs /\
                  gc.abs_fields (abs, F2) = abs))
      (ensures (fun gc i gc' ->
                gc'.abs_fields == gc.abs_fields
                /\ (is_mem_addr i \/ i=mem_hi)
                /\ (is_mem_addr i ==>
                    ~(ptr_lifts gc i)
                    /\ ptr_lifts gc' i
                    /\ (forall (j:mem_addr). i <> j ==> gc'.to_abs j = gc.to_abs j))
                /\ (i=mem_hi ==> gc==gc')))
      = fun ptr abs ->
          let gc = get () in
          if gc.color ptr = Unalloc
          then
          begin let fields = upd_map #(mem_addr * field) #mem_addr gc.fields (ptr, F1) ptr in
                let fields = upd_map #(mem_addr * field) #mem_addr fields (ptr, F2) ptr in
                let gc' = { gc with
                              to_abs=upd_map gc.to_abs ptr abs;
                              color =upd_map gc.color ptr White;
                              fields=fields } in
                set gc';
                ptr
          end
          else if ptr + 1 < mem_hi
          then try_alloc_at_ptr (ptr + 1) abs
          else mem_hi in
    let ptr = try_alloc_at_ptr mem_lo abs in
    if ptr < mem_hi
    then ptr
    else (gc root; alloc root abs)
