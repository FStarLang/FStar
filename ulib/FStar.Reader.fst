module FStar.Reader

type reader (heap:Type) (a:Type) = heap -> M a

let return_reader (heap:Type) (a:Type) (x:a) : reader heap a = fun h -> x
let bind_reader (heap:Type) (a:Type) (b:Type) (x:reader heap a) (f:a -> reader heap b) : reader heap b =
  fun h0 -> let x0 = x h0 in f x0 h0
   (* TODO : elaboration should also work with *)
   (* fun h0 -> f (x0 h0) h0 *)
let get_reader (heap:Type) () : reader heap heap = fun h -> h

new_effect_for_free {
  READER_h (heap:Type) : a:Type -> Effect
  with repr  = reader heap
    ; bind   = bind_reader heap
    ; return = return_reader heap
  and effect_actions
    get = get_reader heap
}

let reader_pre_h  = READER_h.pre
let reader_post_h = READER_h.post
let reader_wp_h   = READER_h.wp

open FStar.Heap

new_effect_for_free READER = READER_h FStar.Heap.heap

effect STRead (a:Type) (pre: (heap -> Type0)) (post:heap -> a -> Type0) = 
  READER a (fun h0 (p:reader_post_h FStar.Heap.heap a) -> pre h0 /\ (forall (x:a). post h0 x ==> p x))

open FStar.ST

assume val read:  #a:Type -> r:ref a -> STRead a
					 (requires (fun h -> True))
					 (ensures (fun h x -> x == sel h r))

unfold let lift_reader_state (a:Type) (wp:reader_wp_h heap a) (h:heap) (p:st_post a) = wp h (fun a -> p (a, h))
sub_effect READER ~> STATE = lift_reader_state
unfold let lift_div_reader (a:Type) (wp:pure_wp a) (h:heap) (p:reader_post_h FStar.Heap.heap a) = wp p
sub_effect DIV ~> READER = lift_div_reader

(* Testing *)

let f (r:ref int) : STRead int 
  (requires (fun h -> True))
  (ensures (fun h x -> x = sel h r + 1) )
  = read r + 1


let g (r:ref int) (s:ref int) : ST unit
  (requires (fun h -> True))
  (ensures (fun h0 (_, h1) -> sel h1 r = (sel h0 r + 1) + (sel h0 s + 1)))
  = let x = f r in
    let y = f s in
    r := x + y
