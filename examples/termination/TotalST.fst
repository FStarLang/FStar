module TotalST
open LowStar.Buffer
open FStar.HyperStack.ST
module HS = FStar.HyperStack
let monotonic (a:Type) (wp:st_wp_h HS.mem a) =
  forall (p1 p2:st_post_h HS.mem a).
    (forall h x. p1 x h ==> p2 x h) ==>
    (forall h. wp p1 h ==> wp p2 h)
let wp (a:Type) = wp:st_wp_h HS.mem a { monotonic _ wp }
inline_for_extraction
let repr a (wp:wp a) = unit -> STATE a wp
unfold
let return_wp a (x:a) : wp a = fun p -> p x
inline_for_extraction
let return a (x:a) : repr a (return_wp _ x) = fun () -> x

unfold
let bind_wp a b (wp_f:wp a) (wp_g:a -> wp b)
  : wp b
  = (fun p m -> wp_f (fun x -> wp_g x p) m)
inline_for_extraction
let bind (a:Type) (b:Type) (wp_f:wp a) (wp_g:a -> wp b)
         (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
  : repr b (bind_wp _ _ wp_f wp_g)
  = fun () -> let x = f () in g x ()

unfold
let stronger a (w:wp a) (w':wp a) =
  st_stronger FStar.HyperStack.mem _ w w'

inline_for_extraction
let subcomp a wp wp' (x:repr a wp)
  : Pure (repr a wp')
         (requires stronger _ wp' wp)
         (ensures fun _ -> True)
  = x

let if_then_else_wp a
                    (wp_f:wp a) 
                    (wp_g:wp a)
                    (b:bool)
  : wp a
  = fun p m ->
      (b ==> wp_f p m) /\
      (not b ==> wp_g p m)

inline_for_extraction
let if_then_else  a
                  (wp_f:wp a) 
                  (wp_g:wp a)
                  (f:repr a wp_f) 
                  (g:repr a wp_g)
                  (b:bool)
  : Type 
  = repr a (if_then_else_wp a wp_f wp_g b)

total
reifiable
reflectable
layered_effect {
  TOTALST : result:Type -> wp:wp result -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

let wp_monotonic (a:Type) (w:pure_wp a) 
  : Lemma (forall (p q:pure_post a).
             (forall (x:a). p x ==> q x) ==> (w p ==> w q))
  = FStar.Monotonic.Pure.wp_monotonic_pure ()

let u : Type = unit

unfold
let lift_pure_wp (a:Type) (w:pure_wp a) 
  : wp a 
  = let w'
      : st_wp_h HS.mem a
      = fun p h ->
          w (fun a -> p a h)
    in
    wp_monotonic a w;
    w'
    

unfold 
inline_for_extraction
let lift_pure_total_st (a:Type) 
                       (w:pure_wp a)
                       (f:u -> PURE a w)
  : Tot (repr a (lift_pure_wp a w))
  = wp_monotonic _ w;
    fun () -> f ()

sub_effect PURE ~> TOTALST = lift_pure_total_st


effect TotST a (pre:HS.mem -> Type0) 
               (post:(m0:HS.mem -> a -> m1:HS.mem{pre m0} -> Type0)) = 
       TOTALST a 
         (fun p (m:HS.mem) -> 
              pre m /\ 
              (forall x (m':HS.mem). post m x m' ==> p x m'))
       
inline_for_extraction
let reflect_stack a (pre:HS.mem -> Type0)
                    (post:(m0:HS.mem -> a -> m1:HS.mem{pre m0} -> Type0))
                    ($f:unit -> Stack a pre post) 
  : TotST a pre post
  = TOTALST?.reflect f
