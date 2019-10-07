module MExn

open FStar.HyperStack.ST

module HS = FStar.HyperStack


type pre_t = HS.mem -> Type0
type post_t (a:Type) = option a -> HS.mem -> Type0
type wp_t (a:Type) =
  wp:(post_t a -> pre_t){
    forall p q.
      (forall x h. p x h ==> q x h) ==>
      (forall h. wp p h ==> wp q h)}


type repr (a:Type) (wp:wp_t a) =
  unit -> STATE (option a) wp

inline_for_extraction
let return (a:Type) (x:a)
: repr a (fun p h -> p (Some x) h)
= fun _ -> Some x

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b
  (fun p ->
    wp_f (fun r ->
      match r with
      | None -> p None
      | Some x -> wp_g x p))
= fun _ ->
  let r = f () in
  match r with
  | None -> None
  | Some x -> (g x) ()

inline_for_extraction
let stronger (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f)
: Pure (repr a wp_g)
  (requires forall p h. wp_g p h ==> wp_f p h)
  (ensures fun _ -> True)
= f

inline_for_extraction
let conjunction (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) (g:repr a wp_g)
  (p:Type0)
: Type
= repr a
  (fun post h ->
    (p ==> wp_f post h) /\
    ((~ p) ==> wp_g post h))


reifiable reflectable
layered_effect {
  EXN : a:Type -> wp_t a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  stronger = stronger;
  conjunction = conjunction
}

inline_for_extraction
let lift_div_exn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> DIV a wp)
: repr a (fun p h -> wp (fun x -> p (Some x) h))
= fun _ -> Some (f ())

sub_effect DIV ~> EXN = lift_div_exn


effect Exn (a:Type) (pre:HS.mem -> Type0) (post:HS.mem -> option a -> HS.mem -> Type0) =
  EXN a (fun p h0 -> pre h0 /\ (forall x h1. (equal_stack_domains h0 h1 /\ post h0 x h1) ==> p x h1))
