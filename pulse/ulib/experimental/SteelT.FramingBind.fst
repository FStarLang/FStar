module SteelT.FramingBind
open Steel.Memory
irreducible
let resolve_framing : unit = ()
irreducible
let resolve_framing_forall : unit = ()


type pre_t = hprop u#1
type post_t (a:Type) = a -> hprop u#1

type repr (a:Type u#a) (pre:pre_t) (post:post_t a) = unit -> unit

let returnc (a:Type u#a) (x:a) (#[@resolve_framing] p:a -> hprop)
: repr a (p x) p
= admit()

open Steel.Memory.Tactics

let can_be_split_into_forall (#a:Type) (outer inner:post_t a) (delta:pre_t)
  = forall x. can_be_split_into (outer x) (inner x) delta

let bind (a:Type) (b:Type)
  (#[@resolve_framing] outer_pre:pre_t)
  (#[@resolve_framing] pre_f:pre_t)
  (#[@resolve_framing] post_f:post_t a)
  (#[@resolve_framing] post_g:post_t b)
  (#[@resolve_framing] frame_f:hprop)
  (#[@resolve_framing] _u:squash (can_be_split_into outer_pre pre_f frame_f))
  (#[@resolve_framing] frame_g:hprop)
  (#[@resolve_framing] pre_g:post_t a)
  (#[@resolve_framing_forall] _v:squash (can_be_split_into_forall
    (fun x -> post_f x `star` frame_f) pre_g frame_g))
  (f:repr a pre_f post_f)
  (g:(x:a -> repr b (pre_g x) post_g))
: repr b outer_pre (fun y -> post_g y `star` frame_g)
= admit()

let subcomp (a:Type) (pre:pre_t) (post:post_t a)
  (f:repr a pre post)
: Pure (repr a pre post)
  (requires True)
  (ensures fun _ -> True)
= f


let if_then_else (a:Type) (pre:pre_t) (post:post_t a)
  (f:repr a pre post)
  (g:repr a pre post)
  (p:Type0)
: Type
= repr a pre post

#push-options "--lax"
reifiable reflectable
layered_effect {
  SteelT : a:Type -> pre:pre_t -> post:post_t a -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}
#pop-options

let bind_pure_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre_g post_g))
: repr b pre_g post_g
= admit()

polymonadic_bind (PURE, SteelT) |> SteelT = bind_pure_steel

let bind_steel_pure (a:Type) (b:Type)
    (pre_f:pre_t) (post_f:hprop)
    (wp_g:a -> pure_wp b)
    (f:repr a pre_f (fun _ -> post_f))
    (g:(x:a -> unit -> PURE b (wp_g x)))
: repr b pre_f (fun _ -> post_f)
= admit()

polymonadic_bind (SteelT, PURE) |> SteelT = bind_steel_pure

open FStar.Tactics
module T = FStar.Tactics

inline_for_extraction noextract let resolve_frame () : Tac unit =
  let open FStar.Algebra.CommMonoid.Equiv in
  norm [delta_only [`%can_be_split_into]];
  norm [delta_attr [`%__reduce__];
        delta_only [
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  canon()

[@(resolve_implicits)
  (resolve_framing)]
let resolve () : Tac unit =
    let rec aux (i:int) : Tac unit =
    T.dump ("State: " ^ string_of_int i);
    match T.goals () with
    | [] -> ()
    | g :: _ ->
      let f = T.term_as_formula' (goal_type g) in
      T.print ("Goal formula is " ^ (formula_to_string f));
      match f with
      | Comp (Eq _) _ _ ->
        T.print "Solving equality goal\n";
        T.trefl();
        aux (i + 1)

      | _ -> //has to be framing
        T.print "Solving framing goal\n";
        T.focus resolve_frame;
        aux (i + 1)
  in
  aux 0


[@(resolve_implicits)
  (resolve_framing_forall)]
let resolve_forall () : Tac unit =
  // TODO: Implement this
  T.dump "hello";
  T.trivial ()

assume
val myref : Type0

assume
val myref_hprop (x:myref) : hprop

assume
val dependent_provides (_:unit)
  : SteelT myref emp myref_hprop

assume
val nop (_:unit) : SteelT unit emp (fun c -> emp)

//#push-options "--print_implicits --debug_level ResolveImplicitsHook"
val test_ok1 (_:unit)
  : SteelT myref emp (fun x -> myref_hprop x)
// TODO: (AF) It does not seem like F* picks resolve_forall for
// the resolve_framing_forall attribute
[@expect_failure]
let test_ok1 _
  = let tr = dependent_provides () in
    nop ();
    tr
