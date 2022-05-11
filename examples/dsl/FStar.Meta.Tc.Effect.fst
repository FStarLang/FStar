module FStar.Meta.Tc.Effect

open FStar.Tactics
open FStar.Monotonic.Pure

type tc_result (a:Type) =
  | Tc_success : x:a -> tc_result a
  | Tc_failure : msg:string -> tc_result a

type wp_t (a:Type) = pure_wp (tc_result a)

type repr (a:Type) (wp:wp_t a) =
  unit -> DIV (tc_result a) wp

unfold
let return_wp (#a:Type) (x:a) : wp_t a =
  as_pure_wp (fun post -> post (Tc_success x))

let return (a:Type) (x:a) : repr a (return_wp x) =
  fun _ -> Tc_success x

unfold
let bind_wp (#a #b:Type)
  (wp_f:wp_t a)
  (wp_g:a -> wp_t b)
  : wp_t b
  = elim_pure_wp_monotonicity_forall ();
    as_pure_wp (fun post ->
                wp_f (fun r ->
                      match r with
                      | Tc_success x -> wp_g x post
                      | Tc_failure m -> post (Tc_failure m)))

let bind (a b:Type)
  (wp_f:wp_t a)
  (wp_g:a -> wp_t b)
  (f:repr a wp_f)
  (g:(x:a -> repr b (wp_g x)))
  : repr b (bind_wp wp_f wp_g)
  = elim_pure_wp_monotonicity_forall ();
    fun _ ->
    let r = f () in
    match r with
    | Tc_success x -> g x ()
    | Tc_failure m -> Tc_failure m

unfold
let if_then_else_wp (#a:Type) (wp_then:wp_t a) (wp_else:wp_t a) (b:bool)
  : wp_t a
  = elim_pure_wp_monotonicity wp_then;
    elim_pure_wp_monotonicity wp_else;
    as_pure_wp (fun post -> (b ==> wp_then post) /\
                         ((~ b) ==> wp_else post))

let if_then_else (a:Type)
  (wp_then wp_else:wp_t a)
  (f:repr a wp_then)
  (g:repr a wp_else)
  (b:bool)
  : Type
  = repr a (if_then_else_wp wp_then wp_else b)

let subcomp (a:Type)
  (wp_f:wp_t a)
  (wp_g:wp_t a)
  (f:repr a wp_f)
  : Pure
      (repr a wp_g)
      (requires forall post. wp_g post ==> wp_f post)
      (ensures fun _ -> True)
  = f

effect {
  MetaTC (a:Type) (wp:wp_t a)
  with { repr; return; bind; if_then_else; subcomp }
}

effect MetaTc (a:Type) (pre:pure_pre) (post:pure_post' (tc_result a) pre) =
  MetaTC a (as_pure_wp (fun p -> pre /\ (forall r. post r ==> p r)))

unfold
let lift_DIV_MetaTC_wp (#a:Type) (wp:pure_wp a) : wp_t a =
  elim_pure_wp_monotonicity wp;
  as_pure_wp (fun post -> wp (fun r -> post (Tc_success r)))

let lift_DIV_MetaTC (a:Type)
  (wp:pure_wp a)
  (f:eqtype_as_type unit -> DIV a wp)
  : repr a (lift_DIV_MetaTC_wp wp)
  = elim_pure_wp_monotonicity wp;
    fun _ -> Tc_success (f ())

sub_effect DIV ~> MetaTC = lift_DIV_MetaTC

exception Meta_tc_failed of string

unfold
let lift_MetaTC_TAC_wp (#a:Type) (wp:wp_t a)
  : tac_wp_t a
  = let open FStar.Tactics.Result in
    elim_pure_wp_monotonicity wp;
    fun ps post ->
    wp (fun r ->
        match r with
        | Tc_success x -> post (Success x ps)
        | Tc_failure m -> post (Failed (Meta_tc_failed m) ps))

let lift_MetaTC_TAC (a:Type) (wp:wp_t a) (f:repr a wp)
  : tac_repr a (lift_MetaTC_TAC_wp wp)
  = let open FStar.Tactics.Result in
    elim_pure_wp_monotonicity wp;
    fun ps ->
    let r = f () in
    match r with
    | Tc_success x -> Success x ps
    | Tc_failure m -> Failed (Meta_tc_failed m) ps

sub_effect MetaTC ~> TAC = lift_MetaTC_TAC
