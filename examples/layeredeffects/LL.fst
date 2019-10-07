module LL


type epre_t = Type0
type epost_t (a:Type) = option a -> Type0
type ewp_t (a:Type) =
  wp:(epost_t a -> epre_t)

assume WP_m1 :
  forall (a:Type) (wp:ewp_t a).
    (forall p q.
       (forall r. p r ==> q r) ==>
       (wp p ==> wp q))
       

type erepr (a:Type) (wp:ewp_t a) = unit -> PURE (option a) wp


let ereturn (a:Type) (x:a)
: erepr a (fun p -> p (Some x))
= fun _ -> Some x

let ebind (a:Type) (b:Type)
  (wp_f:ewp_t a) (wp_g:a -> ewp_t b)
  (f:erepr a wp_f) (g:(x:a -> erepr b (wp_g x)))
: erepr b
  (fun p ->
    wp_f (fun r ->
      match r with
      | None -> p None
      | Some x -> wp_g x p))
= fun _ ->
  let r = f () in
  match r with
  | None -> None
  | Some x -> g x ()

let estronger (a:Type)
  (wp_f:ewp_t a) (wp_g:ewp_t a)
  (f:erepr a wp_f)
: Pure (erepr a wp_g)
  (requires forall p. wp_g p ==> wp_f p)
  (ensures fun _ -> True)
= f

let econjunction (a:Type)
  (wp_f:ewp_t a) (wp_g:ewp_t a)
  (f:erepr a wp_f) (g:erepr a wp_g)
  (p:Type0)
: Type
= erepr a
  (fun post ->
    (p ==> wp_f post) /\
    ((~ p) ==> wp_g post))


layered_effect {
  EXN : a:Type -> ewp_t a -> Effect
  with
  repr = erepr;
  return = ereturn;
  bind = ebind;
  stronger = estronger;
  conjunction = econjunction
}


assume WP_m2 :
  forall (a:Type) (wp:pure_wp a).
    (forall p q.
       (forall x. p x ==> q x) ==>
       (wp p ==> wp q))

let lift_pure_exn (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: erepr a (fun p -> wp (fun x -> p (Some x)))
= fun _ -> Some (f ())

sub_effect PURE ~> EXN = lift_pure_exn



type pre_t = nat -> Type0
type post_t (a:Type) = option (a & nat) -> Type0
type wp_t0 (a:Type) = post_t a -> pre_t

unfold
let monotonic_wp (#a:Type) (wp:wp_t0 a) =
  forall p q.
    (forall r. p r ==> q r) ==>
    (forall n. wp p n ==> wp q n)

type wp_t (a:Type) =
  wp:(post_t a -> pre_t){monotonic_wp wp}

type repr (a:Type) (wp:wp_t a) =
  n:nat -> EXN (a & nat) (fun p -> wp p n)

let return (a:Type) (x:a)
: repr a (fun p n -> p (Some (x, n)))
= fun n -> (x, n)

#set-options "--max_fuel 0 --initial_ifuel 4 --max_ifuel 4"

let lemma_monotonic (#a:Type) (wp:wp_t a) (p:post_t a) (q:post_t a) (n:nat)
: Lemma
  (requires forall r. p r ==> q r)
  (ensures wp p n ==> wp q n)
= ()

let post_a (a:Type) (b:Type) (wp_g:a -> wp_t b) (p:post_t b) : post_t a =
  fun r ->
  match r with
  | None -> p None
  | Some r -> Prims.auto_squash (wp_g (Mktuple2?._1 r) p (Mktuple2?._2 r))

unfold
let bind_wp0 (a:Type) (b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : post_t b -> pre_t =
  fun p n -> wp_f (post_a a b wp_g p) n

//#restart-solver
//#set-options "--log_queries"

open FStar.Tactics

#set-options "--print_full_names --print_implicits --print_bound_var_types" //--debug_level Rel --debug LL"
let bind_wp (a:Type) (b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : wp_t b
= assert (monotonic_wp (bind_wp0 a b wp_f wp_g)) by
    (//compute ();
     //ignore (forall_intro ());
     //ignore (forall_intro ());
     //ignore (implies_intro ());
     //ignore (forall_intro ());
     //apply_lemma (`lemma_monotonic);
     norm [delta_only [`%monotonic_wp]];
     ignore (forall_intro ());
     ignore (forall_intro ());
     ignore (implies_intro ());
     ignore (forall_intro ());
     norm [delta_only [`%bind_wp0]];
     apply_lemma (`lemma_monotonic);
     dump "C");
  bind_wp0 a b wp_f wp_g

// let bind (a:Type) (b:Type)
//   (wp_f:wp_t a) (wp_g:a -> wp_t b)
//   (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
// : repr b (bind_wp a b wp_f wp_g)
// = fun n ->
//   let (x, n) = f n in
//   g x n
