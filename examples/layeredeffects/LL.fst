module LL


type epre_t = Type0
type epost_t (a:Type) = option a -> Type0
type ewp_t (a:Type) =
  wp:(epost_t a -> epre_t){
    forall p q.
      (forall r. p r ==> q r) ==>
      (wp p ==> wp q)}

type erepr (a:Type) (wp:ewp_t a) = unit -> PURE (option a) wp

inline_for_extraction
let ereturn (a:Type) (x:a)
: erepr a (fun p -> p (Some x))
= fun _ -> Some x

inline_for_extraction
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

inline_for_extraction
let estronger (a:Type)
  (wp_f:ewp_t a) (wp_g:ewp_t a)
  (f:erepr a wp_f)
: Pure (erepr a wp_g)
  (requires forall p. wp_g p ==> wp_f p)
  (ensures fun _ -> True)
= f

inline_for_extraction
let econjunction (a:Type)
  (wp_f:ewp_t a) (wp_g:ewp_t a)
  (f:erepr a wp_f) (g:erepr a wp_g)
  (p:Type0)
: Type
= erepr a
  (fun post ->
    (p ==> wp_f post) /\
    ((~ p) ==> wp_g post))

reifiable reflectable
layered_effect {
  EXN : a:Type -> ewp_t a -> Effect
  with
  repr = erepr;
  return = ereturn;
  bind = ebind;
  stronger = estronger;
  conjunction = econjunction
}

inline_for_extraction
let lift_pure_exn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> PURE a wp)
: erepr a (fun p -> wp (fun x -> p (Some x)))
= fun _ -> Some (f ())

sub_effect PURE ~> EXN = lift_pure_exn

effect Exn (a:Type) (pre:Type0) (post:option a -> Type0) =
  EXN a (fun p -> pre /\ (forall r. post r ==> p r))



type pre_t = nat -> Type0
type post_t (a:Type) = option (a & nat) -> Type0
type wp_t0 (a:Type) = post_t a -> pre_t

unfold
let monotonic_wp (#a:Type) (wp:wp_t0 a) =
  forall p q.
    (forall r. p r ==> q r) ==>
    (forall n. wp p n ==> wp q n)

type wp_t (a:Type) =
  wp:wp_t0 a{monotonic_wp wp}

type repr (a:Type) (wp:wp_t a) =
  n:nat -> EXN (a & nat) (fun p -> wp p n)

inline_for_extraction
let return (a:Type) (x:a)
: repr a (fun p n -> p (Some (x, n)))
= fun n -> (x, n)

//#set-options "--max_fuel 0 --initial_ifuel 4 --max_ifuel 4"

unfold
let post_a (a:Type) (b:Type) (wp_g:a -> wp_t b) (p:post_t b) : post_t a =
  fun r ->
  match r with
  | None -> p None
  | Some r -> Prims.auto_squash (wp_g (Mktuple2?._1 r) p (Mktuple2?._2 r))

let lemma_monotonic2 (#a:Type) (#b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) (p:post_t b) (q:post_t b) (n:nat)
: Lemma
  (requires forall (r:option (a & nat)). post_a a b wp_g p r ==> post_a a b wp_g q r)
  (ensures wp_f (post_a a b wp_g p) n ==> wp_f (post_a a b wp_g q) n)
= admit ()

unfold
let bind_wp0 (a:Type) (b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : post_t b -> pre_t =
  fun p n -> wp_f (post_a a b wp_g p) n

open FStar.Tactics

unfold
let bind_wp (a:Type) (b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b) : wp_t b
= assert (monotonic_wp (bind_wp0 a b wp_f wp_g)) by
    (norm [delta_only [`%monotonic_wp]];
     let p_binder = forall_intro () in
     let q_binder = forall_intro () in
     ignore (implies_intro ());
     ignore (forall_intro ());
     norm [delta_only [`%bind_wp0]];
     let wp_f_binder, wp_g_binder =
       match (cur_binders ()) with
       | _::_::wp_f::wp_g::_ -> wp_f, wp_g
       | _ -> fail "" in
     apply_lemma (`(lemma_monotonic2 (`#(binder_to_term wp_f_binder)) (`#(binder_to_term wp_g_binder)) (`#(binder_to_term p_binder)) (`#(binder_to_term q_binder))));
     norm [delta_only [`%post_a]];
     ignore (forall_intro ()));
  bind_wp0 a b wp_f wp_g

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b (bind_wp a b wp_f wp_g)
= fun n ->
  let (x, n) = f n in
  g x n

inline_for_extraction
let stronger (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f)
: Pure (repr a wp_g)
  (requires forall p n. wp_g p n ==> wp_f p n)
  (ensures fun _ -> True)
= f

inline_for_extraction
let conjunction (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) (g:repr a wp_g)
  (p:Type0)
: Type
= repr a
  (fun post n ->
    (p ==> wp_f post n) /\
    ((~ p) ==> wp_g post n))

reifiable reflectable
layered_effect {
  STEXN : a:Type -> wp:wp_t a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  stronger = stronger;
  conjunction = conjunction
}

inline_for_extraction
let lift_pure_stexn (a:Type) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)}) (f:unit -> PURE a wp)
: repr a (fun p n -> wp (fun x -> p (Some (x, n))))
= fun n -> (f (), n)

sub_effect PURE ~> STEXN = lift_pure_stexn


effect StExn (a:Type) (pre:nat -> Type0) (post:nat -> option (a & nat) -> Type0) =
  STEXN a (fun p n -> pre n /\ (forall r. post n r ==> p r))


(*** Application ***)

assume val get_n1
: n:nat ->
  Pure (option (nat * nat))
  (requires n > 0)
  (ensures fun r ->
    match r with
    | None -> True
    | Some (n1, n2) -> n1 == n /\ n2 == n + 1)

type flt = {
  n1 : nat;
  n2 : nat;
  n3 : i:nat{n1 > 0 /\ n2 = n1 + 1 /\ i = n2 + 1}
}

let get_flt (n:nat)
: Pure (option flt)
  (requires n > 0)
  (ensures fun r ->
    match r with
    | None -> True
    | Some flt -> flt.n1 == n)
= let r = get_n1 n in
  match r with
  | None -> None
  | Some (x, n) ->
    let r = get_n1 n in
    match r with
    | None -> None
    | Some (y, n) ->
      let r = get_n1 n in
      match r with
      | None -> None
      | Some (z, _) -> Some ({ n1 = x; n2 = y; n3 = z })


inline_for_extraction
let get_n1_exn_ (n:nat)
: unit ->
  Pure (option (nat * nat))
  (requires n > 0)
  (ensures fun r ->
    match r with
    | None -> True
    | Some (n1, n2) -> n1 == n /\ n2 == n + 1)
= fun _ ->
  get_n1 n

inline_for_extraction
let get_n1_exn (n:nat)
: Exn (nat * nat)
  (requires n > 0)
  (ensures fun r ->
    match r with
    | None -> True
    | Some (n1, n2) -> n1 == n /\ n2 == n + 1)
= EXN?.reflect (get_n1_exn_ n)

inline_for_extraction
let get_flt_exn (n:nat)
: Exn flt
  (requires n > 0)
  (ensures fun r ->
    match r with
    | None -> True
    | Some flt -> flt.n1 == n)
= let x, n = get_n1_exn n in
  let y, n = get_n1_exn n in
  let z, _ = get_n1_exn n in
  { n1 = x; n2 = y; n3 = z}

inline_for_extraction
let get_n1_stexn_ (_:unit)
: n:nat ->
  Exn (nat * nat)
  (requires n > 0)
  (ensures fun r ->
    match r with
    | None -> True
    | Some (n1, n2) -> n1 == n /\ n2 == n + 1)
= fun n -> get_n1_exn n

inline_for_extraction
let get_n1_stexn (_:unit)
: StExn nat
  (requires fun n -> n > 0)
  (ensures fun n r ->
    match r with
    | None -> True
    | Some (n1, n2) -> n1 == n /\ n2 == n + 1)
= STEXN?.reflect (get_n1_stexn_ ())

let get_n1_stexn2 (_:unit)
: StExn nat
  (requires fun n -> n > 0)
  (ensures fun _ _ -> True)
= let n = get_n1_stexn () in
  n

inline_for_extraction
let get_flt_stexn (_:unit)
: StExn flt
  (requires fun n -> n > 0)
  (ensures fun n r ->
    match r with
    | None -> True
    | Some (flt, _) -> flt.n1 == n)
= let x = get_n1_stexn () in
  let y = get_n1_stexn () in
  let z = get_n1_stexn () in
  { n1 = x; n2 = y; n3 = z}


let get_flt_stexn_reified (n:nat)
: Pure (option (flt * nat))
  (requires n > 0)
  (ensures fun r ->
    match r with
    | None -> True
    | Some (flt, _) -> flt.n1 == n)
= reify (reify (get_flt_stexn ()) n) ()
