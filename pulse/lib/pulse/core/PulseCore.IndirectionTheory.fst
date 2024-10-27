module PulseCore.IndirectionTheory
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality

type base : Type u#a =

let pred' #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1))) : Type u#(a+1) =
  f:(m:pos{m<n} -> (knot_t m & ff.other) -> ff.tt) { f == (fun m x -> f m x) }

let funext #t (#s: t->Type) (f1 f2: (x:t -> s x)) (h: (x:t -> squash (f1 x == f2 x))) :
    squash ((fun x -> f1 x) == (fun x -> f2 x)) =
  let lem x : Lemma (f1 x == f2 x) = h x in
  assert ((fun x -> f1 x) == (fun x -> f2 x)) by
    Tactics.V2.Derived.l_to_r [quote lem]

let funext' #t (#s: t->Type) (f1 f2: (f:(x:t -> s x) {f == fun x -> f x})) (h: (x:t -> squash (f1 x == f2 x))) :
    squash (f1 == f2) =
  funext f1 f2 h

let pred'_ext #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1)))
    (f1 f2: pred' ff n knot_t)
    (h: (m:pos{m<n} -> x:(knot_t m & ff.other) -> squash (f1 m x == f2 m x)))
    : squash (f1 == f2) =
  funext (fun m x -> f1 m x) (fun m x -> f2 m x) fun m ->
    funext _ _ fun x -> h m x

irreducible let irred_true : b:bool{b} = true

let rec iterate #t (step: (n:nat->(m:nat{m<n}->t)->t)) : nat -> t =
  fun n -> if irred_true then step n (iterate step) else assert False

let congr_fun #t #s (f: t->s) (x1: t) (x2: t {x1==x2}) : squash (f x1 == f x2) = ()

let iterate_eq_fun #t (step: (n:nat->(m:nat{m<n}->t)->t)) :
    squash (iterate step == (fun n -> step n (iterate step))) =
  let f (b:bool{b}) n : t = (if b then step n (iterate step) else assert False) in
  assert_norm (iterate step == f irred_true);
  congr_fun f irred_true true

let iterate_eq #t (step: (n:nat->(m:nat{m<n}->t)->t)) (n: nat) : squash (iterate step n == step n (iterate step)) =
  iterate_eq_fun step

let f_pred' #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1))) : Type u#(a+1) =
  f (pred' ff n knot_t)

let k_n #f (ff: functor u#a f) : nat -> Type u#(a+1) =
  // FIXME: this fails when defined directly as a let rec because of universe bugs
  iterate (f_pred' ff)

let k_n_eq #f (ff: functor u#a f) (n: nat) :
    squash (k_n ff n == f (pred' ff n (k_n ff))) = 
  iterate_eq_fun (f_pred' ff);
  assert_norm (k_n ff n == iterate (f_pred' ff) n)

let k_n_unfold #f (#ff: functor u#a f) #n (x: k_n ff n) : f (pred' ff n (k_n ff)) =
  k_n_eq ff n; x

let k_n_fold #f (#ff: functor u#a f) #n (x: f (pred' ff n (k_n ff))) : k_n ff n =
  k_n_eq ff n; x

let approx' #f (#ff: functor u#a f) (#n: nat) (m: nat { m <= n }) (x: pred' ff n (k_n ff)) : pred' ff m (k_n ff) =
  fun l h -> x l h

let knot_t #f (ff: functor u#a f) : Type u#(a+1) =
  n:nat & k_n ff (n+1)

let up_pred #f (#ff: functor u#a f) n (x: pred' ff n (k_n ff)) : pred (knot_t ff) ff.other ff.tt =
  F.on_dom (knot_t ff & ff.other) fun ((|m, h|), o) -> if m+1 < n then x (m+1) (h, o) else ff.t_bot

let down_pred #f (#ff: functor u#a f) n (x: pred (knot_t ff) ff.other ff.tt) : pred' ff n (k_n ff) =
  fun m (h, o) -> x ((| m-1, h |), o)

let down_up_pred #f (ff: functor u#a f) #n (x: pred' ff n (k_n ff)) :
    squash (down_pred n (up_pred n x) == x) =
  pred'_ext _ _ _ (down_pred n (up_pred n x)) x fun m h -> ()

let approx_ #f (#ff: functor u#a f) (n:nat) : (pred (knot_t ff) ff.other ff.tt ^-> pred (knot_t ff) ff.other ff.tt) =
  F.on_dom (pred (knot_t ff) ff.other ff.tt) fun x ->
  F.on_dom (knot_t ff & ff.other) fun h -> if h._1._1+1 < n then x h else ff.t_bot

let on_dom_ext #t #s (f g: t ^-> s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x;
  F.extensionality _ _ f g

let down #f (#ff: functor u#a f) (x: nat & f (pred (knot_t ff) ff.other ff.tt)) : knot_t ff =
  let (n: nat), h = x in
  (| n, k_n_fold (ff.fmap (down_pred (n+1)) h) |)

let up #f (#ff: functor u#a f) (x: knot_t ff) : nat & f (pred (knot_t ff) ff.other ff.tt) =
  let (| n, h |) = x in
  (n, ff.fmap (up_pred (n+1)) (k_n_unfold h))

let up_down_pred #f (#ff: functor u#a f) (n:pos) (x: pred (knot_t ff) ff.other ff.tt) :
    squash (up_pred n (down_pred n x) == approx (n-1) x) =
  on_dom_ext ((up_pred n (down_pred n x))) (approx (n-1) x) fun mho ->
    let ((|m,h|),o) = mho in
    assert up_pred n (down_pred n x) ((|m,h|), o) ==
      (if m+1 < n then down_pred #f #ff n x (m+1) (h,o) else ff.t_bot);
    assert up_pred n (down_pred n x) mho == approx (n-1) x mho

let down_up #f (#ff: functor u#a f) (x: knot_t ff) : squash (down (up x) == x) =
  let (| n, h |) = x in
  let h = k_n_unfold h in
  assert (down (up x))._1 == n;
  assert (up x)._2 == ff.fmap (up_pred (n+1)) h;
  assert k_n_unfold #f #ff #(n+1) (down (up x))._2 ==
    ff.fmap (down_pred (n+1)) (ff.fmap (up_pred (n+1)) h);
  ff.fmap_comp (pred' ff (n+1) (k_n ff)) _ (pred' ff (n+1) (k_n ff)) (down_pred (n+1)) (up_pred (n+1));
  assert ff.fmap (down_pred (n+1)) (ff.fmap (up_pred (n+1)) h) == ff.fmap (compose (down_pred (n+1)) (up_pred (n+1))) h;
  on_dom_ext (compose (down_pred (n+1)) (up_pred #f #ff (n+1))) id (fun h -> down_up_pred ff h);
  ff.fmap_id _ h;
  assert ff.fmap id h == h

let up_down #f (#ff: functor u#a f) (n: nat) (h: f (pred (knot_t ff) ff.other ff.tt)) :
    squash (up (down #f #ff (n, h)) == (n, ff.fmap (approx n) h)) =
  assert (up (down #f #ff (n, h)))._1 == n;
  assert (up (down #f #ff (n, h)))._2 == ff.fmap (up_pred (n+1)) (ff.fmap (down_pred (n+1)) h);
  ff.fmap_comp _ _ _ (up_pred (n+1)) (down_pred #f #ff (n+1));
  assert (up (down #f #ff (n, h)))._2 == ff.fmap (compose (up_pred (n+1)) (down_pred (n+1))) h;
  on_dom_ext (compose (up_pred (n+1)) (down_pred #f #ff (n+1))) (approx n) (fun x -> up_down_pred (n+1) x);
  ()
