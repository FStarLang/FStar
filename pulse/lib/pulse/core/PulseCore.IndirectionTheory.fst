module PulseCore.IndirectionTheory
module F = FStar.FunctionalExtensionality

let pred' #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1))) : Type u#(a+1) =
  f:(m:nat{m<n} -> (knot_t m & ff.other) -> ff.tt) { f == (fun m x -> f m x) }

let funext #t (#s: t->Type) (f1 f2: (x:t -> s x)) (h: (x:t -> squash (f1 x == f2 x))) :
    squash ((fun x -> f1 x) == (fun x -> f2 x)) =
  let lem x : Lemma (f1 x == f2 x) = h x in
  assert ((fun x -> f1 x) == (fun x -> f2 x)) by
    Tactics.V2.Derived.l_to_r [quote lem]

let pred'_ext #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1)))
    (f1 f2: pred' ff n knot_t)
    (h: (m:nat{m<n} -> x:(knot_t m & ff.other) -> squash (f1 m x == f2 m x)))
    : squash (f1 == f2) =
  funext (fun m x -> f1 m x) (fun m x -> f2 m x) fun m ->
    funext _ _ fun x -> h m x

// Gadget to control unfolding
irreducible let irred_true : b:bool{b} = true

let f_pred' #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1))) : Type u#(a+1) =
  f (pred' ff n knot_t)

let rec k' #f (ff: functor u#a f) : nat -> Type u#(a+1) =
  fun n -> if irred_true then f_pred' ff n (k' ff) else (assert False; Type u#a)

let k'_eq #f (ff: functor u#a f) (n: nat) :
    squash (k' ff n == f (pred' ff n (k' ff))) =
  let g (b: bool{b}) n : Type =
    if b then f_pred' ff n (k' ff) else (assert False; Type u#a) in
  assert_norm (g irred_true == k' ff)

let k'_unfold #f (#ff: functor u#a f) #n (x: k' ff n) : f (pred' ff n (k' ff)) =
  k'_eq ff n; x

let k'_fold #f (#ff: functor u#a f) #n (x: f (pred' ff n (k' ff))) : k' ff n =
  k'_eq ff n; x

let approx' #f (#ff: functor u#a f) (#n: nat) (m: nat { m <= n }) (x: pred' ff n (k' ff)) : pred' ff m (k' ff) =
  fun l h -> x l h

let knot_t #f (ff: functor u#a f) : Type u#(a+1) =
  n:nat & k' ff n

let up_pred #f (#ff: functor u#a f) n (x: pred' ff n (k' ff)) : pred (knot_t ff) ff.other ff.tt =
  F.on_dom (knot_t ff & ff.other) fun ((|m, h|), o) -> if m < n then x m (h, o) else ff.t_bot

let down_pred #f (#ff: functor u#a f) n (x: pred (knot_t ff) ff.other ff.tt) : pred' ff n (k' ff) =
  fun m (h, o) -> x ((| m, h |), o)

let down_up_pred #f (ff: functor u#a f) #n (x: pred' ff n (k' ff)) :
    squash (down_pred n (up_pred n x) == x) =
  pred'_ext _ _ _ (down_pred n (up_pred n x)) x fun m h -> ()

let approx_ #f (#ff: functor u#a f) (n:nat) : (pred (knot_t ff) ff.other ff.tt ^-> pred (knot_t ff) ff.other ff.tt) =
  F.on_dom (pred (knot_t ff) ff.other ff.tt) fun x ->
  F.on_dom (knot_t ff & ff.other) fun h -> if h._1._1+1 < n then x h else ff.t_bot

let on_dom_ext #t #s (f g: t ^-> s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x; F.extensionality _ _ f g

let down #f (#ff: functor u#a f) (x: nat & f (pred (knot_t ff) ff.other ff.tt)) : knot_t ff =
  (| fst x, k'_fold (ff.fmap (down_pred (fst x)) (snd x)) |)

let up #f (#ff: functor u#a f) (x: knot_t ff) : nat & f (pred (knot_t ff) ff.other ff.tt) =
  (dfst x, ff.fmap (up_pred (dfst x)) (k'_unfold (dsnd x)))

let up_down_pred #f (#ff: functor u#a f) (n:nat) (x: pred (knot_t ff) ff.other ff.tt) :
    squash (up_pred n (down_pred n x) == approx n x) =
  on_dom_ext ((up_pred n (down_pred n x))) (approx n x) fun _ -> ()

let down_up #f (#ff: functor u#a f) (x: knot_t ff) : squash (down (up x) == x) =
  let (| n, h |) = x in
  let h = k'_unfold h in
  ff.fmap_comp (pred' ff n (k' ff)) _ (pred' ff n (k' ff)) (down_pred n) (up_pred n);
  on_dom_ext (compose (down_pred n) (up_pred #f #ff n)) id (down_up_pred ff);
  ff.fmap_id _ h;
  assert ff.fmap id h == h

let up_down #f (#ff: functor u#a f) (n: nat) (h: f (pred (knot_t ff) ff.other ff.tt)) :
    squash (up (down #f #ff (n, h)) == (n, ff.fmap (approx n) h)) =
  ff.fmap_comp _ _ _ (up_pred n) (down_pred #f #ff n);
  on_dom_ext (compose (up_pred n) (down_pred #f #ff n)) (approx n) (fun x -> up_down_pred n x)
