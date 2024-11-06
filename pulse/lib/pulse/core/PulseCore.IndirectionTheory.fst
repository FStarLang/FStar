module PulseCore.IndirectionTheory

let pred' #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1))) : Type u#(a+1) =
  restricted_t (m:nat {m<n}) fun m -> knot_t m & ff.other ^-> prop

let f_ext #t #s (f g: restricted_t t s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x; extensionality _ _ f g

irreducible let irred_true : b:bool{b} = true // gadget to control unfolding

let rec k' #f (ff: functor u#a f) : nat -> Type u#(a+1) =
  fun n -> if irred_true then f (pred' ff n (k' ff)) else (assert False; Type u#a)

let k'_eq #f (ff: functor u#a f) (n: nat) : squash (k' ff n == f (pred' ff n (k' ff))) = ()

let k'_unfold #f (#ff: functor u#a f) (#n: Ghost.erased nat) (x: k' ff n) : f (pred' ff n (k' ff)) =
  k'_eq ff n; x

let k'_fold #f (#ff: functor u#a f) (#n: Ghost.erased nat) (x: f (pred' ff n (k' ff))) : k' ff n =
  k'_eq ff n; x

type knot_t #f (ff: functor f) = m: Ghost.erased nat & k' #f ff m

let unpack_pred #f (#ff: functor u#a f) n (x: pred' ff n (k' ff)) : predicate ff =
  on_dom (knot_t ff & ff.other) #(fun _ -> prop) fun ((|m, h|), o) -> if m < n then x m (h, o) else False

let pack_pred #f (#ff: functor u#a f) n (x: predicate ff) : pred' ff n (k' ff) =
  on_dom (m:nat {m<n}) fun m -> on_dom _ fun (h, o) -> x ((| Ghost.hide m, h |), o)

let pack_unpack_pred #f (ff: functor u#a f) #n (x: pred' ff n (k' ff)) =
  f_ext (pack_pred n (unpack_pred n x)) x fun m ->
    f_ext (pack_pred n (unpack_pred n x) m) (x m) fun x -> ()

let level #f #ff x = dfst x
let pack #f #ff m x = (| m, k'_fold (ff.fmap (pack_pred #f #ff m) x) |)
let unpack #f #ff x = ff.fmap (unpack_pred (dfst x)) (k'_unfold (dsnd x))

let unpack_pack_pred #f (#ff: functor u#a f) (n:nat) (x: predicate ff) =
  f_ext ((unpack_pred n (pack_pred n x))) (approx n x) fun _ -> ()

let pack_unpack #f #ff (| n, h |) =
  let h = k'_unfold h in
  ff.fmap_comp (pred' ff n (k' ff)) _ (pred' ff n (k' ff)) (pack_pred n) (unpack_pred n);
  f_ext (compose (pack_pred n) (unpack_pred #f #ff n)) id (pack_unpack_pred ff);
  ff.fmap_id _ h;
  assert ff.fmap id h == h

let unpack_pack #f #ff n h =
  ff.fmap_comp _ _ _ (unpack_pred n) (pack_pred #f #ff n);
  f_ext (compose (unpack_pred n) (pack_pred #f #ff n)) (approx n) fun x -> unpack_pack_pred n x
