module PulseCore.IndirectionTheoryModel
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
let compose #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = F.on_dom a (fun x -> f (g x))
let id #a : (a ^-> a) = F.on_dom a (fun x -> x)
#push-options "--print_implicits --print_universes"
class functor (f: Type u#a -> Type u#a) = {
  fmap: (
    #a:Type ->
    #b:Type ->
    (a -> b) ->
    f a ->
    f b
  );
  fmap_id: (
    a:Type ->
    x:f a ->
    squash (fmap (id #a) == id #(f a))
  );
  fmap_comp: (
      a:Type ->
      b:Type ->
      c:Type ->
      b2c:(b -> c) ->
      a2b:(a -> b) ->
      squash (compose (fmap b2c) (fmap a2b ) ==
              fmap (compose b2c a2b))
  );
  tt : Type u#b;
  t_bot: tt;
}

class pre_knot (k:Type u#a) = {
  f:Type u#a -> Type u#a;
  ff: functor f;
  down: (nat & f (k -> ff.tt)) -> k;
  up: k -> (nat & f (k -> ff.tt));
}
instance pk_functor #k {| pk: pre_knot k |} : functor pk.f = pk.ff
let predicate (k:Type) {| pk:pre_knot k |} = k -> pk.ff.tt
let level (#k:Type) {| pk:pre_knot k |} (x:k) = fst (pk.up x)
let approx (#k:Type) {| pk:pre_knot k |} (n:nat) (p:predicate k)
: predicate k
= fun (w:k) -> if level w >= n then pk.ff.t_bot else p w

class knot (k:Type u#a) = {
  pk: pre_knot k;
  down_up: (
    x:k ->
    squash (down #k (up #k x) == x)
  );
  up_down: (
    n:nat ->
    x:(pk.f (k -> pk.ff.tt)) ->
    squash (up (down (n, x)) == (n, fmap (approx n) x))
  )
}
instance pre_knot_of_knot #k {| kk: knot k |} : pre_knot k = kk.pk

let test #k {| kk:knot k |} (x:k) = level x
let test2 #k {| kk:knot k |} (n:nat) (p:predicate k) = approx n p

module U = FStar.Universe
type pnat =
  | Z
  | S of pnat
let rec ipred (f:Type u#a -> Type u#a) {| ff: functor f |} (n:pnat)
: Type u#a
= match n with
  | Z -> U.raise_t unit
  | S n' -> ipred f n' & (f (ipred f n') -> ff.tt)
module T = FStar.Tactics
let fold_ipred_z
     (#f:Type u#a -> Type u#a)
     {| ff: functor f |}
: ipred f Z
= 
// coerce_eq  
//   ( _ by (
//     T.trefl())
//   )
  (U.raise_val ())

let fold_ipred_succ 
     (#f:Type u#a -> Type u#a)
     {| ff: functor f |}
     (n:pnat)
     (fst:ipred f n)
     (snd:(f (ipred f n) -> ff.tt))
: ipred f (S n)
= 
// coerce_eq  
//   ( _ by (
//     T.trefl())
//   )
  (fst, snd)

let unfold_ipred_succ 
     (#f:Type u#a -> Type u#a)
     {| ff: functor f |}
     (n:pnat)
     (pp:ipred f (S n))
: ipred f n &
  (f (ipred f n) -> ff.tt)
= 
// coerce_eq  
//   ( _ by (
//     T.trefl()
//     )
//   )
  pp

let tknot (f:Type u#a -> Type u#a) {| ff: functor f |}
: Type u#a
= n:pnat & f (ipred f n)

let klevel (#f:Type -> Type) {| ff:functor f |} (x:tknot f) = dfst x
let pred (f:Type -> Type) {| ff:functor f |} = tknot f -> ff.tt

let rec strat (f:Type u#a -> Type u#a) {| ff:functor f |} (n:pnat) (p:pred f)
: ipred f n
= match n with
  | Z -> fold_ipred_z #f #ff
  | S n -> 
    let fst : ipred f n = strat f n p in
    let snd : f (ipred f n) -> ff.tt = fun fi -> p (| n, fi |) in 
    fold_ipred_succ n fst snd

let rec psum (p q:pnat)
: pnat
= match p with
  | Z -> q
  | S p' -> S (psum p' q)

let rec floor (#f:Type u#a -> Type u#a) {| ff:functor f |}
          (m n:pnat)
          (p:ipred f (psum m n))
: ipred f n
= match m with
  | Z -> p
  | S m' -> 
    let fst, snd = unfold_ipred_succ (psum m' n) p in
    floor m' n fst

assume
val dec_leq (n k:pnat) 
: either
    (m:pnat { k == psum n m })
    (m:pnat { n == psum m (S k) })

let unstrat (#f: Type u#a -> Type u#a) {| ff:functor f |}
            (n:pnat) (p:ipred f n)
: pred f
= fun k -> 
    match dec_leq n (klevel k) with
    | Inl _ -> ff.t_bot
    | Inr m ->
      let p_sk : ipred f (S (klevel k)) = floor m (S (klevel k)) p in
      let _, pred_sk = unfold_ipred_succ _ p_sk in
      pred_sk (dsnd k)


let rec psum_snd (m n:pnat)
: Lemma (psum m (S n) == S (psum m n))
= match m with
  | Z -> ()
  | S m' -> psum_snd m' n

let rec floor_first (#f:Type u#a -> Type u#a) {| ff:functor f |}
          (m n:pnat)
          (p:ipred f (psum m (S n)))
: Lemma
  (ensures
    (psum_snd m n;
     fst (unfold_ipred_succ _ (floor m (S n) p)) ==
     floor m n (fst <| unfold_ipred_succ (psum m n) p)))
= psum_snd m n;
  match m with
  | Z -> ()
  | S m' -> 
    let p1, p2 = unfold_ipred_succ (psum m' (S n)) p in
    floor_first m' n p1

let rec floor_shuffle (#f:Type u#a -> Type u#a) {| ff:functor f |}
          (m n:pnat)
          (p:ipred f (psum m (S n)))
: Lemma
  (ensures
    (psum_snd m n;
     fst (unfold_ipred_succ _ (floor m (S n) p)) ==
     floor (S m) n p))
= psum_snd m n;
  match m with
  | Z -> ()
  | S m' -> 
    let p1, p2 = unfold_ipred_succ (psum m' (S n)) p in
    floor_shuffle m' n p1

let rec floor_equiv (#f:Type u#a -> Type u#a) {| ff:functor f |}
          (m1 m2 n:pnat)
          (p1:ipred f (psum m1 n))
          (p2:ipred f (psum m2 n))
: Lemma
  (requires
    floor _ _ p1 == floor _ _ p2)
  (ensures
    strat f n (unstrat _ p1) == strat f n (unstrat _ p2))
  (decreases n)
= match n with
  | Z -> ()
  | S n' ->
    psum_snd m1 n';
    psum_snd m2 n';
    assert (psum m1 n == psum m1 (S n'));
    calc (==) {
        strat f n (unstrat _ p1);
      (==) {}
        strat f (S n') (unstrat _ p1);
      (==) { _ by (T.trefl()) }
        fold_ipred_succ n' 
          (strat f n' (unstrat _ p1))
          (fun fi -> (unstrat _ p1) (| n', fi |));
      (==) { admit() (* by congruence  under fun fi, feq *) }
        fold_ipred_succ n' 
          (strat f n' (unstrat _ p1))
          (snd (unfold_ipred_succ _ (floor m1 n p1))); 
      (==) { (* by hyp *) }
        fold_ipred_succ n' 
          (strat f n' (unstrat _ p1))
          (snd (unfold_ipred_succ _ (floor m2 n p2)));
      (==) 
      {
        floor_shuffle #f m1 n' p1;
        floor_shuffle #f m2 n' p2;
        assert (floor (S m1) n' p1 == floor (S m2) n' p2);
        calc (==) {
          (strat f n' (unstrat _ p1));
        (==) { floor_equiv (S m1) (S m2) n' p1 p2 }
          (strat f n' (unstrat _ p2));
        }
      }
      fold_ipred_succ n' 
        (strat f n' (unstrat _ p2))
        (snd (unfold_ipred_succ _ (floor m2 n p2)));
      (==) { admit () (* by congruence  under fun fi *) }
        fold_ipred_succ n' 
          (strat f n' (unstrat _ p2))
          (fun fi -> (unstrat _ p2) (| n', fi |));
      (==) { _ by (T.trefl()) }
        strat f (S n') (unstrat _ p2);
      (==) {}
        strat f n (unstrat _ p2);
    }
