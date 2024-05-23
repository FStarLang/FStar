module Lib.LoopCombinators

let rec repeat_left lo hi a f acc =
  if lo = hi then acc
  else repeat_left (lo + 1) hi a f (f lo acc)

let rec repeat_left_all_ml lo hi a f acc =
  if lo = hi then acc
  else repeat_left_all_ml (lo + 1) hi a f (f lo acc)

let rec repeat_right lo hi a f acc =
  if lo = hi then acc
  else f (hi - 1) (repeat_right lo (hi - 1) a f acc)

let rec repeat_right_all_ml lo hi a f acc =
  if lo = hi then acc
  else f (hi - 1) (repeat_right_all_ml lo (hi - 1) a f acc)

let rec repeat_right_plus lo mi hi a f acc =
  if hi = mi then ()
  else repeat_right_plus lo mi (hi - 1) a f acc

let unfold_repeat_right lo hi a f acc0 i = ()

let eq_repeat_right lo hi a f acc0 = ()

let rec repeat_left_right lo hi a f acc =
  if lo = hi then ()
  else
    begin
    repeat_right_plus lo (lo + 1) hi a f acc;
    repeat_left_right (lo + 1) hi a f (f lo acc)
    end

let repeat_gen n a f acc0 =
  repeat_right 0 n a f acc0

let repeat_gen_all_ml n a f acc0 =
  repeat_right_all_ml 0 n a f acc0

let unfold_repeat_gen n a f acc0 i = ()
(* // Proof when using [repeat_left]:
  repeat_left_right 0 (i + 1) a f acc0;
  repeat_left_right 0 i a f acc0
*)

let eq_repeat_gen0 n a f acc0 = ()

let repeat_gen_def n a f acc0 = ()

let repeati #a n f acc0 =
  repeat_gen n (fixed_a a) f acc0

let repeati_all_ml #a n f acc0 =
  repeat_gen_all_ml n (fixed_a a) f acc0

let eq_repeati0 #a n f acc0 = ()

let unfold_repeati #a n f acc0 i =
  unfold_repeat_gen n (fixed_a a) f acc0 i

let repeati_def #a n f acc0 = ()

let repeat #a n f acc0 =
  repeati n (fixed_i f) acc0

let eq_repeat0 #a f acc0 = ()

let unfold_repeat #a n f acc0 i =
  unfold_repeati #a n (fixed_i f) acc0 i


let repeat_range #a min max f x =
  repeat_left min max (fun _ -> a) f x

let repeat_range_all_ml #a min max f x =
  repeat_left_all_ml min max (fun _ -> a) f x

let repeat_range_inductive #a min max pred f x =
  repeat_left min max (fun i -> x:a{pred i x}) f x

let repeati_inductive #a n pred f x0 =
  repeat_range_inductive #a 0 n pred f x0

let unfold_repeat_right_once 
    (lo:nat)
    (hi:nat{lo < hi})
    (a:(i:nat{lo <= i /\ i <= hi} -> Type))
    (f:(i:nat{lo <= i /\ i < hi} -> a i -> a (i + 1)))
    (acc:a lo)
  : Lemma (repeat_right lo hi a f acc ==
           f (hi - 1) (repeat_right lo (hi - 1) a f acc))
  = ()

module T = FStar.Tactics

let refine_eq (a:Type) (p q:a -> prop) (x:squash (forall (i:a). p i <==> q i))
  : Lemma ((i:a{p i} == i:a{q i}))
  = let pext (a:Type) (p q: a -> prop) (_:squash (forall (x:a). p x <==> q x)) (x:a) : Lemma (p x == q x) 
        = FStar.PropositionalExtensionality.apply (p x) (q x)
    in
    assert (i:a{p i} == i:a{q i})
        by (T.l_to_r [quote (pext a p q x)]; T.trefl())

let nat_refine_equiv (n:nat)
  : Lemma ((i:nat{i <= n}) == (i:nat{0<=i /\ i<=n})) 
  = let b2t_prop (b:bool) 
      : Lemma ((b2t b) `subtype_of` unit) 
      = assert_norm (b2t b == squash (equals b true))
    in
    refine_eq nat (fun (i:nat) -> b2t_prop (i <= n); b2t (i <= n)) (fun (i:nat) -> 0 <= i /\ i <= n) ()

let a' (#a:Type) (n:nat) (pred:(i:nat{i <= n} -> a -> Type)) = fun (i:nat{i<=n}) -> x:a{pred i x}

let repeati_repeat_left_rewrite_type (#a:Type) (n:nat) (pred:(i:nat{i <= n} -> a -> Type))
                                     (f:repeatable #a #n pred)
                                     (x0:a{pred 0 x0})
  : Lemma (repeati_inductive n pred f x0 ==
           repeat_left 0 n (a' n pred) f x0)
  =  assert (repeati_inductive n pred f x0 ==
             repeat_left 0 n (a' n pred) f x0)
         by (T.norm [delta_only [`%repeati_inductive;
                                 `%repeat_range_inductive;
                                 `%a']];
             T.l_to_r [`nat_refine_equiv];                                                   
             T.trefl())

(* This proof is technical, for multiple reasons. 

   1. It requires an extensionality lemma at the level to types to
      relate the type of a dependent function and an eta expansion of
      that type

   2. It requires an extensionality lemma at the level of the
      computation, which also introduces an eta expansion on f to
      retype it

   3. The retyping introduces a function type at a different by
      propositional equal domain, so it requires a use of rewriting
      based on propositional extensionality to prove that the retyping
      is benign

   The proof was simpler earlier, when F* had eta
   equivalence. But the use of eta reduction in the SMT encoding which
   this was relying on was a bit dodgy. In particular, the eta
   reduction hid the retyping and so was silently (and
   unintentionally) also enabling the use of propositional
   extensionality. Now, that has to be explicit.
*)      
let repeati_inductive_repeat_gen #a n pred f x0 =
  let eta_a n (a:(i:nat{0 <= i /\ i <= n} -> Type)) = fun i -> a i in
  let eta_f (f:repeatable #a #n pred) (i:nat{i < n}) (x:a' n pred i) : a' n pred (i + 1) = f i x in
  let rec repeat_right_eta
    (n:nat)
    (hi:nat{hi <= n})
    (a:(i:nat{0 <= i /\ i <= n} -> Type))
    (f:(i:nat{0 <= i /\ i < n} -> a i -> a (i + 1)))
    (acc:a 0) 
   : Lemma (ensures repeat_right 0 hi a f acc == repeat_right 0 hi (eta_a n a) f acc) 
           (decreases hi)
   = if hi = 0
     then () 
     else (repeat_right_eta n (hi - 1) a f acc)
  in
  repeat_right_eta n n (a' n pred) (eta_f f) x0;
  assert (repeat_gen n (fun i -> x:a{pred i x}) f x0 ==
          repeat_right 0 n (fun (i:nat{i <= n}) -> x:a{pred i x}) f x0)
       by (T.norm [delta_only [`%repeat_gen]];
           T.trefl());
  assert_norm (a' n pred == (fun (i:nat{i <= n}) -> x:a{pred i x}));
  assert (repeat_right 0 n (fun (i:nat{i <= n}) -> x:a{pred i x}) f x0 ==
          repeat_right 0 n (a' n pred) f x0);
  let rec repeat_right_eta_f
    (hi:nat{hi <= n})
    (acc:a' n pred 0)
   : Lemma (ensures repeat_right 0 hi (a' n pred) f acc ==
                    repeat_right 0 hi (a' n pred) (eta_f f) acc)
           (decreases hi)
   = if hi = 0
     then () 
     else (repeat_right_eta_f (hi - 1) acc)
  in
  repeati_repeat_left_rewrite_type n pred f x0;
  assert (repeati_inductive n pred f x0 ==
          repeat_left 0 n (a' n pred) f x0);
  repeat_left_right 0 n (a' n pred) f x0;
  assert (repeat_left 0 n (a' n pred) f x0 ==
          repeat_right 0 n (a' n pred) f x0); 
  repeat_right_eta_f n x0
  

let repeat_gen_inductive n a pred f x0 =
  let f' (i:nat{i < n})
	 (x:a i{pred i x /\ x == repeat_gen i a f x0})
	 : x':a (i + 1){pred (i + 1) x' /\ x' == repeat_gen (i + 1) a f x0}
	 = f i x in
  repeat_gen n (fun i -> x:a i{pred i x /\ x == repeat_gen i a f x0}) f' x0

let repeati_inductive' #a n pred f x0 =
  let f'
    (i:nat{i < n})
    (x:a{pred i x /\ x == repeati i f x0})
    : x':a{pred (i + 1) x' /\ x' == repeati (i + 1) f x0}
    = f i x in
  repeat_gen n (fun i -> x:a{pred i x /\ x == repeati i f x0}) f' x0
