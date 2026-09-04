module JoinRefinedLowerBounds

(* Two refined lower bounds on the same unification variable must be
   *joined*, not widened to their common base, when the bases agree only
   after delta-unfolding: [natlt n1] and [natlt n2] both unfold to a
   refinement of [nat], and widening to [nat] loses exactly what is needed
   to satisfy the later upper bound [natlt (max n1 n2)]. *)

let natlt (n:nat) = i:nat{i < n}

let max (a b:nat) : nat = if a > b then a else b

let merge_either (f1 : 'a -> GTot 'c) (f2 : 'b -> GTot 'c) (x : either 'a 'b) : GTot 'c =
  match x with
  | Inl y -> f1 y
  | Inr y -> f2 y

let test (a b:Type0) (n1 n2:nat)
         (f1 : a -> GTot (natlt n1))
         (f2 : b -> GTot (natlt n2))
  : (either a b -> GTot (natlt (max n1 n2)))
  = merge_either f1 f2

(* Conversely, when the two bases are already syntactically equal the join
   *is* widened to the base: a disjunction of two unrelated postconditions
   is not a type either side was written at. This is what keeps [eq2]'s
   type index usable by [apply] and friends. *)

assume val f (x y : int) : Tot (r:int{r == x + y})

let symm (x y : int) = assert (f x y == f y x)
