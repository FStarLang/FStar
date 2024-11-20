module Bug2684a

class typeclass (ty:Type0) = {
  meh: unit;
}

assume val the_ty: Type0
assume val the_pf: typeclass the_ty
instance _: typeclass the_ty = the_pf

// No bug if we:
// - remove `pf` in `t3`
// - try to remove the parameter of type `t2 p1` in `t3`
assume val t1: Type0
assume val t2: t1 -> Type0
assume val t3: ty:Type0 -> pf:typeclass ty -> p1:t1 -> p2:t2 p1 -> Type0

assume val t4: ty:Type0 -> pf:typeclass ty -> Type0

// No bug if we don't use meta-programmed typeclass instantiation
assume val t3_to_t4: #ty:Type0 -> {|pf:typeclass ty|} -> #p1:t1 -> #p2:t2 p1 -> t:t3 ty pf p1 p2 -> t4 ty pf

assume val t4_pred: t4 the_ty the_pf -> prop
assume val dtuple_pred: p1:t1 & p2:t2 p1 & t3 the_ty the_pf p1 p2 -> prop
// No bug if instead of `nat` we have a `int`
assume val nat_pred: nat -> prop

//Bug is still there if `n1` has type `int`
val the_lemma: p1:t1 -> p2:t2 p1 -> t:t3 the_ty the_pf p1 p2 -> n1:nat -> tl:t4 the_ty the_pf -> Lemma
  (requires t4_pred tl)
  (ensures True)
let the_lemma p1 p2 t n1 tl =
  // No bug if we remove this line, or if we instantiate the typeclass explicitly
  let _ = t3_to_t4 t in
  // No bug if we remove this line
  let (|_, _, _|) = (|p1, p2, t|) in

  // No bug if in the next 3 introduce/eliminate we
  // - remove `n0 <= n1`
  // - remove `nat_pred n0`
  // - replace `dtuple_pred (|p1, p2, t|)` with `True`
  // - remove one of the eliminates / introduce
  introduce (exists n0. n0 <= n1 /\ nat_pred n0) ==> dtuple_pred (|p1, p2, t|)
  with _. (
    eliminate exists n0. n0 <= n1 /\ nat_pred n0
    returns dtuple_pred (|p1, p2, t|)
    with _. (
      // No bug if we use `nat_pred` or a predicate for a new type
      // Bug is still there if we use `dtuple_pred` instead of `t4_pred`
      eliminate exists x. t4_pred x
      returns dtuple_pred (|p1, p2, t|)
      with _. (
        admit()
      )
    )
  )
