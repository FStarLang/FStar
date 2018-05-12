module FStar.PropositionalExtensionality

assume val axiom : unit -> Lemma (forall (p1:prop) (p2:prop). (p1 <==> p2) <==> (p1 == p2))

let apply (p1 p2:prop) : Lemma ((p1 <==> p2) <==> (p1 == p2)) =
  axiom ()

(*
 * AR: 05/12: these lemmas provide equations for logical operations in prims
 *            which now get a shallow embedding only (changes related to logical)
 *            these are needed in FStar.TSet etc., which use prop
 *            and need to know that eq2 etc. are sub-singletons
 *            when proper prop comes in from c_prop-dev, these should go away
 *)
let lemma_l_True_equation (_:unit)
  :Lemma (l_True == squash c_True)
  = assert_norm (l_True == squash c_True)

let lemma_l_False_equation (_:unit)
  :Lemma (l_False == squash c_False)
  = assert_norm (l_False == squash c_False)

let lemma_eq2_equation (#a:Type) (x y:a)
  :Lemma ((x == y) == squash (equals x y))
  = assert_norm ((x == y) == squash (equals x y))

let lemma_eq3_equation (#a:Type) (#b:Type) (x:a) (y:a)
  :Lemma ((x === y) == squash (h_equals x y))
  = assert_norm ((x === y) == squash (h_equals x y))

let lemma_l_and_equation (p q:Type0)
  :Lemma ((p /\ q) == squash (c_and p q))
  = assert_norm ((p /\ q) == squash (c_and p q))

let lemma_l_or_equation (p q:Type0)
  :Lemma ((p \/ q) == squash (c_or p q))
  = assert_norm ((p \/ q) == squash (c_or p q))

let lemma_l_imp_equation (p q:Type0)
  :Lemma ((p ==> q) == squash (p -> GTot q))
  = assert_norm ((p ==> q) == squash (p -> GTot q))

let lemma_l_not_equation (p:Type0)
  :Lemma ((~ p) == squash (p -> GTot False))
  = assert_norm ((~ p) == squash (p -> GTot False))

let lemma_l_Forall_equation (a:Type) (p:a -> GTot Type0)
  :Lemma ((l_Forall #a p) == squash (x:a -> GTot (p x)))
  = assert_norm ((l_Forall #a p) == squash (x:a -> GTot (p x)))

let lemma_l_Exists_equation (a:Type) (p:a -> GTot Type0)
  :Lemma ((l_Exists #a p) == squash (x:a & p x))
  = assert_norm ((l_Exists #a p) == squash (x:a & p x))
