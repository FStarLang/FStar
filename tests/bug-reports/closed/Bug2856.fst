module Bug2856

// The implicit type parameter and constructor field share a name. Their
// projectors must not produce duplicate declarations in the SMT encoding.
noeq
type ty #a (x:a) =
  | I : (a:nat) -> ty x

let _ = assert (forall x. x + 1 > x)

let field_value (#a:Type) (x:a) (n:nat) : Lemma (I?.a (I #a #x n) == n) = ()
