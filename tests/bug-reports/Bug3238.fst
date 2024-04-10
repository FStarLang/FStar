module Bug3238

open FStar.Range

assume val p : range -> prop

assume val lem : r:range -> Lemma (p r)

let test () : range =
  let r = normalize_term (mk_range "asd" 1 2 3 4) in
  Classical.forall_intro lem;
  assert (p r);
  r
