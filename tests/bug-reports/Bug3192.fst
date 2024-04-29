module Bug3192

open FStar.Tactics.V2
open FStar.Reflection.Typing

let id (x:int) : int = x

[@@expect_failure [19]]
let bad (x y : term) =
  let t1 = `(id (`#x)) in
  let t2 = `(id (`#y)) in
  assert_norm (t1 == t2)

let t_unit = `()

let mk_eq2 (ty t1 t2 : term) : Tot term =
  (`squash (eq2 #(`#ty) (`#t1) (`#t2)))

let valid (g:env) (phi:term) : prop =
  squash (typing g t_unit (E_Total, mk_squash phi))

[@@expect_failure [19]]
let test (g t0 t1 t2 ty : _) =
  assume (valid g (mk_eq2 ty t0 t1));
  assert (valid g (mk_eq2 ty t0 t2));
  ()

[@@expect_failure [19]]
let test2 (ty t0 t1 : term) =
  let t1 = mk_eq2 ty t0 t0 in
  let t2 = mk_eq2 ty t0 t1 in
  assert (t1 == t2)
