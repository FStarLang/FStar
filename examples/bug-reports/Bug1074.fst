module Bug1074

type foo =
  | MkFoo: nat -> foo

assume type bar : foo -> Type0

let works (x: (f:foo & bar f)) =
  let (| mk, _ |) = x in
  let MkFoo i = mk in
  i

let used_to_fails (x: (f:foo & bar f)) =
  let (| MkFoo i, _ |) = x in
  i

%Fail [54]
let fails_but_thats_ok (x: (f:foo & bar f)) =
  let (| MkFoo i, j |) = x in
  j

let does_not_fail_if_annot (x: (f:foo & bar f)) : bar (dfst x) =
  let (| MkFoo i, j |) = x in
  j
