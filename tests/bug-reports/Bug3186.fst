module Bug3186

let base (x:int) (_: unit {equals x 0}) =
  assert (x == 0)

let base2 (x:int) (hyp: equals x 0) =
  let Refl = hyp in 
  assert (x == 0)

let base2' (x:int) (hyp: equals x 0) =
  assert (x == 0)

[@@expect_failure [19]]
let base3 (x:int) =
  assume (equals x 0);
  (* This fails since (equals x 0) is not encoded as a formula
     in the SMT solver, as there is no enclosing squash *)
  assert (x == 0)

type vec (a: Type) : n: nat -> Type =
  | Nil : vec a 0
  | Cons : #n: nat -> hd: a -> tl: vec a n -> vec a (n + 1)

// example from book
let pconv_vec_z (#a: Type) (#n: nat) (_: (n == 0)) (v: vec a n) : vec a 0 = v

let pconv_vec_z' (#a: Type) (#n: nat) (_:unit{equals n 0}) (v: vec a n) : vec a 0 = v

let pconv_vec_z'' (#a: Type) (#n: nat) (_:(_:unit{equals n 0})) (v: vec a n) : vec a 0 = v
