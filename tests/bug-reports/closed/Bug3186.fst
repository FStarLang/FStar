module Bug3186


let base (x:int) (_: unit {x == 0}) =
  assert (x == 0)

let base2 (x:int) (_: (x == 0)) =
  assert (x == 0)

let base3 (x:int) =
  assume (nonempty (equals x 0));
  (* [Prims.nonempty] is a plain definition (unfolding to an existential),
     so the SMT solver does see through it. *)
  assert (x == 0)

type vec (a: Type) : n: nat -> Type =
  | Nil : vec a 0
  | Cons : #n: nat -> hd: a -> tl: vec a n -> vec a (n + 1)

// example from book
let pconv_vec_z (#a: Type) (#n: nat) (_: (n == 0)) (v: vec a n) : vec a 0 = v

let pconv_vec_z' (#a: Type) (#n: nat) (_:unit{n == 0}) (v: vec a n) : vec a 0 = v

let pconv_vec_z'' (#a: Type) (#n: nat) (_:(_:unit{n == 0})) (v: vec a n) : vec a 0 = v
