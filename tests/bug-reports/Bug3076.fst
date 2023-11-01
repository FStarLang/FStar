module Bug3076

#set-options "--fuel 0 --ifuel 0"

type t2 = int & int

let f2 (x:t2) : t2=
  match x with
  | (x1, x2) -> (x2, x1)

// We can prove things on pairs with an ifuel of 0 (instead of 1)
let f2_lemma (x:t2) : Lemma (f2 (f2 x) == x) = ()

type t3 = int & (int & int)

let f3 (x:t3) : t3 =
  match x with
  | (x1, (x2, x3)) -> (x2, (x3, x1))

let f3_lemma (x:t3) : Lemma (f3 ( f3 (f3 x)) == x) = ()

#push-options "--ifuel 1"
type t1 = option int & int

let f1 (x:t1) : t1 =
  match x with
  | (Some x1, x2) -> (Some x2, x1)
  | (None, x2) -> (None, x2)

let f1_lemma (x:t1) : Lemma (f1 (f1 x) == x)  = ()
#pop-options

#push-options "--fuel 0 --ifuel 0"
type t4 = unit & unit

let f4 (x:t4) =
  match x with
  | (x1, x2) -> (x2, x1)

let f4_lemma (x:t4)
  : Lemma (f4 x == x)
  = ()
#pop-options