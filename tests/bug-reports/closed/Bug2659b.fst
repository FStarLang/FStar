module Bug2659b

//
// A slightly modified version of Bug2659
//   that does not use degenerate effects,
//   but assumes a return_False,
//   since in the absence of degeneracy, implementing such an assume False is not possible
//
// It illustrates the typechecking of indexed effects implicits
//

[@@ erasable]
noeq type bool0 = | BT | BF

[@@ erasable]
noeq type index : (b : bool0) -> Type =
  | IT : index BT

let elim_index_BF (i : index BF) : Lemma False
  = ()

//
// The repr is an a, as opposed to unit in the original Bug 2659 report
//
type repr0 (a : Type) (b : bool0) (p : index b) = a

let return0 (a : Type) (x : a) : repr0 a BT IT = x

let bind0
      (a0 a1 : Type) (b0:bool0) (p0:index b0)
      (b1 : bool0) (p1 : index b1)
      (r0 : repr0 a0 b0 p0) (r1 : a0 -> repr0 a1 b1 p1)
  : repr0 a1 b1 p1
  = r1 r0

//
// The two monads are used directly: their indices cannot be effect indices
// any more, since an effect representation must have shape a:Type -> Type.
//

let ( let! ) (a0 a1 : Type) (b0:bool0) (p0:index b0) (b1 : bool0) (p1 : index b1)
             (r0 : repr0 a0 b0 p0) (r1 : a0 -> repr0 a1 b1 p1)
  : repr0 a1 b1 p1
  = bind0 a0 a1 b0 p0 b1 p1 r0 r1

let lift_pure_e0 (a : Type) (f : unit -> a) : repr0 a BT IT = f ()


let repr1 (a : Type) (b : bool0) = a

let return1 (a : Type) (x : a) : repr1 a BT = x

//
// The bind has a precondition False,
//   so it can never be applied
//

let bind1
      (a0 a1 : Type) (b0 b1 : bool0)
      (r0 : repr1 a0 b0) (r1 : a0 -> repr1 a1 b1)
  : Pure (repr1 a1 b1) False (fun _ -> True)
  = false_elim ()

let lift_pure_e1 (a : Type) (f : unit -> a) : repr1 a BT = f ()

let lift_e0_e1
      (a : Type) (b : bool0) (p : index b)
      (r : repr0 a b p)
  : repr1 a b
  = r


assume val return_False (_:unit) : repr0 (squash False) BT IT

let make_BF (f : squash False) : unit -> repr0 unit BF (false_elim ()) = false_elim ()

//
// Sequencing in the E1 monad is impossible: its bind has precondition False.
// Under the old indexed-effect elaboration this was hidden, because the
// indices of the continuation were typechecked in the top context.
//

[@@ expect_failure [19]]
let absurd_e1 () : repr1 unit BT =
  bind1 _ _ _ _ (return1 _ ()) (fun _ -> return1 _ ())
