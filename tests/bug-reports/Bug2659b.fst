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

total reflectable effect {
  E0 (a : Type) (b : bool0) (p : index b)
  with {
    repr   = repr0;
    return = return0;
    bind   = bind0;
  }
}

let lift_pure_e0 (a : Type) (wp : pure_wp a) (f : unit -> PURE a wp)
  : Pure (repr0 a BT IT)
         (requires as_requires wp)
         (ensures fun _ -> True)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    f ()

sub_effect PURE ~> E0 = lift_pure_e0


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

total reifiable effect {
  E1 (a : Type) (b : bool0)
  with {
    repr   = repr1;
    return = return1;
    bind   = bind1;
  }
}

let lift_pure_e1 (a : Type) (wp : pure_wp a) (f : unit -> PURE a wp)
  : Pure (repr1 a BT)
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    f ()

sub_effect PURE ~> E1 = lift_pure_e1


let lift_e0_e1
      (a : Type) (b : bool0) (p : index b)
      (r : repr0 a b p)
  : repr1 a b
  = r

sub_effect E0 ~> E1 = lift_e0_e1


assume val return_False (_:unit) : E0 (squash False) BT IT

let make_BF (f : squash False) : unit -> E0 unit BF (false_elim ()) = false_elim ()

//
// Here we compute:
//   type of return_False () as E0 (squash False) BT IT
//   type of make_BF f () as E0 unit BF (false_elim ())
//
// And then the index false_elim () is typechecked in the top context, since the bind looks like:
//   M.bind #is #js f (fun (x:a) -> g), so the indices js of g are typechecked in the top context, without x
//
// And that fails in SMT

[@@ expect_failure [19]]
let absurd_e1 () : E1 unit BF =
  let f = return_False () in
  make_BF f ()
