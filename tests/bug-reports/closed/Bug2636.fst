module Bug2636
open FStar.Tactics.V2


open FStar.Nonempty

type prop_with_pre (p : prop) (pf : squash p) : Type0
  = | PropWithPre

let lazy_and : prop
  = False /\ nonempty (prop_with_pre False ())


type this_type (t : Type) = | ThisType

let and_right (p0 p1 : prop) (_ : this_type (p0 /\ p1)) : prop
  = p1

//let  pwp_False  : Type0 = Bug2636.and_right Prims.l_False (Bug2636.prop_with_pre Prims.l_False ()) (Bug2636.ThisType)

// This fails to check now, in the application of exact,
// since the core typechecker returns a guard equal to False.
[@@expect_failure [189]]
let pwp_False : prop
  = _ by (apply (`and_right);
          dump "A";
          // [this_type (?p0 /\ ?p1)]
          exact (`(ThisType #lazy_and)))

// Just an utility function
// type display_term (#a : Type) (x : a) = unit

// let _ : display_term pwp_False
//   = _ by (norm [delta_only [`%pwp_False; `%and_right]];
//           dump "pwp_False"; // prop_with_pre l_False ()
//           exact (`()))


// let extract_pre (p : Type0) (pf : squash p) (_ : this_type (prop_with_pre p pf))
//   : squash p
//   = pf

// [@@expect_failure]
// let absurd : squash False
//   = _ by (apply (`extract_pre);
//           // [this_type (prop_with_pre l_False ?pf)]
//           exact (`(ThisType #pwp_False)))
