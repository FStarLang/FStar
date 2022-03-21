module Bug2184

[@(strict_on_arguments [0])]
let ty (p : unit) : Type0 = unit

(*
 * We need to prove unit <: ty p
 * But due to strict_on_arguments ty p doesn't reduce
 *   in the unifier, and then the rigid-rigid subtyping query fails
 *)
[@@ expect_failure]
let test (p:unit) : ty p = ()

(*
 * But we could invoke SMT explicitly to complete this proof
 *   (from @Kachoc)
 *)
let coerce (#a:Type) (#b:Type{a == b}) (x:a) : b = x

let test_alt (p:unit) : ty p = coerce ()
