module ValueRestriction

//val r : ref (option 'a)
// adding this signature fails, but not very convincingly
//value-restriction.fst(4,8-4,16) : Error
//Expected type "( -> Tot (ref (option 'a)))";
//got type "(ref U14519)"

let r = ref None  // -- this *leaks* an unification variable

val r1 : ref (option string)
let r1 = r                  // -- variable gets instantiated to string

val r2 : ref (option int)
let r2 = r
//value-restriction.fst(10,9-10,10) : Error
//Expected expression of type "(ref (option int))";
//got expression "r" of type "(ref (option string))"

// should try this once the above problem is fixed

//let write () = r1 := Some "foo"

//let v : int = Some.v (!r2)
