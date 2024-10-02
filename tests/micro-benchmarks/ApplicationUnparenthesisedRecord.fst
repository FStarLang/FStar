module ApplicationUnparenthesisedRecord

type foo = { x: int; }

// A function that operates on `foo`
val f: foo -> foo
let f { x } = { x = x + 10 }

// Parenthesis can be omitted on function application
let ex1 = f ({ x = 3 })
let ex2 = f  { x = 3 }

// Though in the context of a named binder, this is a conflict, so
// parentheses are mandatory in that case. Otherwise [x:τ{x=1}] is
// ambiguous: it would either be:
//  - [τ] refined with [x=1] or
//  - [τ] applied to the record value [{x=1}].

// Example by Tahina Ramananandro:
type u = {x : unit}
let ffalse (_: u) = nat
let g (b: bool) : (if b then Type0 else (u → Type0)) = if b then unit else ffalse
type dummy =
  | Dummy1 : x: g true { x = () }    (* binder [x] of type [g true] refined such that [x] equals [()]
                                        ([g true] reduces to [unit]) *)
             → dummy
  | Dummy2 : x: g false ({ x = () }) (* binder [x] of type [g false ({x = ()})]
                                        ([g false something_of_type_u] reduces to [nat]) *)
             → dummy

// Omitting parentheses in [Dummy2] would fail; F* would parse that as
// a refinement, not a function application. For instance:
[@@expect_failure [12; 189]]
type dummy' =
  | Dummy3: x: g false { x = () }
             → dummy
