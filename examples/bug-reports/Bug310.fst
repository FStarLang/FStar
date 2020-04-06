module Bug310

(* Test capture of type variables *)

// [a] is emitted as 'a and 'Aa is emitted as 'Aa
type capture0 (a:Type) 'Aa = 'Aa*a

// [a] is emitted as ['a] and ['a] is emitted as ['a1]
type capture1 (a:Type) 'a = 'a*a

// [_a] is emitted as ['ua], and 'Aa is unchanged
type capture2 (_a:Type) 'Aa = 'Aa*_a

// [_a] is emitted as ['ua], and ['ua[ is emitted as ['ua1]
type capture3 (_a:Type) 'ua = 'ua*_a

// primes in type variables rewritten
// so, [a'] is extracted as ['au]
// and ['au] is extracted as ['au1]
type tickvar (a':Type) 'au = a' * a' * 'au

(* Clashes between top-level definitions and keywords *)

// [struct] is an OCaml keyword; so it is extracted as [struct1]
let struct = 0
// [struct1] is extracted as [struct11] to avoid capturing the previous def
let struct1 = 17
// [struct11] is extracted as [struct111] etc.
let struct11 = 18

(* Clashes between record fields and keywords *)

//both field names are ocaml keywords
//They are extracted as
// - [struct2] (to not clash with [struct1] above, though that isn't strictly necessary)
// - [constraint1]
type record_t = {
  struct : int;
  constraint: bool
}

(* Capture of local names, due to extraction-inserted eta expansions around magics *)

//1. Give [r] a non-prenex quantified type that
// will for F* to translate the argument [f] as [Obj.t -> Obj.t]
val r: unit -> a:Type -> f:(a -> a) -> int
let r _ _ _ = 0

//2. A binary function that we'll partially apply and pass to [r]
val g: int -> int -> int
let g _ _ = 0

val ko: int -> Tot int
let ko a =
  let a21 = a in
  let a = a in
  r () int (g a21) //we get an eta-expanded magic on [g a21]. The new variable is named [uu__1556], not clashing with any variable in scope

(* Capture avoidance even after reduction: the 2nd [x] is extracted as [x1] *)
let test =
  let x = 0 in
  [@inline_let] let y = x in
  let x = 2 in
  (y, x)
