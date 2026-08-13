module ExtDatatypesMutual

/// Mutually recursive inductives and mutually recursive functions over them.
/// **Known C limitation, XFAIL_C** -- same root cause as ExtDatatypesRec:
/// the recursive occurrence is laid out by value, giving
/// "field 'case_Neg' has incomplete type" from the C compiler rather than a
/// diagnostic from krml.

module I32 = FStar.Int32
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one : U32.t = 1ul
let two : U32.t = 2ul
let three : U32.t = 3ul
let seven : U32.t = 7ul

type expr =
  | Lit : U32.t -> expr
  | Neg : expr -> expr
  | Sum : elist -> expr
and elist =
  | ENil : elist
  | ECons : expr -> elist -> elist

let rec eval (e:expr) : U32.t =
  match e with
  | Lit v -> v
  | Neg e -> U32.sub_mod 0ul (eval e)
  | Sum l -> eval_list l
and eval_list (l:elist) : U32.t =
  match l with
  | ENil -> 0ul
  | ECons e tl -> U32.add_mod (eval e) (eval_list tl)

/// A mutually recursive *predicate*, to check that the two functions are
/// emitted in an order the backend can handle (forward declarations in C).
let rec is_lit (e:expr) : bool =
  match e with
  | Lit _ -> true
  | Neg _ -> false
  | Sum l -> all_lits l
and all_lits (l:elist) : bool =
  match l with
  | ENil -> true
  | ECons e tl -> is_lit e && all_lits tl

let main () : I32.t =
     chk 1l (U32.eq (eval (Lit seven)) 7ul)
 &&& chk 2l (U32.eq (eval (Neg (Lit one))) 4294967295ul)
 &&& chk 3l (U32.eq (eval (Sum (ECons (Lit one) (ECons (Lit two) ENil)))) 3ul)
 &&& chk 4l (U32.eq (eval (Sum ENil)) 0ul)
 &&& chk 5l (U32.eq (eval (Neg (Neg (Lit three)))) 3ul)
 &&& chk 6l (is_lit (Lit one))
 &&& chk 7l (not (is_lit (Neg (Lit one))))
 &&& chk 8l (all_lits (ECons (Lit one) ENil))
 &&& chk 9l (not (all_lits (ECons (Neg (Lit one)) ENil)))
