module CLamDef

(* Section 33.1.  A definition whose body is a lambda.  [go] has type arity
   two and binder arity one, so its result type is an arrow and its body is a
   closure over its own parameter -- which the C backend rejected as a
   captured lambda, although there is nothing to capture: [k] is [go]'s
   parameter and the lambda's binder is [go]'s second one.

   This is not eta-expansion and does not carry section 25.3's re-evaluation
   hazard, because there is nothing in front of the lambda to re-evaluate.

   It is here as its own case because Pulse writes eta-contracted definitions
   as a matter of course -- an [fn] of two binders extracts with the second in
   the result arrow -- so every Pulse program of more than one argument
   reaches the backend in this shape. *)

module U32 = FStar.UInt32

let ap (f : U32.t -> U32.t) (r : U32.t) : U32.t = f r

let go (k : U32.t) : U32.t -> U32.t = ap (fun x -> U32.add_mod x k)

(* The same shape one link further along: [go2]'s body is a *call* that
   returns a function rather than a lambda, so it is section 25's expansion
   and not the absorption above.  Both have to work for the Pulse spelling,
   which produces one of each. *)
let go2 (k : U32.t) : U32.t -> U32.t = go (U32.add_mod k 1ul)

let main () : U32.t =
  if go 3ul 4ul = 7ul && go2 3ul 4ul = 8ul then 0ul else 1ul
