module CoreNestedEffectfulLets

(* Each [&&] with an effectful operand is elaborated into a let of an
   effectful computation nested in the definition of the next one. Core
   types such a let at its result type refined by an existential over the
   definition's (refined) type; the term used to double in size at each level
   of nesting. *)

open FStar.All

let hide (#a:Type) (x:a) : ML a = x

let main () : ML int =
  let ok =
    hide true && true && true && true && true && true && true && true &&
    true && true && true && true && true && true && true && true &&
    true && true && true && true && true && true && true && true &&
    true && true && true && true && true && true && true && true &&
    true && true && true && true && true && true && true && true
  in
  if ok then 0 else 1
