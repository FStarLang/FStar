module Bug1952a

type carrier = Type -> Type

// lawless functor
type t (c: carrier) =
  #a:Type -> #b:Type -> (a -> b) -> c a -> c b

let map (#c: carrier) [|map: t c|]: t c = map

(* fails with
  `(Error 189) Expected expression of type "t c";
   got expression "map" of type
   "(#[FStar.Tactics.Typeclasses.tcresolve ()] map: t c) -> Prims.Tot (t c)"` *)
let ( <$> ) #c [|t c|]: t c = map

(* fails with
  `(Error 120) Expected a term with 2 implicit arguments,
  but Control.Map.map has only 1` *)
let ( <$$> ) #c [|t c|]: t c = map #c
