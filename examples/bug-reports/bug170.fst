module Bug170

type t =
  | A
assume type sorted: t -> Type
assume val split: unit -> Dv t
assume val merge: l1:t -> Dv (r:t{sorted l1})
assume val foo : t -> Dv t

val mergesort: t -> Dv t
let mergesort l =
  match split() with
    | A ->
      let sl1 = foo l in
      merge sl1
