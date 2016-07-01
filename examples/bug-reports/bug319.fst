module Bug319

type t =
  | T: f:(t -> Tot False) -> t

let delta = T (fun x -> x.f x)

let omega: False = delta.f delta

val bug: unit -> Lemma False
let bug _ = ()
