module Bug212

noeq type foo : (unit -> Tot bool) -> Type =
  | Test : f:(unit -> Tot bool) -> foo f

val bar : foo (fun x -> true) -> unit
let bar t = match t with
  | Test f -> ()
