module Bug015

val foo2 : m : int -> z : int -> unit
let rec foo2 m =
  match m with
  | _ -> (fun l -> foo2 m l)
