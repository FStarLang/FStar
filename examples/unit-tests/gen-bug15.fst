
module GenBug15

val foo2 : m : int -> l : int -> unit
let foo2 m =
  match m with
  | 0 -> (fun l => ())
  | _ -> (fun l => ())
