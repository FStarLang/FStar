module Bug933

let rec f (x: option nat) : unit =
  match x with
  | Some s -> g s
  | _ -> ()
and g s = ()
