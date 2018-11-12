module Bug1449

assume val acc : string -> string -> Dv string

let rec f a l : Dv _ =
  match l with
  | [] -> a
  | hd::tl -> f (acc hd a) tl
