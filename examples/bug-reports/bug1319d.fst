module Bug1319d

noeq
type foo a =
  | Foo : (b:Type -> foo b) -> foo a

[@(expect_failure [54])]
let rec f (t : option 'a) = match t with
  | Some b -> Foo (fun _ -> f b)
  | _ -> admit ()
