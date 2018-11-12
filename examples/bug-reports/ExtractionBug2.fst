module ExtractionBug2

type list (a: Type) =
  | Nil
  | Cons of a * (list a)

let rec app_my_lists (#a: Type) (l1: list a) (l2: list a): list a =
  match l1 with
  | Nil -> l2
  | Cons (x, xs) -> Cons (x, app_my_lists xs l2)

let rec app l1 l2 =
  match l1 with
  | [] -> l2
  | x::xs -> x :: (app xs l2)
