module FStarC.Class.Listlike

open FStarC.Effect

let is_empty (#e #s : Type) {| listlike e s |} (l : s) : bool =
  match view l with
  | VNil -> true
  | VCons _ _ -> false

let singleton (#e #s : Type) {| listlike e s |} (x : e) : s =
  cons x empty

let rec to_list (#e #s : Type) {| listlike e s |} (l : s) : list e =
  match view l with
  | VNil -> []
  | VCons x xs -> x :: to_list xs

let rec from_list (#e #s : Type) {| listlike e s |} (l : list e) : s =
  match l with
  | [] -> empty
  | x :: xs -> cons x (from_list xs)
