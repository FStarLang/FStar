module DecreasesTypeWarning

let rec f (x:nat)  () : string =
  if x = 0 then "" else f (x - 1) ()
and g (xs:list nat) () : string =
  match xs with
  | [] -> ""
  | x::xs -> f x () ^ g xs ()
