#light "off"
module FStar.Projection.Util

let rec list_exists f l = 
  match l with
  | []    -> false
  | x::xs -> f x || list_exists f xs

let rec list_find f l = 
  match l with  
  | []    -> None
  | x::xs -> if f x then Some x else list_find f xs

let rec string_make n c = 
  if n = 0 then "" 
  else c ^ (string_make (n-1) c)
