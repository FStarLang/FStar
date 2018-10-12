module Simple
[@ plugin]
let id (x:int{x >= 0}) =
  let rec countdown (y:nat) =
    if y=0 then x
    else countdown (y - 1)
  in
  countdown x

[@ plugin]
let poly_id (#a:Type) (x:int{x >= 0}) (r:a) : a =
  let rec countdown (y:nat) =
    if y=0 then r
    else countdown (y - 1)
  in
  countdown x

[@ plugin]
let mk_n_list (#a:Type) (n:nat) (x:a) : list a =
  let rec aux (n:nat) out =
    if n = 0 then out
    else aux (n - 1) (x :: out)
  in
  aux n []

[@ plugin]
let poly_list_id (#a:Type) (l:list a) =
  let rec aux (l:list a) (out:list a) =
      match l with
      | [] -> List.Tot.rev out
      | hd::tl -> aux tl (hd::out)
  in
  aux l []

[@ plugin]
let rec eq_int_list (l m :list int) : Tot bool (decreases l) =
  match l, m with
  | [], [] -> true
  | l::ls, m::ms -> l = m && eq_int_list ls ms
  | _ -> false
