module FStarC.Class.Ord

open FStarC
open FStarC.Effect
open FStar.Tactics.Typeclasses

let (<?)  x y = cmp x y =  Lt
let (<=?) x y = cmp x y <> Gt
let (>?)  x y = cmp x y =  Gt
let (>=?) x y = cmp x y <> Lt

let min x y = if x <=? y then x else y
let max x y = if x >=? y then x else y

instance ord_eq (a:Type) (d : ord a) : Tot (deq a) = d.super

let rec sort #a xs =
   let rec insert (x:a) (xs:list a) : list a =
   match xs with
   | [] -> [x]
   | y::ys -> if x <=? y then x :: y :: ys else y :: insert x ys
  in
  match xs with
  | [] -> []
  | x::xs -> insert x (sort xs)

(* An advantage of not having instance canonicity:
we can just construct a dictionary with this new function
without to use a newtype (which would involve a traversal
of the list to convert into!). *)
let sort_by #a (f : a -> a -> order) xs =
  let d : ord a = {
    super = { (=?) = (fun a b -> f a b = Eq) };
    cmp = f;
  } in
  sort #a #d xs

let dedup #a xs =
  let open FStarC.List in
  let out = fold_left (fun out x -> if existsb (fun y -> x =? y) out then out else x :: out) [] xs in
  List.rev out

let rec insert_nodup #a {| ord a |} (x:a) (xs:list a) : list a =
  match xs with
  | [] -> [x]
  | y::ys ->
    match cmp x y with
    | Eq -> xs
    | Lt -> x :: xs
    | Gt -> y :: insert_nodup x ys

let rec sort_dedup #a xs =
  match xs with
  | [] -> []
  | x::xs -> insert_nodup x (sort_dedup xs)

let ord_list_diff (#a:Type0) {| ord a |} (xs ys : list a) : list a & list a =
  let open FStarC.Order in
  let xs = xs |> sort_dedup in
  let ys = ys |> sort_dedup in
  let rec go (xd, yd) xs ys : list a & list a =
    match xs, ys with
    | x::xs, y::ys -> (
      match cmp x y with
      | Lt -> go (x::xd, yd)    xs      (y::ys)
      | Eq -> go (xd,    yd)    xs      ys
      | Gt -> go (xd,    y::yd) (x::xs) ys
    )
    (* One of the two is empty, that's it *)
    | xs, ys -> (List.rev_append xd xs, List.rev_append yd ys)
  in
  go ([], []) xs ys

instance ord_int : ord int = {
   super = solve;
   cmp = compare_int;
}

instance ord_bool : ord bool = {
   super = solve;
   cmp = compare_bool;
}

instance ord_unit : ord unit = {
   super = solve;
   cmp = (fun _ _ -> Eq);
}

instance ord_string : ord string = {
   super = solve;
   cmp = (fun x y -> order_from_int (String.compare x y));
}

instance ord_option #a (d : ord a) : Tot (ord (option a)) = {
   super = solve;
   cmp = (fun x y -> match x, y with
          | None, None -> Eq
          | Some _, None -> Gt
          | None, Some _ -> Lt
          | Some x, Some y -> cmp x y
          );
}

instance ord_list #a (d : ord a) : Tot (ord (list a)) = {
   super = solve;
   cmp = (fun l1 l2 -> compare_list l1 l2 cmp);
}

instance ord_either #a #b (d1 : ord a) (d2 : ord b) : Tot (ord (either a b)) = {
   super = solve;
   cmp = (fun x y -> match x, y with
          | Inl _, Inr _ -> Lt
          | Inr _, Inl _ -> Gt
          | Inl x, Inl y -> cmp x y
          | Inr x, Inr y -> cmp x y
          );
}

instance ord_tuple2 #a #b (d1 : ord a) (d2 : ord b) : Tot (ord (a & b)) = {
   super = solve;
   cmp = (fun (x1, x2) (y1, y2) -> 
          lex (cmp x1 y1) (fun () ->
          cmp x2 y2));
}

instance ord_tuple3 #a #b #c (d1 : ord a) (d2 : ord b) (d3 : ord c): Tot (ord (a & b & c)) = {
   super = solve;
   cmp = (fun (x1, x2, x3) (y1, y2, y3) -> 
          lex (cmp x1 y1) (fun () ->
          lex (cmp x2 y2) (fun () ->
          cmp x3 y3)));
}

instance ord_tuple4 #a #b #c #d (d1 : ord a) (d2 : ord b) (d3 : ord c) (d4 : ord d): Tot (ord (a & b & c & d)) = {
   super = solve;
   cmp = (fun (x1, x2, x3, x4) (y1, y2, y3, y4) -> 
          lex (cmp x1 y1) (fun () ->
          lex (cmp x2 y2) (fun () ->
          lex (cmp x3 y3) (fun () ->
          cmp x4 y4))));
}

instance ord_tuple5 #a #b #c #d #e (d1 : ord a) (d2 : ord b) (d3 : ord c) (d4 : ord d) (d5 : ord e): Tot (ord (a & b & c & d & e)) = {
   super = solve;
   cmp = (fun (x1, x2, x3, x4, x5) (y1, y2, y3, y4, y5) -> 
          lex (cmp x1 y1) (fun () ->
          lex (cmp x2 y2) (fun () ->
          lex (cmp x3 y3) (fun () ->
          lex (cmp x4 y4) (fun () ->
          cmp x5 y5)))));
}

instance ord_tuple6 #a #b #c #d #e #f (d1 : ord a) (d2 : ord b) (d3 : ord c) (d4 : ord d) (d5 : ord e) (d6 : ord f): Tot (ord (a & b & c & d & e & f)) = {
   super = solve;
   cmp = (fun (x1, x2, x3, x4, x5, x6) (y1, y2, y3, y4, y5, y6) -> 
          lex (cmp x1 y1) (fun () ->
          lex (cmp x2 y2) (fun () ->
          lex (cmp x3 y3) (fun () ->
          lex (cmp x4 y4) (fun () ->
          lex (cmp x5 y5) (fun () ->
          cmp x6 y6))))));
}
