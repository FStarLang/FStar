module SortBy
open FStar.All

class ord (a:Type) = { cmp : a -> a -> ML int }

let rec sort (#a:Type) {| ord a |} (xs: list a) : ML (list a) =
  let rec insert (x:a) (xs:list a) : ML (list a) =
    match xs with
    | [] -> [x]
    | y :: ys -> if cmp x y <= 0 then x :: y :: ys else y :: insert x ys
  in
  match xs with
  | [] -> []
  | x :: xs -> insert x (sort xs)

(* Section 3.2b: [d] is a local name for a dictionary assembled on the fly out
   of a [Mono] parameter.  It is not a runtime parameter, and the key
   computation has to see through the [let] to know that.  This is the shape
   [FStarC.Class.Ord.sort_by] is written in. *)
let sort_by (#[@@@monomorphize] a:Type) ([@@@monomorphize] f : a -> a -> ML int)
            (xs: list a) : ML (list a) =
  let d : ord a = { cmp = f } in
  sort #a #d xs

(* A chain of [let]s, to check the unfolding runs to a fixpoint. *)
let sort_desc (#[@@@monomorphize] a:Type) ([@@@monomorphize] f : a -> a -> ML int)
              (xs: list a) : ML (list a) =
  let g : a -> a -> ML int = fun x y -> f y x in
  let d : ord a = { cmp = g } in
  let e : ord a = d in
  sort #a #e xs

let main () : ML unit =
  let pr (l: list int) : ML unit =
    match l with
    | x :: _ -> FStar.IO.print_string (string_of_int x)
    | [] -> FStar.IO.print_string "e" in
  pr (sort_by (fun (x:int) y -> x - y) [3;1;2]);
  pr (sort_desc (fun (x:int) y -> x - y) [3;1;2]);
  FStar.IO.print_string "\n"
