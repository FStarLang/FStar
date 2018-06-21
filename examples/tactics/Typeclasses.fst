module Typeclasses

open FStar.Tactics
open FStar.Tactics.Typeclasses

noeq
type eq a = {
    eq : a -> a -> bool;
}

[@tcnorm] let deq (#a:Type) [|eq a|] = Mkeq?.eq (solve ())

noeq
type additive a = {
    zero : a;
    plus : a -> a -> a;
}

[@tcnorm] let zero (#a:Type) [|additive a|] = Mkadditive?.zero (solve ())
[@tcnorm] let plus (#a:Type) [|additive a|] = Mkadditive?.plus (solve ())

noeq
type num a = {
    eq_super : eq a;
    add_super : additive a;
    minus : a -> a -> a;
}
[@tcnorm] let minus (#a:Type) [|num a|] = Mknum?.minus (solve ())

// Needed!
[@instance] let num_eq  (d : num 'a) : eq 'a = d.eq_super
[@instance] let add_num (d : num 'a) : additive 'a = d.add_super

let eq_instance_of_eqtype (#a:eqtype) : eq a =
  { eq = fun x y -> x = y }

[@instance] let eq_int : eq int  = eq_instance_of_eqtype
[@instance] let eq_bool : eq bool  = eq_instance_of_eqtype

[@instance] let eq_list (eqA : eq 'a) : eq (list 'a) =
  let rec eqList (xs ys : list 'a) = match xs, ys with
  | [], [] -> true
  | x::xs, y::ys -> deq x y && eqList xs ys
  | _, _ -> false
  in
  { eq = eqList }

let _ = assert (deq 1 1)
let _ = assert (not (deq 1 2))

[@instance]
let add_int : additive int = { zero = 0; plus = (+) }

[@instance]
let num_int : num int =
  { eq_super = solve  ();
    add_super = solve ();
    minus = (fun x y -> x - y); }

[@instance]
let add_bool : additive bool =
  { zero = false; plus = (fun x y -> x || y) }

[@instance]
let num_bool : num bool =
  { eq_super = solve  (); add_super = solve () ; minus = (fun x y -> x && not y) (* ?? *); }

[@instance]
let add_list #a : additive (list a) =
  { zero = []; plus = (@) }

let _ = assert (plus 1 2 = 3)
let _ = assert (plus false false = false)
let _ = assert (plus true false = true)
let _ = assert (plus [1] [2] = [1;2])

(* Up to now, that was simple overloading. Let's try some polymorphic uses *)

let rec sum (#a:Type) [|additive a|] (l : list a) : a =
    match l with
    | [] -> zero
    | x::xs -> plus x (sum xs)

let sum2 (#a:Type) [|additive a|] (l : list a) : a =
    List.Tot.fold_right plus l zero

let _ = assert_norm (sum2 [1;2;3;4] == 10)
let _ = assert_norm (sum2 [false; true] == true)

let sandwich (#a:Type) [|num a|] (x y z : a) : a =
    if deq x y
    then plus x z
    else minus y z

let test1 = sum [1;2;3;4;5;6]
let test2 = plus 40 (minus 10 8)
