module Bug2125b

open FStar.List.Tot
open FStar.Tactics
open FStar.Calc

open FStar.FunctionalExtensionality

val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0

let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val w (a : Type u#a) : Type u#(max 1 a)
let w a = (w0 a)

val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

val interp (#a : Type) : list a -> w a
let interp #a (l:list a) = fun p -> forall x. memP x l ==> p x

let dm (a : Type) (wp : w a) : Type =
  ( pre:Type & (squash pre -> c:(list a){wp `w_ord` interp c}) )

let irepr (a : Type) (wp: w a) =
  dm a wp

let rec pmap #a #b #pre (#post:b->Type0)
  (f : (x:a -> Pure b (requires (pre x)) (ensures post)))
  (l : list a)
  : Pure (list (v:b{post v}))
         (requires (forall x. memP x l ==> pre x))
         (ensures (fun _ -> True))
  = match l with
    | [] -> []
    | x::xs -> f x :: pmap #_ #_ #pre #post f xs


let rec conjmapl #a
    (p : a -> Type0)
    (l : list a)
  : Pure Type0 (requires True)
               (ensures (fun pp -> pp ==> (forall x. memP x l ==> p x)))
  = match l with
    | [] -> True
    | x::xs -> p x /\ conjmapl p xs

let rec myflatten #a #wp (xss : list (m:(list a){wp `w_ord` interp m})) : m:(list a){wp `w_ord` interp m} =
  match xss with
  | [] -> []
  | xs::xss -> admit (); xs @ myflatten xss

[@@expect_failure [66]]
let ibind
  (a : Type) (b : Type)
  (wp_v : w a) (wp_f: a -> w b)
  (v : irepr a wp_v) (f : (x:a -> irepr b (wp_f x)))
: irepr b (fun _ -> False)
= let pre : Type0 = dfst v /\ conjmapl (fun x -> dfst (f x)) (dsnd v ()) in
  (| pre, (fun _ ->
             let vs = dsnd v () in
             let xss = pmap #a #(list b) #(fun x -> dfst (f x)) (fun x -> dsnd (f x) ()) vs in
             myflatten #_ #_ xss) |)

[@@expect_failure [66]]
let ibind2
  (a : Type) (b : Type)
  (wp_v : w a) (wp_f: a -> w b)
  (v : irepr a wp_v) (f : (x:a -> irepr b (wp_f x)))
: irepr b (fun _ -> False)
= let pre : Type0 = dfst v /\ conjmapl (fun x -> dfst (f x)) (dsnd v ()) in
  (| pre, (fun _ ->
             let vs = dsnd v () in
             let xss = pmap #a #(list b) #(fun x -> dfst (f x)) (fun x -> dsnd (f x) ()) vs in
             magic ()) |)
