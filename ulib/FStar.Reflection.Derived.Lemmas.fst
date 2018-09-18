module FStar.Reflection.Derived.Lemmas

open FStar.Reflection.Types
open FStar.Reflection.Basic
open FStar.Reflection.Data
open FStar.Reflection.Derived

val uncurry: ('a -> 'b -> 'c) -> (('a * 'b) -> 'c)
let uncurry f (x, y) = f x y

val curry: (('a * 'b) -> 'c) -> ('a -> 'b -> 'c)
let curry f x y = f (x, y)

// A glorified `id`
val list_ref: #a: Type -> #p: (a -> Type) -> l: list a ->
  Pure (list (x: a{p x})) (requires (forall_list p l)) (ensures (fun _ -> True))
let rec list_ref #a #p l =
  match l with
  | [] -> []
  | x :: xs -> x :: list_ref #a #p xs

val collect_app_ref: t: term -> (h: term{h == t \/ h << t}) * list (a: argv{fst a << t})
let collect_app_ref t =
  let h, a = collect_app t in
  admit (); // collect_app_order t;
  h, list_ref #_ #(fun a -> fst a << t) a

