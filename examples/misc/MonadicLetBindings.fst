module MonadicLetBindings
open FStar.List.Tot

/// This module illustrates monadic let bindings, which exist in
/// OCaml, see https://v2.ocaml.org/manual/bindingops.html.
///
/// Monadic let bindings allows the user to write custom _let
/// operators_ to ease writing monadic programs.

(**** The [option] monad *)
// Bind operator
let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
  = match x with
  | Some x -> f x
  | None   -> None

// Sort of applicative
let (and?) (x: option 'a) (y: option 'b): option ('a * 'b)
  = match x, y with
  | Some x, Some y -> Some (x, y)
  | _ -> None

let head: list _ -> option _
  = function | v::_ -> Some v
             |   _ -> None

let option_example (a b: list (int * int)) (c: option bool) = 
  let? haL, haR = head a 
  and? hbL, hbR = head b in
  match? c with
  | true  -> Some (haL + hbL)
  | false -> Some (haR + hbR)

let letPunning (a: option int)
  = let? a in // equivalent to [let? a = a in]
    Some (a + 10)

let _ = assert_norm (option_example [(1,2)] [(3,4)] (Some true) == Some 4)
let _ = assert_norm (option_example [] [(3,4)] (Some true) == None)


(**** The [list] monad *)
let ( let:: ) (l: list 'a) (f: 'a -> list 'b): list 'b
  = flatten (map f l)

let rec zip (a: list 'a) (b: list 'b): list ('a * 'b)
  = match a, b with
  | ha::ta, hb::tb -> (ha,hb)::zip ta tb
  | _            -> []

let ( and:: ) (a: list 'a) (b: list 'b): list ('a * 'b)
  = zip a b

let list_example1 =
  let:: x = [10;20;30] in
  [x + 1; x + 2; x + 3]

let _ = assert_norm (list_example1 == [11;12;13;21;22;23;31;32;33])

let list_example2 =
  let:: x = [10;20;30]
  and:: y = ["A";"B";"C"] in
  [x + 5, y ^ "!"]

let _ = assert_norm (list_example2 == [15, "A!"; 25, "B!"; 35, "C!"])

(**** Example: evaluating expressions *)
type exp =
  | Const: int -> exp
  | Addition: exp -> exp -> exp
  | Division: exp -> exp -> exp

let rec eval (e: exp): option int
  = match e with
  | Const x -> Some x
  | Addition x y -> let? x = eval x
                   and? y = eval y in
                   Some (x + y)
  | Division x y -> match? eval y with
                 | 0 -> None
                 | y -> let? x = eval x in
                       Some (x / y)

