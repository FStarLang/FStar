module CherryGlobal
module U32 = FStar.UInt32

let rec fold (#a #b: Type) (f: b -> a -> b) (acc: b) (l: list a) : Tot b (decreases l) =
  match l with [] -> acc | x :: tl -> fold f (f acc x) tl

let rec join (l: list string) : string =
  match l with [] -> "" | [x] -> x | x :: tl -> x ^ "," ^ join tl

let add (a b: int) : int = a + b
let adder (n: int) : int -> int = fun x -> x + n

(* Globals of counted types: computed once, then persistent. *)
let big : int = 100000000000 * 100000000000
let nums : list int = [1; 2; big]
let names : list string = ["a"; "b" ^ "c"; string_of_int big]
let greeting : string = "hello" ^ ", " ^ "world"
let inc3 : int -> int = adder 3
let plus : int -> int -> int = add
let fns : list (int -> int) = [adder 1; inc3; (fun x -> x * big)]

noeq type cfg = { label: string; f: int -> int; xs: list int }
let config : cfg = { label = greeting; f = inc3; xs = nums }

(* A global computed from another global. *)
let sum_nums : int = fold add 0 nums

let main () : U32.t =
  let s = greeting ^ "!" in
  let t = join names in
  let a = inc3 4 in
  let b = plus 2 5 in
  let c = fold (fun acc (g: int -> int) -> g acc) 1 fns in
  let d = config.f (fold add 0 config.xs) in
  let n2 = 1 :: nums in
  if s = "hello, world!" &&
     t = "a,bc," ^ string_of_int big &&
     a = 7 && b = 7 &&
     c = 5 * big &&
     d = big + 6 &&
     sum_nums = big + 3 &&
     fold add 0 n2 = big + 4 &&
     config.label = "hello, world"
  then 0ul else 1ul
