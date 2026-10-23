module CherryClosure
module U32 = FStar.UInt32

let rec map (#a #b: Type) (f: a -> b) (l: list a) : list b =
  match l with [] -> [] | x :: tl -> f x :: map f tl

let rec fold (#a #b: Type) (f: b -> a -> b) (acc: b) (l: list a) : Tot b (decreases l) =
  match l with [] -> acc | x :: tl -> fold f (f acc x) tl

let rec join (l: list string) : string =
  match l with [] -> "" | [x] -> x | x :: tl -> x ^ "," ^ join tl

(* A top-level function as a value, and partially applied. *)
let add (a b: int) : int = a + b
let suffix (s: string) (t: string) : string = t ^ s

(* Closures returning closures: arity raising and partial application of
   the raised function. *)
let adder (n: int) : int -> int = fun x -> x + n
let compose (#a #b #c: Type) (f: b -> c) (g: a -> b) : a -> c = fun x -> f (g x)
let twice (f: int -> int) : int -> int = compose f f

(* Called with more arguments than the definition takes. *)
let pick (b: bool) : int -> int = if b then adder 1 else twice (fun x -> x * 3)

(* Lambdas capturing counted values: a list, a string, and a closure. *)
let tag_all (t: string) (l: list string) : list string = map (fun x -> t ^ ":" ^ x) l
let scale_all (k: int) (l: list int) : list int = map (fun x -> x * k) l
let with_len (l: list int) : list int =
  let n = fold (fun c _ -> c + 1) 0 l in
  map (fun x -> x + n) l

(* Closures held in data. *)
noeq type handler = { name: string; run: int -> int }

let run_all (hs: list handler) (x: int) : list string =
  map (fun h -> h.name ^ "=" ^ string_of_int (h.run x)) hs

(* A closure given fewer arguments than it takes, from inside a closure. *)
let mul (a b: int) : int = a * b
let partials (l: list (int -> int -> int)) : list (int -> int) =
  map (fun (f: int -> int -> int) -> f 10) l

let main () : U32.t =
  let l = [1; 2; 3] in
  let big = 100000000000 in
  let a = map (add big) l in
  let b = map (suffix "!") ["x"; "y"] in
  let c = map (compose (adder 2) (fun x -> x * 10)) l in
  let d = pick true 5 + pick false 1 in
  let e = tag_all "t" ["a"; "b"] in
  let f = scale_all big l in
  let g = with_len l in
  let k = "!" in
  let h = fold (fun acc x -> acc ^ x ^ k) "" ["p"; "q"] in
  let hs = [ { name = "inc"; run = adder 1 };
             { name = "sq"; run = (fun x -> x * x) };
             { name = "tw"; run = twice (add big) } ] in
  let r = run_all hs 7 in
  let fs = map adder l in
  let i = fold (fun acc (f: int -> int) -> f acc) 0 fs in
  let k2 = "?" in
  let ps = partials [mul; (fun a b -> a - b); (fun a b -> a + b + String.length k2)] in
  let j = map (fun (f: int -> int) -> f 3) ps in
  if fold add 0 a = 3 * big + 6 &&
     join b = "x!,y!" &&
     fold add 0 c = 66 &&
     d = 15 &&
     join e = "t:a,t:b" &&
     fold add 0 f = 6 * big &&
     fold add 0 g = 15 &&
     h = "p!q!" &&
     join r = "inc=8,sq=49,tw=200000000007" &&
     i = 6 &&
     fold add 0 j = 30 + 7 + 14
  then 0ul else 1ul
