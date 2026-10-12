module CherryExn
module U32 = FStar.UInt32
open FStar.All

(* Exceptions (cherry.md, "Exceptions"), as error returns: a raise leaves
   every function between it and its handler, each releasing what it holds,
   which AddressSanitizer's leak check sees.  The inputs come through [hide]
   so that extraction cannot fold them. *)
let hide (#a: Type) (x: a) : ML a = x

exception Boom of int
exception Bang of string & list int
exception Plain

let rec len (l: list int) : nat = match l with [] -> 0 | _ :: t -> 1 + len t

(* Deep in a non-tail recursion, with a list held at every level. *)
let rec down (n: int) (acc: list string) : ML (list string) =
  if n = 0 then raise (Boom 42)
  else if n = 1000 then raise (Bang ("deep", [1; 2; 3]))
  else let r = down (n - 1) ("x" :: acc) in "y" :: r

let f (n: int) : ML string =
  try (let l = down n [] in match l with [] -> "nil" | x :: _ -> x) with
  | Boom k -> "boom " ^ string_of_int k
  | Bang (s, l) -> "bang " ^ s ^ " " ^ string_of_int (len l)
  | e -> raise e

(* Not caught here: the inner [try] raises it again. *)
let g (n: int) : ML string =
  try f n with Plain -> "plain" | e -> raise e

(* A raise before the cell that reuses the matched one is built. *)
let rec map_chk (l: list int) : ML (list int) =
  match l with
  | [] -> []
  | x :: tl -> if x < 0 then raise (Boom x) else let tl' = map_chk tl in (x + 1) :: tl'

let rec sum (l: list int) (a: int) : int = match l with [] -> a | x :: t -> sum t (a + x)

let try_map (l: list int) : ML int =
  try sum (map_chk l) 0 with Boom k -> k | e -> raise e

(* Through closures, and a closure applied to more than it takes. *)
let thrower (s: string) : int -> ML int =
  fun x -> if x > 5 then raise (Bang (s, [])) else x

let apply (h: int -> ML int) (x: int) : ML int = let y = h x in y + 1

let through (n: int) : ML string =
  try string_of_int (apply (thrower "c") n) with Bang (a, _) -> "bang " ^ a | e -> raise e

let k (x: int) : ML (string -> ML string) =
  if x > 0 then raise (Boom x) else (fun y -> y ^ "!")

let over (h: int -> ML (string -> ML string)) (x: int) (s: string) : ML string =
  try h x s with Boom _ -> "over" | e -> raise e

(* Mutable state survives, and a raise from a handler is caught outside. *)
let rec go (r: ref (list string)) (i n: int) : ML unit =
  if i < 10 then begin
    (if i = n then raise (Bang ("loop", [])) else ());
    r := "it" :: !r;
    go r (i + 1) n
  end

let loop (n: int) : ML string =
  let r = alloc ["start"] in
  try go r 0 n; "done" with
  | Bang _ -> (match !r with x :: _ -> x | [] -> "nil")
  | e -> raise e

let nested (n: int) : ML string =
  try (try (if n > 0 then raise (Boom n) else "z") with Boom _ -> raise Plain | e -> raise e) with
  | Plain -> "plain"
  | e -> raise e

(* [failwith] raises [Failure], which can be caught. *)
let pick (l: list string) : ML string = match l with x :: _ -> x | [] -> failwith ("empty " ^ "list")

let fails (l: list string) : ML string =
  try pick l with Failure m -> "failure: " ^ m | e -> raise e

(* A global's initializer. *)
let glob : string = try (let _ = k (hide 1) in "no") with Boom _ -> "global" | e -> raise e

let main () : ML U32.t =
  let ok1 = g (hide 10) = "boom 42" && g (hide 2000) = "bang deep 3" &&
            g (hide 20000) = "bang deep 3" &&
            (try raise Plain with Plain -> true | _ -> false) in
  let ok2 = try_map (hide [1; 2; 3]) = 9 && try_map (hide [1; (-7); 3]) = (-7) in
  let ok3 = through (hide 3) = "4" && through (hide 9) = "bang c" &&
            over k (hide 0) (hide "a" ^ "b") = "ab!" && over k (hide 1) (hide "a" ^ "b") = "over" in
  let ok4 = loop (hide 4) = "it" && loop (hide 40) = "done" &&
            nested (hide 1) = "plain" && nested (hide 0) = "z" && glob = "global" in
  let ok5 = fails (hide ["a"]) = "a" && fails (hide []) = "failure: empty list" in
  if ok1 && ok2 && ok3 && ok4 && ok5 then 0ul else 1ul
