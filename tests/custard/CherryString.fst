module CherryString
module U32 = FStar.UInt32

(* The accumulator is uniquely referenced, so each append is in place. *)
let rec build (acc: string) (n: nat) : Tot string (decreases n) =
  if n = 0 then acc else build (acc ^ "ab") (n - 1)

let rec repeat (s: string) (n: nat) : string =
  if n = 0 then "" else s ^ repeat s (n - 1)

type person = { name: string; age: int }

let greet (p: person) : string =
  "Hi " ^ p.name ^ " (" ^ string_of_int p.age ^ ")"

let rec join (l: list string) : string =
  match l with
  | [] -> ""
  | [x] -> x
  | x :: tl -> x ^ "," ^ join tl

let classify (s: string) : U32.t =
  match s with
  | "a" -> 1ul
  | "bb" -> 2ul
  | _ -> 0ul

let sub_eq (s: string) (i l: nat) (r: string) : bool =
  if i + l <= String.length s then String.sub s i l = r else false

let index_eq (s: string) (i: nat) (c: FStar.Char.char) : bool =
  if i < String.length s then String.index s i = c else false

let main () : U32.t =
  let b = build "" 1000 in
  let ok_build = String.length b = 2000 && sub_eq b 1996 4 "abab" in
  let u = "h\u00e9llo w\u20acrld" in
  let ok_utf8 =
    String.length u = 11 && index_eq u 1 '\u00e9' && index_eq u 7 '\u20ac' &&
    sub_eq u 6 5 "w\u20acrld" && sub_eq u 0 0 "" in
  let ok_cmp =
    String.compare "abc" "abd" < 0 && String.compare "b" "a" > 0 &&
    String.compare "x" "x" = 0 && String.compare "ab" "abc" < 0 &&
    "abc" <> "abd" && repeat "xy" 3 = "xyxyxy" in
  let ok_pat = classify "bb" = 2ul && classify ("b" ^ "b") = 2ul && classify "c" = 0ul in
  let p = { name = "Ann"; age = pow2 70 } in
  let ok_rec = greet p = "Hi Ann (1180591620717411303424)" && p.name = "Ann" in
  let ok_list = join ["a"; "bc"; p.name; repeat "-" 2] = "a,bc,Ann,--" in
  if not ok_build then 1ul else if not ok_utf8 then 2ul else
  if not ok_cmp then 3ul else if not ok_pat then 4ul else
  if not ok_rec then 5ul else if not ok_list then 6ul else 0ul
