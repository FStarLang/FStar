module CherryBorrow
module U32 = FStar.UInt32

(* Borrowed parameters, borrowed fields, and the tail calls they keep. *)
let rec length (l: list string) : nat = match l with [] -> 0 | _ :: t -> 1 + length t

let rec rev_onto (l: list string) (acc: list string) : list string =
  match l with [] -> acc | x :: t -> rev_onto t (x :: acc)

let rec mem (s: string) (l: list string) : bool =
  match l with [] -> false | x :: t -> x = s || mem s t

(* Nested matches on borrowed fields, and a field returned. *)
let rec last2 (l: list (list string)) : string =
  match l with
  | [] -> "none"
  | [x :: _] -> x
  | _ :: t -> last2 t

(* Shadowing a borrowed field with an owned value. *)
let rec heads (l: list (list string)) : list string =
  match l with
  | [] -> []
  | x :: t ->
    let x = (match x with [] -> "-" | y :: _ -> y ^ "") in
    x :: heads t

(* Mutual recursion through borrowed and owned parameters. *)
let rec evens (l: list string) : list string =
  match l with [] -> [] | x :: t -> x :: odds t
and odds (l: list string) : list string =
  match l with [] -> [] | _ :: t -> evens t

(* A function with a borrowed parameter, as a closure. *)
let count_in (l: list string) (s: string) : nat = if mem s l then 1 else 0

let rec sum_map (f: string -> nat) (l: list string) : nat =
  match l with [] -> 0 | x :: t -> f x + sum_map f t

let rec app (a b: list string) : list string = match a with [] -> b | x :: t -> x :: app t b

(* Strings: owned for in-place append, borrowed for reading. *)
let rec concat (acc: string) (l: list string) : Tot string (decreases l) =
  match l with [] -> acc | x :: t -> concat (acc ^ x) t

type pair = { fst: list string; snd: string }
let swap (p: pair) : pair = { fst = p.snd :: p.fst; snd = "s" }
let pfst (p: pair) : list string = match p with { fst = f } -> f

let main () : U32.t =
  let l = ["a"; "b"; "c"; "d"] in
  let r = rev_onto l [] in
  let ll = [l; r; []] in
  let h = heads ll in
  let c = concat "" (app (evens l) (odds r)) in
  let k = sum_map (count_in r) ["a"; "z"; "c"] in
  let p = swap { fst = l; snd = "x" } in
  let ok =
    length l = 4 && mem "c" r && not (mem "q" l) &&
    last2 ll = "none" && last2 [r; ["y"]] = "y" &&
    concat "" h = "ad-" && c = "acca" && k = 2 && length (pfst p) = 5 in
  if ok then 0ul else 1ul
