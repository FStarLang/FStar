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

(* Conventions given by attributes rather than inferred: a borrowed parameter
   that is stored (an inc at the store), an owned one that is only read (a
   dec at the end), and a mix with an inferred parameter. *)
let cons_b ([@@@cherry_borrowed] x: string) ([@@@cherry_borrowed] l: list string) : list string =
  x :: l
let len_o ([@@@cherry_owned] l: list string) : nat = 1 + length l
let rec app_bo ([@@@cherry_borrowed] a: list string) ([@@@cherry_owned] b: list string) (s: string)
  : list string =
  match a with [] -> s :: b | x :: t -> x :: app_bo t b s

(* Record projections of a borrowed value are borrowed: read, chained,
   returned, stored, and from a record held in a ref's cell. *)
type wrap = { inner: pair; tag: string }
let plen (p: pair) : nat = length p.fst + (if mem p.snd p.fst then 1 else 0)
let wlen (w: wrap) : nat = plen w.inner + length w.inner.fst
let wfst (w: wrap) : list string = w.inner.fst
let wcons (w: wrap) : list string = w.tag :: w.inner.fst
let rec wsum (ws: list wrap) : nat = match ws with [] -> 0 | w :: t -> wlen w + wsum t

let main () : U32.t =
  let l = ["a"; "b"; "c"; "d"] in
  let r = rev_onto l [] in
  let ll = [l; r; []] in
  let h = heads ll in
  let c = concat "" (app (evens l) (odds r)) in
  let k = sum_map (count_in r) ["a"; "z"; "c"] in
  let p = swap { fst = l; snd = "x" } in
  let cb = cons_b "z" l in
  let lo = len_o cb + len_o (cons_b "y" []) in
  let ab = app_bo l (app_bo r [] "m") "n" in
  let w = { inner = { fst = l; snd = "c" }; tag = "t" } in
  let ws = wsum [w; { w with tag = "u" }] in
  let wf = wfst w in
  let wc = wcons { inner = { fst = r; snd = "q" }; tag = "t" } in
  let fb = sum_map (fun s -> len_o (cons_b s l)) ["a"; "b"] in
  let ok =
    length l = 4 && mem "c" r && not (mem "q" l) &&
    last2 ll = "none" && last2 [r; ["y"]] = "y" &&
    concat "" h = "ad-" && c = "acca" && k = 2 && length (pfst p) = 5 &&
    lo = 8 && concat "" ab = "abcdndcbam" && fb = 12 && length l = 4 &&
    ws = 18 && length wf = 4 && concat "" wc = "tdcba" in
  if ok then 0ul else 1ul
