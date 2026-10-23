module CherryRecordUpdate
module U32 = FStar.UInt32

(* Record updates (cherry.md): [{ r with f = v }] on a boxed record changes a
   unique [r] in place, and copies a shared or persistent one, which stays
   as it was.  ASan checks that the replaced fields are released exactly
   once on both paths. *)

[@@FStar.Attributes.cherry_boxed]
type env = { name: string; depth: int; seen: list string; admit: bool; tag: string }

let set_name (e:env) (s:string) : env = { e with name = s }

let push (e:env) (s:string) : env = { e with seen = s :: e.seen; depth = e.depth + 1 }

let rec push_all (e:env) (l:list string) : Tot env (decreases l) =
  match l with
  | [] -> e
  | x :: t -> push_all (push e x) t

(* [e] is still needed after the update. *)
let both (e:env) : env & env = ({ e with admit = true }, e)

let rec join (l: list string) : string = match l with [] -> "" | x :: t -> x ^ join t

let show (e:env) : string =
  e.name ^ ":" ^ string_of_int e.depth ^ ":" ^ join e.seen ^ ":" ^
  (if e.admit then "a" else "-") ^ ":" ^ e.tag

let global : env = { name = "g"; depth = 0; seen = ["s"]; admit = false; tag = "t" }

let main () : U32.t =
  let e0 = { name = "n" ^ "0"; depth = 0; seen = []; admit = false; tag = "t" ^ "0" } in
  let e1 = set_name e0 "m" in                     (* e0 shared: copies *)
  let e2 = push_all (set_name e1 "k") ["a"; "b"] in (* unique: in place *)
  let g1 = push global "x" in                     (* persistent: copies *)
  let (b1, b2) = both e2 in
  let ok =
    show e0 = "n0:0::-:t0" && show e1 = "m:0::-:t0" && show e2 = "k:2:ba:-:t0" &&
    show g1 = "g:1:xs:-:t" && show global = "g:0:s:-:t" &&
    show b1 = "k:2:ba:a:t0" && show b2 = "k:2:ba:-:t0" in
  if ok then 0ul else 1ul
