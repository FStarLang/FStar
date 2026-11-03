module CherryClaim
open FStar.All
module U32 = FStar.UInt32

(* A shared cell whose only reference is the one in hand (rc = -1) is claimed:
   it becomes this thread's own again and is reused or updated in place, like
   a unique one (cherry.md, "Heap cell reuse").  Values put into a global
   reference are shared, and taking them out and clearing the reference
   leaves exactly that.  A shared cell that is still referenced elsewhere is
   copied, and the other reference sees it unchanged.  ASan checks that every
   field is released exactly once on each path. *)

[@@FStar.Attributes.cherry_boxed]
type env = { name: string; depth: int; seen: list string; tag: string }

let push (e:env) (s:string) : env = { e with seen = s :: e.seen }

let rec join (l: list string) : string = match l with [] -> "" | x :: t -> x ^ join t

let show (e:env) : string =
  e.name ^ ":" ^ string_of_int e.depth ^ ":" ^ join e.seen ^ ":" ^ e.tag

let rec bump (l:list int) : list int =
  match l with
  | [] -> []
  | x :: t -> (x + 1) :: bump t

let rec sum (l:list int) : int = match l with [] -> 0 | x :: t -> x + sum t

let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n - 1)

(* Each starts as [None]: a global's initial value is persistent. *)
let renv : ref (option env) = alloc None
let rlist : ref (option (list int)) = alloc None
let rstr : ref (option string) = alloc None

let take (#a:Type) (r:ref (option a)) (d:a) : ML a =
  let v = match !r with Some v -> v | None -> d in
  r := None;
  v

let main () : ML U32.t =
  renv := Some { name = "n" ^ "0"; depth = 0; seen = []; tag = "t" ^ "0" };
  rlist := Some (upto 1000);
  rstr := Some ("a" ^ "b");
  (* Sole references: updated, reused and appended to in place. *)
  let e = push (take renv ({ name = ""; depth = 0; seen = []; tag = "" })) "x" in
  let l = bump (take rlist []) in
  let s = take rstr "" ^ "c" in
  let ok1 = show e = "n0:0:x:t0" && sum l = 501500 && s = "abc" in
  (* Still referenced by the global reference: copied. *)
  renv := Some e;
  rlist := Some l;
  rstr := Some s;
  let e' = match !renv with Some v -> push v "y" | None -> e in
  let l' = match !rlist with Some v -> bump v | None -> l in
  let s' = (match !rstr with Some v -> v | None -> "") ^ "d" in
  let ok2 = show e' = "n0:0:yx:t0" && sum l' = 502500 && s' = "abcd" &&
            (match !renv with Some v -> show v = "n0:0:x:t0" | None -> false) &&
            (match !rlist with Some v -> sum v = 501500 | None -> false) &&
            (match !rstr with Some v -> v = "abc" | None -> false) in
  if ok1 && ok2 then 0ul else 1ul
