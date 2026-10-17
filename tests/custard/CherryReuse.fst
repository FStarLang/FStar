module CherryReuse
module U32 = FStar.UInt32

(* Heap cell reuse: a cell whose last reference a match consumes is rebuilt
   in place.  Each function runs on unique and on shared input; ASan checks
   that neither path frees or reuses a live cell. *)
let rec map_len (l: list string) : list nat =
  match l with [] -> [] | x :: t -> FStar.String.strlen x :: map_len t

let rec rev_onto (l: list string) (acc: list string) : list string =
  match l with [] -> acc | x :: t -> rev_onto t (x :: acc)

(* Only some paths build a cell; the others free the token. *)
let rec filter_short (l: list string) : list string =
  match l with
  | [] -> []
  | x :: t -> if FStar.String.strlen x < 2 then x :: filter_short t else filter_short t

type tree =
  | Leaf
  | One : string -> tree
  | Node : tree -> string -> tree -> tree

(* Reuse across constructors: a [Node] cell holds a [One], and a [One] cell
   is too small for a [Node], so that one allocates. *)
let rec shrink (t: tree) : tree =
  match t with
  | Leaf -> Leaf
  | One s -> Node Leaf s Leaf
  | Node Leaf s Leaf -> One s
  | Node l s r -> Node (shrink r) s (shrink l)

let rec size (t: tree) : nat =
  match t with Leaf -> 0 | One _ -> 1 | Node l _ r -> size l + 1 + size r

let rec cat (t: tree) : string =
  match t with Leaf -> "" | One s -> s | Node l s r -> cat l ^ s ^ cat r

(* A wildcard field is released on the unique path. *)
let rec tails (l: list string) : list string =
  match l with [] -> [] | _ :: t -> "-" :: tails t

let rec join (l: list string) : string = match l with [] -> "" | x :: t -> x ^ join t

let main () : U32.t =
  let l = ["a"; "bb"; "c"; "ddd"] in
  let n1 = map_len l in                        (* l shared: copies *)
  let r = rev_onto l [] in                     (* l shared *)
  let f = filter_short ["x"; "yy"; "z"] in     (* unique: in place *)
  let n2 = map_len (rev_onto ["p"; "qq"] []) in (* unique *)
  let t = Node (One "a") "b" (Node Leaf "c" (One "d")) in
  let t1 = shrink t in                         (* t shared *)
  let t2 = shrink (shrink t1) in               (* unique *)
  let ts = tails ["u"; "v"] in
  let ok =
    join l = "abbcddd" && join r = "dddcbba" && join f = "xz" &&
    (match n1 with [1; 2; 1; 3] -> true | _ -> false) &&
    (match n2 with [2; 1] -> true | _ -> false) &&
    size t1 = 4 && cat t1 = "dcba" && size t2 = 4 && cat t = "abcd" &&
    cat t2 = "dcba" && join ts = "--" in
  if ok then 0ul else 1ul
