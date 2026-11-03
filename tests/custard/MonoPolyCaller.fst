module MonoPolyCaller
open FStar.All
module L = FStar.List.Tot

(* Section 3.2b without --custard_monomorphize_types.  The callbacks of a
   polymorphic container are [Mono], so rule 5 makes the container's type
   parameters [Mono] too; but the callers below are themselves polymorphic,
   and pass their own runtime type parameters.  Types are compiled uniformly
   here, so those stay free type variables of the specialization rather than
   being rejected. *)
type tree (k:Type) (v:Type) =
  | Leaf : tree k v
  | Node : tree k v -> k -> v -> tree k v -> tree k v

let rec iter (#k #v:Type) (m:tree k v) ([@@@monomorphize] f : k -> v -> ML unit) : ML unit =
  match m with
  | Leaf -> ()
  | Node l x y r -> iter l f; f x y; iter r f

let rec fold (#k #v #a:Type) (m:tree k v) ([@@@monomorphize] f : k -> v -> a -> a) (acc:a) : a =
  match m with
  | Leaf -> acc
  | Node l x y r -> fold r f (f x y (fold l f acc))

(* [k] and [v] are runtime type parameters of the caller. *)
let count (#k #v:Type) (m:tree k v) : int =
  fold m (fun _ _ n -> n + 1) 0

(* The callback's type mentions the caller's [k] and [v] at positions where
   [fold] has its own [k] and [v]: the specialization must not confuse the
   two. *)
let flatten (#k #v:Type) (m:tree int (list (k & v))) : list (k & v) =
  fold m (fun _ vs acc -> L.append vs acc) []

(* Only [v] is mentioned by the callback, so [iter_values]'s [k] stays its
   own type variable, while the caller's [k] arrives free inside [v]: two
   different variables with the same name. *)
let rec iter_values (#k #v:Type) (m:tree k v) ([@@@monomorphize] f : v -> ML unit) : ML unit =
  match m with
  | Leaf -> ()
  | Node l _ y r -> iter_values l f; f y; iter_values r f

let sum_lengths (#k:Type) (m:tree int (list k)) (n:ref int) : ML unit =
  iter_values m (fun vs -> n := !n + L.length vs)

(* The specialization has to know [v] is a [ref] to assign it with [:=]. *)
let reset (m:tree string (ref bool)) : ML unit =
  iter m (fun _ r -> r := false)

let main () : ML unit =
  let r1 = alloc true in
  let r2 = alloc true in
  let m = Node (Node Leaf "a" r1 Leaf) "b" r2 Leaf in
  reset m;
  let p = Node Leaf 1 [("x", 1); ("y", 2)] (Node Leaf 2 [("z", 3)] Leaf) in
  FStar.IO.print_string (string_of_int (count m));
  FStar.IO.print_string " ";
  FStar.IO.print_string (string_of_int (L.length (flatten p)));
  FStar.IO.print_string " ";
  let n = alloc 0 in
  sum_lengths p n;
  FStar.IO.print_string (string_of_int !n);
  FStar.IO.print_string " ";
  FStar.IO.print_string (if !r1 || !r2 then "set" else "reset");
  FStar.IO.print_string "\n"
