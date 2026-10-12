module CherrySepApp
module U32 = FStar.UInt32
module L = CherrySepLib
module IA = FStar.ImmutableArray
open FStar.All
open FStar.Dyn

(* The application half of CherrySepLib: it uses the library's types, whose
   counting helpers it generates for itself, and its exceptions and dynamic
   values, which it recognizes by name. *)
let hide (#a: Type) (x: a) : ML a = x

exception Mine of list int

let rec sum (l: list int) : int = match l with [] -> 0 | x :: t -> x + sum t

let main () : ML U32.t =
  let a = sum (L.mk (hide 4)) + sum L.g in
  let b = try L.boom (hide "x") with L.Oops m -> (if m = "x" then 1 else 100) | e -> raise e in
  let d = L.wrap (hide [5]) in
  assume (dyn_has_ty d (list int));
  let l : list int = undyn d in
  let k = hide 3 in
  let m = L.map (fun x -> x * k) (hide [1; 2; 3]) in
  let m2 = try sum (L.map (fun x -> if x = 2 then raise (Mine [x; x]) else x) (hide [1; 2; 3]))
           with Mine l -> 100 + sum l | e -> raise e in
  let p1 = L.protect (fun () -> raise (L.Oops "cb")) in
  let p2 = try L.protect (fun () -> raise (Mine [9])) with Mine _ -> "mine" | e -> raise e in
  let f = L.adder (hide 10) in
  let r = L.cell (hide [1; 1]) in
  r := 4 :: !r;
  let ia = L.arr (hide [2; 3]) in
  assume (IA.length ia = 2);
  let s1 = L.Poly (hide [1]) in
  let eq1 = L.same s1 (L.Poly [1]) && not (L.same s1 (L.Circle 1)) && s1 = L.Poly [1] in
  assume (dyn_has_ty L.gd L.shape);
  let gs : L.shape = undyn L.gd in
  let ok = a = 16 && b = 1 && sum l = 5 && sum m = 18 && m2 = 104 &&
           p1 = "caught cb" && p2 = "mine" && f 5 = 15 && sum !r = 6 &&
           IA.index ia 1 = 3 && eq1 && gs = L.Poly [7; 8] in
  if ok then 0ul else 1ul
