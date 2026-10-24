module BenchClosures
(* Higher-order list functions over closures that capture counted and
   uncounted values. *)
module U32 = FStar.UInt32

let rec map (f: int -> int) (l: list int) : list int =
  match l with [] -> [] | x :: t -> f x :: map f t

let rec filter (f: int -> bool) (l: list int) : list int =
  match l with [] -> [] | x :: t -> if f x then x :: filter f t else filter f t

let rec foldl (f: int -> int -> int) (acc: int) (l: list int) : Tot int (decreases l) =
  match l with [] -> acc | x :: t -> foldl f (f acc x) t

let rec range (n: int) (acc: list int) : Tot (list int) (decreases (if n <= 0 then 0 else n)) =
  if n <= 0 then acc else range (n - 1) (n :: acc)

let compose (f g: int -> int) (x: int) : int = f (g x)

let rec go (j: int) (l: list int) (acc: int) : Tot int (decreases (if j <= 0 then 0 else j)) =
  if j <= 0 then acc else
  let k = j % 7 + 2 in
  let f = compose (fun x -> x + j) (fun x -> x * k) in
  let s = foldl (fun a x -> a + x) 0 (map f (filter (fun x -> x % k = 0) l)) in
  go (j - 1) l (acc + s)

let main () : U32.t =
  let l = range 1000 [] in
  if go 20000 l 0 = 59051879544 then 0ul else 1ul
