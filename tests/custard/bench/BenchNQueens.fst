module BenchNQueens
(* Koka's nqueens: every solution as a list, with the partial solutions
   sharing their tails. *)
module U32 = FStar.UInt32

let rec safe (queen: int) (diag: int) (xs: list int) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | q :: qs -> queen <> q && queen <> q + diag && queen <> q - diag && safe queen (diag + 1) qs

let rec append_safe (queen: int) (xs: list int) (xss: list (list int))
  : Tot (list (list int)) (decreases (if queen <= 0 then 0 else queen)) =
  if queen <= 0 then xss
  else if safe queen 1 xs then append_safe (queen - 1) xs ((queen :: xs) :: xss)
  else append_safe (queen - 1) xs xss

let rec extend (queen: int) (acc: list (list int)) (xss: list (list int))
  : Tot (list (list int)) (decreases xss) =
  match xss with
  | [] -> acc
  | xs :: rest -> extend queen (append_safe queen xs acc) rest

let rec find_solutions (n: int) (queen: int)
  : Tot (list (list int)) (decreases (if queen <= 0 then 0 else queen)) =
  if queen <= 0 then [[]] else extend n [] (find_solutions n (queen - 1))

let rec len (#a: Type) (l: list a) (acc: int) : int =
  match l with [] -> acc | _ :: t -> len t (acc + 1)

let main () : U32.t =
  if len (find_solutions 13 13) 0 = 73712 then 0ul else 1ul
