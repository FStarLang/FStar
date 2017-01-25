module FStar.DM4F.IntStoreAux

abstract type index = nat

abstract val nth_opt (n:index) (l:list int) : Tot (option int)
let rec nth_opt (n:index) (l:list int) : Tot (option int) (decreases n) = match n, l with
  | 0, x :: xs -> Some x
  | _, [] -> None
  | n, x :: xs -> nth_opt (n-1) xs

abstract val set_nth_opt (acc:list int) (n:index) (l:list int) (y:int) : Tot (option (list int))
abstract let rec set_nth_opt (acc : list int) (n:index) (l:list int) (y:int)
  : Tot (option (list int)) (decreases n)
= match n, l with
  | 0, x :: xs -> Some (List.Tot.rev acc @ y :: xs)
  | _, [] -> None
  | n, x :: xs -> set_nth_opt (x :: acc) (n-1) xs y

let index_from_nat (n:nat) : index = n

let rec in_ (r:index) (store:list int) : Tot Type0 (decreases r) =
  match r, store with
  | 0, x :: xs -> True
  | _, [] -> False
  | r, x :: xs -> (r-1) `in_` xs
