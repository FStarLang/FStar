
module Coincidence

val mem: int -> list int -> Tot bool
let rec mem a l =
  match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl


val sorted: list int -> Tot bool
let rec sorted l =
  match l with
  | x::y::xs -> x < y && sorted (y::xs)
  | _ -> true


val lemma1 : y:int -> xs:list int ->
  Pure unit (requires (sorted xs && (xs = [] || y < Cons.hd xs)))
            (ensures (fun _ -> not (mem y xs)))
let rec lemma1 y xs =
  match xs with
  | []     -> ()
  | x::xs' -> lemma1 y xs'

val coincidence : xs:(list int){sorted xs} -> ys : (list int){sorted ys} ->
        Tot (zs:(list int){forall z. mem z zs <==> (mem z xs && mem z ys)})
let rec coincidence xs ys =
  match xs, ys with
  | x::xs', y::ys' ->
    if x = y then              x :: coincidence xs' ys'
    else if x < y then (lemma1 x ys; coincidence xs' ys)
    else               (lemma1 y xs; coincidence xs  ys')
  | _ -> []
