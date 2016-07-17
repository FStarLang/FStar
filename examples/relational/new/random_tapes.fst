module Random_Tapes

open Rel
open Bijection

(* Experimenting with random tapes *)

type random_tape = int -> Tot int

val sample : random_tape -> int -> Tot int
let sample r i =  r i

  (* Working around some bug with projectors *)
val left : r:(rel random_tape) -> Tot ( r':random_tape{R.l r = r'})
let left r = R.l r

val right : r:(rel random_tape) -> Tot (r':random_tape{R.r r = r'})
let right r = R.r r

  (*Just for testing purposes (use instead of bij for much faster verification) *)
type bla (#a:Type) (#b:Type) = a -> Tot b

type rel_random_tape (b:(int -> Tot bla)) = r:(rel random_tape){forall i. b i (left r i) = right r i}

val id : bla #int #int 
let id x = x 

  (* Working around a bug *)
val add' : int -> int -> Tot int
let add' x y = y + x

val minus' : int -> int -> Tot int
let minus' x y = y - x

  (* Proving the function used is a blaection *)
val add : int -> Tot (bla #int #int)
let add x = cut (inverses (add' x) (minus' x)); add' x 

  (* Definition of a simple one time pad *)
val otp : int -> random_tape -> int -> Tot int
let otp n r i = n + r i

  (* Random tape used for relational verification *)
val otp_rand : x:(rel int) -> int -> Tot (bla #int #int)
let otp_rand x i = if i = 0 then 
                     add (R.l x - R.r x)
                   else 
                     id

  (* otp perfectly hides input *)
val otp_eq : x:(rel int) -> r:(rel_random_tape (otp_rand x)) ->
            Lemma (b2t (r_eq(lift3 otp x r (R 0 0))))
let otp_eq x r = ()

  (* Same thing for a pair of values *)
val otp2 : int -> int -> random_tape -> int -> int -> Tot (int * int)
let otp2 n m r i j = (n + r i, m + r j)

val otp2_rand : x:(rel int) -> y:(rel int) -> int -> Tot (bla #int #int)
let otp2_rand x y i = 
  match i with
  | 0 -> add (R.l x - R.r x)
  | 1 -> add (R.l y - R.r y)
  | _ -> id

val otp2_eq : x:(rel int) -> y:(rel int) -> r:(rel_random_tape (otp2_rand x y)) ->
            Lemma (b2t (r_eq(lift5 otp2 x y r (R 0 0) (R 1 1))))
let otp2_eq x y r = ()
