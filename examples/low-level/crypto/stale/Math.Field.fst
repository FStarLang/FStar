module Math.Field

open Math.Definitions

(** Field component definitions **)
assume new type felem
assume val zero: felem
type non_zero = f:felem{f <> zero}
assume val one: non_zero
assume val add: felem -> felem -> Tot felem
assume val mul: felem -> felem -> Tot felem
assume val opp: x:felem -> Tot (opp_x:felem{add x opp_x = zero})
assume val inv: x:non_zero -> Tot (inv_x:non_zero{mul x inv_x = one})
assume val mul_non_zero: x:non_zero -> y:non_zero -> Tot (z:non_zero{z = mul x y})

(* Group and field properties *)
assume val field_is_group_1: unit -> Lemma (abelianGroup #felem zero opp add)
assume val field_is_group_2: unit -> Lemma (abelianGroup #non_zero one inv mul_non_zero)
assume val field_is_commutative_field: unit -> 
  Lemma (commutativeField #felem zero one opp add inv mul)

(** Additional definitions, lemmas & notations **)

(* Equality in the field *)
assume new type equal: felem -> felem -> Type
assume val lemma_equal_intro: x:felem -> y:felem -> Lemma
  (requires (x == y))
  (ensures (equal x y))
  [SMTPat (equal x y)]
assume val lemma_equal_elim: x:felem -> y:felem -> Lemma
  (requires (equal x y))
  (ensures (x = y))
  [SMTPat (equal x y)]
assume val lemma_equal_refl: x:felem -> y:felem -> Lemma
  (requires (x = y))
  (ensures (equal x y))
  [SMTPat (equal x y)]

(* Subtraction and division definitions *)
val sub: x:felem -> y:felem -> Tot felem
let sub x y = add x (opp y)
val div: x:felem -> y:felem{y<>zero} -> Tot felem
let div x y = mul x (inv y)

(* Syntactic sugar: add is infix op ^+ and mul is infix op ^*
   scalar mult is +* and exponentiation is ^^ 
   subtraction is ^- and division is ^/ *)
let op_Hat_Plus = add
let op_Hat_Star = mul
let op_Plus_Star n x = 
  field_is_group_1 (); scalar_multiplication #felem zero opp add n x
val op_Hat_Hat: felem -> nat -> Tot felem
let rec op_Hat_Hat x n =
  match n with | 0 -> one | _ -> mul x (op_Hat_Hat x (n-1))
let op_Hat_Subtraction = sub 
let op_Hat_Slash = div

// Characteristic of the field
assume val characteristic: n:nat{
  ((exists c. c +* one = zero) ==> (n +* one = zero /\ (forall m. m +* one = zero ==> m >= n))) // finite field
  /\ (~(exists c. c +* one = zero) ==> n = 0) // infinite field
  }

(** Some lemmas **)
val sub_lemma: x:felem -> y:felem -> 
  Lemma
    (requires (x <> y))
    (ensures (sub x y <> zero))
    [SMTPat (sub x y)]
let sub_lemma x y = field_is_group_1 ()

(* Morphism between integers and field elements *)
assume val to_felem: x:int -> Tot felem
