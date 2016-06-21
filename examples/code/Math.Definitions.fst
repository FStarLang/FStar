module Math.Definitions

/////////////////////////////////////////////////////////////////
// In SSR:
// Record Zmodule (V : Type) : Type := Mixin
//  { zero : V;
//    opp : V -> V;
//    add : V -> V -> V;
//    _ : associative add;
//    _ : commutative add;
//    _ : left_id zero add;
//    _ : left_inverse zero opp add }
//////////////////////////////////////////////////////////////////
abstract type abelianGroup (#a:Type) (zero:a) (opp:a -> Tot a) (add:a -> a -> Tot a)  =
  // add is by typing a internal composition law for the group
  (forall x y z. add (add x y) z = add x (add y z)) // Associativity
  /\ (forall x y. add x y = add y x) // Commutativity
  /\ (forall x. add x zero = x) // Neutral element 
  /\ (forall x. add x (opp x) = zero) // Inverse

(*  Field predicate *)
abstract type commutativeField (#a:Type) (zero:a) (one:a) (opp:a -> Tot a) (add:a -> a -> Tot a) (inv:(e:a{e<>zero}) -> Tot a) (mul:a -> a -> Tot a) = 
  // '+' internal composition law
  (forall x y z. add (add x y) z = add x (add y z)) // '+' law's associativity
  /\ (forall x y. add x y = add y x)                 // '+' law's commutativity
  /\ (forall x. add x zero = x )                     // '+' neutral element // no need for the /\ since it is commutative
  /\ (forall x. add x (opp x) = zero)
  // '*' internal composition law
  /\ (forall x y z. mul (mul x y) z = mul x (mul y z)) // '*' law's associativity
  /\ (forall x y. mul x y = mul y x)                   // '*' law's commutativity
  /\ (forall x. mul x one = x)                         // '*' neutral element
  /\ (forall (x:a{x<>zero}). mul x (inv x) = one)       // inverse
  // Field properties
  /\ (zero <> one) 
  /\ (forall x y z. mul x (add y z) = add (mul x y) (mul x z) /\ mul (add x y) z = add (mul x z) (mul y z)) // Distributivity

val mandatory_lemma: n:nat ->
  Lemma (requires (n <> 0))
	(ensures (n-1>=0))
let mandatory_lemma n = ()	

val scalar_multiplication: #a:Type -> zero:a -> opp:(a -> Tot a) -> add:(a -> a -> Tot a){abelianGroup zero opp add} -> scalar:nat -> v:a -> Tot a (decreases scalar)
let rec scalar_multiplication #a zero opp add n p =
  match n with
  | 0 -> zero
  | _ -> 
    mandatory_lemma n;
    add p (scalar_multiplication zero opp add (n-1) p)
