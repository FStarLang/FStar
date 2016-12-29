module Bijection

open FStar.Constructive

type injective 'a 'b (f:('a -> Tot 'b)) =
       (forall (x1:'a) (x2:'a). f x1 == f x2 ==> x1 == x2)

type inverse 'a 'b (fab:('a -> Tot 'b)) (fba:('b -> Tot 'a)) =
       (forall (x:'a). fba (fab x) == x) /\ (forall (y:'b). fab (fba y) == y)

type bijective 'a 'b (f:('a -> Tot 'b)) =
  (f':('b -> Tot 'a) & squash(inverse 'a 'b f f'))
       (* cexists (fun (f':'b -> Tot 'a) -> *)
       (*   t:ctrue{inverse 'a 'b f f' /\ injective 'a 'b f /\ injective 'b 'a f'}) *)

val even : int -> Tot bool
let even i = (i % 2 = 0)

val foo : nat -> Tot int
let foo n = if even n then n/2 else -((n+1)/2)

val foo_inv : int -> Tot nat
let foo_inv i = let open FStar.Mul in if i >= 0 then i*2 else ((-i)*2)-1

val bijective_foo : bijective nat int foo
let bijective_foo = (| foo_inv, ()|)


#set-options "--detail_errors"

let pos_mul_stability (n1 n2 : pos) : Lemma (op_Multiply n1 n2 > 0) = ()

let nat_mul_stability (n1 n2 : nat) : Lemma (op_Multiply n1 n2 >= 0) =
  if n1 = 0 then assert (op_Multiply n1 n2 = 0)
  else if n2 = 0 then assert (op_Multiply n1 n2 = 0)
  else (assert (n1 > 0 /\ n2 > 0) ; pos_mul_stability n1 n2)

let mul_pred_nat (n:nat) : Lemma (n `mul` (n-1) / 2 >= 0)
  = if n = 0 then () else let n' : nat = n - 1 in nat_mul_stability n n'



val bar : nat * nat -> Tot nat
let bar (n1, n2) =
  let k : nat = n1 + n2 in
  let open FStar.Mul in
  if k = 0 then 0
  else begin
    let k' : nat = k - 1 in
    nat_mul_stability k k' ;
    k * (k-1) / 2 + n1
  end

let mul = op_Multiply

let g (x:nat) : int = x `mul` (x-1) / 2


let rec find_k0 (i k : nat)
  : Pure nat (requires (b2t (k >= g i)))
           (ensures (fun r -> g r <= k /\ k < g (r+1)))
  = if g (i+1) > k then i else find_k0 (i+1) k


let bar_inv : nat -> Tot (nat * nat)
let bar_inv k =
  find_k0 0 k

(*
  let rec find_antecedent #n f k i =
    if k = 0
    then None
    else if f (k-1) = i then Some (k-1)
    else find_antecedent f (k-1) i
*)
