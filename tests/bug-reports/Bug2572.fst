module Bug2572

module TC = FStar.Tactics.Typeclasses

class equatable (t:Type) = {
  eq: t -> t -> bool;
  reflexivity : (x:t -> Lemma (eq x x));
  symmetry: (x:t -> y:t -> Lemma (requires eq x y) (ensures eq y x));
  transitivity: (x:t -> y:t -> z:t -> Lemma (requires (x `eq` y /\ y `eq` z)) (ensures (x `eq` z)))
} 

[@@expect_failure [347]]
instance ( = ) (#t:Type) {|h: equatable t|} = h.eq

let ( = ) (#t:Type) {|h: equatable t|} = h.eq

class has_mul (t:Type) = { 
  mul : t -> t -> t;
  [@@@TC.no_method] eq: equatable t;
  [@@@TC.no_method] congruence: (x:t -> y:t -> z:t -> w:t 
                                 -> Lemma (requires (x=z) /\ (y=w)) 
                                         (ensures (mul x y)=(mul z w)))
} 

[@@expect_failure [347]]
instance ( * ) (#t:Type) {|m: has_mul t|} = m.mul
let ( * ) (#t:Type) {|m: has_mul t|} = m.mul

class has_add (t:Type) = {  
  add : t -> t -> t;
  [@@@TC.no_method] eq: equatable t;
  [@@@TC.no_method] congruence: (x:t -> y:t -> z:t -> w:t 
                                 -> Lemma (requires (x=z) /\ (y=w)) 
                                         (ensures add x y = add z w))  
} 

[@@expect_failure [347]]
instance ( + ) (#t:Type) {|a: has_add t|} = a.add
let ( + ) (#t:Type) {|a: has_add t|} = a.add

instance int_equatable : equatable int = {
  eq = op_Equality;
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ())
}

instance eq_of_add (t:Type) {| h: has_add t |} : equatable t = h.eq 
instance eq_of_mul (t:Type) {| h: has_mul t |} : equatable t = h.eq 

class semigroup (t:Type) = {  
  [@@@TC.no_method] has_mul : has_mul t; 
  [@@@TC.no_method] associativity: (x:t -> y:t -> z:t -> Lemma (((x * y) * z) = (x * (y * z))))
}

class add_semigroup (t:Type) = {
  [@@@TC.no_method] has_add : has_add t; 
  [@@@TC.no_method] associativity: (x:t -> y:t -> z:t -> Lemma (x = y))
}
