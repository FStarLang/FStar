module Bug2366

(* Testcase for #2366, reported by @hacklex *)

//The bug was in typechecking the last definition,
//  the admit here is intentional
#push-options "--admit_smt_queries true"

type binary_op (a:Type) = a -> a -> a
type unary_op (a:Type) = a -> a
type predicate (a:Type) = a -> bool
type binary_relation (a: Type) = a -> a -> bool
 
[@@"opaque_to_smt"]
let is_reflexive  (#a:Type) (r: binary_relation a) = forall (x:a).     x `r` x
[@@"opaque_to_smt"]
let is_symmetric  (#a:Type) (r: binary_relation a) = forall (x y:a).   x `r` y == y `r` x
[@@"opaque_to_smt"]
let is_transitive (#a:Type) (r: binary_relation a) = forall (x y z:a). x `r` y /\ y `r` z ==> x `r` z 
 
type equivalence_relation (a: Type) = r:binary_relation a{is_reflexive r /\ is_symmetric r /\ is_transitive r}
 
[@@"opaque_to_smt"]
let equivalence_wrt_condition (#a: Type) (op: binary_op a) (eq: equivalence_relation a) = 
  (forall (x y z:a). (x `eq` y) ==> ((x `op` z) `eq` (y `op` z))  /\ (z `op` x) `eq` (z `op` y))
  
type equivalence_wrt (#a: Type) (op: binary_op a) = eq:equivalence_relation a{equivalence_wrt_condition op eq}

[@@"opaque_to_smt"]
let is_left_id_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (u `op` x) `eq` x // left identity
[@@"opaque_to_smt"]
let is_right_id_of (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (x `op` u) `eq` x // right identity
[@@"opaque_to_smt"]
let is_neutral_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = is_left_id_of u op eq /\ is_right_id_of u op eq // neutral element

[@@"opaque_to_smt"]
let is_unit (#a: Type) (x: a) (op:binary_op a) (eq: equivalence_relation a) 
  = exists (y:a). (is_neutral_of (x `op` y) op eq /\ is_neutral_of (y `op` x) op eq)
  
type units_of (#a: Type) (mul: binary_op a) (eq: equivalence_relation a) = x:a{is_unit x mul eq}

[@@"opaque_to_smt"]  
let respects_equivalence (#a:Type) (f: unary_op a) (eq: equivalence_relation a) = forall (x y:a). (x `eq` y) ==> (f x) `eq` (f y)

type unary_op_on_units_of (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) =
  f:unary_op(units_of op eq){
   respects_equivalence f (    
     reveal_opaque (`%is_reflexive (*`*)) (is_reflexive #a); 
     reveal_opaque (`%is_reflexive (*`*)) (is_reflexive #(units_of op eq)); 
     reveal_opaque (`%is_symmetric (*`*)) (is_symmetric #a);   
     reveal_opaque (`%is_symmetric (*`*)) (is_symmetric #(units_of op eq));   
     reveal_opaque (`%is_transitive (*`*)) (is_transitive #a);
     reveal_opaque (`%is_transitive (*`*)) (is_transitive #(units_of op eq));
     reveal_opaque (`%is_unit (*`*)) (is_unit #a); 
     //added the backtick to limit github highlighting disaster
     eq
   )
  }

noeq type magma (#a: Type) =  
{
  op: binary_op a;
  eq: equivalence_wrt op;
  inv: unary_op_on_units_of op eq;
  neutral: a
}

[@@"opaque_to_smt"]
let is_associative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y z:a). ((x `op` y) `op` z) `eq` (x `op` (y `op` z))
[@@"opaque_to_smt"]
let is_commutative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y:a). (x `op` y) `eq` (y `op` x)


let yields_inverses_for_units (#a:Type) (op: binary_op a) (eq: (t: equivalence_wrt op {is_associative op t})) (inv: unary_op_on_units_of op eq) = 
  forall (x: units_of op eq). is_neutral_of (op (inv x) x) op eq /\ is_neutral_of (op x (inv x)) op eq

let all_are_units (#a:Type) (op: binary_op a) (eq: equivalence_wrt op {is_associative op eq}) = 
  forall (x:a). is_unit x op eq
  
type semigroup (#a:Type)             = g: magma #a{is_associative g.op g.eq /\ yields_inverses_for_units #a g.op g.eq g.inv}
type commutative_magma (#a:Type)     = g: magma #a{is_commutative g.op g.eq}
type commutative_semigroup (#a:Type) = g: semigroup #a{is_commutative g.op g.eq}
type monoid (#a:Type)                = g: semigroup #a{is_neutral_of g.neutral g.op g.eq}
type commutative_monoid (#a:Type)    = g: monoid #a{is_commutative g.op g.eq}
type group (#a:Type)                 = g: monoid #a{all_are_units g.op g.eq}
type commutative_group (#a:Type)     = g: group #a{is_commutative g.op g.eq}
[@@"opaque_to_smt"]
let is_left_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). (x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))
[@@"opaque_to_smt"]
let is_right_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). ((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z))
[@@"opaque_to_smt"]
let is_fully_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). ((x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))) /\ (((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z)))



let is_unit_normal (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) (x:a) = is_neutral_of (unit_part_func x) mul eq


type unit_normal_of (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) = x:a { is_unit_normal mul eq unit_part_func x }

[@@"opaque_to_smt"]
let is_absorber_of (#a:Type) (z:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). ((x `op` z) `eq` z) && ((z `op` x) `eq` z)


let nat_function_defined_on_non_absorbers (#a:Type) (op: binary_op a) (eq: equivalence_relation a) 
  = f: (a -> (option nat)) { forall (x:a). (f x)=None ==> is_absorber_of x op eq }
  
noeq type ring (#a: Type) = {
  addition: commutative_group #a;
  multiplication: (t: monoid #a {is_fully_distributive t.op addition.op t.eq});
  eq: (t:equivalence_relation a{ equivalence_wrt_condition addition.op t /\ equivalence_wrt_condition multiplication.op t /\ t==addition.eq /\ t==multiplication.eq });
  unit_part_of: a -> units_of multiplication.op eq;
  normal_part_of: a -> unit_normal_of multiplication.op eq unit_part_of;
  euclidean_norm: nat_function_defined_on_non_absorbers multiplication.op eq 
} 


[@@"opaque_to_smt"]
let has_no_absorber_divisors (#a:Type) (op: binary_op a) (eq: equivalence_relation a) = forall (x y: a). is_absorber_of (op x y) op eq <==> (is_absorber_of x op eq) \/ (is_absorber_of y op eq)

type domain (#a: Type) = r:ring #a { has_no_absorber_divisors r.multiplication.op r.eq /\ ~(r.eq r.addition.neutral r.multiplication.neutral \/ r.eq r.multiplication.neutral r.addition.neutral ) }

[@@"opaque_to_smt"]
let is_idempotent (#a:Type) (r: unary_op a) (eq: equivalence_relation a)  = forall (x:a). (r x) `eq` (r (r x))

[@@"opaque_to_smt"]
let is_neutral_invariant (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) (f: a -> a) = 
  forall (x:a). (is_neutral_of x mul eq ==> eq x (f x) /\ eq (f x) x)

[@@"opaque_to_smt"]
let yields_units (#a: Type) (f: a->a) (mul: binary_op a) (eq: equivalence_relation a) = 
  forall (x:a). is_unit (f x) mul eq

unfold type non_absorber_of (#a:Type) (op: binary_op a) (eq: equivalence_relation a) = z:a{~(is_absorber_of z op eq)}
  
let unary_is_distributive_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) (x y: a)
 = (f (x `op` y)) `eq` ((f x) `op` (f y))

[@@"opaque_to_smt"]
let unary_over_nonzeros_distributes_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) = 
  forall (x y: non_absorber_of op eq). unary_is_distributive_over f op eq x y

let is_unit_part_function (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (f: a -> units_of mul eq) = 
  is_idempotent f eq /\
  is_neutral_invariant mul eq f /\
  yields_units f mul eq /\
  respects_equivalence f eq /\
  unary_over_nonzeros_distributes_over f mul eq

[@@"opaque_to_smt"]
let yields_unit_normals (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: a -> a) =
  forall (x:a). is_unit_normal mul eq unit_part_func (f x)

[@@"opaque_to_smt"]
let unary_distributes_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) = 
  forall (x y: a). unary_is_distributive_over f op eq x y

[@@"opaque_to_smt"]
let unit_and_normal_decomposition_property (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) 
                                           (up: a->a) (np: a->a) = forall (x:a). (x `eq` mul (up x) (np x)) /\ (mul (up x) (np x) `eq` x)

[@@"opaque_to_smt"]
let is_normal_part_function (#a:Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: a -> unit_normal_of mul eq unit_part_func) = 
  is_idempotent f eq /\
  is_neutral_invariant mul eq f /\
  respects_equivalence f eq /\
  yields_unit_normals mul eq unit_part_func f /\
  unary_distributes_over f mul eq /\
  unit_and_normal_decomposition_property mul eq unit_part_func f

  
type integral_domain (#a: Type) = r:domain #a 
{ 
  is_commutative r.multiplication.op r.eq /\
  is_unit_part_function r.unit_part_of /\
  is_normal_part_function r.unit_part_of r.normal_part_of    
}

unfold let is_zero_of (#a: Type) (r: ring #a) (x: a) = is_absorber_of x r.multiplication.op r.eq

let is_valid_denominator_of (#a:Type) (d: integral_domain #a) (x: a) = 
  is_unit_normal d.multiplication.op d.eq d.unit_part_of x /\ ~(is_zero_of d x)

type valid_denominator_of (#a:Type) (d: integral_domain #a) = (t: a{is_valid_denominator_of d t})
#pop-options

type fraction (#a:Type) (d: integral_domain #a) = 
 | Fraction : (num: a) -> (den: valid_denominator_of d) -> fraction d
