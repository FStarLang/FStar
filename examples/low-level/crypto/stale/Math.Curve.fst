module Math.Curve

open FStar.Ghost
open Math.Definitions
open Math.Field

(*** Core definitions ***)
(* Curve equation *)
assume val a: felem
assume val b: felem
assume val is_weierstrass_curve: unit ->
  Lemma ((((4 +* (a ^^ 3)) ^+ (27 +* (b ^^ 2))) <> zero) /\ characteristic <> 2  /\ characteristic <> 3)
assume val characteristic_corollary: x:felem{x<>zero} -> Lemma (2 +* x <> zero)

type affine_point =
  | Inf
  | Finite: x:felem -> y:felem -> affine_point
  
val get_x: p:affine_point{Finite? p} -> Tot felem
let get_x p = Finite.x p
val get_y: p:affine_point{Finite? p} -> Tot felem
let get_y p = Finite.y p

(* Definition of an affine point on the curve *)
val on_curve: affine_point -> Tot bool
let on_curve p = (Inf? p || (Finite? p && (let x, y = get_x p, get_y p in (y ^^ 2) = ((x ^^ 3) ^+ (a ^* x) ^+ b))))
type curvePoint (p:affine_point) = b2t(on_curve p)

(* Type of points on the curve *)
type celem = p:affine_point{curvePoint p}

(* Definition of the opposite *)
val neg': affine_point -> Tot affine_point
let neg' p = 
  if Inf? p then Inf
  else Finite (Finite.x p) (opp (Finite.y p))

(* The opposite of a point on the curve is on the curve, proven in Coq *)
assume val neg_lemma: p:affine_point ->
  Lemma (ensures (curvePoint p ==> curvePoint (neg' p)))

(* Opposite of a curve point *)
val neg: celem -> Tot celem
let neg p = neg_lemma p; neg' p

(* Definition of the addition, same as the SSReflect one *)
val add': affine_point -> affine_point -> Tot affine_point
let add' p1 p2 =
  if not(on_curve p1) then Inf
  else if not(on_curve p2) then Inf 
  else if Inf? p1 then p2
  else if Inf? p2 then p1
  else (
    cut(Finite? p1 /\ Finite? p2); 
    let x1 = get_x p1 in 
    let x2 = get_x p2 in 
    let y1 = get_y p1 in 
    let y2 = get_y p2 in 
    if x1 = x2 then (
      if y1 = y2 && y1 <> zero then (
	characteristic_corollary y1;
	let lam = ((3 +* (x1 ^^ 2) ^+ a) ^/ (2 +* y1)) in 
	let x = ((lam ^^ 2) ^- (2 +* x1)) in
	let y = ((lam ^* (x1 ^- x)) ^- y1) in
	Finite x y
      ) else (
	Inf
      )
    )
    else (
      cut (True /\ x1 <> x2);
      let lam = (y2 ^- y1) ^/ (x2 ^- x1) in
      let x = ((lam ^^ 2) ^- x1 ^- x2) in
      let y = (lam ^* (x1 ^- x) ^- y1) in
      Finite x y
    )
  )

(* The addition is always on the curve, proven in Coq *)
assume val add_lemma: p:affine_point -> q:affine_point ->
  Lemma (curvePoint (add' p q))

(* Sum of two curve points *)
val add: p:celem -> q:celem -> Tot celem
let add p q = 
  add_lemma p q; add' p q

(* The point at infinity, the opposite and the addition on the curve 
   form an abelian group, proven in Coq *)
assume val ec_group_lemma:
  unit -> Lemma (abelianGroup #celem Inf neg add)

let smul n p = 
  ec_group_lemma ();
  scalar_multiplication #celem Inf neg add n p

(*** Additional properties ***)
(* Equality of curve elements *)
assume type equal: celem -> celem -> Type
assume val lemma_equal_intro: e1:celem -> e2:celem -> Lemma
  (requires (Curve.Inf? e1 /\ Curve.Inf? e2) 
	     \/ (Curve.Finite? e1 /\ Curve.Finite? e2 /\ get_x e1 == get_x e2 /\ get_y e1 == get_y e2))
  (ensures (equal e1 e2))
  [SMTPat (equal e1 e2)]
assume val lemma_equal_elim: e1:celem -> e2:celem -> Lemma
    (requires (equal e1 e2))
    (ensures  (e1 = e2))
    [SMTPat (equal e1 e2)]
assume val lemma_equal_refl: e1:celem -> e2:celem -> Lemma
    (requires (e1 = e2))
    (ensures  (equal e1 e2))
    [SMTPat (equal e1 e2)]

(* General lemmas *)
val add_equality: a:celem -> b:celem -> c:celem -> d:celem ->
  Lemma (requires (equal a c /\ equal b d))
	(ensures (equal (add a b) (add c d)))
let add_equality a b c d = ()

val add_commutativity: a:celem -> b:celem -> 
  Lemma (requires (True)) 
	(ensures (add a b = add b a))
let add_commutativity a b = ec_group_lemma ()

(* Other point representations *)
type projective_point = | Proj: x:felem -> y:felem -> z:felem -> projective_point
type jacobian_point = | Jac: x:felem -> y:felem -> z:felem -> jacobian_point

type point = | Affine: p:affine_point -> point 
	     | Projective: p:projective_point -> point
	     | Jacobian: p:jacobian_point -> point

assume val to_affine: point -> Tot (p:point{Affine? p})
assume val to_projective: point -> Tot (p:point{Projective? p})
assume val to_jacobian: point -> Tot (p:point{Jacobian? p })

type onCurve (p:point{Affine? p}) =
  (let p' = Affine.p p in curvePoint p')
  
(* Extension of the definition to all coordinate systems *)
type isOnCurve (p:point) =
  (Affine? p /\ onCurve p)
  \/ (Projective? p /\ onCurve (to_affine p))
  \/ (Jacobian? p /\ onCurve (to_affine p))

type ec_elem = p:point{ isOnCurve p }

(* Addition between any points *)
val add_point: point -> point -> Tot point
let add_point p q = 
  let p' = Affine.p (to_affine p) in let q' = Affine.p (to_affine q) in
  Affine (add' p' q')
  
type eq (p1:point) (p2:point) = 
  (Inf? (Affine.p (to_affine p1)) /\ Inf? (Affine.p (to_affine p2))) \/
  (Finite? (Affine.p (to_affine p1)) /\ Finite? (Affine.p (to_affine p2)) /\ get_x (Affine.p (to_affine p1)) ^- get_x (Affine.p (to_affine p2)) = zero)

let op_Plus_Star n p = smul n p

assume val smul_lemma: q:celem -> n:nat -> m:nat -> Lemma
  (requires (True))
  (ensures (add (n +* q) (m +* q) = ((n + m) +* q)))
  (decreases n)
