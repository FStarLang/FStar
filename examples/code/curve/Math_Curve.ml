
open Prims

let a : Math_Field.felem = (Obj.magic (()))


let b : Math_Field.felem = (Obj.magic (()))


let is_weierstrass_curve : Prims.unit  ->  Prims.unit = (fun __4 -> ())


let characteristic_corollary : Math_Field.felem  ->  Prims.unit = (fun x -> ())

type affine_point =
| Inf
| Finite of Math_Field.felem * Math_Field.felem


let is_Inf = (fun _discr_ -> (match (_discr_) with
| Inf (_) -> begin
true
end
| _ -> begin
false
end))


let is_Finite = (fun _discr_ -> (match (_discr_) with
| Finite (_) -> begin
true
end
| _ -> begin
false
end))


let ___Finite___x : affine_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Finite (x, y) -> begin
x
end))


let ___Finite___y : affine_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Finite (x, y) -> begin
y
end))


let get_x : affine_point  ->  Math_Field.felem = (fun p -> (___Finite___x p))


let get_y : affine_point  ->  Math_Field.felem = (fun p -> (___Finite___y p))


let on_curve : affine_point  ->  Prims.bool = (fun p -> ((is_Inf p) || ((is_Finite p) && (

let uu____57 = ((get_x p), (get_y p))
in (match ((Obj.magic (uu____57))) with
| (x, y) -> begin
((Math_Field.op_Hat_Hat y (Prims.parse_int "2")) = (Math_Field.op_Hat_Plus (Math_Field.op_Hat_Plus (Math_Field.op_Hat_Hat x (Prims.parse_int "3")) (Math_Field.op_Hat_Star a x)) b))
end)))))


type 'Ap curvePoint =
Prims.unit Prims.b2t


type celem =
affine_point


let neg' : affine_point  ->  affine_point = (fun p -> (match ((is_Inf p)) with
| true -> begin
Inf
end
| uu____68 -> begin
Finite ((___Finite___x p), (Math_Field.opp (___Finite___y p)))
end))


let neg_lemma : affine_point  ->  Prims.unit = (fun p -> ())


let neg : celem  ->  celem = (fun p -> (neg' p))


let add' : affine_point  ->  affine_point  ->  affine_point = (fun p1 p2 -> (match ((not ((on_curve p1)))) with
| true -> begin
Inf
end
| uu____160 -> begin
(match ((not ((on_curve p2)))) with
| true -> begin
Inf
end
| uu____161 -> begin
(match ((is_Inf p1)) with
| true -> begin
p2
end
| uu____162 -> begin
(match ((is_Inf p2)) with
| true -> begin
p1
end
| uu____163 -> begin
(

let x1 = (get_x p1)
in (

let x2 = (get_x p2)
in (

let y1 = (get_y p1)
in (

let y2 = (get_y p2)
in (match ((x1 = x2)) with
| true -> begin
(match (((y1 = y2) && (y1 <> Math_Field.zero))) with
| true -> begin
(

let lam = (Math_Field.op_Hat_Slash (Math_Field.op_Hat_Plus (Math_Field.op_Plus_Star (Prims.parse_int "3") (Math_Field.op_Hat_Hat x1 (Prims.parse_int "2"))) a) (Math_Field.op_Plus_Star (Prims.parse_int "2") y1))
in (

let x = (Math_Field.op_Hat_Subtraction (Math_Field.op_Hat_Hat lam (Prims.parse_int "2")) (Math_Field.op_Plus_Star (Prims.parse_int "2") x1))
in (

let y = (Math_Field.op_Hat_Subtraction (Math_Field.op_Hat_Star lam (Math_Field.op_Hat_Subtraction x1 x)) y1)
in Finite (x, y))))
end
| uu____190 -> begin
Inf
end)
end
| uu____191 -> begin
(

let lam = (Math_Field.op_Hat_Slash (Math_Field.op_Hat_Subtraction y2 y1) (Math_Field.op_Hat_Subtraction x2 x1))
in (

let x = (Math_Field.op_Hat_Subtraction (Math_Field.op_Hat_Subtraction (Math_Field.op_Hat_Hat lam (Prims.parse_int "2")) x1) x2)
in (

let y = (Math_Field.op_Hat_Subtraction (Math_Field.op_Hat_Star lam (Math_Field.op_Hat_Subtraction x1 x)) y1)
in Finite (x, y))))
end)))))
end)
end)
end)
end))


let add_lemma : affine_point  ->  affine_point  ->  Prims.unit = (fun p q -> ())


let add : celem  ->  celem  ->  celem = (fun p q -> (add' p q))


let ec_group_lemma : Prims.unit  ->  Prims.unit = (fun __365 -> ())


let smul : Prims.nat  ->  celem  ->  celem = (fun n p -> (Math_Definitions.scalar_multiplication Inf neg add n p))


type ('A__450, 'A__451) equal =
Prims.unit


let lemma_equal_intro : celem  ->  celem  ->  Prims.unit = (fun e1 e2 -> ())


let lemma_equal_elim : celem  ->  celem  ->  Prims.unit = (fun e1 e2 -> ())


let lemma_equal_refl : celem  ->  celem  ->  Prims.unit = (fun e1 e2 -> ())


let add_equality : celem  ->  celem  ->  celem  ->  celem  ->  Prims.unit = (fun a b c d -> ())


let add_commutativity : celem  ->  celem  ->  Prims.unit = (fun a b -> ())

type projective_point =
| Proj of Math_Field.felem * Math_Field.felem * Math_Field.felem


let ___Proj___x : projective_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Proj (x, y, z) -> begin
x
end))


let ___Proj___y : projective_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Proj (x, y, z) -> begin
y
end))


let ___Proj___z : projective_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Proj (x, y, z) -> begin
z
end))

type jacobian_point =
| Jac of Math_Field.felem * Math_Field.felem * Math_Field.felem


let ___Jac___x : jacobian_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Jac (x, y, z) -> begin
x
end))


let ___Jac___y : jacobian_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Jac (x, y, z) -> begin
y
end))


let ___Jac___z : jacobian_point  ->  Math_Field.felem = (fun projectee -> (match ((Obj.magic (projectee))) with
| Jac (x, y, z) -> begin
z
end))

type point =
| Affine of affine_point
| Projective of projective_point
| Jacobian of jacobian_point


let is_Affine = (fun _discr_ -> (match (_discr_) with
| Affine (_) -> begin
true
end
| _ -> begin
false
end))


let is_Projective = (fun _discr_ -> (match (_discr_) with
| Projective (_) -> begin
true
end
| _ -> begin
false
end))


let is_Jacobian = (fun _discr_ -> (match (_discr_) with
| Jacobian (_) -> begin
true
end
| _ -> begin
false
end))


let ___Affine___p : point  ->  affine_point = (fun projectee -> (match ((Obj.magic (projectee))) with
| Affine (p) -> begin
p
end))


let ___Projective___p : point  ->  projective_point = (fun projectee -> (match ((Obj.magic (projectee))) with
| Projective (p) -> begin
p
end))


let ___Jacobian___p : point  ->  jacobian_point = (fun projectee -> (match ((Obj.magic (projectee))) with
| Jacobian (p) -> begin
p
end))


let to_affine : point  ->  point = (Obj.magic ((fun __797 -> ())))


let to_projective : point  ->  point = (Obj.magic ((fun __802 -> ())))


let to_jacobian : point  ->  point = (Obj.magic ((fun __807 -> ())))


type 'Ap onCurve =
Prims.unit curvePoint


type 'Ap isOnCurve =
(((Prims.unit Prims.b2t, Prims.unit onCurve) Prims.l_and, (Prims.unit Prims.b2t, Prims.unit onCurve) Prims.l_and) Prims.l_or, (Prims.unit Prims.b2t, Prims.unit onCurve) Prims.l_and) Prims.l_or


type ec_elem =
point


let add_point : point  ->  point  ->  point = (fun p q -> (

let p' = (___Affine___p (to_affine p))
in (

let q' = (___Affine___p (to_affine q))
in Affine ((add' p' q')))))


type ('Ap1, 'Ap2) eq =
((Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_and, ((Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and) Prims.l_or


let op_Plus_Star : Prims.nat  ->  celem  ->  celem = (fun n p -> (smul n p))


let smul_lemma : celem  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun q n m -> ())




