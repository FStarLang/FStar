
open Prims

type ('Aa, 'Azero, 'Aopp, 'Aadd) abelianGroup =
(((Prims.unit, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and


type ('Aa, 'Azero, 'Aone, 'Aopp, 'Aadd, 'Ainv, 'Amul) commutativeField =
(((((((((Prims.unit, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


let mandatory_lemma : Prims.nat  ->  Prims.unit = (fun n -> ())


let rec scalar_multiplication = (fun zero opp add n p -> (match (n) with
| _0_20 when (_0_20 = (Prims.parse_int "0")) -> begin
zero
end
| uu____348 -> begin
(add p (scalar_multiplication zero opp add (n - (Prims.parse_int "1")) p))
end))




