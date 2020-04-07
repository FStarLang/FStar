module Bug1986

(*
 * 72: Identifier not found (good error)
 * 133: Name not found (bad error, internal)
 *)

(* Used to give (Error 133) Name "FStar.Pervasives.__proj__Mkdtuple4__item__b" not found *)
[@(expect_failure [72])]
let f x = x.b

type box (a:Type) = | Box : x:a -> box a

(* Works fine *)
let px (r:box 'a) = r.x

(* Used to give (Error 133) Name "Fields.__proj__Box__item__a" not found *)
[@(expect_failure [72])]
let pa (r:box 'a) = r.a

type box2 (x:Type) = | A : box2 x

type box3 (x:Type) = { z : bool }

(* x not shadowed by above *)
let px' (r : box 'a) = r.x

let pz r = r.z
