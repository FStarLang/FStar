module Bug1534

type ok (a:int) = | Mkok : b:int -> ok a

type ok2 (a:int) : eqtype = | Mkok2 : b:int -> ok2 a

type ok3 (a:int) : bool -> Type = | Mkok3 : b:int -> ok3 a true

[@(expect_failure [313])]
type bad (a:int) = | Mkbad : a:int -> bad a

[@(expect_failure [313])]
type bad2 (a:int) : eqtype = | Mkbad2 : a:int -> ok2 a

[@(expect_failure [313])]
type bad3 (a:int) : bool -> Type = | Mkbad3 : a:int -> bad3 a true

(* Sanity check that this works with implicits *)
type eq' (#a:Type) : a -> a -> Type =
    | Refl' : x:a -> eq' x x

[@(expect_failure [313])]
type eq'bad (#a:Type) : a -> a -> Type =
    | Refl'bad : a:Type -> x:a -> eq'bad x x
