module PropEncoding

(* The SMT encoding of prop is extensional: a prop is encoded as a boxed SMT
   boolean recording its validity. So propositional extensionality, excluded
   middle, and the fact that every prop is either True or False hold out of the
   box. *)

let every_prop_is_true_or_false = assert (forall (p: prop). p == True \/ p == False)

let excluded_middle (p: prop) = assert (p \/ ~p)

let prop_ext (p q: prop) = assert ((p <==> q) ==> p == q)

let true_is_not_false = assert (~(True == False))

(* Extensionality must not make abstract props provable. In particular,
   prop-valued type constructors, which are `new` and would otherwise be given a
   distinct SMT constructor id, must stay uninterpreted. *)

assume val prop_val : int -> prop
[@@expect_failure] let leak_val (x:int) : squash (prop_val x) = ()

assume new type prop_typ : int -> prop
[@@expect_failure] let leak_typ (x:int) : squash (prop_typ x) = ()

assume new type prop_typ0 : prop
[@@expect_failure] let leak_typ0 () : squash prop_typ0 = ()

assume new type prop_typ2 : int -> int -> prop
[@@expect_failure] let leak_typ2 (x y:int) : squash (prop_typ2 x y) = ()
