
module Norm

open Prims
open Stlc

(* need to define the reflexive-transitive closure of step, somehow *)
assume type steps : exp -> exp -> Type

type halts e = (exists (e':exp). (steps e e' /\ is_value e'))

assume val value_halts : v:exp ->
  Lemma (requires (is_value v))
        (ensures (halts v))

(* This has a negative occurrence of R that makes Coq succumb,
   although this definition is just fine (the type decreases) *)
type R =
  | R_bool : e:exp{typing empty e = Some TBool /\ halts e} -> R TBool e
  | R_arrow : e:exp -> t1:ty -> t2:ty{typing empty e = Some (TArrow t1 t2)
      /\ halts e /\ (forall (e':exp). R t1 e' ==> R t2 (EApp e e'))} ->
      R (TArrow t1 t2) e
(* How do we get "non-uniform" inductive relation arguments in F*?
   For our definition none of the arguments is uniform
norm.fst(19,62-19,71) : Error
Expected a type-to-type constructor or function;
got a type "(R TBool e)" of kind "Type"
*)


(*
type R (t:ty) (e:exp) =
  | R_bool : u0:unit{typing empty e = Some TBool /\ halts e} -> R TBool e
  | R_arrow : t1:ty -> t2:ty{typing empty e = Some (TArrow t1 t2)
      /\ halts e /\ (forall (e':exp). R t1 e' ==> R t2 (EApp e e'))} ->
      R (TArrow t1 t2) e


time ../../bin/fstar.exe --fstar_home ../.. stlc.fst norm.fst --print_implicits
Error norm.fst(17,8-17,9): The following problems were found:
	Subtyping check failed; expected type (R #'e820 #'e821); got type (R #t #e) (norm.fst(18,4-18,10))
Error norm.fst(17,8-17,9): Unconstrained unification variables 'e821,'e820 in type signature (#t:ty -> #e:exp -> projectee:_959:(R #t #e){(is_R_bool #'e820 #'e821 _959)} -> Tot ty); please add an annotation
Error norm.fst(17,15-17,16): The following problems were found:
	Subtyping check failed; expected type (R #'e822 #'e823); got type (R #t #e) (norm.fst(18,4-18,10))
Error norm.fst(17,15-17,16): Unconstrained unification variables 'e823,'e822 in type signature (#t:ty -> #e:exp -> projectee:_959:(R #t #e){(is_R_bool #'e822 #'e823 _959)} -> Tot exp); please add an annotation
Error norm.fst(18,13-18,15): The following problems were found:
	Subtyping check failed; expected type (R #'e824 #'e825); got type (R #t #e) (norm.fst(18,4-18,10))
Error norm.fst(18,13-18,15): Unconstrained unification variables 'e825,'e824 in type signature (#t:ty -> #e:exp -> projectee:_959:(R #t #e){(is_R_bool #'e824 #'e825 _959)} -> Tot u0:unit{(((typing empty e) = (Some #ty TBool)) /\ (halts e))}); please add an annotation
Error norm.fst(17,8-17,9): The following problems were found:
	Subtyping check failed; expected type (R #'e828 #'e829); got type (R #t #e) (norm.fst(19,4-19,11))
Error norm.fst(17,8-17,9): Unconstrained unification variables 'e829,'e828 in type signature (#t:ty -> #e:exp -> projectee:_961:(R #t #e){(is_R_arrow #'e828 #'e829 _961)} -> Tot ty); please add an annotation
Error norm.fst(17,15-17,16): The following problems were found:
	Subtyping check failed; expected type (R #'e830 #'e831); got type (R #t #e) (norm.fst(19,4-19,11))
Error norm.fst(17,15-17,16): Unconstrained unification variables 'e831,'e830 in type signature (#t:ty -> #e:exp -> projectee:_961:(R #t #e){(is_R_arrow #'e830 #'e831 _961)} -> Tot exp); please add an annotation
Error norm.fst(19,14-19,16): The following problems were found:
	Subtyping check failed; expected type (R #'e832 #'e833); got type (R #t #e) (norm.fst(19,4-19,11))
Error norm.fst(19,14-19,16): Unconstrained unification variables 'e833,'e832 in type signature (#t:ty -> #e:exp -> projectee:_961:(R #t #e){(is_R_arrow #'e832 #'e833 _961)} -> Tot ty); please add an annotation
Error norm.fst(19,23-19,25): The following problems were found:
	Subtyping check failed; expected type (R #'e834 #'e835); got type (R #t #e) (norm.fst(19,4-19,11))
Error norm.fst(19,23-19,25): Unconstrained unification variables 'e842,'e841,'e839,'e838,'e835,'e834 in type signature (#t:ty -> #e:exp -> projectee:_961:(R #t #e){(is_R_arrow #'e834 #'e835 _961)} -> Tot t2:ty{((((typing empty e) = (Some #ty (TArrow (t1 #'e838 #'e839 projectee) t2))) /\ (halts e)) /\ (forall (e':exp). ((R (t1 #'e841 #'e842 projectee) e') ==> (R t2 (EApp e e')))))}); please add an annotation
Verified module: Prims
Verified module: Stlc
Verified module: Norm
Error: 14 errors were reported (see above)
../../bin/fstar.exe --fstar_home ../.. stlc.fst norm.fst --print_implicits  2.47s user 0.08s system 8% cpu 28.494 total
*)

(* In Coq we define R by recursion on the type,
   we don't have fixpoints in Type in F* though, do we?
The type of R is
val R : ty -> exp -> Type
*)
(*
Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
  has_type empty t T /\ halts t /\
  (match T with
   | TBool  => True
   | TArrow T1 T2 => (forall s, R T1 s -> R T2 (tapp t s))
   | TProd T1 T2 => (R T1 (tfst t)) /\ (R T2 (tsnd t)) 
   end).
*)
