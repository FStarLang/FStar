
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
   although this definition is just fine (the type decreases);
   we have similar problems in F* at this point *)
type R : ty -> exp -> Type =
  | R_bool : e:exp{typing empty e = Some TBool /\ halts e} -> R TBool e
  | R_arrow : t1:ty -> t2:ty
               -> e:exp{typing empty e = Some (TArrow t1 t2) /\ halts e}
               -> (e':exp -> R t1 e' -> Tot (R t2 (EApp e e')))
               -> R (TArrow t1 t2) e
(* I agree we should get a negative occurrence error;
   but the 10(!) errors we get are incomprehensible:
time ../../bin/fstar.exe --fstar_home ../.. stlc.fst norm.fst --print_implicits
Error norm.fst(20,13-20,14): The following problems were found:
	Subtyping check failed; expected type (R #'e819 #'e820); got type (R #_0 #_1) (norm.fst(20,4-20,10))
Error norm.fst(20,13-20,14): Unconstrained unification variables 'e820,'e819 in type signature (#_0:ty -> #_1:exp -> projectee:_958:(R #_0 #_1){(is_R_bool #'e819 #'e820 _958)} -> Tot e:exp{(((typing empty e) = (Some #ty TBool)) /\ (halts e))}); please add an annotation
Error norm.fst(21,14-21,16): The following problems were found:
	Subtyping check failed; expected type (R #'e823 #'e824); got type (R #_0 #_1) (norm.fst(21,4-21,11))
Error norm.fst(21,14-21,16): Unconstrained unification variables 'e824,'e823 in type signature (#_0:ty -> #_1:exp -> projectee:_960:(R #_0 #_1){(is_R_arrow #'e823 #'e824 _960)} -> Tot ty); please add an annotation
Error norm.fst(21,23-21,25): The following problems were found:
	Subtyping check failed; expected type (R #'e825 #'e826); got type (R #_0 #_1) (norm.fst(21,4-21,11))
Error norm.fst(21,23-21,25): Unconstrained unification variables 'e826,'e825 in type signature (#_0:ty -> #_1:exp -> projectee:_960:(R #_0 #_1){(is_R_arrow #'e825 #'e826 _960)} -> Tot ty); please add an annotation
Error norm.fst(22,18-22,19): The following problems were found:
	Subtyping check failed; expected type (R #'e827 #'e828); got type (R #_0 #_1) (norm.fst(21,4-21,11))
Error norm.fst(22,18-22,19): Unconstrained unification variables 'e834,'e833,'e832,'e831,'e828,'e827 in type signature (#_0:ty -> #_1:exp -> projectee:_960:(R #_0 #_1){(is_R_arrow #'e827 #'e828 _960)} -> Tot e:exp{(((typing empty e) = (Some #ty (TArrow (t1 #'e831 #'e832 projectee) (t2 #'e833 #'e834 projectee)))) /\ (halts e))}); please add an annotation
Error norm.fst(22,18-22,19): The following problems were found:
	Subtyping check failed; expected type _960:(R #'e841 #'e842){(is_R_arrow #'e827 #'e828 _960)}; got type _960:(R #_0 #_1){(is_R_arrow #'e835 #'e836 _960)} (norm.fst(21,4-21,11))
Error unknown(0,0-0,0): Unconstrained unification variables 'e842,'e841,'e840,'e839,'e838,'e837,'e836,'e835 in type signature (#_0:ty -> #_1:exp -> projectee:_960:(R #_0 #_1){(is_R_arrow #'e835 #'e836 _960)} -> Tot (e':exp -> _:(R (t1 #'e837 #'e838 projectee) e') -> Tot (R (t2 #'e839 #'e840 projectee) (EApp (e #'e841 #'e842 projectee) e')))); please add an annotation
Verified module: Prims
Verified module: Stlc
Verified module: Norm
Error: 10 errors were reported (see above)
*)

(* My original attempt
  | R_arrow : e:exp -> t1:ty -> t2:ty{typing empty e = Some (TArrow t1 t2)
      /\ halts e /\ (forall (e':exp). R t1 e' ==> R t2 (EApp e e'))} ->
      R (TArrow t1 t2) e

time ../../bin/fstar.exe --fstar_home ../.. stlc.fst norm.fst --print_implicits
Error norm.fst(20,13-20,14): The following problems were found:
	Subtyping check failed; expected type (R #'e820 #'e821); got type (R #_0 #_1) (norm.fst(20,4-20,10))
Error norm.fst(20,13-20,14): Unconstrained unification variables 'e821,'e820 in type signature (#_0:ty -> #_1:exp -> projectee:_958:(R #_0 #_1){(is_R_bool #'e820 #'e821 _958)} -> Tot e:exp{(((typing empty e) = (Some #ty TBool)) /\ (halts e))}); please add an annotation
Error norm.fst(22,14-22,15): The following problems were found:
	Subtyping check failed; expected type (R #'e824 #'e825); got type (R #_0 #_1) (norm.fst(22,4-22,11))
Error norm.fst(22,14-22,15): Unconstrained unification variables 'e825,'e824 in type signature (#_0:ty -> #_1:exp -> projectee:_960:(R #_0 #_1){(is_R_arrow #'e824 #'e825 _960)} -> Tot exp); please add an annotation
Error norm.fst(22,23-22,25): The following problems were found:
	Subtyping check failed; expected type (R #'e826 #'e827); got type (R #_0 #_1) (norm.fst(22,4-22,11))
Error norm.fst(22,23-22,25): Unconstrained unification variables 'e827,'e826 in type signature (#_0:ty -> #_1:exp -> projectee:_960:(R #_0 #_1){(is_R_arrow #'e826 #'e827 _960)} -> Tot ty); please add an annotation
Error norm.fst(22,32-22,34): The following problems were found:
	Subtyping check failed; expected type (R #'e828 #'e829); got type (R #_0 #_1) (norm.fst(22,4-22,11))
Error norm.fst(22,32-22,34): Unconstrained unification variables 'e842,'e841,'e840,'e839,'e837,'e836,'e835,'e834,'e832,'e831,'e829,'e828 in type signature (#_0:ty -> #_1:exp -> projectee:_960:(R #_0 #_1){(is_R_arrow #'e828 #'e829 _960)} -> Tot t2:ty{((((typing empty (e #'e831 #'e832 projectee)) = (Some #ty (TArrow (t1 #'e834 #'e835 projectee) t2))) /\ (halts (e #'e836 #'e837 projectee))) /\ (forall (e':exp). ((R (t1 #'e839 #'e840 projectee) e') ==> (R t2 (EApp (e #'e841 #'e842 projectee) e')))))}); please add an annotation
Verified module: Prims
Verified module: Stlc
Verified module: Norm
Error: 8 errors were reported (see above)
../../bin/fstar.exe --fstar_home ../.. stlc.fst norm.fst --print_implicits  2.49s user 0.10s system 17% cpu 14.620 total
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
