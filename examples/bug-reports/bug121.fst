// This file needs --universes now

module Bug121

open FStar.FunctionalExtensionality

type var = nat

type exp =
  | EVar   : var -> exp
  | ELam   : exp -> exp

type sub = var -> Tot exp

type renaming (s:sub) = (forall (x:var). EVar? (s x))

assume val is_renaming : s:sub -> Tot (n:int{  (renaming s  ==> n=0) /\
                                      (~(renaming s) ==> n=1)})

val sub_inc : var -> Tot exp
let sub_inc y = EVar (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if EVar? e then 0 else 1

val subst : s:sub -> e:exp -> Pure exp (requires True)
     (ensures (fun e' -> (renaming s /\ EVar? e) ==> EVar? e'))
     (decreases %[is_var e; is_renaming s; e])
let rec subst s e =
  match e with
  | EVar x -> s x
  | ELam e1 ->
     let sub_elam : y:var -> Tot (e:exp{renaming s ==> EVar? e}) =
       fun y -> if y=0 then EVar y
                       else subst sub_inc (s (y-1))            (* shift +1 *)
     in ELam (subst sub_elam e1)

val sub_elam: s:sub -> Tot sub
let sub_elam s y = if y=0 then EVar y
                   else subst sub_inc (s (y-1))

(* Substitution extensional; trivial with the extensionality axiom *)
val subst_extensional: s1:sub -> s2:sub{feq s1 s2} -> e:exp ->
                        Lemma (requires True) (ensures (subst s1 e = subst s2 e))
                       (* [SMTPat (subst s1 e);  SMTPat (subst s2 e)] *)
let subst_extensional s1 s2 e = ()

(* This only works automatically with the patterns in
   subst_extensional above; it would be a lot cooler if this worked
   without, since that increases checking time.  Even worse, there is
   no way to prove this without the SMTPat (e.g. manually), or to use
   the SMTPat only locally, in this definition (`using` needed). *)
val sub_lam_hoist : e:exp -> s:sub -> Lemma (requires True)
      (ensures (subst s (ELam e) = ELam (subst (sub_elam s) e)))
let sub_lam_hoist e s = ()
