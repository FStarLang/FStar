module Bug186b

open FStar.Classical

type typ =
  | TArr : typ -> typ -> typ

type var = nat

type exp =
  | EVar   : var -> exp
  | ELam   : typ -> exp -> exp

type sub = var -> Tot exp

opaque type renaming (s:sub) = (forall (x:var). EVar? (s x))

val is_renaming : s:sub -> Tot (n:int{  (renaming s  ==> n=0) /\
                                      (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

val sub_inc_above : nat -> var -> Tot exp
let sub_inc_above n y = if y<n then EVar y else EVar (y+1)

val sub_inc : var -> Tot exp
let sub_inc = sub_inc_above 0

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if EVar? e then 0 else 1

val subst : s:sub -> e:exp -> Pure exp (requires True)
     (ensures (fun e' -> (renaming s /\ EVar? e) ==> EVar? e'))
     (decreases %[is_var e; is_renaming s; e])
let rec subst s e =
  match e with
  | EVar x -> s x

  | ELam t e1 ->
     let subst_elam : y:var -> Tot (e:exp{renaming s ==> EVar? e}) =
       fun y -> if y=0 then EVar y
                       else subst sub_inc (s (y-1))            (* shift +1 *)
     in ELam t (subst subst_elam e1)

val subst_elam: s:sub -> Tot sub
let subst_elam s y =
  if y = 0 then EVar y
  else subst sub_inc (s (y-1))

type env = var -> Tot (option typ)

val extend : env -> var -> typ -> Tot env
let extend g x t y = if y < x then g y
                     else if y = x then Some t
                     else g (y-1)

type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
            x:var{Some? (g x)} ->
            typing g (EVar x) (Some?.v (g x))
  | TyLam : #g:env ->
            t:typ ->
            #e1:exp ->
            #t':typ ->
            typing (extend g 0 t) e1 t' ->
            typing g (ELam t e1) (TArr t t')

val shift_up_above : nat -> exp -> Tot exp
let shift_up_above n e = subst (sub_inc_above n) e

assume opaque val weakening : x:nat -> #g:env -> #e:exp -> #t:typ -> t':typ ->
      h:typing g e t -> Tot (typing (extend g x t') (shift_up_above x e) t)
      (decreases h)

type subst_typing (s:sub) (g1:env) (g2:env) =
  (x:var{Some? (g1 x)} -> Tot(typing g2 (s x) (Some?.v (g1 x))))

val substitution :
      #g1:env -> #e:exp -> #t:typ -> s:sub -> #g2:env ->
      h1:typing g1 e t ->
      hs:subst_typing s g1 g2 ->
      Tot (typing g2 (subst s e) t) (decreases h1)
(* This makes F* explode. It is likely because of the call to weakening *)
let rec substitution g1 e t s g2 h1 hs =
match h1 with
| TyLam tlam hbody ->
let hs' : subst_typing (subst_elam s) (extend g1 0 tlam) (extend g2 0 tlam) = fun y ->
  let hgamma2 = hs (y - 1) in weakening 0 tlam hgamma2
in magic()
| _ -> magic()
