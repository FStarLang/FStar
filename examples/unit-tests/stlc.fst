
module Stlc
open Prims.PURE

type ty =
  | TBool  : ty
  | TArrow : ty -> ty -> ty

type exp =
  | EVar   : int -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : int -> ty -> exp -> exp
  | ETrue  : exp
  | EFalse : exp
  | EIf    : exp -> exp -> exp -> exp

val is_value : exp -> Tot bool
let is_value e =
  match e with
  | EAbs _ _ _ -> true
  | ETrue      -> true
  | EFalse     -> true
  | _          -> false

(* Because we only consider call-by-value reduction, we will ever only
   substitute closed values, so this definition of substitution is
   good enough *)
val subst : int -> exp -> exp -> Tot exp
let rec subst x e e' =
  match e' with
  | EVar xprime -> if x = xprime then e else e'
(* CH: This fails because the SMT encoding can't find xsecond for some reason
   Seems the same problem as: https://github.com/FStarLang/FStar/issues/22
  | EAbs xsecond t e1 ->
      EAbs xsecond t (if x = xsecond then e1 else (subst x e e1))
*)
  | EAbs xsecond t e1 -> EAbs xsecond t e1
  | EApp e1 e2 -> EApp (subst x e e1) (subst x e e2)
  | ETrue -> ETrue
  | EFalse -> EFalse
  | EIf e1 e2 e3 -> EIf (subst x e e1) (subst x e e2) (subst x e e3)

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | EAbs x t e' -> Some (subst x e2 e')
          | _           -> None
        else
          match (step e2) with
          | Some e2' -> Some (EApp e1 e2')
          | None     -> None
      else begin
        match (step e1) with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None
      end
  | EIf e1 e2 e3 ->
      if is_value e1 then
        match e1 with
        | ETrue   -> Some e2
        | EFalse  -> Some e3
        | _       -> None
      else begin
        match (step e1) with
        | Some e1' -> Some (EIf e1' e2 e3)
        | None     -> None
      end
  | _ -> None

type env = int -> Tot (option ty)

val empty : env
let empty _ = None

(* CH: This should work but it seems that F* stumbles upon the type abbreviation
val extend : env -> int -> ty -> Tot env
let extend g x t  = (fun x' -> if x = x' then Some t else g x')
Expected a term of type "(_:env -> _:int -> _:ty -> Tot env)";
got a function "(fun g:<UNKNOWN> x:<UNKNOWN> t:<UNKNOWN> x':<UNKNOWN> -> (match (op_Equality x x') with true  -> (Some t)
	false  -> (g x')))"
Filed as: https://github.com/FStarLang/FStar/issues/23
*)

val extend : env -> int -> ty -> int -> Tot (option ty)
let extend g x t  = (fun x' -> if x = x' then Some t else g x')

let x45 = extend (extend empty 42 TBool) 0 (TArrow TBool TBool)

val extend_eq : g:env -> x:int -> a:ty -> Fact unit
      (ensures ((extend g x a) x) == Some a)
let extend_eq g x a = ()

(* CH: turning int into nat we get again the non-trivial precondition problem *)
val extend_neq : g:env -> x1:int -> a:ty -> x2:int -> Pure unit
      (requires (x2 =!= x1))
      (ensures \r => ((extend g x2 a) x1) == g x1)
let extend_neq g x1 a x2 = ()

(* CH: swapped env and exp args until functions are ignored from the
   lex ordering or until we can write decreasing clauses *)
val typing : exp -> env -> Tot (option ty)
let rec typing e g =
  match e with
  | EVar x -> g x
  | EAbs x t e1 -> begin
      match typing e1 (extend g x t) with
      | Some t' -> Some (TArrow t t')
      | None    -> None
      end
  | EApp e1 e2 -> begin
      match typing e1 g, typing e2 g with
      | Some (TArrow t11 t12), Some t2 -> if t11 = t2 then Some t12 else None
      | _                    , _       -> None
      end
  | ETrue  -> Some TBool
  | EFalse -> Some TBool
  | EIf e1 e2 e3 -> begin
      match typing e1 g, typing e2 g, typing e3 g with
      | Some TBool, Some t2, Some t3 -> if t2 = t3 then Some t2 else None
      | _         , _      , _       -> None
       end
  | _ -> None

val canonical_forms_bool : e:exp -> Pure unit
      (requires ((typing e empty == Some TBool) /\ (is_value e == true)))
      (ensures \r => (e == true) \/ (e == false))
let canonical_forms_bool e = ()

val canonical_forms_fun : e:exp -> t1:ty -> t2:ty -> Pure unit
      (requires ((typing e empty == Some (TArrow t1 t2)) /\ (is_value e == true)))
      (ensures \r => (exists (x:int). (exists (e':exp). (e == EAbs x t1 e'))))
let canonical_forms_fun e t1 t2 = ()

(* CH: This is proved without even needing induction or the lemmas,
   again, too good to be true (see stlc-false.fst) *)
val progress : e:exp -> t:ty -> Pure unit
      (requires (typing e empty == Some t))
      (ensures \r => (is_value e \/ (exists (e':exp). step e == Some e')))
let rec progress e t = ()

val appears_free_in : x:int -> e:exp -> Tot bool
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs y t e1 -> if x = y then false else appears_free_in x e1
  | EIf e1 e2 e3 ->
      appears_free_in x e1 || appears_free_in x e2 || appears_free_in x e3
  | _ -> false

(* CH: can we specify these kind of type-level functions?
   Or do I need to inline them everywhere? *)
(* val closed : exp -> Tot Type *)
(* let closed e = (forall (x:int), ~(appears_free_in x e)) *)

val free_in_context : x:int -> e:exp -> t:ty -> g:env -> Pure unit
      (requires (appears_free_in x e == true /\ typing e g == Some t))
      (ensures \r => (exists (t':ty). g x == Some t'))
let free_in_context x e t g = ()

val context_invariance : g:env -> g':env -> e:exp -> t:ty -> Pure unit
      (requires (typing e g == Some t /\
                   (forall (x:int). appears_free_in x e == true ==>
                                    g x == g' x)))
      (ensures \r => (typing e g' == Some t))
let context_invariance g g' e t = ()

val substitution_preserves_typing :
      g:env -> x:int -> e:exp -> u:ty -> t:ty -> v:exp -> Pure unit
          (requires (typing e (extend g x u) == Some t /\
                       (typing v empty == Some u)))
          (ensures \r => (typing (subst x v e) g == Some t))
let substitution_preserves_typing g x e u t v = ()

val preservation : e:exp -> e':exp -> t:ty -> Pure unit
      (requires (typing e empty == Some t /\ step e == Some e'))
      (ensures \r => (typing e' empty == Some t))
let preservation e e' t = ()
