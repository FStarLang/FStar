
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
  | EVar x' -> if x = x' then e else e'
  | EAbs x' t e1 ->
      EAbs x' t (if x = x' then e1 else (subst x e e1))
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
      (ensures ((extend g x a) x) = Some a)
let extend_eq g x a = ()

val extend_neq : g:env -> x1:int -> a:ty -> x2:int -> Pure unit
      (requires (x2 =!= x1))
      (ensures \r => ((extend g x2 a) x1) = g x1)
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
      (requires ((typing e empty = Some TBool) /\ (is_value e = true)))
      (ensures \r => (e = ETrue) \/ (e = EFalse))
let canonical_forms_bool e =
  match e with
  | EVar x -> ()
  | EAbs x' t e1 ->
      (* strange that F* can't prove this simple case *)
      (* This fails now, but maybe if we manage to get rid of the existentials
         by replacing them with testers and projectors?
      assert(exists (t1:ty). exists (t2:ty).
               typing (EAbs x' t e1) = Some (TArrow t1 t2)); *)
      admit()
  | EApp e1 e2 -> ()
  | ETrue -> ()
  | EFalse -> ()
  | EIf e1 e2 e3 -> ()

val canonical_forms_fun : e:exp -> t1:ty -> t2:ty -> Pure unit
      (requires ((typing e empty = Some (TArrow t1 t2)) /\ (is_value e = true)))
      (ensures \r => (is_EAbs e))
let canonical_forms_fun e t1 t2 = ()

val progress : e:exp -> t:ty -> Pure unit
      (requires (typing e empty = Some t))
      (ensures \r => (is_value e \/ (is_Some (step e))))
let rec progress e t =
  match e with
  | EVar x ->
      (* assert(typing (EVar x) empty = None); -- this fails *)
      admit()
  | EAbs x' t e1 -> ()
  | EApp e1 e2 ->
(* problem: for progress e1 and progress e2 we don't have anything to
   pass for t; implicit lemma instantiation might help for such cases *)
      assert(exists (t1:ty). exists (t2:ty).
               typing e1 empty = Some (TArrow t1 t2) /\
               typing e2 empty = Some t1);
          (* The assert is proved, but it's not enough.
             We want to apply progress for the existentially
             quantified t1 and t2 above! How can we do that?
             If we prove unique existence for something logical
             can we somehow soundly expose it back to F*? *)
      if is_value e1 then
        if is_value e2 then ()
        else admit()
      else admit()
  | ETrue -> ()
  | EFalse -> ()
  | EIf e1 e2 e3 ->
      progress e1 TBool; progress e2 t; progress e3 t;
      if is_value e1 then canonical_forms_bool e1

val appears_free_in : x:int -> e:exp -> Tot bool
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs y t e1 -> if x = y then false else appears_free_in x e1
  | EIf e1 e2 e3 ->
      appears_free_in x e1 || appears_free_in x e2 || appears_free_in x e3
  | _ -> false

type closed e = (forall (x:int). not (appears_free_in x e))

val free_in_context : x:int -> e:exp -> t:ty -> g:env -> Pure unit
      (requires (appears_free_in x e = true /\ typing e g = Some t))
      (ensures \r => (is_Some (g x)))
let free_in_context x e t g = ()

val context_invariance : g:env -> g':env -> e:exp -> t:ty -> Pure unit
      (requires (typing e g = Some t /\
                   (forall (x:int). appears_free_in x e = true ==>
                                    g x = g' x)))
      (ensures \r => (typing e g' = Some t))
let context_invariance g g' e t = ()

val substitution_preserves_typing :
      g:env -> x:int -> e:exp -> u:ty -> t:ty -> v:exp -> Pure unit
          (requires (typing e (extend g x u) = Some t /\
                       (typing v empty = Some u)))
          (ensures \r => (typing (subst x v e) g = Some t))
let substitution_preserves_typing g x e u t v = ()

val preservation : e:exp -> e':exp -> t:ty -> Pure unit
      (requires (typing e empty = Some t /\ step e = Some e'))
      (ensures \r => (typing e' empty = Some t))
let preservation e e' t = ()

(* CH: With this purely-executable way of specifying things we can't
   do rule induction, and that is restrictive and will probably lead
   to rather unnatural proofs. *)
