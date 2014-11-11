
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

val extend : env -> int -> ty -> Tot env
let extend g x t x' = if x = x' then Some t else g x'

val append: env -> env -> Tot env
let append g1 g2 x = 
  match g2 x with 
    | None -> g1 x
    | found -> found

let x45 = extend (extend empty 42 TBool) 0 (TArrow TBool TBool)

val extend_eq : g:env -> x:int -> a:ty -> Fact unit
      (ensures ((extend g x a) x) = Some a)
let extend_eq g x a = ()

val extend_neq : g:env -> x1:int -> a:ty -> x2:int -> Pure unit
      (requires (x1 <> x2))
      (ensures \r -> ((extend g x1 a) x2) = g x2)
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

val canonical_forms_bool : e:exp -> Pure unit
      (requires (typing e empty=Some TBool /\ is_value e))
      (ensures \r -> is_ETrue e \/ is_EFalse e)
let canonical_forms_bool e = ()

val canonical_forms_fun : e:exp -> t1:ty -> t2:ty -> Pure unit
      (requires (typing e empty = Some (TArrow t1 t2) /\ is_value e))
      (ensures \r -> (is_EAbs e))
let canonical_forms_fun e t1 t2 = ()

val sel_empty : x:int -> Fact unit
      (ensures (is_None (empty x)))
let sel_empty x = ()

val sel_empty' : x:int -> Fact unit
      (ensures (empty x = None))
let sel_empty' x = ()

val progress : e:exp -> t:ty -> Pure unit
      (requires (typing e empty = Some t))
      (ensures \r -> (is_value e \/ (is_Some (step e))))
let rec progress e t =
  match e with
  | EApp e1 e2 -> begin
      match typing e1 empty with
      | Some (TArrow t1 t2) ->
          progress e1 (TArrow t1 t2); progress e2 t1
      end
  | EIf e1 e2 e3 ->
      progress e1 TBool; progress e2 t; progress e3 t;
      if is_value e1 then canonical_forms_bool e1
  | EVar _
  | ETrue
  | EFalse
  | EAbs _ _ _ -> () (* NS: writing default cases for recursive functions is bad for the solver. TODO: fix *)

val appears_free_in : x:int -> e:exp -> Tot bool
let rec appears_free_in x e =
  match e with
  | EVar y -> x = y
  | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
  | EAbs y _ e1 -> x <> y && appears_free_in x e1
  | EIf e1 e2 e3 ->
      appears_free_in x e1 || appears_free_in x e2 || appears_free_in x e3
  | ETrue
  | EFalse -> false

logic type closed e = (forall (x:int). not (appears_free_in x e))

val free_in_context : x:int -> e:exp -> g:env -> Pure unit
      (requires (appears_free_in x e /\ is_Some (typing e g)))
      (ensures \r -> (is_Some (g x)))
let rec free_in_context x e g =
  match e with
  | EAbs y t e1 -> 
     if x = y 
     then ()
     else free_in_context x e1 (extend g y t)

  | EApp e1 e2 -> 
     if appears_free_in x e1
     then free_in_context x e1 g
     else free_in_context x e2 g

  | EIf e1 e2 e3 -> 
     if      appears_free_in x e1 then free_in_context x e1 g
     else if appears_free_in x e2 then free_in_context x e2 g
     else                              free_in_context x e3 g

  | _ -> ()


(* Corollary of free_in_context *)
val typable_empty_closed : x:int -> e:exp -> Lemma
      (requires (is_Some (typing e empty) /\ appears_free_in x e))
      (ensures False)
      ([VPat (appears_free_in x e)])
let typable_empty_closed x e = free_in_context x e empty

logic type Equal (e:exp) (g1:env) (g2:env) = 
          (forall (x:int). appears_free_in x e ==> g1 x==g2 x)

val context_invariance : e:exp -> t:ty -> g:env -> g':env -> Pure unit
      (requires (typing e g = Some t /\ Equal e g g'))
      (ensures \r -> (typing e g' = Some t))
let rec context_invariance e t g g' =
  match e with
  | EAbs x t e1 -> 
     let (Some t') = typing e1 (extend g x t) in
     context_invariance e1 t' (extend g x t) (extend g' x t) 

  | EApp e1 e2 -> 
     let (Some (TArrow t1 t2)) = typing e1 g in
     context_invariance e1 (TArrow t1 t2) g g';
     context_invariance e2 t1 g g'

  | EIf e1 e2 e3 ->
     context_invariance e1 TBool g g';
     context_invariance e2 t g g';
     context_invariance e3 t g g'

  | _ -> ()

val append_assoc: x:int -> u:ty -> g1:env -> g2:env 
                -> Lemma (requires True)
                         (ensures (forall (e:exp). Equal e 
                                     (extend (append g1 g2) x u)
                                     (append g1 (extend g2 x u))))
                         ([VPat (extend (append g1 g2) x u)])
let append_assoc x u g1 g2 = ()
  (* (\* let gg = extend (append g1 g2) x u in *\) *)
  (* (\* let gg' = append g1 (extend g2 x u) in *\) *)
  (* let proof : y:int -> Fact unit (appears_free_in y e ==> (extend (append g1 g2) x u y == append g1 (extend g2 x u) y)) = fun y ->  *)
  (*   let gg = extend (append g1 g2) x u in *)
  (*   let gg' = append g1 (extend g2 x u) in *)
  (*   if appears_free_in y e *)
  (*   then () *)
  (*   else () in *)
  (* qintro proof *)
  
    

val substitution_preserves_typing :
      x:int -> e:exp -> u:ty -> t:ty -> v:exp -> g1:env -> g2:env -> Pure unit
          (requires (typing e (append (extend g1 x u) g2) = Some t
                     /\ typing v empty = Some u))
          (ensures \r -> (typing (subst x v e) (append g1 g2) = Some t))
let rec substitution_preserves_typing x e u t v g1 g2  =
  match e with
  | ETrue -> ()
  | EFalse -> ()
  | EVar x' ->
    let g1g2 = append g1 g2 in
    if is_None (g2 x) && x'=x
    then begin
      assert (Equal v empty g1g2);
      context_invariance v u empty g1g2;
      admit()
    end
    else begin
      let g1xg2 = append (extend g1 x u) g2 in
      assert (Equal e g1xg2 g1g2);
      context_invariance e t g1xg2 g1g2;
      admit()
    end

  | EApp e1 e2 ->
    let (Some (TArrow t1 t2)) = typing e1 (append (extend g1 x u) g2) in
    substitution_preserves_typing x e1 u (TArrow t1 t2) v g1 g2;
    substitution_preserves_typing x e2 u t1 v g1 g2

  | EIf e1 e2 e3 ->
    substitution_preserves_typing x e1 u TBool v g1 g2;
    substitution_preserves_typing x e2 u t v g1 g2;
    substitution_preserves_typing x e3 u t v g1 g2

  | EAbs x' t e1 -> 
    substitution_preserves_typing x e1 u t v g1 (extend g2 x' t) 

(* (\* Need to strengthen the IH with a context on the right *\) *)
(*     admit() (\* EAbs x t (if x = x' then e1 else (subst x e e1)) *\) *)


(* val preservation : e:exp -> e':exp -> t:ty -> Pure unit *)
(*       (requires (typing e empty = Some t /\ step e = Some e')) *)
(*       (ensures \r -> (typing e' empty = Some t)) *)
(* let rec preservation e e' t = *)
(*   match e with *)
(*   | EApp e1 e2 -> begin *)
(*       match typing e1 empty with *)
(*       | Some (TArrow t1 t2) -> begin *)
(*           assert(typing e2 empty = Some t1); (\* -- works *\) *)
(*           assert(typing e empty = Some t2); (\* -- works *\) *)
(*           if is_value e1 then *)
(*             if is_value e2 then *)
(*               match e1 with *)
(*               | EAbs x t e' -> *)
(*                   assert(step e = Some (subst x e2 e')); (\* -- works *\) *)
(* (\*                  assert (t = t1); -- this should work, but it doesn't *\) *)
(* (\*                  assert(typing e' (extend empty x t1) = Some t2); *)
(*                       -- this should work, but it doesn't *\) *)
(* (\*                  substitution_preserves_typing empty x e' t1 t2 e2 *)
(*                       -- this should work, but now precondition fails *\) *)
(*                   admit() *)
(*             else *)
(*               match (step e2) with *)
(*               | Some e2' -> preservation e2 e2' t1 *)
(*           else *)
(*             match (step e1) with *)
(*             | Some e1' -> preservation e1 e1' (TArrow t1 t2) *)
(*           end *)
(*       end *)
(*   | EIf e1 _ _ -> *)
(*       if is_value e1 then () *)
(*       else begin *)
(*         match (step e1) with *)
(*         | Some e1' -> preservation e1 e1' TBool *)
(*       end *)
(*   | _ -> () *)

(* (\* CH: With this purely-executable way of specifying things we can't *)
(*    do rule induction, and that is restrictive and will probably lead *)
(*    to rather unnatural proofs. *\) *)
