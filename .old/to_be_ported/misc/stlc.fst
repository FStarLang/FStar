(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(* Formalizing STLC in F*  *)
module STLC_Classic

logic data type typ = 
  | TUnit : typ
  | TArrow : typ -> typ -> typ

logic data type value =
  | Unit : value
  | Var : string -> value
  | Lam : string -> typ -> exp -> value
and exp = 
  | Value : value -> exp
  | App : exp -> exp -> exp

type env = Map.map
logic val Emp : env
logic val Sel : env -> string -> typ
logic val Concat : env -> env -> env
logic val Singleton : string -> typ -> env
type In = Map.In string
logic val Upd : env -> string -> typ -> env
type Equal = Map.Equal
define Emp_def:Emp = Map.Emp
define Sel_def:forall g x. Sel g x = Map.Sel string typ g x 
define Concat_def:forall g1 g2. Concat g1 g2 = Map.Concat g1 g2
define Singleton_def:forall x t. Singleton x t = Map.Singleton string typ x t
define Upd_def:forall g x t. Upd g x t=Map.Upd string typ g x t

type Typing : env => exp => typ => E
assume Typing_unit: forall g. Typing g (Value Unit) TUnit
assume Typing_var: forall g x. In g x 
                          ==> Typing g (Value (Var x)) (Sel g x)
assume Typing_lam: forall g x t t' e. Typing (Upd g x t) e t'
                          ==> Typing g (Value (Lam x t e)) (TArrow t t')
assume Typing_app: forall g e1 e2 t1 t2. 
                            Typing g e1 (TArrow t1 t2) /\ Typing g e2 t1
                          ==> Typing g (App e1 e2) t2

assume Typing_value_inv: forall g v t.{:pattern (Typing g (Value v) t)} 
                            Typing g (Value v) t 
                         ==> (Unit_is v ==> TUnit_is t)
                         /\ (TUnit_is t ==> Var_is v \/ Unit_is v)
                         /\ (Var_is v ==> In g (Var_proj_0 v) /\ t=Sel g (Var_proj_0 v))
                         /\ (Lam_is v ==> 
                               TArrow_is t 
                             /\ TArrow_proj_0 t = Lam_proj_1 v
                             /\ Typing (Upd g (Lam_proj_0 v) (Lam_proj_1 v)) (Lam_proj_2 v) (TArrow_proj_1 t))
                         /\ (TArrow_is t ==> Lam_is v \/ Var_is v)
assume Typing_app_inv: forall g e1 e2 t2. Typing g (App e1 e2) t2
                         ==> (exists t t'. Typing g e1 t /\ Typing g e2 t')
                             /\ (forall t1. Typing g e2 t1 ==> 
                                   (forall t'. Typing g e1 t' ==> t'=TArrow t1 t2))

type WellTyped = fun g e => exists t. Typing g e t

val compute_type: g:env -> e:exp -> o:option (t:typ{Typing g e t}){WellTyped g e ==> Some_is o}
let rec compute_type g e = match e with 
  | Value (Var x) -> 
    if Map.contains g x then 
      Some (Sel g x <: t:typ{Typing g e t})
    else None
  | Value Unit -> Some (TUnit <: t:typ{Typing g e t})
  | Value (Lam x t body) -> 
    (match compute_type (Upd g x t) body with 
      | None -> None
      | Some t' -> Some (TArrow t t' <: t:typ{Typing g e t}))
  | App e1 e2 -> 
    match compute_type g e2 with 
      | None -> None
      | Some targ -> 
        match compute_type g e1 with 
          | None -> None
          | Some t -> 
            match t with 
              | TUnit -> None
              | TArrow targ' tres -> 
                if targ=targ' then Some (tres <: t:typ{Typing g e t}) else None

val typing_unique: g:env -> e:exp -> t1:typ{Typing g e t1} -> t2:typ{Typing g e t2} -> u:unit{t1=t2}
let rec typing_unique g e t1 t2 = match e with 
  | Value Unit -> ()
  | Value (Var x) -> ()
  | Value (Lam x tx body) -> 
    (match t1, t2 with 
      | TArrow _ t1b, TArrow _ t2b -> 
        typing_unique (Upd g x tx) body t1b t2b
      | TUnit, _ -> unreachable()
      | _, TUnit -> unreachable ())
  | App e1 e2 -> 
    match compute_type g e2 with 
      | None -> unreachable ()
      | Some targ -> typing_unique g e1 (TArrow targ t1) (TArrow targ t2)

val weakening:g1:env -> g2:env -> e:exp -> t:typ{Typing (Concat g1 g2) e t}              
           -> y:string{not(In g1 y)} -> ty:typ 
           -> u:unit{Typing (Concat (Upd g1 y ty) g2) e t}
let rec weakening g1 g2 e t y ty = match e with 
  | Value Unit -> ()
  | Value (Var x) -> ()
  | Value (Lam z tz body) -> 
      weakening g1 (Upd g2 z tz) body (TArrow_proj_1 t) y ty
  | App e1 e2 -> 
      match compute_type (Concat g1 g2) e1 with 
        | None -> unreachable ()
        | Some TUnit -> unreachable ()
        | Some (TArrow t1 t2) -> 
            weakening g1 g2 e1 (TArrow t1 t2) y ty;
            weakening g1 g2 e2 t1 y ty

logic val bvars: exp -> env 
assume Bvar_Unit: bvars (Value Unit) = Emp
assume Bvar_Var: forall x.{:pattern (bvars (Value (Var x)))} bvars (Value (Var x)) = Emp
assume Bvar_Lam: forall x t e.{:pattern (bvars (Value (Lam x t e)))} bvars (Value (Lam x t e)) = Concat (Singleton x t) (bvars e)
assume Bvar_App: forall e1 e2.{:pattern (bvars (App e1 e2))} bvars (App e1 e2) = Concat (bvars e1) (bvars e2)

val rename: g:env -> g':env -> y:string{not(In g' y)} -> z:string{not(In g z \/ In g' z)} -> tyz:typ
         -> e:exp{not(In (bvars e) z)} -> te:typ{Typing (Concat (Upd g y tyz) g') e te}
         -> e':exp{Typing (Concat (Upd g z tyz) g') e' te}
let rec rename g g' y z tyz e te = match e with 
  | Value Unit -> e
  | Value (Var w) -> 
    if w=y 
    then Value (Var z)
    else e
  | Value (Lam w tw body) -> 
      if w=y 
      then 
        assert (Equal (Upd (Concat (Upd g y tyz) g') w tw)
                      (Upd (Concat g g') w tw));
        weakening g (Upd g' w tw) body (TArrow_proj_1 te) z tyz;
        e
      else 
        let body' = rename g (Upd g' w tw) y z tyz body (TArrow_proj_1 te) in 
          Value (Lam w tw body')
  | App e1 e2 -> 
      match compute_type (Concat (Upd g y tyz) g') e1 with 
        | None -> unreachable ()
        | Some t -> 
            let e1' = rename g g' y z tyz e1 t in
            let e2' = rename g g' y z tyz e2 (TArrow_proj_0 t) in
              App e1' e2'

val subst: g:env -> g':env -> tx:typ -> te:typ 
        -> x:string{not(In g' x)}
        -> v:value{Typing (Concat g g') (Value v) tx}
        -> e:exp{Typing (Concat (Upd g x tx) g') e te}
        -> e':exp{Typing (Concat g g') e' te}
let rec subst g g' tx te x v e = match e with 
  | Value (Var y) -> 
    if x=y 
    then Value v
    else Value (Var y)

  | Value Unit -> Value Unit

  | Value (Lam y targ body) -> 
    if x=y 
    then 
      assert (Equal 
                (Upd (Concat (Upd g x tx) g') y targ) 
                (Upd (Concat g g') y targ));
      e
    else 
      let z = Map.fresh (Concat (Concat (Upd g x tx) g') (bvars e)) in 
      weakening (Concat g g') Emp (Value v) tx z targ;
        (* Typing (Upd (Concat g g') z targ) (Value v) tx *)
      let body = rename (Concat (Upd g x tx) g') Emp y z targ body (TArrow_proj_1 te) in
        (* Typing (Upd (Concat (Upd g x tx) g') z targ) body (TArrow_proj_1 te) *)
      let body' = subst g (Upd g' z targ) tx (TArrow_proj_1 te) x v body in  
        (* Typing (Upd (Concat g g') z targ) body te *)
        Value (Lam z targ body')
        
  | App e1 e2 -> 
    match compute_type (Concat (Upd g x tx) g') e1 with 
      | None -> unreachable ()
      | Some TUnit -> unreachable ()
      | Some (TArrow t1 t2) -> 
        let e1' = subst g g' tx (TArrow t1 t2) x v e1 in 
        let e2' = subst g g' tx t1 x v e2 in 
        App e1' e2'
          
val eval: e:exp -> t:typ{Typing Emp e t} -> v:value{Typing Emp (Value v) t}
let rec eval e t = match e with 
  | Value v -> v
  | App e1 e2 -> 
    match compute_type Emp e1 with 
      | None -> unreachable ()
      | Some TUnit -> unreachable ()
      | Some (TArrow t1 t2) -> 
        match eval e1 (TArrow t1 t2) with 
          | Unit -> unreachable ()
          | Var x -> unreachable ()
          | Lam x t body -> 
            let arg = eval e2 t1 in 
            eval (subst Emp Emp t1 t2 x arg body) t2
