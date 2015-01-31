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
//////////////////////////////////////////////////////////////////////////
//Refinement subtyping with higher-order unification 
//with special treatment for higher-order patterns 
//////////////////////////////////////////////////////////////////////////

#light "off"
module Microsoft.FStar.Tc.Rel

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc.Rel2

type guard_formula = Rel2.guard_formula
type guard_t = Rel2.guard_t

let rel1_g g = Rel2.guard_of_guard_formula g

let rel1_g_opt = function
    | None -> None
    | Some g -> Some (rel1_g g)

let new_kvar r b = 
    if !Options.rel2
    then Rel2.new_kvar r b
    else Rel1.new_kvar r b

let new_tvar r b k = 
    if !Options.rel2
    then Rel2.new_tvar r b k
    else Rel1.new_tvar r b k
   
let new_evar r b t = 
    if !Options.rel2 
    then Rel2.new_evar r b t
    else Rel1.new_evar r b t

let close_guard b g =
    if !Options.rel2 
    then Rel2.close_guard b g
    else Rel1.close_guard b (g.guard_f) |> rel1_g

let apply_guard g e =
    if !Options.rel2 
    then Rel2.apply_guard g e
    else Rel1.apply_guard g.guard_f e |> rel1_g

let trivial_guard =
    if !Options.rel2
    then Rel2.trivial_guard
    else Trivial |> rel1_g

let is_trivial g = 
    Rel2.is_trivial g
    
let conj_guard g1 g2 = Rel2.conj_guard g1 g2
let imp_guard g1 g2 = Rel2.imp_guard g1 g2
let guard_of_guard_formula g = Rel2.guard_of_guard_formula g
let guard_f g = g.guard_f

let guard_to_string env g = 
    if !Options.rel2
    then Rel2.guard_to_string env g
    else Rel1.guard_to_string env g.guard_f

let solve_deferred_constraints e g = 
    if !Options.rel2
    then Rel2.solve_deferred_constraints e g
    else g

let try_discharge_guard e g = 
    if !Options.rel2
    then Rel2.try_discharge_guard e g
    else Rel1.try_discharge_guard e g.guard_f

let try_keq env k k' =
    if !Options.rel2
    then Rel2.try_keq env k k'
    else Rel1.try_keq env k k' |> rel1_g_opt

let keq env topt k1 k2 = 
    if !Options.rel2
    then Rel2.keq env topt k1 k2
    else Rel1.keq env topt k1 k2 |> rel1_g

let subkind env k1 k2 = 
    if !Options.rel2
    then Rel2.subkind env k1 k2
    else Rel1.subkind env k1 k2 |> rel1_g

let try_teq env t1 t2 = 
    if !Options.rel2
    then Rel2.try_teq env t1 t2
    else Rel1.try_teq env t1 t2 |> rel1_g_opt

let teq env t1 t2 = 
    if !Options.rel2
    then Rel2.teq env t1 t2
    else Rel1.teq env t1 t2 |> rel1_g

let try_subtype env t1 t2 = 
    if !Options.rel2
    then Rel2.try_subtype env t1 t2
    else Rel1.try_subtype env t1 t2 |> rel1_g_opt
    
let subtype env t1 t2 = 
    if !Options.rel2
    then Rel2.subtype env t1 t2
    else Rel1.subtype env t1 t2 |> rel1_g

let subtype_fail env t1 t2 = 
    if !Options.rel2
    then Rel2.subtype_fail env t1 t2
    else Rel1.subtype_fail env t1 t2 

let trivial_subtype env eopt t1 t2 =
    if !Options.rel2
    then Rel2.trivial_subtype env eopt t1 t2
    else Rel1.trivial_subtype env eopt t1 t2 

let simplify_guard env g = 
    if !Options.rel2
    then Rel2.simplify_guard env g
    else g

let sub_comp e c1 c2 = 
    if !Options.rel2 
    then Rel2.sub_comp e c1 c2
    else Rel1.sub_comp e c1 c2 |> rel1_g_opt

   