(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Reflection.Compare

open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Reflection.Builtins
open FStar.Reflection.Derived
open FStar.Order

let compare_name (n1 n2 : name) : order =
    compare_list n1 n2 (fun s1 s2 -> order_from_int (compare_string s1 s2))

let compare_fv (f1 f2 : fv) : order =
    compare_name (inspect_fv f1) (inspect_fv f2)

let compare_const (c1 c2 : vconst) : order =
    match c1, c2 with
    | C_Unit, C_Unit -> Eq
    | C_Int i, C_Int j -> order_from_int (i - j)
    | C_True, C_True -> Eq
    | C_False, C_False -> Eq
    | C_String s1, C_String s2 -> order_from_int (compare_string s1 s2)
    | C_Range r1, C_Range r2 -> Eq
    | C_Reify, C_Reify -> Eq
    | C_Reflect l1, C_Reflect l2 -> compare_name l1 l2
    | C_Unit,  _ -> Lt       | _, C_Unit  -> Gt
    | C_Int _, _ -> Lt       | _, C_Int _ -> Gt
    | C_True,  _ -> Lt       | _, C_True  -> Gt
    | C_False, _ -> Lt       | _, C_False -> Gt
    | C_String _, _ -> Lt    | _, C_String _ -> Gt
    | C_Range _, _ -> Lt     | _, C_Range _ -> Gt
    | C_Reify, _ -> Lt       | _, C_Reify -> Gt
    | C_Reflect _, _ -> Lt   | _, C_Reflect _ -> Gt

let compare_binder (b1 b2 : binder) : order =
    let bview1 = inspect_binder b1 in
    let bview2 = inspect_binder b2 in
    compare_bv bview1.binder_bv bview2.binder_bv

let compare_ident (i1 i2:ident) : order =
  order_from_int (compare_string (fst i1) (fst i2))

let rec compare_universe (u1 u2:universe) : order =
  match inspect_universe u1, inspect_universe u2 with
  | Uv_Zero, Uv_Zero -> Eq
  | Uv_Succ u1, Uv_Succ u2 -> compare_universe u1 u2
  | Uv_Max us1, Uv_Max us2 ->
    compare_list us1 us2 (fun x y -> compare_universe x y)
  | Uv_BVar n1, Uv_BVar n2 -> compare_int n1 n2
  | Uv_Name i1, Uv_Name i2 -> compare_ident i1 i2
  | Uv_Unif u1, Uv_Unif u2 -> Eq  //AR: TODO
  | Uv_Unk, Uv_Unk -> Eq
  | Uv_Zero, _ -> Lt | _, Uv_Zero -> Gt
  | Uv_Succ _, _ -> Lt | _, Uv_Succ _ -> Gt
  | Uv_Max _, _ -> Lt | _, Uv_Max _ -> Gt
  | Uv_BVar _, _ -> Lt | _, Uv_BVar _ -> Gt
  | Uv_Name _, _ -> Lt | _, Uv_Name _ -> Gt
  | Uv_Unif _, _ -> Lt | _, Uv_Unif _ -> Gt
  | Uv_Unk, _ -> Lt

let compare_universes (us1 us2:universes) : order =
  compare_list us1 us2 compare_universe

let rec compare_term (s t : term) : Tot order (decreases s) =
    match inspect_ln s, inspect_ln t with
    | Tv_Var sv, Tv_Var tv ->
        compare_bv sv tv

    | Tv_BVar sv, Tv_BVar tv ->
        compare_bv sv tv

    | Tv_FVar sv, Tv_FVar tv ->
        compare_fv sv tv

    | Tv_UInst sv sus, Tv_UInst tv tus ->
        lex (compare_fv sv tv) (fun _ -> compare_universes sus tus)

    | Tv_App h1 a1, Tv_App h2 a2 ->
        lex (compare_term h1 h2) (fun () -> compare_argv a1 a2)

    | Tv_Abs b1 e1, Tv_Abs b2 e2 ->
        lex (compare_binder b1 b2) (fun () -> compare_term e1 e2)

    | Tv_Refine bv1 e1, Tv_Refine bv2 e2 ->
        lex (compare_bv bv1 bv2) (fun () -> compare_term e1 e2)

    | Tv_Arrow b1 e1, Tv_Arrow b2 e2 ->
        lex (compare_binder b1 b2) (fun () -> compare_comp e1 e2)

    | Tv_Type su, Tv_Type tu -> compare_universe su tu

    | Tv_Const c1, Tv_Const c2 ->
        compare_const c1 c2

    | Tv_Uvar u1 _, Tv_Uvar u2 _->
        compare_int u1 u2

    | Tv_Let _r1 _attrs1 bv1 t1 t1', Tv_Let _r2 _attrs2 bv2 t2 t2' ->
        lex (compare_bv bv1 bv2) (fun () ->
        lex (compare_term t1 t2) (fun () ->
             compare_term t1' t2'))

    | Tv_Match _ _ _, Tv_Match _ _ _ ->
        Eq // TODO

    | Tv_AscribedT e1 t1 tac1 _, Tv_AscribedT e2 t2 tac2 _ ->
        lex (compare_term e1 e2) (fun () ->
        lex (compare_term t1 t2) (fun () ->
        match tac1, tac2 with
        | None, None -> Eq
        | None, _  -> Lt
        | _, None -> Gt
        | Some e1, Some e2 -> compare_term e1 e2))

    | Tv_AscribedC e1 c1 tac1 _, Tv_AscribedC e2 c2 tac2 _ ->
        lex (compare_term e1 e2) (fun () ->
        lex (compare_comp c1 c2) (fun () ->
        match tac1, tac2 with
        | None, None -> Eq
        | None, _  -> Lt
        | _, None -> Gt
        | Some e1, Some e2 -> compare_term e1 e2))

    | Tv_Unknown, Tv_Unknown ->
        Eq

    // From here onward, they must have different constructors. Order them arbitrarily as in the definition.
    | Tv_Var _, _      -> Lt   | _, Tv_Var _      -> Gt
    | Tv_BVar _, _     -> Lt   | _, Tv_BVar _     -> Gt
    | Tv_FVar _, _     -> Lt   | _, Tv_FVar _     -> Gt
    | Tv_UInst _ _, _  -> Lt   | _, Tv_UInst _ _  -> Gt
    | Tv_App _ _, _    -> Lt   | _, Tv_App _ _    -> Gt
    | Tv_Abs _ _, _    -> Lt   | _, Tv_Abs _ _    -> Gt
    | Tv_Arrow _ _, _  -> Lt   | _, Tv_Arrow _ _  -> Gt
    | Tv_Type _, _    -> Lt    | _, Tv_Type _    -> Gt
    | Tv_Refine _ _, _ -> Lt   | _, Tv_Refine _ _ -> Gt
    | Tv_Const _, _    -> Lt   | _, Tv_Const _    -> Gt
    | Tv_Uvar _ _, _   -> Lt   | _, Tv_Uvar _ _   -> Gt
    | Tv_Match _ _ _, _  -> Lt | _, Tv_Match _ _ _  -> Gt
    | Tv_AscribedT _ _ _ _, _  -> Lt | _, Tv_AscribedT _ _ _ _ -> Gt
    | Tv_AscribedC _ _ _ _, _  -> Lt | _, Tv_AscribedC _ _ _ _ -> Gt
    | Tv_Unknown, _    -> Lt   | _, Tv_Unknown    -> Gt
and compare_term_list (l1 l2:list term) : Tot order (decreases l1) =
  match l1, l2 with
  | [], [] -> Eq
  | [], _ -> Lt
  | _, [] -> Gt
  | hd1::tl1, hd2::tl2 ->
    lex (compare_term hd1 hd2) (fun () -> compare_term_list tl1 tl2)

and compare_argv (a1 a2 : argv) : Tot order (decreases a1) =
    let a1, q1 = a1 in
    let a2, q2 = a2 in
    match q1, q2 with
    (* We should never see Q_Meta here *)
    | Q_Implicit, Q_Explicit -> Lt
    | Q_Explicit, Q_Implicit -> Gt
    | _, _ -> compare_term a1 a2
and compare_comp (c1 c2 : comp) : Tot order (decreases c1) =
    let cv1 = inspect_comp c1 in
    let cv2 = inspect_comp c2 in
    match cv1, cv2 with
    | C_Total t1, C_Total t2

    | C_GTotal t1, C_GTotal t2 -> compare_term t1 t2

    | C_Lemma p1 q1 s1, C_Lemma p2 q2 s2 ->
      lex (compare_term p1 p2)
          (fun () ->
            lex (compare_term q1 q2)
                (fun () -> compare_term s1 s2)
          )

    | C_Eff us1 eff1 res1 args1 _decrs1,
      C_Eff us2 eff2 res2 args2 _decrs2 ->
        (* This could be more complex, not sure it is worth it *)
        lex (compare_universes us1 us2)
            (fun _ -> lex (compare_name eff1 eff2)
                       (fun _ -> compare_term res1 res2))

    | C_Total _, _  -> Lt     | _, C_Total _ -> Gt
    | C_GTotal _, _  -> Lt    | _, C_GTotal _ -> Gt
    | C_Lemma _ _ _, _  -> Lt   | _, C_Lemma _ _ _ -> Gt
    | C_Eff _ _ _ _ _, _ -> Lt    | _, C_Eff _ _ _ _ _ -> Gt
