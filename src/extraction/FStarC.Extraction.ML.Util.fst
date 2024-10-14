(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStarC.Extraction.ML.Util
open Prims
open FStar.Pervasives
open FStarC.Compiler.Effect
open FStarC.Compiler.List
open FStar open FStarC
open FStarC.Compiler
open FStarC.Compiler.Util
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Const
open FStarC.Ident
open FStarC.Errors
module BU = FStarC.Compiler.Util
module U = FStarC.Syntax.Util
module UEnv = FStarC.Extraction.ML.UEnv
module PC = FStarC.Parser.Const
module Range = FStarC.Compiler.Range
module S = FStarC.Syntax.Syntax
module N = FStarC.TypeChecker.Normalize
module Env = FStarC.TypeChecker.Env

open FStarC.Class.Show

let codegen_fsharp () = Options.codegen () = Some Options.FSharp

let pruneNones (l : list (option 'a)) : list 'a =
    List.fold_right (fun  x ll -> match x with
                          | Some xs -> xs::ll
                          | None -> ll) l []


let mk_range_mle = with_ty MLTY_Top <| MLE_Name (["FStar"; "Range"], "mk_range")
let dummy_range_mle = with_ty MLTY_Top <| MLE_Name (["FStar"; "Range"], "dummyRange")

(* private *)
let mlconst_of_const' (sctt : sconst) =
  match sctt with
  | Const_effect       -> failwith "Unsupported constant"

  | Const_range _
  | Const_unit          -> MLC_Unit
  | Const_char   c      -> MLC_Char  c
  | Const_int    (s, i) -> MLC_Int   (s, i)
  | Const_bool   b      -> MLC_Bool  b
  | Const_string (s, _) -> MLC_String (s)

  | Const_range_of
  | Const_set_range_of ->
    failwith "Unhandled constant: range_of/set_range_of"

  | Const_real _
  | Const_reify _
  | Const_reflect _ ->
    failwith "Unhandled constant: real/reify/reflect"

let mlconst_of_const (p:Range.range) (c:sconst) =
    try mlconst_of_const' c
    with _ -> failwith (BU.format2 "(%s) Failed to translate constant %s " (Range.string_of_range p) (show c))

let mlexpr_of_range (r:Range.range) : mlexpr' =
    let cint (i : int) : mlexpr =
        MLC_Int (string_of_int i, None) |> MLE_Const |> with_ty ml_int_ty
    in
    let cstr (s : string) : mlexpr =
        MLC_String s |> MLE_Const |> with_ty ml_string_ty
    in
    let drop_path = BU.basename in

    // This is not being fully faithful since it disregards
    // the use_range, but I assume that's not too bad.
    //
    // We drop the path of the file to be independent of the machine
    // where this was extracted. Otherwise we run into some headaches
    // with CI, stability, and moving ml files between hosts. The idea
    // is that the pathless filename is enough to locate the actual file,
    // since it must have been loaded as a dependency by F*.
    MLE_App (mk_range_mle, [Range.file_of_range r |> drop_path |> cstr;
                            Range.start_of_range r |> Range.line_of_pos |> cint;
                            Range.start_of_range r |> Range.col_of_pos  |> cint;
                            Range.end_of_range r   |> Range.line_of_pos |> cint;
                            Range.end_of_range r   |> Range.col_of_pos  |> cint;
                            ])

let mlexpr_of_const (p:Range.range) (c:sconst) : mlexpr' =
    (* Special case ranges, which can be extracted but not as constants.
     * Maybe a sign that there shouldn't really be a Const_range *)
    match c with
    | Const_range r ->
        mlexpr_of_range r

    | _ ->
        MLE_Const (mlconst_of_const p c)

let rec subst_aux (subst:list (mlident & mlty)) (t:mlty)  : mlty =
    match t with
    | MLTY_Var  x -> (match BU.find_opt (fun (y, _) -> y=x) subst with
                     | Some ts -> snd ts
                     | None -> t) // TODO : previously, this case would abort. why? this case was encountered while extracting st3.fst
    | MLTY_Fun (t1, f, t2) -> MLTY_Fun(subst_aux subst t1, f, subst_aux subst t2)
    | MLTY_Named(args, path) -> MLTY_Named(List.map (subst_aux subst) args, path)
    | MLTY_Tuple ts -> MLTY_Tuple(List.map (subst_aux subst) ts)
    | MLTY_Top
    | MLTY_Erased -> t

let try_subst ((formals, t):mltyscheme) (args:list mlty) : option mlty =
    if List.length formals <> List.length args
    then None
    else Some (subst_aux (List.zip (ty_param_names formals) args) t)

let subst ts args =
    match try_subst ts args with
    | None ->
      failwith "Substitution must be fully applied (see GitHub issue #490)"
    | Some t ->
      t

let udelta_unfold (g:UEnv.uenv) = function
    | MLTY_Named(args, n) ->
      begin match UEnv.lookup_tydef g n with
        | Some ts ->
          begin
            match try_subst ts args with
            | None ->
              failwith (BU.format3 "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                                                 (string_of_mlpath n)
                                                 (BU.string_of_int (List.length args))
                                                 (BU.string_of_int (List.length (fst ts))))
            | Some r -> Some r
          end
        | _ -> None
      end
    | _ -> None

let eff_leq f f' = match f, f' with
    | E_PURE, _          -> true
    | E_ERASABLE, E_ERASABLE   -> true
    | E_IMPURE, E_IMPURE -> true
    | _ -> false

let eff_to_string = function
    | E_PURE -> "Pure"
    | E_ERASABLE -> "Erasable"
    | E_IMPURE -> "Impure"

let join r f f' = match f, f' with
    | E_IMPURE, E_PURE
    | E_PURE  , E_IMPURE
    | E_IMPURE, E_IMPURE -> E_IMPURE
    | E_ERASABLE , E_ERASABLE  -> E_ERASABLE
    | E_PURE  , E_ERASABLE  -> E_ERASABLE
    | E_ERASABLE , E_PURE   -> E_ERASABLE
    | E_PURE  , E_PURE   -> E_PURE
    | _ -> failwith (BU.format3 "Impossible (%s): Inconsistent effects %s and %s"
                            (Range.string_of_range r)
                            (eff_to_string f) (eff_to_string f'))

let join_l r fs = List.fold_left (join r) E_PURE fs

let mk_ty_fun = List.fold_right (fun {mlbinder_ty} t -> MLTY_Fun(mlbinder_ty, E_PURE, t))

(* type_leq is essentially the lifting of the sub-effect relation, eff_leq, into function types.
   type_leq_c is a coercive variant of type_leq, which implements an optimization to erase the bodies of ghost functions.
   Specifically, a function (f : t -> Pure t') can be subsumed to (t -> Ghost t')
   In the case where f is a function literal, \x. e, subsuming it to (t -> Ghost t') means that we can simply
   erase e to unit right away.
*)
let rec type_leq_c (unfold_ty:unfold_t) (e:option mlexpr) (t:mlty) (t':mlty) : (bool & option mlexpr) =
    match t, t' with
    | MLTY_Var x, MLTY_Var y ->
        if x = y
        then true, e
        else false, None

    | MLTY_Fun (t1, f, t2), MLTY_Fun (t1', f', t2') ->
        let mk_fun xs body =
            match xs with
            | [] -> body
            | _ ->
                let e = match body.expr with
                | MLE_Fun(ys, body) -> MLE_Fun(xs@ys, body)
                | _ -> MLE_Fun(xs, body) in
            with_ty (mk_ty_fun xs body.mlty) e in
        begin match e with
        | Some ({expr=MLE_Fun(x::xs, body)}) ->
            if type_leq unfold_ty t1' t1
            && eff_leq f f'
            then if f=E_PURE
                && f'=E_ERASABLE
                then if type_leq unfold_ty t2 t2'
                    then let body = if type_leq unfold_ty t2 ml_unit_ty
                                    then ml_unit
                                    else with_ty t2' <| MLE_Coerce(ml_unit, ml_unit_ty, t2') in
                            true, Some (with_ty (mk_ty_fun [x] body.mlty) <| MLE_Fun([x], body))
                    else false, None
                else let ok, body = type_leq_c unfold_ty (Some <| mk_fun xs body) t2 t2' in
                    let res = match body with
                        | Some body -> Some (mk_fun [x] body)
                        | _ ->  None in
                    ok, res
            else false, None

        | _ ->
            if type_leq unfold_ty t1' t1
            && eff_leq f f'
            && type_leq unfold_ty t2 t2'
            then true, e
            else false, None
        end

    | MLTY_Named(args, path), MLTY_Named(args', path') ->
        if path=path'
        then if List.forall2 (type_leq unfold_ty) args args'
            then true, e
            else false, None
        else begin match unfold_ty t with
                    | Some t -> type_leq_c unfold_ty e t t'
                    | None -> (match unfold_ty t' with
                                    | None -> false, None
                                    | Some t' -> type_leq_c unfold_ty e t t')
            end

    | MLTY_Tuple ts, MLTY_Tuple ts' ->
        if List.forall2 (type_leq unfold_ty) ts ts'
        then true, e
        else false, None

    | MLTY_Top, MLTY_Top -> true, e

    | MLTY_Named _, _ ->
        begin match unfold_ty t with
        | Some t -> type_leq_c unfold_ty e t t'
        | _ ->  false, None
        end

    | _, MLTY_Named _ ->
        begin match unfold_ty t' with
        | Some t' -> type_leq_c unfold_ty e t t'
        | _ -> false, None
        end

    | MLTY_Erased, MLTY_Erased ->
      true, e

    | _ -> false, None

and type_leq g t1 t2 : bool = type_leq_c g None t1 t2 |> fst

let rec erase_effect_annotations (t:mlty) =
    match t with
    | MLTY_Fun(t1, f, t2) ->
      MLTY_Fun(erase_effect_annotations t1, E_PURE, erase_effect_annotations t2)
    | _ -> t

let is_type_abstraction = function
    | (Inl _, _)::_ -> true
    | _ -> false

let is_xtuple (ns, n) =
  if FStarC.Parser.Const.is_tuple_datacon_string (BU.concat_l "." (ns@[n]))
  (* Returns the integer k in "Mktuplek" *)
  then Some (BU.int_of_char (BU.char_at n 7))
  else None

let resugar_exp e = match e.expr with
    | MLE_CTor(mlp, args) ->
        (match is_xtuple mlp with
        | Some n -> with_ty e.mlty <| MLE_Tuple args
        | _ -> e)
    | _ -> e

let record_field_path = function
    | f::_ ->
        let ns, _ = BU.prefix (ns_of_lid f) in
        ns |> List.map (fun id -> (string_of_id id))
    | _ -> failwith "impos"

let record_fields fs vs = List.map2 (fun (f:lident) e -> (string_of_id (ident_of_lid f)), e) fs vs
//
//let resugar_pat q p = match p with
//    | MLP_CTor(d, pats) ->
//      begin match is_xtuple d with
//        | Some n -> MLP_Tuple(pats)
//        | _ ->
//          match q with
//            | Some (Record_ctor (_, fns)) ->
//              let p = record_field_path fns in
//              let fs = record_fields fns pats in
//              MLP_Record(p, fs)
//            | _ -> p
//      end
//    | _ -> p


let is_xtuple_ty (ns, n) =
  if FStarC.Parser.Const.is_tuple_constructor_string (BU.concat_l "." (ns@[n]))
  (* Returns the integer k in "tuplek" *)
  then Some (BU.int_of_char (BU.char_at n 5))
  else None

let resugar_mlty t = match t with
    | MLTY_Named (args, mlp) ->
      begin match is_xtuple_ty mlp with
        | Some n -> MLTY_Tuple args
        | _ -> t
      end
    | _ -> t
    
let flatten_ns ns = String.concat "_" ns
let flatten_mlpath (ns, n) = String.concat "_" (ns@[n])
let ml_module_name_of_lid (l:lident) =
  let mlp = l |> ns_of_lid |> List.map string_of_id,  string_of_id (ident_of_lid l) in
  flatten_mlpath mlp


let rec erasableType (unfold_ty:unfold_t) (t:mlty) :bool =
   let erasableTypeNoDelta (t:mlty) =
     if t = ml_unit_ty then true
     else match t with
          | MLTY_Named (_, (["FStar"; "Ghost"], "erased")) -> true
          (* erase tactic terms, unless extracting for tactic compilation *)
          | MLTY_Named (_, (["FStar"; "Tactics"; "Effect"], "tactic")) -> Options.codegen () <> Some Options.Plugin
          | _ -> false // this function is used by another function which does delta unfolding
   in
   if erasableTypeNoDelta t
   then true
   else match unfold_ty t with
     | Some t -> erasableType unfold_ty t
     | None  -> false

let rec eraseTypeDeep unfold_ty (t:mlty) : mlty =
    match t with
    | MLTY_Fun (tyd, etag, tycd) ->
      if etag=E_PURE
      then MLTY_Fun (eraseTypeDeep unfold_ty tyd, etag, eraseTypeDeep unfold_ty tycd)
      else t
    | MLTY_Named (lty, mlp) ->
      if erasableType unfold_ty t
      then MLTY_Erased
      else MLTY_Named (List.map (eraseTypeDeep unfold_ty) lty, mlp)  // only some named constants are erased to unit.
    | MLTY_Tuple lty ->  MLTY_Tuple (List.map (eraseTypeDeep unfold_ty) lty)
    | _ ->  t

let prims_op_equality = with_ty MLTY_Top <| MLE_Name (["Prims"], "op_Equality")
let prims_op_amp_amp  = with_ty (mk_ty_fun [{mlbinder_name="x";mlbinder_ty=ml_bool_ty;mlbinder_attrs=[]};
                                            {mlbinder_name="y";mlbinder_ty=ml_bool_ty;mlbinder_attrs=[]}] ml_bool_ty) <| MLE_Name (["Prims"], "op_AmpAmp")
let conjoin e1 e2 = with_ty ml_bool_ty <| MLE_App(prims_op_amp_amp, [e1;e2])
let conjoin_opt e1 e2 = match e1, e2 with
    | None, None -> None
    | Some x, None
    | None, Some x -> Some x
    | Some x, Some y -> Some (conjoin x y)

let mlloc_of_range (r: Range.range) =
    let pos = Range.start_of_range r in
    let line = Range.line_of_pos pos in
    line, Range.file_of_range r

let rec doms_and_cod (t:mlty) : list mlty & mlty =
    match t with
      | MLTY_Fun (a,_,b) ->
        let ds, c = doms_and_cod b in
        a::ds, c
      | _ ->
          [], t

let argTypes  (t: mlty) : list mlty =
    fst (doms_and_cod t)

let rec uncurry_mlty_fun t =
    match t with
    | MLTY_Fun (a,_,b) ->
        let args, res = uncurry_mlty_fun b in
        a::args, res
    | _ -> [], t

let list_elements (e:mlexpr) : option (list mlexpr) =
  let rec list_elements acc e =
    match e.expr with
    | MLE_CTor (([ "Fstar_guts.Prims" ], "Cons" ), [ hd; tl ]) ->
      list_elements (hd :: acc) tl
    | MLE_CTor (([ "Fstar_guts.Prims" ], "Nil" ), []) ->
      List.rev acc |> Some
    | MLE_CTor (([ "Prims" ], "Cons" ), [ hd; tl ]) ->
      list_elements (hd :: acc) tl
    | MLE_CTor (([ "Prims" ], "Nil" ), []) ->
      List.rev acc |> Some
    | _ -> None
  in
  list_elements [] e
