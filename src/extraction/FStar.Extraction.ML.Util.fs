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
#light "off"
module FStar.Extraction.ML.Util
open FStar.All
open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Const
open FStar.Ident
module BU = FStar.Util
module U = FStar.Syntax.Util
module UEnv = FStar.Extraction.ML.UEnv

let pruneNones (l : list<option<'a>>) : list<'a> =
    List.fold_right (fun  x ll -> match x with
                          | Some xs -> xs::ll
                          | None -> ll) l []


let mlconst_of_const (sctt : sconst) =
  match sctt with
  | Const_range _
  | Const_effect       -> failwith "Unsupported constant"
  | Const_unit         -> MLC_Unit
  | Const_char   c     -> MLC_Char  c
  | Const_int    (s, i)-> MLC_Int   (s, i)
  | Const_bool   b     -> MLC_Bool  b
  | Const_float  d     -> MLC_Float d

  | Const_bytearray (bytes, _) ->
      MLC_Bytes bytes

  | Const_string (bytes, _) ->
      MLC_String (string_of_unicode (bytes))

  | Const_reify
  | Const_reflect _ ->
    failwith "Unhandled constant: reify/reflect"

let mlconst_of_const' (p:Range.range) (c:sconst) =
    try mlconst_of_const c
    with _ -> failwith (BU.format2 "(%s) Failed to translate constant %s " (Range.string_of_range p) (Print.const_to_string c))

let rec subst_aux (subst:list<(mlident * mlty)>) (t:mlty)  : mlty =
    match t with
    | MLTY_Var  x -> (match BU.find_opt (fun (y, _) -> y=x) subst with
                     | Some ts -> snd ts
                     | None -> t) // TODO : previously, this case would abort. why? this case was encountered while extracting st3.fst
    | MLTY_Fun (t1, f, t2) -> MLTY_Fun(subst_aux subst t1, f, subst_aux subst t2)
    | MLTY_Named(args, path) -> MLTY_Named(List.map (subst_aux subst) args, path)
    | MLTY_Tuple ts -> MLTY_Tuple(List.map (subst_aux subst) ts)
    | MLTY_Top -> MLTY_Top

let subst ((formals, t):mltyscheme) (args:list<mlty>) : mlty =
    if List.length formals <> List.length args
    then failwith "Substitution must be fully applied (see GitHub issue #490)"
    else subst_aux (List.zip formals args) t

let udelta_unfold (g:UEnv.env) = function
    | MLTY_Named(args, n) ->
      begin match UEnv.lookup_ty_const g n with
        | Some ts ->
//          UEnv.debug g (fun _ -> printfn "Instantiating %A with %d formals with %d args"
//                                     n (List.length <| fst ts) (List.length args));
          Some (subst ts args)
        | _ -> None
      end
    | _ -> None


let eff_leq f f' = match f, f' with
    | E_PURE, _          -> true
    | E_GHOST, E_GHOST   -> true
    | E_IMPURE, E_IMPURE -> true
    | _ -> false

let eff_to_string = function
    | E_PURE -> "Pure"
    | E_GHOST -> "Ghost"
    | E_IMPURE -> "Impure"

let join r f f' = match f, f' with
    | E_IMPURE, E_PURE
    | E_PURE  , E_IMPURE
    | E_IMPURE, E_IMPURE -> E_IMPURE
    | E_GHOST , E_GHOST  -> E_GHOST
    | E_PURE  , E_GHOST  -> E_GHOST
    | E_GHOST , E_PURE   -> E_GHOST
    | E_PURE  , E_PURE   -> E_PURE
    | _ -> failwith (BU.format3 "Impossible (%s): Inconsistent effects %s and %s"
                            (Range.string_of_range r)
                            (eff_to_string f) (eff_to_string f'))

let join_l r fs = List.fold_left (join r) E_PURE fs

let mk_ty_fun = List.fold_right (fun (_, t0) t -> MLTY_Fun(t0, E_PURE, t))

type unfold_t = mlty -> option<mlty>

(* type_leq is essentially the lifting of the sub-effect relation, eff_leq, into function types.
   type_leq_c is a coercive variant of type_leq, which implements an optimization to erase the bodies of ghost functions.
   Specifically, a function (f : t -> Pure t') can be subsumed to (t -> Ghost t')
   In the case where f is a function literal, \x. e, subsuming it to (t -> Ghost t') means that we can simply
   erase e to unit right away.
*)
let rec type_leq_c (unfold_ty:unfold_t) (e:option<mlexpr>) (t:mlty) (t':mlty) : (bool * option<mlexpr>) =
    match t, t' with
        | MLTY_Var x, MLTY_Var y ->
          if fst x = fst y
          then true, e
          else false, None

        | MLTY_Fun (t1, f, t2), MLTY_Fun (t1', f', t2') ->
          let mk_fun xs body = match xs with
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
                   && f'=E_GHOST
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

        | _ -> false, None

and type_leq g t1 t2 : bool = type_leq_c g None t1 t2 |> fst

let is_type_abstraction = function
    | (Inl _, _)::_ -> true
    | _ -> false

let is_xtuple (ns, n) =
    if ns = ["Prims"] || ns = ["FStar"; "Pervasives"]
    then match n with
            | "Mktuple2" -> Some 2
            | "Mktuple3" -> Some 3
            | "Mktuple4" -> Some 4
            | "Mktuple5" -> Some 5
            | "Mktuple6" -> Some 6
            | "Mktuple7" -> Some 7
            | "Mktuple8" -> Some 8
            | _ -> None
    else None

let resugar_exp e = match e.expr with
    | MLE_CTor(mlp, args) ->
        (match is_xtuple mlp with
        | Some n -> with_ty e.mlty <| MLE_Tuple args
        | _ -> e)
    | _ -> e

let record_field_path = function
    | f::_ ->
        let ns, _ = BU.prefix f.ns in
        ns |> List.map (fun id -> id.idText)
    | _ -> failwith "impos"

let record_fields fs vs = List.map2 (fun (f:lident) e -> f.ident.idText, e) fs vs
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
    if ns = ["FStar"; "Pervasives"]
    then match n with
            | "tuple2" -> Some 2
            | "tuple3" -> Some 3
            | "tuple4" -> Some 4
            | "tuple5" -> Some 5
            | "tuple6" -> Some 6
            | "tuple7" -> Some 7
            | "tuple8" -> Some 8
            | _ -> None
    else None

let resugar_mlty t = match t with
    | MLTY_Named (args, mlp) ->
      begin match is_xtuple_ty mlp with
        | Some n -> MLTY_Tuple args
        | _ -> t
      end
    | _ -> t

let codegen_fsharp () = Option.get (Options.codegen()) = "FSharp"
let flatten_ns ns =
    if codegen_fsharp()
    then String.concat "." ns
    else String.concat "_" ns
let flatten_mlpath (ns, n) =
    if codegen_fsharp()
    then String.concat "." (ns@[n])
    else String.concat "_" (ns@[n])
let mlpath_of_lid (l:lident) = (l.ns |> List.map (fun i -> i.idText),  l.ident.idText)

let rec erasableType (unfold_ty:unfold_t) (t:mlty) :bool =
    //printfn "(* erasability of %A is %A *)\n" t (g.erasableTypes t);
   if UEnv.erasableTypeNoDelta t
   then true
   else match unfold_ty t with
     | Some t -> (erasableType unfold_ty t)
     | None  -> false

let rec eraseTypeDeep unfold_ty (t:mlty) : mlty =
    match t with
    | MLTY_Fun (tyd, etag, tycd) -> if etag=E_PURE then MLTY_Fun (eraseTypeDeep unfold_ty tyd, etag, eraseTypeDeep unfold_ty tycd) else t
    | MLTY_Named (lty, mlp) -> if erasableType unfold_ty t then UEnv.erasedContent else MLTY_Named (List.map (eraseTypeDeep unfold_ty) lty, mlp)  // only some named constants are erased to unit.
    | MLTY_Tuple lty ->  MLTY_Tuple (List.map (eraseTypeDeep unfold_ty) lty)
    | _ ->  t

let prims_op_equality = with_ty MLTY_Top <| MLE_Name (["Prims"], "op_Equality")
let prims_op_amp_amp  = with_ty (mk_ty_fun [(("x",0), ml_bool_ty); (("y",0), ml_bool_ty)] ml_bool_ty) <| MLE_Name (["Prims"], "op_AmpAmp")
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

let rec argTypes  (t: mlty) : list<mlty> =
    match t with
      | MLTY_Fun (a,_,b) -> a::(argTypes b)
      | _ -> []

let rec uncurry_mlty_fun t =
    match t with
    | MLTY_Fun (a,_,b) ->
        let args, res = uncurry_mlty_fun b in
        a::args, res
    | _ -> [], t
