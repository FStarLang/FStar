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
module Microsoft.FStar.Backends.ML.Util
open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Backends.ML.Syntax

let pruneNones (l : list<option<'a>>) : list<'a> =
    List.fold_right (fun  x ll -> match x with 
                          | Some xs -> xs::ll
                          | None -> ll) l []


let mlconst_of_const (sctt : sconst) =
  match sctt with
  | Const_unit         -> MLC_Unit
  | Const_char   c     -> MLC_Char  c
  | Const_uint8  c     -> MLC_Byte  c
  | Const_int    c     -> MLC_Int32 (Util.int32_of_int (Util.int_of_string c))
  | Const_int32  i     -> MLC_Int32 i
  | Const_int64  i     -> MLC_Int64 i
  | Const_bool   b     -> MLC_Bool  b
  | Const_float  d     -> MLC_Float d

  | Const_bytearray (bytes, _) ->
      MLC_Bytes bytes

  | Const_string (bytes, _) ->
      MLC_String (string_of_unicode (bytes))

let rec subst_aux (subst:list<(mlident * mlty)>) (t:mlty) = 
    match t with 
    | MLTY_Var  x -> Util.find_opt (fun (y, _) -> y=x) subst |> must |> snd
    | MLTY_Fun (t1, f, t2) -> MLTY_Fun(subst_aux subst t1, f, subst_aux subst t2)
    | MLTY_Named(args, path) -> MLTY_Named(List.map (subst_aux subst) args, path)
    | MLTY_Tuple ts -> MLTY_Tuple(List.map (subst_aux subst) ts)
    | MLTY_App(t1, t2) -> MLTY_App(subst_aux subst t1, subst_aux subst t2)
    | MLTY_Top -> MLTY_Top

let subst ((formals, t):mltyscheme) (args:list<mlty>) : mlty = 
    if List.length formals <> List.length args
    then failwith "Substitution must be fully applied"
    else subst_aux (List.zip formals args) t

let delta_unfold g t = None //TODO

let rec equiv (g:Env.env) (t:mlty) (t':mlty) : bool = 
    match t, t' with 
    | MLTY_Var  x, MLTY_Var y -> 
      fst x = fst y

    | MLTY_Fun (t1, f, t2), MLTY_Fun (t1', f', t2') ->
      equiv g t1 t1' 
      //&& f=f' NS: removing this for now, until effects are properly translated
      && equiv g t2 t2'

    | MLTY_Named(args, path), MLTY_Named(args', path') when (path=path') -> 
      List.forall2 (equiv g) args args'

    | MLTY_Tuple ts, MLTY_Tuple ts' -> 
      List.forall2 (equiv g) ts ts'

    | MLTY_Top, MLTY_Top -> true

    | MLTY_Named _, _ -> 
      begin match delta_unfold g t with 
        | Some t -> equiv g t t'
        | _ -> false
      end

    | _, MLTY_Named _ -> 
      begin match delta_unfold g t' with 
        | Some t -> equiv g t t'
        | _ -> false
      end
      
    | _ -> false

let unit_binder = 
    let x = Util.gen_bvar Tc.Recheck.t_unit in
    v_binder x

let is_type_abstraction = function 
    | (Inl _, _)::_ -> true
    | _ -> false

let tbinder_prefix t = match (Util.compress_typ t).n with 
    | Typ_fun(bs, c) ->
      begin match Util.prefix_until (function (Inr _, _) -> true | _ -> false) bs with 
        | None -> bs
        | Some (bs, b, rest) -> bs
      end

    | _ -> []