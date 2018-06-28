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
open FStar
open FStar.Ident
open FStar.Extraction.ML.Syntax
module S = FStar.Syntax.Syntax
module BU = FStar.Util

val codegen_fsharp : unit -> bool
val pruneNones : list<(option<'a>)> -> list<'a>
val mk_range_mle : mlexpr
val mlconst_of_const : p:Range.range -> c:Const.sconst -> mlconstant
val mlexpr_of_const : p:Range.range -> c:Const.sconst -> mlexpr'
val mlexpr_of_range : r:Range.range -> mlexpr'
val subst : mlidents * mlty -> args:list<mlty> -> mlty
val udelta_unfold : g:UEnv.env -> _arg1:mlty -> option<mlty>
val eff_leq : f:e_tag -> f':e_tag -> bool
val eff_to_string : _arg1:e_tag -> string
val join : r:Range.range -> f:e_tag -> f':e_tag -> e_tag
val join_l : r:Range.range -> fs:Prims.list<e_tag> -> e_tag
val mk_ty_fun : (Prims.list<(mlident * mlty)> -> mlty -> mlty)
type unfold_t = mlty -> option<mlty>
val type_leq_c : unfold_ty:unfold_t -> e:option<mlexpr> -> t:mlty -> t':mlty -> bool * option<mlexpr>
val type_leq : g:unfold_t -> t1:mlty -> t2:mlty -> bool
val is_type_abstraction : list<(BU.either<'a,'b> * 'c)> -> bool
val is_xtuple : list<string> * string -> option<int>
val is_xtuple_ty : list<string> * string -> option<int>
val resugar_exp : e:mlexpr -> mlexpr
val resugar_mlty : t:mlty -> mlty
val record_field_path : list<lident> -> list<string>
val record_fields : fs:list<lident> -> vs:list<'a> -> list<(string * 'a)>

val flatten_ns : ns:list<string> -> string
val flatten_mlpath : ns:list<string> * n:string -> string
val mlpath_of_lid : l:lident -> list<string> * string
val erasableType : unfold_ty:unfold_t -> t:mlty -> bool
val eraseTypeDeep : unfold_ty:unfold_t -> t:mlty -> mlty
val prims_op_equality : mlexpr
val prims_op_amp_amp : mlexpr
val conjoin : e1:mlexpr -> e2:mlexpr -> mlexpr
val conjoin_opt : e1:option<mlexpr> -> e2:option<mlexpr> -> option<mlexpr>
val mlloc_of_range : r:Range.range -> int * string
val doms_and_cod : t:mlty -> list<mlty> * mlty
val argTypes : t:mlty -> list<mlty>
val uncurry_mlty_fun : t:mlty -> list<mlty> * mlty

val interpret_plugin_as_term_fun :
               TypeChecker.Env.env
            -> fv:S.fv
            -> t:S.typ
            -> ml_fv:mlexpr'
            -> option<(mlexpr * int * bool)>