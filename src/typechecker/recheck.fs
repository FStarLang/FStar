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
#light "off"

module FStar.TypeChecker.Recheck

open FStar
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Util
open FStar.Range
open FStar.Ident
open FStar.Const
open FStar.TypeChecker.Env

module U = FStar.Syntax.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module C = FStar.Syntax.Const

let tconst l = mk (Tm_fvar(lid_as_fv (set_lid_range l Range.dummyRange) None)) (Some Util.ktype0.n) Range.dummyRange
let t_unit   = tconst C.unit_lid
let t_bool   = tconst C.bool_lid 
let t_uint8  = tconst C.uint8_lid 
let t_int    = tconst C.int_lid   
let t_int32  = tconst C.int32_lid 
let t_int64  = tconst C.int64_lid 
let t_string = tconst C.string_lid
let t_float  = tconst C.float_lid 
let t_char   = tconst C.char_lid  

let typing_const r (s:sconst) = match s with
  | Const_unit -> t_unit
  | Const_bool _ -> t_bool
  | Const_int _ -> t_int
  | Const_int32 _ -> t_int32
  | Const_int64 _ -> t_int64
  | Const_string _ -> t_string
  | Const_float _ -> t_float
  | Const_char _ -> t_char
  | Const_uint8 _ -> t_uint8
  | Const_effect -> Util.ktype0 //NS: really?
  | _ -> raise (Error("Unsupported constant", r))

  //TODO: REMOVE THIS
//this is only supposed return a type that faithfully captures the arity of the term
let rec check t =
    let recompute t = match t.n with
        | Tm_delayed _ -> check (SS.compress t)
        | Tm_bvar a
        | Tm_name a -> a.sort
        | Tm_fvar (fv, _) -> fv.ty
        | Tm_uinst(t, us) -> check t //inaccurate
        | Tm_type u -> mk (Tm_type (U_succ u)) None t.pos
        | Tm_constant s -> typing_const t.pos s
        | Tm_arrow _  -> ktype0 //??
        | Tm_refine _ -> ktype0 
        | Tm_ascribed (_, k, _) 
        | Tm_uvar(_, k) -> k
        | Tm_meta(t, _) -> check t
        | Tm_let(_, e) -> check e 
        | Tm_abs(binders, body, _) -> arrow binders (mk_Total (check body)) //total?
        | Tm_app _   -> failwith (Util.format1 "Refusing to recheck app node: %s" (Print.term_to_string t))
        | Tm_match _ -> failwith "Expect match nodes to be annotated already"
        | Tm_unknown -> t in
    match !t.tk with
        | Some k -> mk k None t.pos
        | None -> let k = recompute t in t.tk := Some k.n; k
