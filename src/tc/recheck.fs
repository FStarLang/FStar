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

module FStar.Tc.Recheck

open FStar
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Util
open FStar.Absyn.Const
open FStar.Util
open FStar.Absyn.Util
open FStar.Const

let oktype = Some ktype
let t_unit   = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.unit_lid   ktype)
let t_bool   = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.bool_lid   ktype)
let t_uint8  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.uint8_lid  ktype)
let t_int    = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.int_lid    ktype)
let t_int32  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.int32_lid  ktype)
let t_int64  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.int64_lid  ktype)
let t_string = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.string_lid ktype)
let t_float  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.float_lid  ktype)
let t_char   = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.char_lid   ktype)

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
  | _ -> raise (Error("Unsupported constant", r))


let rec recompute_kind t =
    let recompute t = match t.n with
        | Typ_delayed _ -> recompute_kind (Util.compress_typ t)
        | Typ_btvar a -> a.sort
        | Typ_const tc -> 
          begin match tc.sort.n with 
            | Kind_unknown -> failwith (Util.format1 "UNKNOWN KIND FOR %s" (Print.typ_to_string t))
            | _ -> tc.sort
          end
        | Typ_fun _
        | Typ_refine _ -> ktype
        | Typ_ascribed (_, k)
        | Typ_uvar(_, k) -> k
        | Typ_meta(Meta_labeled _) 
        | Typ_meta(Meta_slack_formula _)
        | Typ_meta(Meta_pattern _) -> ktype
        | Typ_meta(Meta_named(t, _)) -> recompute_kind t
        | Typ_meta(Meta_refresh_label(t, _, _)) -> recompute_kind t
        | Typ_lam(binders, body) -> mk_Kind_arrow(binders, recompute_kind body) t.pos
        | Typ_app(t1, args) ->
          begin match t1.n with
            | Typ_const tc when (lid_equals tc.v Const.forall_lid
                                || lid_equals tc.v Const.exists_lid
                                || lid_equals tc.v Const.allTyp_lid
                                || lid_equals tc.v Const.exTyp_lid) -> ktype
            | _ ->
              let k1 = recompute_kind t1 in
              let bs, k = Util.kind_formals k1 in
              let rec aux subst bs args = match bs, args with
                | [], [] -> Util.subst_kind subst k
                | _, [] -> (mk_Kind_arrow(bs, k) t.pos) |> Util.subst_kind subst
                | b::bs, a::args ->
                    let subst = Util.subst_formal b a :: subst in
                    aux subst bs args
                | _ -> failwith (Util.format5 "(%s) HEAD KIND is %s\nToo many arguments in type %s; result kind is %s\nwith %s remaining args\n" 
                    (Range.string_of_range t.pos)
                    (Print.kind_to_string k1) (Print.tag_of_typ t) (Print.kind_to_string k) (List.length args |> string_of_int)) in
              aux [] bs args
           end
        | Typ_unknown -> kun in
    match !t.tk with
        | Some k -> k
        | None -> let k = recompute t in t.tk := Some k; k

let rec recompute_typ (e:exp) : typ =
    let recompute e = match e.n with
        | Exp_delayed _ -> recompute_typ (Util.compress_exp e)
        | Exp_bvar x -> x.sort
        | Exp_fvar (f, _) -> f.sort
        | Exp_constant s -> typing_const e.pos s
        | Exp_abs(bs, body) -> mk_Typ_fun(bs, mk_Total (recompute_typ body)) None e.pos
        | Exp_app(head, args) ->
            let t1 = recompute_typ head in
            begin match Util.function_formals t1 with
                | None -> tun
                | Some (bs, c) ->
                  let rec aux subst bs args = match bs, args with
                    | [], [] -> Util.subst_typ subst (Util.comp_result c)
                    | _, [] -> (mk_Typ_fun(bs, c) None e.pos) |> Util.subst_typ subst
                    | b::bs, a::args ->
                        let subst = Util.subst_formal b a :: subst in
                        aux subst bs args
                    | _ -> failwith "Too many arguments" in
                  aux [] bs args
            end

       | Exp_match _ -> failwith "Expect match nodes to be annotated already"
       | Exp_ascribed(_, t, _) -> t
       | Exp_let(_, e) -> recompute_typ e
       | Exp_uvar(_, t) -> t
       | Exp_meta(Meta_desugared(e, _)) -> recompute_typ e in

    match !e.tk with
        | Some t -> t
        | None -> let t = recompute e in e.tk := Some t; t

