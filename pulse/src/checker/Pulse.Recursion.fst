(*
   Copyright 2023 Microsoft Research

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

module Pulse.Recursion

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
open FStar.Tactics.V2
module RU = Pulse.RuntimeUtils

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.PP
module P = Pulse.Syntax.Printer

let rec splitlast #a (l : list a { Cons? l }) :
    res:(list a & a) { List.length (fst res) == List.length l - 1 } =
  match l with
  | [x] -> [], x
  | x::xs ->
    let init, last = splitlast xs in
    x::init, last

let rec map2 #a #b #c (f : a -> b -> Tac c) (xs : list a) (ys : list b { List.length xs == List.length ys }) : Tac (list c) =
  match xs, ys with
  | [], [] -> []
  | x::xx, y::yy -> f x y :: map2 f xx yy

let debug_main g (s: unit -> Tac string) : Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.main"
  then print (s ())
  else ()

let string_as_term (s:string) : R.term =
  R.pack_ln (R.Tv_Const (C_String s))

let freshen_binder (g: env) (b:T.binder) : Tac T.binder =
  { b with uniq = fresh g
         ; ppname = map_seal b.ppname (fun s -> s ^ "'") }

let subst_binder_typ (s : FStar.Stubs.Syntax.Syntax.subst_t) (b : Tactics.NamedView.binder) : Tactics.NamedView.binder =
  { b with sort = FStar.Stubs.Reflection.V2.Builtins.subst_term s b.sort }

let rec freshen_binders (g: env) (bs:binders) :
    Tac (res: binders { List.length res == List.length bs }) =
  match bs with
  | [] -> []
  | b::bs ->
    let b' = freshen_binder g b in
    let bs = map (subst_binder_typ [Stubs.Syntax.Syntax.NT (binder_to_namedv b |> FStar.Stubs.Reflection.V2.Builtins.pack_namedv)
                                                           (binder_to_term b')]) bs in
    b' :: freshen_binders g bs

let elab_b (qbv : option qualifier & binder & bv) : Tot Tactics.NamedView.binder =
  let q, b, bv = qbv in
  {
    uniq = bv.bv_index;
    ppname = b.binder_ppname.name;
    sort = b.binder_ty;
    qual = elab_qual q;
    attrs = [];
  }

let inspect_tot_arrow (ty: term) : option (binder_view & term) =
  match R.inspect_ln ty with
  | R.Tv_Arrow bv c ->
    (match R.inspect_comp c with
    | C_Total t -> Some (R.inspect_binder bv, t)
    | _ -> None)
  | _ -> None

let rec recover_bs (g: env) (qbs: list (option qualifier & binder & bv)) (ty: term) (r: range) :
    Tac (res:(list (option qualifier & binder & bv) & term) { List.length (fst res) >= List.length qbs }) =
  debug_main g
    (fun _ -> Printf.sprintf "recover_bs: qbs = %s, ty = %s\n"
              (string_of_list (fun (_, b,_) -> P.binder_to_string b) qbs)
              (Pulse.Show.show ty));
  match qbs, inspect_tot_arrow ty with
  | [], Some (bv, c) ->
    let { attrs; sort; qual; ppname } = (bv <: R.binder_view) in
    let x = fresh g in
    let px = ({ name = ppname; range = r } <: Pulse.Syntax.Base.ppname), x in
    let env = Pulse.Typing.Env.push_binding g x (fst px) sort in
    let c = open_term_nv c px in
    let bs, c = recover_bs g [] c r in
    let qual =
      match qual with
      | Q_Implicit -> Some Implicit
      | Q_Explicit | Q_Equality -> None
      | Q_Meta t -> Some (Meta t) in
    (qual, { binder_ty = sort; binder_ppname = fst px; binder_attrs = T.seal attrs }, { bv_index = x; bv_ppname = fst px }) :: bs, c
  | qb::qbs, Some (_, c) ->
    let q, b, qbv = qb in
    let bs, c = recover_bs g qbs (open_term' c
      (R.pack_ln (R.Tv_Var (R.pack_namedv { uniq = qbv.bv_index; sort = T.seal b.binder_ty; ppname = b.binder_ppname.name }))) 0) r in
    qb::bs, c
  | qb::qbs, _ ->
    fail_doc g (Some r) [text "main: FnDefn: expected inferred type to be an arrow"; pp ty]
  | [], _ ->
    [], ty

#push-options "--fuel 2 --ifuel 0 --z3rlimit_factor 2"
let add_knot (g : env) (rng : R.range)
             (d : decl{FnDefn? d.d})
: Tac (d : decl{FnDefn? d.d})
= let FnDefn { id; isrec; us; bs; comp; meas; body } = d.d in
  allow_invert bs;
  if List.length bs < 2 then fail g (Some d.range) "main: FnDefn does not have binders";
  (* NB: bs, comp, body are open *)
  debug_main g
    (fun _ -> Printf.sprintf "add_knot: bs = %s\n"
              (string_of_list (fun (_, b,_) -> P.binder_to_string b) bs));

  (* for
       fn rec f (x1:t1) ... (xn:tn) :
         requires pre
         returns x:a
         ensures post

    we elab into

       let  f (x1:t1) ... (xn:tn)
              (f : (x1':t1) -> ... -> (xn':tn) -> stt a pre post)
              : stt a pre post

    without any sort of termination check. Now, for

       ghost fn rec f (x1:t1) ... (xn:tn) :
         requires pre
         returns x:a
         ensures post
         measure meas

    we must elab into

       let  f (x1:t1) ... (xn:tn)
              (f : (x1':t1) -> ... -> (xn':tn){meas' << meas} -> stt a pre post)
              : stt a pre post

    so we need to add the measure refinement. Since `meas` is an
    open term (wrt x1...xn), we must substitute it to create meas',
    subtituting x1' for x1, ..., xn' for xn

  *)
  (* Desugaring added a recursive knot argument at the end *)
  let bs, b_knot = splitlast bs in
  let dummy_body = { body with term = Tm_Unreachable {c = C_Tot tm_unknown} } in
  let d_typ, _ = Pulse.Checker.Abs.arrow_of_abs g (Pulse.Checker.Abs.mk_abs g bs dummy_body comp) in
  let bs, comp = recover_bs g bs d_typ d.range in
  (* freshen *)
  let r_bs0 = List.Tot.map elab_b bs in
  let r_bs = freshen_binders g r_bs0 in
  let binder_to_r_namedv (b:T.binder) : R.namedv =
    R.pack_namedv {
      uniq = b.uniq;
      sort = seal b.sort;
      ppname = b.ppname;
    }
  in
  let prime_subst = map2 (fun (b1 b2 : T.binder) ->
                      R.NT (binder_to_r_namedv b1)
                            (binder_to_term b2)) r_bs0 r_bs in
  let r_bs =
    (* If ghost/atomic, we need to add a decreases refinement on the last arg *)
    match readback_comp comp with
    | Some (C_STAtomic ..) | Some (C_STGhost ..) ->
      if None? meas then (
        let open FStar.Pprint in
        let open Pulse.PP in
        fail_doc g (Some d.range) [
          text "'ghost' and 'atomic' recursive functions require a 'decreases' clause"]
      );
      let init, last = splitlast r_bs in
      let last : FStar.Tactics.NamedView.binder = last in
      let last =
        (* add a refinement to last *)
        let b' : simple_binder = {
          uniq = last.uniq;
          ppname = last.ppname;
          sort = last.sort;
          qual = Q_Explicit;
          attrs = [];
        }
        in
        let meas = Some?.v meas in
        let meas' = R.subst_term prime_subst meas in
        let ref = `(`#meas' << `#meas) in
        (* TODO: this is not always printed *)
        let ref = (`labeled range_0 "Could not prove termination" (`#ref)) in
        { last with
            sort = (pack (Tv_Refine b' ref))
        }
      in
      init @ [last]
    | Some (C_ST _) ->
      r_bs
    | _ ->
      fail_doc g (Some d.range) [text "main: FnDefn has unexpected type"; pp comp]
  in
  let r_res = R.subst_term prime_subst comp in
  let r_ty = FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr r_bs r_res in
  // let open FStar.Pprint in
  // let open Pulse.PP in
  // warn_doc g (Some d.range) [
  //   text "r_ty (type of the knot binder) =" ^/^ pp r_ty
  // ];
  if R.Tv_Unknown? (inspect_ln r_ty) then
    fail g (Some d.range) "error: r_ty is Tv_unknown in add_knot?";
  let b_knot =
    let s, rng = inspect_ident id in
    let b = mk_binder s rng (wr r_ty rng) in
    let bv = {
      bv_index = b_knot._3.bv_index;
      bv_ppname = { name = seal s; range = rng }
    } in
    let q = None in
    (q, b, bv)
  in
  let id' =
    let s, rng = inspect_ident id in
    pack_ident ("__recaux_" ^ s, rng)
  in
  let bs' = bs @ [b_knot] in

  { d with d =
    FnDefn { id=id'; isrec=false; us; bs=bs'; comp = C_Tot comp; meas=None; body }
  }
#pop-options
#push-options "--fuel 0 --ifuel 0"
let tie_knot (g : env)
             (rng : R.range)
             (nm_orig nm_aux : string)
             (r_typ : R.typ) (blob:RT.blob)
: Tac (r:(bool & sigelt & option RT.blob) { let (checked, _, _) = r in ~ checked })
=
  let knot_r_typ =
    (* Remove the last arguments from r_typ, as that is the recursive knot.
    After doing that, we now have the needed type for elaboration. *)
    let bs, c = collect_arr_bs r_typ in
    if not (Cons? bs) then fail g (Some rng) "tie_knot: impossible (1)";
    let bs = init bs in
    if not (Cons? bs) then fail g (Some rng) "tie_knot: impossible (2)";
    mk_arr bs c
  in
  (* This is a temporary implementation. It will just create
  a new letbinding at the appropriate type with a `RU.magic()` body. *)
  let flag, sig, _ = RT.mk_unchecked_let (fstar_env g) (T.cur_module ()) nm_orig (`(magic())) knot_r_typ in
  let nm = string_as_term nm_aux in 
  let sig = RU.add_attribute sig (`("pulse.recursive.knot", `#(nm))) in
  flag, sig, Some blob
#pop-options