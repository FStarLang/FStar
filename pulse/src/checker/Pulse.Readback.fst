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

module Pulse.Readback
module R = FStar.Reflection.V2
open Pulse.Syntax.Base
open Pulse.Reflection.Util
open Pulse.Common
module RU = Pulse.RuntimeUtils
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
module L = FStar.List.Tot.Base
let debug_log (f: unit -> T.Tac unit) : T.Tac unit = if RU.debug_at_level_no_module "readback" then f()

let readback_observability (t:R.term)
: option (obs:observability { elab_observability obs == t })
= let open R in
  match inspect_ln t with
  | R.Tv_FVar fv ->
    let fv_lid = inspect_fv fv in
    if fv_lid = observable_lid
    then Some Observable
    else if fv_lid = neutral_lid
    then Some Neutral
    else None
  | _ -> None

#push-options "--z3rlimit_factor 20"
// TODO: FIXME: may be mark as opaque_to_smt
let try_readback_st_comp (t:R.term)
  : option (c:comp{elab_comp c == t}) =

  let open R in
  let hd, args = collect_app_ln t in
  match inspect_ln hd with
  | Tv_UInst fv [u] ->
    let fv_lid = inspect_fv fv in
    if fv_lid = stt_lid
    then match args with
         | [res; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs; sort=sort } =
                  inspect_binder b
              in    
              assume (fv == stt_fv);
              assume (aq == Q_Explicit           /\
                      attrs == []                /\
                      sort == fst res /\
                      snd res == Q_Explicit      /\
                      snd pre == Q_Explicit      /\
                      snd post == Q_Explicit);

              assume (t == mk_stt_comp u (fst res) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let res' = fst res in
              let pre' = fst pre in
              let post' = body in
              let c = C_ST {u; res=res'; pre=pre';post=post'} in
              Some (c <: c:Pulse.Syntax.Base.comp{ elab_comp c == t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_atomic_lid
    then match args with
         | [res; obs; opened; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs }
                  = inspect_binder b
              in    
              let res' = fst res in
              let? obs' = readback_observability (fst obs) in
              let opened' = fst opened in
              let pre' = fst pre in
              let post' = body in
              assume (t == mk_stt_atomic_comp (fst obs) u (fst res) (fst opened) (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let c = C_STAtomic opened' obs' ({u; res=res'; pre=pre';post=post'}) in
              Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
            | _ -> None)
         | _ -> None
    else if fv_lid = stt_ghost_lid
    then match args with
         | [res; inames; pre; post] ->
           (match inspect_ln (fst post) with
            | Tv_Abs b body ->
              let { qual=aq; attrs=attrs }
                  = inspect_binder b
              in    
              let res' = fst res in
              let inames' = fst inames in
              let pre' = fst pre in
              let post' = body in
              assume (t == mk_stt_ghost_comp u (fst res) inames' (fst pre) (mk_abs (fst res) R.Q_Explicit body));
              let c = C_STGhost inames' ({u; res=res'; pre=pre';post=post'}) in
              Some (c <: c:Pulse.Syntax.Base.comp { elab_comp c == t })
            | _ -> None)
         | _ -> None    
    else None  
  | _ -> None
#pop-options

let readback_comp (t:R.term)
  : option (c:comp { elab_comp c == t }) =

  let ropt = try_readback_st_comp t in
  match ropt with
  | Some c ->
    // debug_log (fun _ -> T.print (Printf.sprintf "readback_comp: %s as\n%s\n" (T.term_to_string t) (P.comp_to_string c)));
    ropt
  | _ ->
    let t' = t in
    Some (C_Tot t' <: c:comp{ elab_comp c == t })

let rec readback_pat (p : R.pattern) : option pattern =
  match p with
  | R.Pat_Cons fv _ args ->
    let fv = R.inspect_fv fv in
    let? args = map_opt_dec p readback_sub_pat args in
    Some (Pat_Cons {fv_name=fv; fv_range=Range.range_0} args)
  | R.Pat_Constant c ->
    Some (Pat_Constant c)
  | R.Pat_Var st nm ->
    Some (Pat_Var nm (RU.map_seal st RU.deep_compress))
  | R.Pat_Dot_Term None -> Some (Pat_Dot_Term None)
  | R.Pat_Dot_Term (Some t) ->
    if R.Tv_Unknown? (R.inspect_ln t)
    then None
    else
      let t = RU.deep_compress t in
      let t = RU.set_range t Range.range_0 in
      Some (Pat_Dot_Term (Some t))
  | _ -> None
and readback_sub_pat (pb : R.pattern & bool) : option (pattern & bool) =
  let (p, b) = pb in
  let? p = readback_pat p in
  Some (p, b)

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 2"
#restart-solver
let rec elab_readback_pat_x (rp : R.pattern) (p : pattern)
  : Lemma (requires readback_pat rp == Some p)
          (ensures elab_pat p == rp)
  = match rp, p with
  | R.Pat_Cons r_fv r_us_opt r_subpats, Pat_Cons {fv_name=fv_name} subpats ->
    assert (fv_name == R.inspect_fv r_fv);
    assert (Some? (readback_pat rp));
    let fv = R.inspect_fv r_fv in

    assert (readback_pat rp ==
             (let? args = map_opt_dec rp readback_sub_pat r_subpats in
              Some (Pat_Cons {fv_name=fv; fv_range=Range.range_0} args)))
        by (T.norm [delta; zeta]);

    let aux1 (i:nat{i < L.length r_subpats})
    : Lemma (r_subpats `L.index` i == (map_dec p subpats elab_sub_pat) `L.index` i)
    =
      lemma_map_opt_dec_index rp readback_sub_pat r_subpats subpats;
      calc (==) {
        map_dec p subpats elab_sub_pat `L.index` i;
        == { lemma_map_dec_index_i p elab_sub_pat subpats i }
        elab_sub_pat (subpats `L.index` i);
        == { () }
        elab_sub_pat (Some?.v (readback_sub_pat (r_subpats `L.index` i)));
        == { elab_readback_subpat (r_subpats `L.index` i) }
        r_subpats `L.index` i;
      }
    in
    Classical.forall_intro aux1;
    FStar.List.Tot.Properties.index_extensionality
        (map_dec p subpats elab_sub_pat)
        r_subpats;

    assert (elab_pat p ==
             R.Pat_Cons (R.pack_fv fv_name) None (map_dec p subpats elab_sub_pat))
        by (T.norm [delta; zeta]);

    assert (R.pack_fv fv_name == r_fv);
    // FIXME: readback will drop the universe annotation, so we cannot
    // really prove this. Should we add it to pulse pattern syntax?
    assume (r_us_opt == None);
    assert (r_subpats == map_dec p subpats elab_sub_pat);
    ()

  | R.Pat_Constant _, Pat_Constant _ -> ()
  | R.Pat_Var st nm, Pat_Var _ _ ->
    Sealed.sealed_singl st (Sealed.seal RT.tun);
    ()
  | _ -> ()
and elab_readback_subpat (pb : R.pattern & bool)
  : Lemma (requires (Some? (readback_sub_pat pb)))
          (ensures elab_sub_pat (Some?.v (readback_sub_pat pb)) == pb)
  = let (p, b) = pb in
    elab_readback_pat_x p (Some?.v (readback_pat p))
#pop-options
