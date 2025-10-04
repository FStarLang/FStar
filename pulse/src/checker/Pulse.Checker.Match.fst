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

module Pulse.Checker.Match

open Pulse.Common
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module L = FStar.List.Tot.Base
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils

noeq
type br_typing_vis : env -> universe -> typ -> term -> pattern -> st_term -> comp_st -> Type =
  | TBRV :
      g:env ->
      sc_u : universe ->
      sc_ty : typ ->
      sc:term ->
      c:comp_st ->
      p:pattern ->
      e:st_term ->
      bs:(list R.binding){RT.bindings_ok_for_pat (fstar_env g) bs (elab_pat p)} ->
      _ : squash (all_fresh g (L.map readback_binding bs)) ->
      _ : squash (Some? (RT.elaborate_pat (elab_pat p) bs)) ->
      _ : squash (~(R.Tv_Unknown? (R.inspect_ln (fst (Some?.v (RT.elaborate_pat (elab_pat p) bs)))))) -> // should be provable from defn of elaborate_pat
      hyp:var {freshv (push_bindings g (L.map readback_binding bs)) hyp} ->
      st_typing (
         push_binding (push_bindings g (L.map readback_binding bs))
              hyp
              ({name=Sealed.seal "branch equality"; range=FStar.Range.range_0})
              (mk_sq_eq2 sc_u sc_ty sc (wr (fst (Some?.v (RT.elaborate_pat (elab_pat p) bs))) Range.range_0))
         ) e c ->
      br_typing_vis g sc_u sc_ty sc p (close_st_term_n e (L.map fst (L.map readback_binding bs))) c

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
      let t = wr t Range.range_0 in
      Some (Pat_Dot_Term (Some t))

  | _ -> None

and readback_sub_pat (pb : R.pattern & bool) : option (pattern & bool) =
  let (p, b) = pb in
  let? p = readback_pat p in
  Some (p, b)

let rec lemma_map_len (f : 'a -> 'b) (xs : list 'a)
  : Lemma (L.length (L.map f xs) == L.length xs)
          [SMTPat (L.length (L.map f xs))]
  = match xs with
    | [] -> ()
    | x::xs -> lemma_map_len f xs

let rec lemma_map_index (f : 'a -> 'b) (xs : list 'a) (i : nat{i < L.length xs})
  : Lemma (L.map f xs `L.index` i == f (xs `L.index` i))
  = match i, xs with
    | 0, _ -> ()
    | _, x::xs -> lemma_map_index f xs (i-1)

let rec __lemma_map_opt_lenx (f : 'a -> option 'b) (xs : list 'a) (ys : list 'b)
  : Lemma (requires map_opt f xs == Some ys)
          (ensures L.length xs == L.length ys)
  = match xs, ys with
    | [], [] -> ()
    | x::xs, y::ys ->
      __lemma_map_opt_lenx f xs ys
    | _ -> assert False

let lemma_map_opt_lenx (f : 'a -> option 'b) (xs : list 'a)
  : Lemma (requires Some? (map_opt f xs))
          (ensures L.length xs == L.length (Some?.v (map_opt f xs)))
          [SMTPat (map_opt f xs)]
  = let Some ys = map_opt f xs in
    __lemma_map_opt_lenx f xs ys

let rec __lemma_map_opt_dec_lenx (top:'z) (f : (x:'a{x << top}) -> option 'b) (xs : list 'a{xs << top}) (ys : list 'b)
  : Lemma (requires map_opt_dec top f xs == Some ys)
          (ensures L.length xs == L.length ys)
  = match xs, ys with
    | [], [] -> ()
    | x::xs, y::ys ->
      __lemma_map_opt_dec_lenx top f xs ys
    | _ -> assert False

let lemma_map_opt_dec_lenx (top:'z) (f : (x:'a{x << top}) -> option 'b) (xs : list 'a{xs << top})
  : Lemma (requires Some? (map_opt_dec top f xs))
          (ensures L.length xs == L.length (Some?.v (map_opt_dec top f xs)))
          [SMTPat (map_opt_dec top f xs)]
  = let Some ys = map_opt_dec top f xs in
    __lemma_map_opt_dec_lenx top f xs ys

let rec __lemma_map_opt_dec_index (top:'z) (f : (x:'a{x << top}) -> option 'b) (xs : list 'a{xs << top}) (ys : list 'b) (i:nat{i < L.length xs})
  : Lemma (requires map_opt_dec top f xs == Some ys)
          (ensures f (xs `L.index` i) == Some (ys `L.index` i))
  = match xs, ys, i with
    | _, _, 0 -> ()
    | x::xs, y::ys, _ ->
     __lemma_map_opt_dec_index top f xs ys (i-1)

let lemma_map_opt_dec_index (top:'z) (f : (x:'a{x << top}) -> option 'b) (xs : list 'a{xs << top}) (ys : list 'b)
  : Lemma (requires map_opt_dec top f xs == Some ys)
          (ensures forall i. f (xs `L.index` i) == Some (ys `L.index` i))
  = Classical.forall_intro (Classical.move_requires (__lemma_map_opt_dec_index top f xs ys))

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 2 --query_stats"
#restart-solver
let rec elab_readback_pat_x (rp : R.pattern) (p : pattern)
  : Lemma (requires readback_pat rp == Some p)
          (ensures elab_pat p == rp)
  = match rp, p with
  | R.Pat_Cons r_fv r_us_opt r_subpats, Pat_Cons {fv_name=fv_name} subpats ->
    assert (fv_name == R.inspect_fv r_fv);
    assert (Some? (readback_pat rp));
    let fv = R.inspect_fv r_fv in
    
    // Unfold to definition, unsure why it's needed
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

    // Unfold to definition, unsure why it's needed
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

val tot_typing_weakening_n
   (#g:env) (#t:term) (#ty:term)
   (bs:list binding{all_fresh g bs})
   (d:tot_typing g t ty)
   : Tot (tot_typing (push_bindings g bs) t ty)
         (decreases bs)
let rec tot_typing_weakening_n bs d =
  match bs with
  | [] -> d
  | (x,t)::bs ->
    let d = Pulse.Typing.Metatheory.tot_typing_weakening_single d x t in
    tot_typing_weakening_n bs d

let patof (b:branch) : pattern = b.pat
let samepat (b1 b2 : branch) : prop = b1.pat == b2.pat
let samepats (bs1 bs2 : list branch) : prop =
  L.map patof bs1 == L.map patof bs2

let open_st_term_bs (t:st_term) (bs:list binding) : st_term =
  let rec aux (bs:list binding) (i:nat) : subst =
    match bs with
    | [] -> []
    | b::bs ->
      (RT.DT i (Pulse.Syntax.Pure.term_of_nvar (ppname_default, fst b))) :: aux bs (i+1)
  in
  let ss = aux (List.rev bs) 0 in
  subst_st_term t ss

let rec r_bindings_to_string (bs : list R.binding) : T.Tac string =
  match bs with
  | [] -> ""
  | b::bs ->
    (T.unseal b.ppname ^ "-" ^ string_of_int b.uniq ^ ":" ^ T.term_to_string b.sort ^ " ") ^ r_bindings_to_string bs

let rec bindings_to_string (bs : list binding) : T.Tac string =
  match bs with
  | [] -> ""
  | b::bs ->
    (string_of_int (fst b) ^ ":" ^ Pulse.Syntax.Printer.term_to_string (snd b) ^ " ") ^ bindings_to_string bs

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
#restart-solver
let check_branch
        (norw:bool)
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_slprop)
        (post_hint:post_hint_for_env g)
        (check:check_t)
        (sc_u : universe)
        (sc_ty:typ)
        (sc:term)
        (p0:R.pattern)
        (e:st_term)
        (bs:list R.binding)
  : T.Tac (p:pattern{elab_pat p == p0}
          & e:st_term
          & c:comp_st{comp_pre c == pre /\ comp_post_matches_hint c (PostHint post_hint)}
          & br_typing_vis g sc_u sc_ty sc p e c)
  =
  let p = (match readback_pat p0 with | Some p -> p | None ->
    fail g (Some e.range) "readback_pat failed")
  in
  elab_readback_pat_x p0 p;
  let pulse_bs = L.map readback_binding bs in
  assume (all_fresh g pulse_bs); (* The reflection API in F* should give us a way to guarantee this, but currently does not *)
  assume (RT.bindings_ok_for_pat (fstar_env g) bs p0);
  let g' = push_bindings g pulse_bs in
  let hyp_var = fresh g' in
  let elab_p = RT.elaborate_pat p0 bs in
  if not (Some? elab_p) then
    fail g (Some e.range) "Failed to elab pattern into term";
  if (R.Tv_Unknown? (R.inspect_ln (fst (Some?.v elab_p)))) then
    fail g (Some e.range) "should not happen: pattern elaborated to Tv_Unknown";
  if Cons? (snd (Some?.v elab_p)) then
    fail g (Some e.range) "should not happen: pattern elaboration missed some binders";
  // T.print ("Elaborated pattern = " ^ Pulse.Show.show (fst (Some?.v elab_p)));
  let elab_p_tm = fst (Some?.v elab_p) in
  let eq_typ = mk_sq_eq2 sc_u sc_ty sc elab_p_tm in
  let g' = push_binding g' hyp_var ({name = Sealed.seal "branch equality"; range = Range.range_0 }) eq_typ in
  let e = open_st_term_bs e pulse_bs in
  let e =
    if norw
    then e
    else
      let t =
        mk_term (Tm_ProofHintWithBinders {
                   binders = [];
                   hint_type = RENAME { pairs = [(sc, elab_p_tm)];
                                        goal = None;
                                        tac_opt = Some Pulse.Reflection.Util.match_rewrite_tac_tm;
                                        elaborated = true };
                   t = e; })
                e.range
      in
      { t with effect_tag = e.effect_tag }
  in
  let pre_typing = tot_typing_weakening_n pulse_bs pre_typing in // weaken w/ binders
  let pre_typing = Pulse.Typing.Metatheory.tot_typing_weakening_single pre_typing hyp_var eq_typ in // weaken w/ branch eq

  let (| e, c, e_d |) =
    let ppname = mk_ppname_no_range "_br" in
    let r = check g' pre pre_typing (PostHint post_hint) ppname e in
    apply_checker_result_k r ppname in
  let br_d : br_typing_vis g sc_u sc_ty sc p (close_st_term_n e (L.map fst pulse_bs)) c = TBRV g sc_u sc_ty sc c p e bs () () () hyp_var e_d in
  (| p, close_st_term_n e (L.map fst pulse_bs), c, br_d |)

#pop-options

let check_branches_aux_t 
        (#g:env)
        (pre:term)
        (post_hint:post_hint_for_env g)
        (sc_u : universe)
        (sc_ty : typ)
        (sc : term)
= (br:branch
   & c:comp_st{comp_pre c == pre /\ comp_post_matches_hint c (PostHint post_hint)}
   & br_typing_vis g sc_u sc_ty sc br.pat br.e c)

let check_branches_aux
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_slprop)
        (post_hint:post_hint_for_env g)
        (check:check_t)
        (sc_u : universe)
        (sc_ty : typ)
        (sc : term)
        (brs0:list branch)
        (bnds: list (R.pattern & list R.binding){L.length brs0 == L.length bnds})
: T.Tac (brs:list (check_branches_aux_t pre post_hint sc_u sc_ty sc)
          {
            samepats brs0 (L.map Mkdtuple3?._1 brs)
          })
= if L.isEmpty brs0 then fail g None "empty match";
  let tr1 (b: branch) (pbs:R.pattern & list R.binding)
    : T.Tac (check_branches_aux_t pre post_hint sc_u sc_ty sc)
    = let e = b.e in
      let (p, bs) = pbs in
      let (| p, e, c, d |) = check_branch (T.unseal b.norw) g pre pre_typing post_hint check sc_u sc_ty sc p e bs in
      (| {pat=p; e; norw=b.norw}, c, d |)
  in
  let r = zipWith tr1 brs0 bnds in
  assume (samepats brs0 (L.map Mkdtuple3?._1 r));
  r

let comp_observability (c:comp_st {C_STAtomic? c}) =
  let C_STAtomic _ obs _ = c in
  obs

let ctag_of_br  (#g #pre #post_hint #sc_u #sc_ty #sc:_)
                (l:check_branches_aux_t #g pre post_hint sc_u sc_ty sc)
: ctag
= let (|_, c, _|) = l in ctag_of_comp_st c

#push-options "--admit_smt_queries true" // Z3 crash
let weaken_branch_observability
      (obs:observability)
      (#g #pre:_) (#post_hint:post_hint_for_env g) 
      (#sc_u #sc_ty #sc:_)
      (c:comp_st{
          C_STAtomic? c /\
          comp_pre c == pre /\
          comp_post_matches_hint c (PostHint post_hint) /\
          comp_observability c == obs
        })
      (checked_br : check_branches_aux_t #g pre post_hint sc_u sc_ty sc { ctag_of_br checked_br == STT_Atomic})
: T.Tac (br:branch & br_typing_vis g sc_u sc_ty sc br.pat br.e c)
= let (| br, c0, typing |) = checked_br in
  match c0 with
  | C_STAtomic i obs' st ->
    if not (sub_observability obs' obs)
    then T.fail "Cannot weaken observability"
    else (
      let d : br_typing_vis g sc_u sc_ty sc br.pat br.e c = 
        let TBRV g sc_u sc_ty sc c p e bs p1 p2 p3 hyp st_typing = typing in
        let st_typing = T_Lift _ _ _ _ st_typing (Lift_Observability _ c obs) in
        let d = TBRV g sc_u sc_ty sc _ p e bs p1 p2 p3 hyp st_typing in
        d
      in
      (| br, d |)
    )
#pop-options

let rec max_obs 
    (checked_brs : list comp_st)
    (obs:observability)
: observability
= match checked_brs with
  | [] -> obs
  | c'::rest -> 
    match c' with
    | C_ST _
    | C_STGhost _ _ ->
      max_obs rest obs
    | C_STAtomic _ obs' _ ->
      max_obs rest (join_obs obs obs')

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
#restart-solver
let join_branches (#g #pre #post_hint #sc_u #sc_ty #sc:_) 
                  (ct:ctag)
                  (checked_brs : list (cbr:check_branches_aux_t #g pre post_hint sc_u sc_ty sc {ctag_of_br cbr == ct}))
: T.Tac (c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (PostHint post_hint) } &
         list (br:branch & br_typing_vis g sc_u sc_ty sc br.pat br.e c))
= match checked_brs with
  | [] -> T.fail "Impossible: empty match"
  | checked_br::rest ->
    let (| br, c, d |) = checked_br in
    match c with
    | C_ST _ 
    | C_STGhost _ _ ->
      let rest = 
        List.Tot.map 
          #(cbr:check_branches_aux_t #g pre post_hint sc_u sc_ty sc {ctag_of_br cbr==ct})
          #(br:branch & br_typing_vis g sc_u sc_ty sc br.pat br.e c)
          (fun (| br, c', d |) -> (| br, d |))
          rest
      in
      (| c, ((| br, d |) :: rest) |)
    | C_STAtomic i obs stc -> 
      let max_obs = max_obs (List.Tot.map Mkdtuple3?._2 rest) obs in
      let c = C_STAtomic i max_obs stc in
      let checked_brs = T.map (weaken_branch_observability max_obs c) checked_brs in
      (| c, checked_brs |)
#pop-options 

let rec least_tag (#g #pre #post_hint #sc_u #sc_ty #sc:_) 
              (checked_brs : list (check_branches_aux_t #g pre post_hint sc_u sc_ty sc))
: ctag
= match checked_brs with
  | [] -> STT_Ghost
  | checked_br::rest ->
    let (| _, c, _ |) = checked_br in
    match c with
    | C_ST _ -> STT
    | C_STGhost _ _ -> least_tag rest
    | C_STAtomic i _ _ -> STT_Atomic


#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 0"
#restart-solver
let weaken_branch_tag_to 
      (#g #pre #post_hint #sc_u #sc_ty #sc:_) 
      (ct:ctag)
      (br :check_branches_aux_t #g pre post_hint sc_u sc_ty sc  { EffectAnnotAtomicOrGhost? post_hint.effect_annot })
: T.Tac (cbr:check_branches_aux_t #g pre post_hint sc_u sc_ty sc { ctag_of_br cbr == ct })
= let (| pe, c, d|) = br in
  if ctag_of_comp_st c = ct then br
  else
    let r = pe.e.range in
    allow_invert ct; allow_invert c;
    match ct, c with
    | STT_Ghost, C_STAtomic _ _ _
    | STT_Ghost, C_ST _ -> T.fail "Unexpected least effect"

    | STT_Atomic, C_ST _ ->
      fail g (Some r)  "Cannot lift a computation from ST to atomic"

    | STT, _ ->
      fail g (Some r)  "Cannot lift a branch to ST"

    | STT_Atomic, C_STGhost _ _ -> (
      let TBRV g sc_u sc_ty sc c p e bs pf1 pf2 pf3 h d = d in
      let d = Pulse.Typing.Combinators.lift_ghost_atomic d in
      let d = TBRV g sc_u sc_ty sc _ p e bs pf1 pf2 pf3 h d in
      (| pe, _, d |)
    )
    


let weaken_branch_tags
      (#g #pre #post_hint #sc_u #sc_ty #sc:_) 
      (checked_brs : list (check_branches_aux_t #g pre post_hint sc_u sc_ty sc) {EffectAnnotAtomicOrGhost? post_hint.effect_annot})
: T.Tac (ct:ctag & list (cbr:check_branches_aux_t #g pre post_hint sc_u sc_ty sc {ctag_of_br cbr == ct}))
= let ct = least_tag checked_brs in
  let brs = T.map (weaken_branch_tag_to ct) checked_brs in
  (| ct, brs |)
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let maybe_weaken_branch_tags
      (#g #pre #post_hint #sc_u #sc_ty #sc:_) 
      (checked_brs : list (check_branches_aux_t #g pre post_hint sc_u sc_ty sc))
: T.Tac (ct:ctag & list (cbr:check_branches_aux_t #g pre post_hint sc_u sc_ty sc {ctag_of_br cbr == ct}))
= match post_hint.effect_annot with
  | EffectAnnotAtomicOrGhost _ -> 
    let ct = least_tag checked_brs in
    let brs = T.map (weaken_branch_tag_to ct) checked_brs in
    (| ct, brs |)
  | _ ->
    match checked_brs with
    | [] -> (| STT_Ghost, [] |)
    | hd::tl ->
      let ct = ctag_of_br hd in
      let checked_brs = T.map #_ #(cbr:check_branches_aux_t #g pre post_hint sc_u sc_ty sc {ctag_of_br cbr == ct}) (fun x -> x) checked_brs in
      (| ct, checked_brs |)
#pop-options
let erase_br_typing #g #sc_u #sc_ty #sc #p #e #c (d: br_typing_vis g sc_u sc_ty sc p e c)
  : br_typing g sc_u sc_ty sc p e c =
  let TBRV g sc_u sc_ty sc c p e bs pf1 pf2 pf3 hyp d = d in
  TBR g sc_u sc_ty sc c p e bs pf1 pf2 pf3 hyp d

(* Hoisting this makes the proof much faster and more stable. *)
let rec check_branches_aux2
  (g:env)
  (sc_u:universe)
  (sc_ty:typ)
  (sc : term)
  (c0 :comp_st)
  (brs : list (br:branch & br_typing_vis g sc_u sc_ty sc br.pat br.e c0))
  : brs_typing g sc_u sc_ty sc (List.Tot.map dfst brs) c0
  = match brs with
    | [] -> TBRS_0 c0
    | (| br, d|)::rest ->
      let { pat; e } = br in
      TBRS_1 c0 pat e (erase_br_typing d) (List.Tot.map dfst rest) (check_branches_aux2 g sc_u sc_ty sc c0 rest)

let check_branches
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_slprop)
        (post_hint:post_hint_for_env g)
        (check:check_t)
        (sc_u : universe)
        (sc_ty : typ)
        (sc : term)
        (brs0:list branch)
        (bnds: list (R.pattern & list R.binding){L.length brs0 == L.length bnds})
: T.Tac (brs:list branch
         & c:comp_st{comp_pre c == pre /\ comp_post_matches_hint c (PostHint post_hint)}
         & brs_typing g sc_u sc_ty sc brs c)
= let checked_brs = check_branches_aux g pre pre_typing post_hint check sc_u sc_ty sc brs0 bnds in
  let (| ct, checked_brs |) = maybe_weaken_branch_tags checked_brs in
  let (| c0, checked_brs |) = join_branches ct checked_brs in
  let brs = List.Tot.map dfst checked_brs in
  let d : brs_typing g sc_u sc_ty sc brs c0 = check_branches_aux2 g sc_u sc_ty sc c0 checked_brs in
  (| brs, c0, d |)
#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 4 --query_stats"
let check
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_slprop)
        (post_hint:post_hint_for_env g)
        (res_ppname:ppname)
        (sc:term)
        (brs:list branch)
        (check:check_t)
  : T.Tac (checker_result_t g pre (PostHint post_hint))
  =

  let g = Pulse.Typing.Env.push_context_no_range g "check_match" in

  let sc_range = Pulse.RuntimeUtils.range_of_term sc in // save range, it gets lost otherwise
  let orig_brs = brs in
  let nbr = L.length brs in

  let (| sc, sc_u, sc_ty, sc_ty_typing, sc_typing |) = compute_tot_term_type_and_u g sc in
  let elab_pats = L.map elab_pat (L.map patof brs) in

  assertby (L.length elab_pats == L.length brs) (fun () ->
    lemma_map_len patof brs;
    lemma_map_len elab_pat (L.map patof brs)
  );

  let (| elab_pats', bnds', complete_d |)
    : (pats : (list R.pattern){L.length pats == nbr}
        & bnds : (list (list R.binding)){L.length bnds == nbr}
        & pats_complete g sc sc_ty pats)
  =
    match T.check_match_complete (elab_env g) sc sc_ty elab_pats with
    | None, issues ->
      let open Pulse.PP in
      fail_doc_with_subissues g (Some sc_range) issues [
        text "Could not verify that this match is exhaustive.";
      ]
    | Some (elab_pats', bnds), _ ->
      (| elab_pats', bnds, PC_Elab _ _ _ _ _ (RT.MC_Tok _ _ _ _ bnds ()) |)
  in
  let new_pats = map_opt readback_pat elab_pats' in 
  if None? new_pats then
    fail g (Some sc_range) "failed to readback new patterns";
  let brs = zipWith (fun p br -> { br with pat=p }) (Some?.v new_pats) brs in
  
  assume (L.map patof brs == Some?.v new_pats);
  
  lemma_map_opt_lenx readback_pat elab_pats';

  // Making sure lengths match.
  assert (L.length elab_pats == nbr);
  assert (L.length elab_pats == nbr);
  assert (L.length elab_pats' == nbr);
  assert (L.length (Some?.v new_pats) == nbr);
  assert (L.length bnds' == nbr);
  assert (L.length elab_pats' == nbr);
  assert (L.length (zip elab_pats' bnds') == nbr);

  let (| brs, c, brs_d |) =
    check_branches g pre pre_typing post_hint check sc_u sc_ty sc brs (zip elab_pats' bnds') in

  (* Provable *)
  assume (L.map (fun br -> elab_pat br.pat) brs == elab_pats');
  let c_typing = comp_typing_from_post_hint c pre_typing post_hint in
  let d = T_Match g sc_u sc_ty sc sc_ty_typing sc_typing c (E c_typing) brs brs_d complete_d in
  checker_result_for_st_typing (| _, _, d |) res_ppname
#pop-options