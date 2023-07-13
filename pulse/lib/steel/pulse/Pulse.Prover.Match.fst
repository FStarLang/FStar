module Pulse.Prover.Match

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Common

module L = FStar.List.Tot
module R = FStar.Reflection.V2
module TermEq = FStar.Reflection.V2.TermEq
module T = FStar.Tactics.V2

module RUtil = Pulse.Reflection.Util
module P = Pulse.Syntax.Printer
module PS = Pulse.Prover.Substs

let equational (t:term) : bool =
  match t.t with
  | Tm_FStar host_term ->
    (match R.inspect_ln host_term with
     | R.Tv_Match _ _ _ -> true
     | _ -> false)
  | _ -> false

let type_of_fv (g:env) (fv:R.fv)
  : T.Tac (option R.term)
  = let n = R.inspect_fv fv in
    match R.lookup_typ (fstar_env g) n with
    | None -> None
    | Some se ->
      match R.inspect_sigelt se with
      | R.Unk -> None
      | R.Sg_Let _ lbs -> (
        L.tryPick
          (fun lb -> 
            let lbv = R.inspect_lb lb in
            if R.inspect_fv lbv.lb_fv = n
            then Some lbv.lb_typ
            else None)
          lbs
      )
      | R.Sg_Val _ _ t -> Some t
      | R.Sg_Inductive _nm _univs params typ _ -> None

let is_smt_fallback (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_FVar fv ->
    let name = R.inspect_fv fv in
    name = ["Steel";"Effect";"Common";"smt_fallback"]
  | _ -> false

(*
  When comparing t0 =?= t1, if they are not syntactically equal, we
  have to decide whether or not we should fire an SMT query to compare
  them for provable equality.

  The criterion is as follows:

  1. We allow an SMT query if either t0 or t1 is "equational". For now, that means
     that either is a match expression.

  2. Otherwise, if they are both applications of `f v0...vn` and `f u0...un`
     of the same head symbol `f`, a top-level constant, then we check if the
     type of `f` decorates any of its binders with the `smt_fallback` attribute. 

        - If none of them are marked as such,
          then we check if `f v0...` is syntactically equal to `f u0...`
          and allow an SMT query to check if vn = vm. That is, the default behavior
          for predicates is that they *last* argument is eligible for SMT equality.

        - Otherwise, for each binder that is NOT marked as `smt_fallback`, we check
          if the corresponding argument is syntactically equal. If so, we allow 
          t0 and t1 to be compared for SMT equality.

          For example, Steel.ST.Reference.pts_to is defined like so:

            /// For instance, [pts_to r (sum_perm (half_perm p) (half_perm p)) (v + 1)]
            /// is unifiable with [pts_to r p (1 + v)]
            val pts_to (#a:Type0)
                      (r:ref a)
                      ([@@@smt_fallback] p:perm)
                      ([@@@smt_fallback] v:a)
              : vprop
*)
let eligible_for_smt_equality (g:env) (t0 t1:term) 
  : T.Tac bool
  = let either_equational () = equational t0 || equational t1 in
    let head_eq (t0 t1:R.term) =
      match R.inspect_ln t0, R.inspect_ln t1 with
      | R.Tv_App h0 _, R.Tv_App h1 _ ->
        TermEq.term_eq h0 h1
      | _ -> false
    in
    match t0.t, t1.t with
    | Tm_FStar t0, Tm_FStar t1 -> (
      let h0, args0 = R.collect_app_ln t0 in
      let h1, args1 = R.collect_app_ln t1 in
      if TermEq.term_eq h0 h1 && L.length args0 = L.length args1
      then (
        match R.inspect_ln h0 with
        | R.Tv_FVar fv
        | R.Tv_UInst fv _ -> (
          match type_of_fv g fv with
          | None -> either_equational()
          | Some t ->
            let bs, _ = R.collect_arr_ln_bs t in
            let is_smt_fallback (b:R.binder) = 
                let bview = R.inspect_binder b in
                L.existsb is_smt_fallback bview.attrs
            in
            let some_fallbacks, fallbacks =
              L.fold_right
                (fun b (some_fallbacks, bs) -> 
                  if is_smt_fallback b
                  then true, true::bs
                  else some_fallbacks, false::bs)
                bs (false, [])
            in
            if not some_fallbacks
            then (
                //if none of the binders are marked fallback
                //then, by default, consider only the last argument as
                //fallback
              head_eq t0 t1
            )
            else (
              let rec aux args0 args1 fallbacks =
                match args0, args1, fallbacks with
                | (a0, _)::args0, (a1, _)::args1, b::fallbacks -> 
                  if b
                  then aux args0 args1 fallbacks
                  else if not (TermEq.term_eq a0 a1)
                  then false
                  else aux args0 args1 fallbacks
                | [], [], [] -> true
                | _ -> either_equational() //unequal lengths
              in
              aux args0 args1 fallbacks
            )
        ) 
        | _ -> either_equational ()
      )
      else either_equational ()
    )
    | _ -> either_equational ()


let refl_uvar (t:R.term) (uvs:env) : option var =
  let open R in
  match inspect_ln t with
  | Tv_Var v ->
    let {uniq=n} = inspect_namedv v in
    if contains uvs n then Some n else None
  | _ -> None

let rec refl_contains_uvar (t:R.term) (uvs:env) (g:env) : T.Tac bool =
  let open R in
  match inspect_ln t with
  | Tv_Var _ -> Some? (refl_uvar t uvs)
  | Tv_BVar _
  | Tv_FVar _
  | Tv_UInst _ _
  | Tv_Const _
  | Tv_Type _ -> false
  | Tv_App hd (arg, _) ->
    let b = refl_contains_uvar hd uvs g in
    if b then true
    else refl_contains_uvar arg uvs g
  | _ -> fail g None "refl_contains_uvar: unsupported reflection term"

let is_uvar (t:term) (uvs:env) : option var =
  match t.t with
  | Tm_FStar t -> refl_uvar t uvs
  | _ -> None

let rec contains_uvar (t:term) (uvs:env) (g:env) : T.Tac bool =
  match t.t with
  | Tm_Emp -> false
  | Tm_Pure p -> contains_uvar p uvs g
  | Tm_Star t1 t2
  | Tm_ExistsSL _ {binder_ty=t1} t2
  | Tm_ForallSL _ {binder_ty=t1} t2 ->
    let b = contains_uvar t1 uvs g in
    if b then true
    else contains_uvar t2 uvs g
  | Tm_VProp
  | Tm_Inames
  | Tm_EmpInames -> false
  | Tm_FStar t -> refl_contains_uvar t uvs g
  | Tm_Unknown -> false

let is_reveal_uvar (t:term) (uvs:env) : option (universe & term & var) =
  match is_pure_app t with
  | Some (hd, None, arg) ->
    (match is_pure_app hd with
     | Some (hd, Some Implicit, ty) ->
       let arg_uvar_index_opt = is_uvar arg uvs in
       (match arg_uvar_index_opt with
        | Some n ->
          (match is_fvar hd with
           | Some (l, [u]) ->
             if l = RUtil.reveal_lid
             then Some (u, ty, n)
             else None
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | _ -> None

let is_reveal (t:term) : bool =
  match leftmost_head t with
  | Some hd ->
    (match is_fvar hd with
     | Some (l, [_]) -> l = RUtil.reveal_lid
     | _ -> false)
  | _ -> false

module RT = FStar.Reflection.Typing
let rec unify (g:env) (uvs:env { disjoint uvs g})
  (#p #p_t:term) (p_typing:tot_typing g p p_t)
  (#q #q_t:term) (q_typing:tot_typing (push_env g uvs) q q_t)
  (ss:PS.ss_t)
  : T.Tac (option (ss':PS.ss_t { ss' `ss_extends` ss /\
                                 PS.dom ss' `Set.subset` freevars q } &
                   RT.equiv (elab_env g) (elab_term p) (elab_term ss'.(q)))) =

  let q0 = q in
  let q = ss.(q) in
  assume (freevars q `Set.disjoint` PS.dom ss);

  if eq_tm p q
  then begin
    assume (PS.dom ss `Set.subset` freevars q);
    Some (| ss, RT.EQ_Refl _ _ |)
  end
  else if not (contains_uvar q uvs g)
  then begin
    if eligible_for_smt_equality g p q
    then let _ = assume (PS.dom ss `Set.subset` freevars q) in
         let v0 = elab_term p in
         let v1 = elab_term q in
         match T.check_equiv (elab_env g) v0 v1 with
         | Some token, _ -> Some (| ss, RT.EQ_Token _ _ _ (FStar.Squash.return_squash token) |)
         | None, _ -> None
    else None
  end
  else match is_reveal_uvar q uvs, is_reveal p with
       | Some (u, ty, n), false ->
         let w = mk_hide u ty p in
         assume (Set.mem n (dom uvs));
         assume (~ (PS.contains PS.empty n));
         assume (Set.disjoint (freevars w) (dom uvs));
         let ss_new = PS.push PS.empty n w in
         assume (n `Set.mem` freevars q);
         assume (Set.equal (PS.dom ss_new) (Set.singleton n));
         assert (Set.disjoint (PS.dom ss_new) (PS.dom ss));
         let ss' = PS.push_ss ss ss_new in
         assume (ss' `ss_extends` ss);
         assume (ss'.(q0) == w);
         assume (PS.dom ss' `Set.subset` freevars q0);  // they are actually equal
         let b, _ = T.check_equiv (elab_env g) (elab_term (mk_reveal u ty w)) (elab_term p) in
         if Some? b
         then let d : RT.equiv (elab_env g) (elab_term p) (elab_term ss'.(q0)) = magic () in
              Some (| ss', d |)
         else None
       | _ ->
         match is_uvar q uvs with
         | Some n ->
           assume (Set.mem n (dom uvs));
           assume (~ (PS.contains PS.empty n));
           assume (Set.disjoint (freevars p) (dom uvs));
           let ss_new = PS.push PS.empty n p in
           assume (n `Set.mem` freevars q);
           assume (Set.equal (PS.dom ss_new) (Set.singleton n));
           assert (Set.disjoint (PS.dom ss_new) (PS.dom ss));
           let ss' = PS.push_ss ss ss_new in
           assume (PS.dom ss' `Set.subset` freevars q0);  // again equal
           assume (ss'.(q0) == p);
           Some (| ss', RT.EQ_Refl _ _ |)
         | _ ->
           match p.t, q.t with
           | Tm_Pure p1, Tm_Pure q1 ->
             let r = unify g uvs
               #p1 #(magic ()) (magic ())
               #q1 #(magic ()) (magic ())
               ss in
             (match r with
              | Some (| ss', _ |) ->
                assume (Set.subset (PS.dom ss') (freevars q0));
                let ss' : ss':PS.ss_t { ss' `ss_extends` ss /\
                                        PS.dom ss' `Set.subset` freevars q0 } = ss' in
                Some (| ss', magic () |)
              | None -> None)

           | _, _ ->
             match is_pure_app p, is_pure_app q with
             | Some (head_p, qual_p, arg_p), Some (head_q, qual_q, arg_q) ->
               if not (qual_p = qual_q) then None
               else begin
                 let r = unify g uvs
                   #head_p #(magic ()) (magic ())
                   #head_q #(magic ()) (magic ())
                   ss in
                 match r with
                 | Some (| ss', _ |) ->
                   let r = unify g uvs
                      #arg_p #(magic ()) (magic ())
                      #arg_q #(magic ()) (magic ())
                      ss' in
                   (match r with
                    | Some (| ss', _|) ->
                      admit ();
                      let ss' : ss':PS.ss_t { ss' `ss_extends` ss /\
                                              PS.dom ss' `Set.subset` freevars q0 } = ss' in
                      Some (| ss', magic () |)
                    | _ -> None)
                 | _ -> None
               end
             | _, _ -> None

let try_match_pq (g:env) (uvs:env { disjoint uvs g})
  (#p:vprop) (p_typing:vprop_typing g p)
  (#q:vprop) (q_typing:vprop_typing (push_env g uvs) q)
  : T.Tac (option (ss:PS.ss_t { PS.dom ss `Set.subset` freevars q } &
                   vprop_equiv g p ss.(q))) =

  let r = unify g uvs p_typing q_typing PS.empty in
  match r with
  | None -> None
  | Some (| ss, _ |) ->
    let ss : ss:PS.ss_t { PS.dom ss `Set.subset` freevars q } = ss in
    Some (| ss, magic () |)

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

let match_step (#preamble:preamble) (pst:prover_state preamble)
  (p:vprop) (remaining_ctxt':list vprop)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.remaining_ctxt == p::remaining_ctxt' /\
             pst.unsolved == q::unsolved'))
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

let q_ss = pst.ss.(q) in
assume (freevars q_ss `Set.disjoint` PS.dom pst.ss);

let ropt = try_match_pq pst.pg pst.uvs #p (magic ()) #q_ss (magic ()) in

debug_prover pst.pg (fun _ ->
  Printf.sprintf "prover matcher: tried to match %s and %s, result: %s"
    (P.term_to_string p) (P.term_to_string q_ss) (if None? ropt then "fail" else "success"));

match ropt with
| None -> None
| Some (| ss_q, veq |) ->
  assert (PS.dom ss_q `Set.disjoint` PS.dom pst.ss);
  
  let ss_new = PS.push_ss pst.ss ss_q in

  let veq : vprop_equiv pst.pg p (ss_q.(pst.ss.(q))) = veq in

  assume (ss_q.(pst.ss.(q)) == ss_new.(q));
  let veq : vprop_equiv pst.pg p ss_new.(q) = coerce_eq veq () in

  let remaining_ctxt_new = remaining_ctxt' in
  let solved_new = q * pst.solved in
  let unsolved_new = unsolved' in

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved)) = pst.k in

  assume (pst.ss.(pst.solved) == ss_new.(pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop (p::remaining_ctxt_new) * preamble.frame) * ss_new.(pst.solved)) =
    coerce_eq k () in

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop remaining_ctxt_new * preamble.frame) * (ss_new.(q) * ss_new.(pst.solved))) =
    k_elab_equiv k (VE_Refl _ _) (magic ()) in
  
  assume (ss_new.(q) * ss_new.(pst.solved) == ss_new.(q * pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop remaining_ctxt_new * preamble.frame) * (ss_new.(solved_new))) =
    coerce_eq k () in

  let pst' : prover_state preamble =
    { pst with remaining_ctxt=remaining_ctxt_new;
               remaining_ctxt_frame_typing=magic ();
               ss=ss_new;
               solved=solved_new;
               unsolved=unsolved_new;
               k;
               goals_inv=magic ();
               solved_inv=magic () } in

  assume (ss_new `ss_extends` pst.ss);
  Some pst'
