module Pulse.Prover.Match

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Metatheory
open Pulse.Checker.VPropEquiv
open Pulse.Prover.Common

module T = FStar.Tactics.V2
module PS = Pulse.Prover.Substs

let try_match_pq (g:env) (uvs:env { disjoint uvs g})
  (#p:vprop) (p_typing:vprop_typing g p)
  (#q:vprop) (q_typing:vprop_typing (push_env g uvs) q)
  : T.Tac (option (ss:PS.t { well_typed_ss ss uvs g /\
                             PS.dom ss `Set.subset` freevars q } &
                   vprop_equiv g p ss.(q))) = magic ()

let compose_ss (ss1 ss2:PS.t) : PS.t = magic ()

let match_step (#preamble:preamble) (pst:prover_state preamble)
  (p:vprop) (remaining_ctxt':list vprop)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.remaining_ctxt == p::remaining_ctxt' /\
             pst.unsolved == q::unsolved'))
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

let q_ss = pst.ss.(q) in
assume (freevars q_ss `Set.disjoint` PS.dom pst.ss);

let ropt = try_match_pq pst.pg pst.uvs #p (magic ()) #q_ss (magic ()) in
match ropt with
| None -> None
| Some (| ss_q, veq |) ->
  assert (PS.dom ss_q `Set.disjoint` PS.dom pst.ss);
  assert (well_typed_ss ss_q pst.uvs pst.pg);

  let ss_new = compose_ss ss_q pst.ss in
  assume (well_typed_ss ss_new pst.uvs pst.pg);

  let veq
    : vprop_equiv pst.pg p (ss_q.(pst.ss.(q))) = veq in
  assume (ss_q.(pst.ss.(q)) == ss_new.(q));
  let veq : vprop_equiv pst.pg p ss_new.(q) = veq in
  
  let remaining_ctxt_new = remaining_ctxt' in
  let solved_new = q * pst.solved in
  let unsolved_new = unsolved' in

  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop pst.remaining_ctxt * pst.ss.(pst.solved)) = pst.k in

  assume (pst.ss.(pst.solved) == ss_new.(pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop (p::remaining_ctxt') * ss_new.(pst.solved)) = pst.k in
  
  // some *s
  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop remaining_ctxt' * (p * ss_new.(pst.solved))) = magic () in
  
  // using veq of p and ss_new.(q)
  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop remaining_ctxt' * (ss_new.(q) * ss_new.(pst.solved))) = magic () in

  assume (ss_new.(q) * ss_new.(pst.solved) == ss_new.(q * pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 preamble.ctxt
        pst.pg (list_as_vprop remaining_ctxt_new * (ss_new.(solved_new))) = k in

  let pst' : prover_state preamble =
    { pst with remaining_ctxt=remaining_ctxt_new;
               ss=ss_new;
               solved=solved_new;
               unsolved=unsolved_new;
               k;
               goals_inv=magic ();
               solved_inv=magic () } in  // this solved_inv ... runtime check or inversion?
  
  assume (ss_new `ss_extends` pst.ss);
  Some pst'
