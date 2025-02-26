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

module DPE.Messages.Parse
#lang-pulse
open Pulse.Lib.Pervasives
open CBOR.Spec
open CBOR.Pulse
open CDDL.Pulse
module Spec = DPE.Messages.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module A = Pulse.Lib.Array

#push-options "--ext 'pulse:env_on_err'"

assume
val dbg : slprop

open Pulse.Lib.Trade


ghost
fn elim_implies (#p #q:slprop) ()
   requires (p @==> q) ** p
   ensures q
{
  open Pulse.Lib.Trade;
  elim_trade p q
}


inline_for_extraction noextract [@@noextract_to "krml"]
let impl_session_message1 : impl_typ Spec.session_message =
  impl_t_array (
    impl_array_group3_concat
      (impl_array_group3_item (impl_uint ()))
      (impl_array_group3_item (impl_bytes ()))
  )


(*

fn impl_session_message0
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item)
        ))
returns res: bool
ensures
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item) /\
            res == Spec.session_message v
        ))
{
  eval_impl_typ impl_session_message1 c
}

*)

noextract [@@noextract_to "krml"]
assume val impl_session_message : impl_typ Spec.session_message

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_command_id: impl_typ Spec.command_id =
  impl_uint_literal Spec.get_profile `impl_t_choice_none`
  impl_uint_literal Spec.open_session `impl_t_choice_none`
  impl_uint_literal Spec.close_session `impl_t_choice_none`
  impl_uint_literal Spec.sync_session `impl_t_choice_none`
  impl_uint_literal Spec.export_session `impl_t_choice_none`
  impl_uint_literal Spec.import_session `impl_t_choice_none`
  impl_uint_literal Spec.initialize_context `impl_t_choice_none`
  impl_uint_literal Spec.derive_child `impl_t_choice_none`
  impl_uint_literal Spec.certify_key `impl_t_choice_none`
  impl_uint_literal Spec.sign `impl_t_choice_none`
  impl_uint_literal Spec.seal `impl_t_choice_none`
  impl_uint_literal Spec.unseal `impl_t_choice_none`
  impl_uint_literal Spec.derive_sealing_public_key `impl_t_choice_none`
  impl_uint_literal Spec.rotate_context_handle `impl_t_choice_none`
  impl_uint_literal Spec.destroy_context

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_default_args_group : impl_matches_map_group Spec.default_args_group =
  impl_matches_map_group_no_restricted (
    impl_matches_map_entry_zero_or_more_cons
      (CDDL.Spec.uint `CDDL.Spec.MapGroupEntry` CDDL.Spec.any)
      (impl_uint ())
      (impl_any ())
      (impl_matches_map_entry_zero_or_more_nil _)
  )
  ()

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_command_message1 : impl_typ Spec.command_message = // Wow, the equivalence with command_message' seems to work out of the box
  impl_t_array (
    impl_array_group3_item impl_command_id `impl_array_group3_concat`
    impl_array_group3_item (impl_t_map impl_default_args_group)
  )

(*

fn impl_command_message0
    (c: cbor)
    (#p: perm)
    (#v: Ghost.erased raw_data_item)
requires
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item)
        ))
returns res: bool
ensures
        (raw_data_item_match p c v ** pure (
            opt_precedes (Ghost.reveal v) (None #raw_data_item) /\
            res == Spec.command_message v
        ))
{
  eval_impl_typ impl_command_message1 c
}

*)

noextract [@@noextract_to "krml"]
assume val impl_command_message : impl_typ Spec.command_message

module U64 = FStar.UInt64

noeq
type dpe_cmd = {
  dpe_cmd_sid: U64.t;
  dpe_cmd_cid: U64.t;
  dpe_cmd_args: cbor;
}

#push-options "--z3rlimit 64" // to let z3 cope with CDDL specs
#restart-solver

noextract [@@noextract_to "krml"]
let parse_dpe_cmd_args_postcond
  (cid: U64.t)
  (vargs: raw_data_item)
  (vcmd: raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= data_item_wf deterministically_encoded_cbor_map_key_order vcmd /\
  Spec.command_message vcmd /\ (
    let Array [Int64 _ cid'; vargs'] = vcmd in
    cid == cid' /\
    vargs == vargs'
  ) /\
  Seq.length rem == 0
  
noextract [@@noextract_to "krml"]
let parse_dpe_cmd_postcond
  (sid: U64.t)
  (cid: U64.t)
  (vargs: raw_data_item)
  (vsess: raw_data_item)
  (_: Seq.seq U8.t)
: Tot prop
= data_item_wf deterministically_encoded_cbor_map_key_order vsess /\
  Spec.session_message vsess /\ (
    let Array [Int64 _ sid'; String _ cmd] = vsess in
    sid == sid' /\ (
    exists vcmd rem .
    cmd == serialize_cbor vcmd `Seq.append` rem /\
    parse_dpe_cmd_args_postcond cid vargs vcmd rem
  ))

noextract [@@noextract_to "krml"]
let parse_dpe_cmd_failure_postcond
 (s: Seq.seq U8.t)
: prop
=
  ~ (exists vsess rem .
    s == serialize_cbor vsess `Seq.append` rem /\ (
      exists sid cid vargs .
      parse_dpe_cmd_postcond sid cid vargs vsess rem
    )
  )


let parse_dpe_cmd_post
  (len:SZ.t)
  (input:A.larray U8.t (SZ.v len))
  (s:erased (Seq.seq U8.t))
  (p:perm)
  (res: option dpe_cmd)
: slprop
= match res with
  | None -> pts_to input #p s ** pure (parse_dpe_cmd_failure_postcond s)
  | Some cmd -> exists* vargs.
      raw_data_item_match 1.0R cmd.dpe_cmd_args vargs **
      (raw_data_item_match 1.0R cmd.dpe_cmd_args vargs @==>
        pts_to input #p s
      ) **
      pure (
        exists (vsess: raw_data_item) (rem: Seq.seq U8.t) .
        Ghost.reveal s == serialize_cbor vsess `Seq.append` rem /\
        parse_dpe_cmd_postcond cmd.dpe_cmd_sid cmd.dpe_cmd_cid vargs vsess rem
      )



fn parse_dpe_cmd (#s:erased (Seq.seq U8.t))
                 (#p:perm)
                 (len:SZ.t)
                 (input:A.larray U8.t (SZ.v len))
    requires
        pts_to input #p s
    returns res:option dpe_cmd
    ensures
      parse_dpe_cmd_post len input s p res
{
    let c = cbor_read_deterministically_encoded_with_typ impl_session_message input len;
    if (not c.cbor_read_is_success) {
        unfold (cbor_read_deterministically_encoded_with_typ_post Spec.session_message input p s c); 
        rewrite each c.cbor_read_is_success as false;
        unfold (cbor_read_deterministically_encoded_with_typ_error_post Spec.session_message input p s); 
        fold (parse_dpe_cmd_post len input s p None);
        None #dpe_cmd
    } else {
        unfold (cbor_read_deterministically_encoded_with_typ_post Spec.session_message input p s c);
        rewrite each c.cbor_read_is_success as true;
        unfold (cbor_read_deterministically_encoded_with_typ_success_post Spec.session_message input p s c);
        with vc . assert (raw_data_item_match 1.0R c.cbor_read_payload vc);
        with vrem1 . assert (pts_to c.cbor_read_remainder #p vrem1);
        stick_consume_r ()
          #(raw_data_item_match 1.0R c.cbor_read_payload vc)
          #(pts_to c.cbor_read_remainder #p vrem1)
          #(pts_to input #p s)
        ;
        let i0 = cbor_array_index c.cbor_read_payload 0sz;
        let cbor_int = cbor_destr_int64 i0;
        let sid = cbor_int.cbor_int_value;
        elim_implies #(raw_data_item_match 1.0R i0 _) ();
        let i1 = cbor_array_index c.cbor_read_payload 1sz;
        stick_trans () #_ #_ #(pts_to input #p s);
        let cbor_str = cbor_destr_string i1;
        stick_trans () #_ #_ #(pts_to input #p s);
        with cs ps . assert (pts_to cbor_str.cbor_string_payload #ps cs);
        let msg = cbor_read_deterministically_encoded_with_typ impl_command_message cbor_str.cbor_string_payload (SZ.of_u64 cbor_str.cbor_string_length);
        if (not msg.cbor_read_is_success) {
            unfold (cbor_read_deterministically_encoded_with_typ_post Spec.command_message cbor_str.cbor_string_payload ps cs msg);
            rewrite each msg.cbor_read_is_success as false;
            unfold (cbor_read_deterministically_encoded_with_typ_error_post Spec.command_message cbor_str.cbor_string_payload ps cs);
            elim_implies ();
            serialize_cbor_inj' vc vrem1;
            fold (parse_dpe_cmd_post len input s p None);
            None #dpe_cmd
        } else {
            unfold (cbor_read_deterministically_encoded_with_typ_post Spec.command_message cbor_str.cbor_string_payload ps cs msg);
            rewrite each msg.cbor_read_is_success as true;
            unfold (cbor_read_deterministically_encoded_with_typ_success_post Spec.command_message cbor_str.cbor_string_payload ps cs msg);
            with vmsg . assert (raw_data_item_match 1.0R msg.cbor_read_payload vmsg);
            with vrem2 . assert (pts_to msg.cbor_read_remainder #ps vrem2);
            stick_consume_r ()
              #(raw_data_item_match 1.0R msg.cbor_read_payload vmsg)
              #(pts_to msg.cbor_read_remainder #ps vrem2)
              #(pts_to cbor_str.cbor_string_payload #ps cs)
            ;
            stick_trans () #_ #_ #(pts_to input #p s);
            if (msg.cbor_read_remainder_length <> 0sz) {
              elim_implies ();
              serialize_cbor_inj' vmsg vrem2;
              serialize_cbor_inj' vc vrem1;
              fold (parse_dpe_cmd_post len input s p None);
              None #dpe_cmd
            } else {
              let cmd_id_cbor = cbor_array_index msg.cbor_read_payload 0sz;
              let cmd_id_int = cbor_destr_int64 cmd_id_cbor;
              let cmd_id = cmd_id_int.cbor_int_value;
              elim_implies #(raw_data_item_match 1.0R cmd_id_cbor _) ();
              let cmd_args = cbor_array_index msg.cbor_read_payload 1sz;
              stick_trans () #_ #_ #(pts_to input #p s);
              with vargs . assert (raw_data_item_match 1.0R cmd_args vargs);

              let res = {
                dpe_cmd_sid = sid;
                dpe_cmd_cid = cmd_id;
                dpe_cmd_args = cmd_args;
              };
              rewrite (raw_data_item_match 1.0R cmd_args vargs ** (raw_data_item_match 1.0R cmd_args vargs @==> pts_to input #p s)) // FIXME: should `fold` honor projectors and not just `match`?
                as (raw_data_item_match 1.0R res.dpe_cmd_args vargs ** (raw_data_item_match 1.0R res.dpe_cmd_args vargs @==> pts_to input #p s));
              fold (parse_dpe_cmd_post len input s p (Some res));
              Some res
            }
        }
    }
}


#pop-options
