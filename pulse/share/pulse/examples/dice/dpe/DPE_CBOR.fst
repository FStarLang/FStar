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

module DPE_CBOR
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Mutex
open Pulse.Class.PtsTo

open DPE
open DPE.Messages.Parse
open CBOR.Spec
open CBOR.Pulse
open CDDL.Pulse

module Cddl = CDDL.Spec
module MsgSpec = DPE.Messages.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module A = Pulse.Lib.Array
module Cast = FStar.Int.Cast
assume
val drop (p:slprop)
    : stt unit p (fun _ -> emp)

#push-options "--ext 'pulse:env_on_err'"

assume
val dbg : slprop

open Pulse.Lib.Trade


ghost
fn elim_implies () (#p #q:slprop)
   requires (p @==> q)
   requires p
   ensures q
{
  open Pulse.Lib.Trade;
  elim_trade p q
}



fn finish (c:cbor_read_t)
          (input:array U8.t)
          (#p:perm)
          (#v:erased (raw_data_item))
          (#s:erased (Seq.seq U8.t))
          (#rem:erased (Seq.seq U8.t))
  requires ((raw_data_item_match 1.0R c.cbor_read_payload v **
               pts_to c.cbor_read_remainder #p rem) @==>
              pts_to input #p s) **
            raw_data_item_match 1.0R c.cbor_read_payload v **
            pts_to c.cbor_read_remainder #p rem **
            'uds_is_enabled
  returns _:bool
  ensures pts_to input #p s
{
   elim_implies ()  #(raw_data_item_match 1.0R c.cbor_read_payload v **
                            pts_to c.cbor_read_remainder #p rem)
                            #(pts_to input #p s);
    drop 'uds_is_enabled;
    false
}


assume Fits_u64 : squash (SZ.fits_u64)

#push-options "--z3rlimit 20"

fn initialize_context (len:SZ.t)
                      (input:A.larray U8.t (SZ.v len))
                      (#s:erased (Seq.seq U8.t))
                      (#p:perm)
    requires
        pts_to input #p s
    returns r:bool
    ensures
        pts_to input #p s
{
    let read = parse_dpe_cmd len input;
    match read
    {
      None ->
      {
        unfold (parse_dpe_cmd_post len input s p None);
        false
      }
      Some cmd ->
      {
        unfold (parse_dpe_cmd_post len input s p (Some cmd));
        if (cmd.dpe_cmd_sid `FStar.UInt64.gte` 4294967296uL) {
          // FIXME: DPE.sid == U16.t, but the CDDL specification for DPE session messages does not specify any bound on sid (if so, I could have used a CDDL combinator and avoided this additional test here)
          elim_stick0 ();
          false
        } else {
          let sid : FStar.UInt16.t = Cast.uint64_to_uint16 cmd.dpe_cmd_sid;
          with vargs . assert (raw_data_item_match 1.0R cmd.dpe_cmd_args vargs);
          let key = cbor_constr_int64 cbor_major_type_uint64 MsgSpec.initialize_context_seed;
          with vkey . assert (raw_data_item_match 1.0R key vkey);
          let read_uds = cbor_map_get_with_typ (impl_str_size cbor_major_type_byte_string EngineTypes.uds_len) key cmd.dpe_cmd_args;
          drop_ (raw_data_item_match _ _ _); // FIXME: HOW HOW HOW can I avoid the arguments to raw_data_item_match, like in Steel?
          match read_uds
          {
            NotFound ->
            {
              unfold (cbor_map_get_with_typ_post (Cddl.str_size cbor_major_type_byte_string (SZ.v EngineTypes.uds_len)) 1.0R (Ghost.reveal vkey) vargs cmd.dpe_cmd_args NotFound); // same here; also WHY WHY WHY the explicit Ghost.reveal
              elim_stick0 ();
              false
            }
            Found uds_cbor ->
            {
              unfold (cbor_map_get_with_typ_post (Cddl.str_size cbor_major_type_byte_string (SZ.v EngineTypes.uds_len)) 1.0R (Ghost.reveal vkey) vargs cmd.dpe_cmd_args (Found uds_cbor)); // same here; also WHY WHY WHY the explicit Ghost.reveal
              let uds = cbor_destr_string uds_cbor;
              A.pts_to_len uds.cbor_string_payload;
              assume_ (exists* t. DPE.sid_pts_to DPE.trace_ref sid t **
                                  pure (DPE.trace_valid_for_initialize_context t));
              with t. assert (DPE.sid_pts_to DPE.trace_ref sid t);
              DPE.initialize_context sid t uds.cbor_string_payload;
              with p' _vv. assert (pts_to uds.cbor_string_payload #p' _vv);
              elim_stick0 () #(pts_to uds.cbor_string_payload #p' _);
              elim_stick0 () #(raw_data_item_match 1.0R _ _);
              elim_stick0 ();
              drop_ (initialize_context_client_perm sid _);
              true
            }
          }
        }
      }
    }
}

#pop-options

#pop-options
