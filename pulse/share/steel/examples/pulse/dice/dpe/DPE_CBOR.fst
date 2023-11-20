module DPE_CBOR
open Pulse.Lib.Pervasives
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
val drop (p:vprop)
    : stt unit p (fun _ -> emp)

#push-options "--ext 'pulse:env_on_err'"

assume
val dbg : vprop

open Pulse.Lib.Stick

#push-options "--z3rlimit 16 --query_stats --ifuel 16" // to let z3 cope with CDDL specs

#push-options "--z3rlimit 20"
```pulse
fn initialize_context (len:SZ.t)
                      (input:A.larray U8.t (SZ.v len))
                      (#s:erased (Seq.seq U8.t))
                      (#p:perm)
    requires
        A.pts_to input #p s
    returns _:option ctxt_hndl_t
    ensures
        A.pts_to input #p s
{
    let read = parse_dpe_cmd len input;
    match read
    {
      None ->
      {
        unfold (parse_dpe_cmd_post len input s p None);
        None #ctxt_hndl_t
      }
      Some cmd ->
      {
        unfold (parse_dpe_cmd_post len input s p (Some cmd));
        if (cmd.dpe_cmd_sid `FStar.UInt64.gte` 4294967296uL) {
          // FIXME: DPE.sid == U32.t, but the CDDL specification for DPE session messages does not specify any bound on sid (if so, I could have used a CDDL combinator and avoided this additional test here)
          elim_stick0 ();
          None #ctxt_hndl_t
        } else {
          let sid : FStar.UInt32.t = Cast.uint64_to_uint32 cmd.dpe_cmd_sid;
          with vargs . assert (raw_data_item_match full_perm cmd.dpe_cmd_args vargs);
          let key = constr_cbor_int64 major_type_uint64 MsgSpec.initialize_context_seed;
          with vkey . assert (raw_data_item_match full_perm key vkey);
          let read_uds = cbor_map_get_with_typ (impl_str_size major_type_byte_string EngineTypes.uds_len) key cmd.dpe_cmd_args;
          drop (raw_data_item_match full_perm key vkey); // FIXME: HOW HOW HOW can I avoid the arguments to raw_data_item_match, like in Steel?
          match read_uds
          {
            NotFound ->
            {
              unfold (cbor_map_get_with_typ_post (Cddl.str_size major_type_byte_string (SZ.v EngineTypes.uds_len)) full_perm (Ghost.reveal vkey) vargs cmd.dpe_cmd_args NotFound); // same here; also WHY WHY WHY the explicit Ghost.reveal
              elim_stick0 ();
              None #ctxt_hndl_t
            }
            Found uds_cbor ->
            {
              unfold (cbor_map_get_with_typ_post (Cddl.str_size major_type_byte_string (SZ.v EngineTypes.uds_len)) full_perm (Ghost.reveal vkey) vargs cmd.dpe_cmd_args (Found uds_cbor)); // same here; also WHY WHY WHY the explicit Ghost.reveal
              let uds = destr_cbor_string uds_cbor;
              A.pts_to_len uds.cbor_string_payload;
              let res = DPE.initialize_context sid uds.cbor_string_payload;
              elim_stick0 ();
              elim_stick0 ();
              elim_stick0 ();
              res
            }
          }
        }
      }
    }
}
```
#pop-options

#pop-options
