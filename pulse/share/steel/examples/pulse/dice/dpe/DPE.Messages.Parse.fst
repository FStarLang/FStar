module DPE.Messages.Parse
open Pulse.Lib.Pervasives
open DPE
open CBOR.Spec
open CBOR.Pulse
open CDDL.Pulse
module Spec = DPE.Messages.Spec
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module A = Pulse.Lib.Array
assume
val drop (p:vprop)
    : stt unit p (fun _ -> emp)

#push-options "--ext 'pulse:env_on_err'"

assume
val dbg : vprop

open Pulse.Lib.Stick

let emp_inames_disjoint (t:inames)
  : Lemma 
    (ensures (t /! emp_inames))
    [SMTPat (Set.disjoint t emp_inames)]
  = admit()

```pulse
ghost
fn elim_implies (_:unit) (#p #q:vprop)
   requires `@(p @==> q) ** p
   ensures q
{
  open Pulse.Lib.Stick;
  rewrite `@(p @==> q) as (stick #emp_inames p q);
  elim_stick #emp_inames #emp_inames p q;
}
```

```pulse
fn finish (c:read_cbor_success_t)
          (#p:perm)
          (#v:erased (raw_data_item))
          (#s:erased (Seq.seq U8.t))
          (#rem:erased (Seq.seq U8.t))
  requires `@((raw_data_item_match c.read_cbor_payload v **
               A.pts_to c.read_cbor_remainder #p rem) @==>
              A.pts_to input #p s) **
            raw_data_item_match c.read_cbor_payload v **
            A.pts_to c.read_cbor_remainder #p rem **
            uds_is_enabled
  returns _:option ctxt_hndl_t
  ensures A.pts_to input #p s
{
   elim_implies ()  #(raw_data_item_match c.read_cbor_payload v **
                            A.pts_to c.read_cbor_remainder #p rem)
                            #(A.pts_to input #p s);
    drop uds_is_enabled;
    None #ctxt_hndl_t
}
```

assume Fits_u64 : squash (SZ.fits_u64)

let impl_session_message : impl_typ Spec.session_message =
  impl_t_array (
    impl_array_group3_concat
      (impl_array_group3_item impl_uint)
      (impl_array_group3_item impl_bytes)
  )

#push-options "--z3rlimit 32"

```pulse
fn initialize_context (len:SZ.t)
                      (input:A.larray U8.t (SZ.v len))
                      (#s:erased (Seq.seq U8.t))
                      (#p:perm)
    requires
        A.pts_to input #p s **
        uds_is_enabled
    returns _:option ctxt_hndl_t
    ensures
        A.pts_to input #p s
{
    let rc = read_deterministically_encoded_cbor_with_typ impl_session_message input len;
    unfold (read_deterministically_encoded_cbor_with_typ_post Spec.session_message input p s rc); 
    match rc
    {
      ParseError ->
      {
        unfold (read_deterministically_encoded_cbor_with_typ_error_post Spec.session_message input p s); //How can this match against the `match ... `
        drop uds_is_enabled;
        None #ctxt_hndl_t
      }
      ParseSuccess c ->
      {
        manurewrite (read_deterministically_encoded_cbor_with_typ_post Spec.session_message input p s rc) (read_deterministically_encoded_cbor_with_typ_success_post Spec.session_message input p s c);
        unfold (read_deterministically_encoded_cbor_with_typ_success_post Spec.session_message input p s c); //How can this match against the `match ... `
        let i0 = cbor_array_index c.read_cbor_payload 0sz;
        let cbor_int = destr_cbor_int64 i0;
        let sid = cbor_int.cbor_int_value;
        elim_implies ();
        let i1 = cbor_array_index c.read_cbor_payload 1sz;
        let cbor_str = destr_cbor_string i1;
        let rc = read_deterministically_encoded_cbor cbor_str.cbor_string_payload (SZ.of_u64 cbor_str.cbor_string_length);
        
        admit();
      }
    }
}
```

#pop-options
