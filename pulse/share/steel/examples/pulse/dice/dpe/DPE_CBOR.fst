module DPE_CBOR
open Pulse.Lib.Pervasives
open DPE
open CBOR.Spec
open CBOR.Pulse
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
  requires `@((raw_data_item_match full_perm c.read_cbor_payload v **
               A.pts_to c.read_cbor_remainder #p rem) @==>
              A.pts_to input #p s) **
            raw_data_item_match full_perm c.read_cbor_payload v **
            A.pts_to c.read_cbor_remainder #p rem **
            uds_is_enabled
  returns _:option ctxt_hndl_t
  ensures A.pts_to input #p s
{
   elim_implies ()  #(raw_data_item_match full_perm c.read_cbor_payload v **
                            A.pts_to c.read_cbor_remainder #p rem)
                            #(A.pts_to input #p s);
    drop uds_is_enabled;
    None #ctxt_hndl_t
}
```

assume Fits_u64 : squash (SZ.fits_u64)

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
    let rc = read_cbor input len;
    unfold (read_cbor_post input p s rc); 
    match rc
    {
      ParseError ->
      {
        unfold (read_cbor_error_post input p s); //How can this match against the `match ... `
        drop uds_is_enabled;
        None #ctxt_hndl_t
      }
      ParseSuccess c ->
      {
        unfold (read_cbor_success_post input p s c); //How can this match against the `match ... `
        with v. assert (raw_data_item_match full_perm c.read_cbor_payload v);
        with rem. assert (A.pts_to c.read_cbor_remainder #p rem);
        let major_type = cbor_get_major_type c.read_cbor_payload;
        if (major_type = major_type_array)
        {
            let arr_len = cbor_array_length c.read_cbor_payload;
            if (arr_len = 2uL)
            {
                let i0 = cbor_array_index c.read_cbor_payload 0sz;
                let major_type = cbor_get_major_type i0;
                if (major_type = major_type_uint64)
                {
                    let cbor_int = destr_cbor_int64 i0;
                    let sid = cbor_int.cbor_int_value;
                    with va'. assert (raw_data_item_match full_perm i0 va');
                    elim_implies () #(raw_data_item_match full_perm i0 va') #(raw_data_item_match full_perm c.read_cbor_payload v);
                    let i1 = cbor_array_index c.read_cbor_payload 1sz;
                    let major_type = cbor_get_major_type i1;
                    if (major_type = major_type_byte_string)
                    {
                        
                        let cbor_str = destr_cbor_string i1;
                        let rc = read_cbor cbor_str.cbor_string_payload (SZ.of_u64 cbor_str.cbor_string_length);
                        
                        admit();
                        // let bs = cbor_bs.cbor_byte_string_value;
                        // with va''. assert (raw_data_item_match i1 va'');
                        // elim_implies () #(raw_data_item_match i1 va'') #(raw_data_item_match c.read_cbor_payload v);
                        // let ctx = mk_context sid bs;
                        // let ctx_hndl = alloc_context ctx;
                        // let c
                    }   
                    else 
                    {
                        admit()
                    }
                }
                else {
                    admit()
                }
            }
            else 
            {
                elim_implies ()  #(raw_data_item_match full_perm c.read_cbor_payload v **
                                A.pts_to c.read_cbor_remainder #p rem)
                                #(A.pts_to input #p s);
                drop uds_is_enabled;
                None #ctxt_hndl_t
            }
        }
        else
        {
            // finish c #p #v #rem #s
            // elim_implies (); this could work, except this has a ** on the left of the @==>
            //                  which remains uninterpreted by Pulse and then unification fails
            elim_implies ()  #(raw_data_item_match full_perm c.read_cbor_payload v **
                            A.pts_to c.read_cbor_remainder #p rem)
                            #(A.pts_to input #p s);
            drop uds_is_enabled;
            None #ctxt_hndl_t
        }
      }
    }
}
```


