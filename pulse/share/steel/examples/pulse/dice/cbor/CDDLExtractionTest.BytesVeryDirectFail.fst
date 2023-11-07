module CDDLExtractionTest.BytesVeryDirectFail
open CBOR.Spec
open CDDL.Spec
open CBOR.Pulse
open CDDL.Pulse

```pulse
fn test
    (c: cbor)
    (v: Ghost.erased raw_data_item)
requires
    raw_data_item_match full_perm c v
ensures
    raw_data_item_match full_perm c v
{
    let unused = impl_bytes c; // successfully typechecks, but fails to extract
    ()
}
```
