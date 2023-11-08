module CDDLExtractionTest.BytesVeryDirect
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
    let unused' = impl_bytes' c; // this extracts well, but this is still not desirable unless and until the type for impl_bytes' can be abbreviated. See also the BytesDirect test, which fails even with one layer of definition.
    // let unused = impl_bytes c;
    ()
}
```
