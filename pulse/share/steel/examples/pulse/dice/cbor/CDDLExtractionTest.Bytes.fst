module CDDLExtractionTest.Bytes
open Pulse.Lib.Pervasives
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

    let unused : bool = impl_bytes c; // this also typechecks, but does not extract either
    ()
}
```
