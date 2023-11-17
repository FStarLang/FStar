module CDDLExtractionTest.Bytes
open Pulse.Lib.Pervasives
open CBOR.Spec
open CDDL.Spec
open CBOR.Pulse
open CDDL.Pulse

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_mytype = impl_bytes ()

```pulse
fn test
    (c: cbor)
    (v: Ghost.erased raw_data_item)
requires
    raw_data_item_match full_perm c v
ensures
    raw_data_item_match full_perm c v
{
    // let unused = eval_impl_typ impl_mytype c; // this also typechecks, but does not extract either
    let unused = impl_bytes () c;
    ()
}
```
