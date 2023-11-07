module CDDLExtractionTest.Assume
open CBOR.Spec
open CDDL.Spec
open CBOR.Pulse
open CDDL.Pulse

assume val mytype: typ

assume val impl_mytype: impl_typ mytype

```pulse
fn test
    (c: cbor)
    (v: Ghost.erased raw_data_item)
requires
    raw_data_item_match full_perm c v
ensures
    raw_data_item_match full_perm c v
{
    let unused = eval_impl_typ impl_mytype c;
    ()
}
```
