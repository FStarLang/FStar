module CDDLExtractionTest.Bytes
open Pulse.Lib.Pervasives
open CBOR.Spec
open CDDL.Spec
open CBOR.Pulse
open CDDL.Pulse

inline_for_extraction noextract [@@noextract_to "krml"]
let impl_mytype = impl_bytes

noextract inline_for_extraction [@@noextract_to "krml"]
val perform
  (#a #pre #post : _)
  (f : unit -> stt a pre post)
  : stt a pre post
let perform f = f ()

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
    let unused = perform (fun () ->  impl_bytes c #full_perm #v);
    ()
}
```
