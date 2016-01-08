(*--build-config
    options:--z3timeout 10 --verify_module Cap --admit_fsi FStar.Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:CONTRIB=../../contrib;
    other-files:
            FStar.FunctionalExtensionality.fst FStar.Classical.fst
            FStar.Set.fsi FStar.Set.fst
            FStar.Heap.fst FStar.ST.fst FStar.All.fst
            FStar.String.fst FStar.List.fst
            seq.fsi FStar.SeqProperties.fst
            $CONTRIB/Platform/fst/Bytes.fst
            $CONTRIB/CoreCrypto/fst/CoreCrypto.fst
            sha1.fst
            mac.fst
            ../security/acls2.fst
  --*)


(* to be used with mac.fst and acls2.fst *)

module Cap (* capabilities *)
open FStar.Seq
open FStar.SeqProperties
open ACLs2
open MAC

//does it verify for trivial reasons, like a bug in the build-config?
(*let testme () =
   assert False*)


assume val utf8: s:string  -> Tot (seq byte)

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    (utf8 s0) == (utf8 s1) ==> s0==s1

opaque logic type CapRead (msg:seq byte) =
    (forall f. msg = utf8 f ==> canRead f)

let k = keygen CapRead

val issue: f:file{ canRead f } -> SHA1.tag
val redeem: f:file -> m:SHA1.tag -> u:unit{ canRead f }

let issue f = MAC.mac k (utf8 f)
let redeem f t = if MAC.verify k (utf8 f) t then () else failwith "bad capability"
(* check_marker *)
