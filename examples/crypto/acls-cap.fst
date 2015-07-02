(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module Pad --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:LIB=../../lib;
    other-files:$LIB/string.fst $LIB/list.fst
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst
            $LIB/seq.fsi $LIB/seqproperties.fst
            sha1.fst
            mac.fst
            ../security/acls2.fst
  --*)


(* to be used with mac.fst and acls2.fst *)

module Cap (* capabilities *)
open Seq
open SeqProperties
open ACLs2
open MAC

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
