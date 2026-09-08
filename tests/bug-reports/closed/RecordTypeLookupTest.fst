module RecordTypeLookupTest

open RecordTypeLookupModA
open RecordTypeLookupModB

let a () : int =
  let open val_a <: RecordTypeLookupModA.shared_t in
  target

let _ = assert_norm (a () == 111)