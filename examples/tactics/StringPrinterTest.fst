module StringPrinterTest

module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module SP = StringPrinter.RecC

let test (x: U32.t) : HST.ST unit (requires (fun _ -> True)) (ensures (fun h _ h' -> B.modifies_0 h h')) =
  SP.test x

let test2 (x: U32.t) : Tot (option U32.t) =
  SP.test_len x

let test3 (x: U32.t) : HST.ST (option unit) (requires (fun _ -> True)) (ensures (fun h _ h' -> B.modifies_0 h h')) =
  SP.example_test x

// krml -tmpdir ou -bundle 'StringPrinter.*' -drop 'FStar.Tactics.*' -drop 'FStar.Reflection.*' StringPrinterTest.fst -dast -skip-linking
