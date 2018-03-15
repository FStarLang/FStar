module StringPrinterTest

module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module SP = StringPrinterTest.Aux

let test3 (x: U32.t) : HST.ST (option unit) (requires (fun _ -> True)) (ensures (fun h _ h' -> B.modifies_0 h h')) =
  SP.example_test x

// krml -tmpdir ou -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
