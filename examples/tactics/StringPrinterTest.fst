module StringPrinterTest

module U32 = FStar.UInt32

let test (x: U32.t) : Tot (option (U32.t)) = 
  StringPrinter.test x

// krml -tmpdir ou -bundle StringPrinter -drop 'FStar.Tactics.*' -drop 'FStar.Reflection.*' StringPrinterTest.fst -dast -skip-linking
