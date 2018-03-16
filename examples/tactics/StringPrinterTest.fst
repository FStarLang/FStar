module StringPrinterTest

module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module SP = StringPrinterTest.Aux
module U8 = FStar.UInt8
module HS = FStar.HyperStack

let test3 (x: U32.t) : HST.ST (option (B.buffer U8.t))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    match res with
    | None -> h' == h
    | Some b -> SP.buffer_create_mm_post HS.root h h' b
  ))
= SP.example_test x

let print_list_cipher_suite (x: list SP.cipher_suite) : HST.ST (option (B.buffer U8.t))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    match res with
    | None -> h' == h
    | Some b -> SP.buffer_create_mm_post HS.root h h' b
  ))
= SP.print_list_cipher_suite x

// krml -tmpdir ou -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
