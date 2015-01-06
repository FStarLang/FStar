module IlltypedUntrustedClientCode
  open System.IO
  let passwd  = "C:/etc/password"
  let readme  = "C:/public/README"
  let tmp     = "C:/temp/tempfile"

// BEGIN: DoIt
  let doit () =
    let v1 = read tmp in
    let v2 = read readme in
    let v3 = read passwd in
    write tmp "hello!";
    write passwd "junk";
    ()
// END: DoIt
