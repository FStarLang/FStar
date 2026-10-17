(* Model implementation of FStar.Errors.Msg: verified, but never extracted (the real implementation is native). *)
module FStar.Errors.Msg

open FStar.Pprint

let text s = arbitrary_string s
let mkmsg s = [doc_of_string s]
