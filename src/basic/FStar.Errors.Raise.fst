module FStar.Errors.Raise

include FStar.Errors
include FStar.Errors.Msg
include FStar.Errors.Codes
include FStar.Pprint
module Range = FStar.Compiler.Range
module SP = FStar.Syntax.Print

let error     = raise_error
let err       = raise_err
let error_doc = raise_error_doc
let err_doc   = raise_err_doc

let ttd = SP.pretty_term.pp
let str = Pprint.doc_of_string
