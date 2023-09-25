module FStar.Errors.Raise

include FStar.Errors
include FStar.Errors.Msg
include FStar.Errors.Codes
include FStar.Pprint
module Range = FStar.Compiler.Range

val error     : (raw_error & string) -> Range.range -> 'a
val err       : (raw_error & string) -> 'a
val error_doc : (raw_error & error_message) -> Range.range -> 'a
val err_doc   : (raw_error & error_message) -> 'a

val ttd : Syntax.Syntax.term -> document
val str : string -> document
