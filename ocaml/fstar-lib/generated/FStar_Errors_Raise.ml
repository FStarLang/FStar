open Prims
let error :
  'a .
    (FStar_Errors_Codes.raw_error * Prims.string) ->
      FStar_Compiler_Range_Type.range -> 'a
  = FStar_Errors.raise_error
let err : 'a . (FStar_Errors_Codes.raw_error * Prims.string) -> 'a =
  FStar_Errors.raise_err
let error_doc :
  'a .
    (FStar_Errors_Codes.raw_error * FStar_Errors_Msg.error_message) ->
      FStar_Compiler_Range_Type.range -> 'a
  = FStar_Errors.raise_error_doc
let err_doc :
  'a . (FStar_Errors_Codes.raw_error * FStar_Errors_Msg.error_message) -> 'a
  = FStar_Errors.raise_err_doc
let (ttd : FStar_Syntax_Syntax.term -> FStar_Pprint.document) =
  FStar_Syntax_Print.pretty_term.FStar_Class_PP.pp
let (str : Prims.string -> FStar_Pprint.document) =
  FStar_Pprint.doc_of_string