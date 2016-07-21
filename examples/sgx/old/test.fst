module Test

open FStar.UInt64
open Ast
open FStar.List


val interpret: stmt -> (sgxmem->u64) -> (lowsgxmem->u64) ->((sgxmem->u64)*(lowsgxmem->u64))
let rec interpret (progstmt:stmt) (sgxenv:sgxmem->u64) (lowsgxenv:lowsgxmem->u64) = begin match progstmt with
  | Skip -> (sgxenv, lowsgxenv)
  | _   ->(sgxenv, lowsgxenv)
end

