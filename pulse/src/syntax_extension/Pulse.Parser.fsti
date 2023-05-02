module Pulse.Parser

val parse_peek_id (contents:string)
                  (r:FStar.Compiler.Range.range)
  : either string
           (string & FStar.Compiler.Range.range)

val parse_decl (contents:string)
               (r:FStar.Compiler.Range.range)
  : either ParseSugar.decl
           (string & FStar.Compiler.Range.range)

