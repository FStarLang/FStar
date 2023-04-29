module Pulse.Parser

val parse_peek_id (contents:string)
                   (r:FStar.Compiler.Range.range)
  : either string
           (string & FStar.Compiler.Range.range)
           
