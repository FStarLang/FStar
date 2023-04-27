module Pulse.Parser

val parse (contents:string)
          (r:FStar.Compiler.Range.range)
  : either FStar.Parser.AST.decl //Pulse.Syntax.st_term
           (string & FStar.Compiler.Range.range)
           
