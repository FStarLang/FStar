module Pulse.ASTBuilder
module R = FStar.Reflection
val parse_pulse (env:R.env) 
                (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : Dv (either Pulse.Syntax.st_term (option (string & R.range)))
  // Option can be empty if all errors were already logged.
