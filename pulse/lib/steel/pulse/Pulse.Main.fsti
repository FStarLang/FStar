module Pulse.Main
module RT = FStar.Reflection.Typing

[@@plugin]
val check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : RT.dsl_tac_t