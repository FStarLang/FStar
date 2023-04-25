module PulseASTBuilder
open FStar.Parser.AST
open FStar.Parser.AST.Util
module BU = FStar.Compiler.Util
module List = FStar.Compiler.List
let extension_parser ctx contents rng =
  match Pulse.Parser.parse contents rng with
  | Inr (err, r) ->
      Inl { message = err; range = r }

  | Inl pulse_ast -> 
      BU.print_string "Successfully parsed pulse term!\n";
      Inl { message = "not yet"; range = rng }

let _ = 
    register_extension_parser "pulse" extension_parser
