module PulseASTBuilder
open FStar.Parser.AST
open FStar.Parser.AST.Util
open FStar.Ident
module BU = FStar.Compiler.Util
module List = FStar.Compiler.List
module A = FStar.Parser.AST

let extension_parser ctx contents rng =
  match Pulse.Parser.parse_peek_id contents rng with
  | Inr (err, r) ->
       Inl { message = err; range = r }

  | Inl id ->
      BU.print1 "Successfully peeked at fn %s!\n" id;
      Inl { message = "not yet"; range = rng }

let _ = 
    register_extension_parser "pulse" extension_parser
