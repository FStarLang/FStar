module FStar.TypeChecker.Primops.Errors.Msg

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Class.Monad

module Z = FStar.BigInt
module PC = FStar.Parser.Const

open FStar.TypeChecker.Primops.Base

let ops =
  let nm l = PC.p2l ["FStar"; "Stubs"; "Errors"; "Msg"; l] in
  let open FStar.Errors.Msg in
    [
      mk1 0 (nm "text") text;
      mk2 0 (nm "sublist") sublist;
      mk1 0 (nm "bulleted") bulleted;
      mk1 0 (nm "mkmsg") mkmsg;
      mk1 0 (nm "subdoc") subdoc;
      mk1 0 (nm "renderdoc") renderdoc;
      mk1 0 (nm "backtrace_doc") backtrace_doc;
      mk1 0 (nm "rendermsg") rendermsg;
    ]
