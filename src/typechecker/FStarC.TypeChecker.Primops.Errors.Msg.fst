module FStarC.TypeChecker.Primops.Errors.Msg

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Monad

module PC = FStarC.Parser.Const

open FStarC.TypeChecker.Primops.Base

let ops =
  let nm l = PC.p2l ["FStar"; "Stubs"; "Errors"; "Msg"; l] in
  let open FStarC.Errors.Msg in
    [
      mk1 0 (nm "text") text;
      mk2' 0 (nm "sublist")
        (fun b es -> Some (sublist b es))
        (fun b es -> Some (sublist b es));
      mk1' 0 (nm "bulleted")
        (fun l -> Some (bulleted l))
        (fun l -> Some (bulleted l));
      mk1 0 (nm "mkmsg") mkmsg;
      mk1 0 (nm "subdoc") subdoc;
      mk1' 0 (nm "renderdoc")
        (fun d -> Some (renderdoc d))
        (fun d -> Some (renderdoc d));
      mk1' 0 (nm "backtrace_doc")
        (fun () -> Some (backtrace_doc ()))
        (fun () -> Some (backtrace_doc ()));
      mk1' 0 (nm "rendermsg")
        (fun m -> Some (rendermsg m))
        (fun m -> Some (rendermsg m));
    ]
