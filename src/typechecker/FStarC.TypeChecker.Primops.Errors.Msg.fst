module FStarC.TypeChecker.Primops.Errors.Msg

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Monad

module PC = FStarC.Parser.Const

open FStarC.TypeChecker.Primops.Base

let ops =
  let nm l = PC.p2l ["FStar"; "Errors"; "Msg"; l] in
  let open FStarC.Errors.Msg in
    [
      mk1 0 (nm "text") text;
      mk1 0 (nm "mkmsg") mkmsg;
    ]
