module FStarC.Basefiles

open FStarC
open FStarC.Effect

module O  = FStarC.Options
module BU = FStarC.Util
module E  = FStarC.Errors

let must_find (fn:string) : string =
  match Find.find_file fn with
  | Some f -> f
  | None ->
    E.raise_error0 E.Fatal_ModuleNotFound [
      E.text (BU.format1 "Unable to find required file \"%s\" in the module search path." fn);
    ]

let prims () =
  match O.custom_prims() with
  | Some fn -> fn (* user-specified prims *)
  | None -> must_find "Prims.fst"

let prims_basename () = BU.basename (prims ())
let pervasives () = must_find "FStar.Pervasives.fsti"
let pervasives_basename () = BU.basename (pervasives ())
let pervasives_native_basename () = must_find "FStar.Pervasives.Native.fst" |> BU.basename
