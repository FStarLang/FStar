open Prims
let (must_find : Prims.string -> Prims.string) =
  fun fn ->
    let uu___ = FStarC_Find.find_file fn in
    match uu___ with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_Util.format1
                "Unable to find required file \"%s\" in the module search path."
                fn in
            FStarC_Errors_Msg.text uu___3 in
          [uu___2] in
        FStarC_Errors.raise_error0 FStarC_Errors_Codes.Fatal_ModuleNotFound
          () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___1)
let (prims : unit -> Prims.string) =
  fun uu___ ->
    let uu___1 = FStarC_Options.custom_prims () in
    match uu___1 with
    | FStar_Pervasives_Native.Some fn -> fn
    | FStar_Pervasives_Native.None -> must_find "Prims.fst"
let (prims_basename : unit -> Prims.string) =
  fun uu___ -> let uu___1 = prims () in FStarC_Compiler_Util.basename uu___1
let (pervasives : unit -> Prims.string) =
  fun uu___ -> must_find "FStar.Pervasives.fsti"
let (pervasives_basename : unit -> Prims.string) =
  fun uu___ ->
    let uu___1 = pervasives () in FStarC_Compiler_Util.basename uu___1
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu___ ->
    let uu___1 = must_find "FStar.Pervasives.Native.fst" in
    FStarC_Compiler_Util.basename uu___1