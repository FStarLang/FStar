open Prims
let (find_deps_if_needed :
  Prims.string Prims.list ->
    (Prims.string ->
       FStarC_Parser_Dep.parsing_data FStar_Pervasives_Native.option)
      -> (Prims.string Prims.list * FStarC_Parser_Dep.deps))
  =
  fun files ->
    fun get_parsing_data_from_cache ->
      let uu___ = FStarC_Parser_Dep.collect files get_parsing_data_from_cache in
      match uu___ with
      | (all_files, deps) ->
          (match all_files with
           | [] ->
               (FStarC_Errors.log_issue0
                  FStarC_Errors_Codes.Error_DependencyAnalysisFailed ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                  (Obj.magic
                     "Dependency analysis failed; reverting to using only the files provided");
                (files, deps))
           | uu___1 -> ((FStarC_Compiler_List.rev all_files), deps))