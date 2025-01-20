open Prims
let (rfrac : FStarC_BaseTypes.float) =
  FStarC_Compiler_Util.float_of_string "1.0"
let (width : Prims.int) = (Prims.of_int (100))
let (pp : FStarC_Pprint.document -> Prims.string) =
  fun d -> FStarC_Pprint.pretty_string rfrac width d
let (term_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Pprint.document)
  =
  fun env ->
    fun tm ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let e = FStarC_Syntax_Resugar.resugar_term' env tm in
           FStarC_Parser_ToDocument.term_to_document e)
let (univ_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.universe -> FStarC_Pprint.document)
  =
  fun env ->
    fun u ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let e =
             FStarC_Syntax_Resugar.resugar_universe' env u
               FStarC_Compiler_Range_Type.dummyRange in
           FStarC_Parser_ToDocument.term_to_document e)
let (term_to_string' :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun tm ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ -> let d = term_to_doc' env tm in pp d)
let (univ_to_string' :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.universe -> Prims.string) =
  fun env ->
    fun u ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ -> let d = univ_to_doc' env u in pp d)
let (comp_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.comp -> FStarC_Pprint.document)
  =
  fun env ->
    fun c ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let e = FStarC_Syntax_Resugar.resugar_comp' env c in
           FStarC_Parser_ToDocument.term_to_document e)
let (comp_to_string' :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ -> let d = comp_to_doc' env c in pp d)
let (sigelt_to_doc' :
  FStarC_Syntax_DsEnv.env ->
    FStarC_Syntax_Syntax.sigelt -> FStarC_Pprint.document)
  =
  fun env ->
    fun se ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let uu___1 = FStarC_Syntax_Resugar.resugar_sigelt' env se in
           match uu___1 with
           | FStar_Pervasives_Native.None -> FStarC_Pprint.empty
           | FStar_Pervasives_Native.Some d ->
               FStarC_Parser_ToDocument.decl_to_document d)
let (sigelt_to_string' :
  FStarC_Syntax_DsEnv.env -> FStarC_Syntax_Syntax.sigelt -> Prims.string) =
  fun env ->
    fun se ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ -> let d = sigelt_to_doc' env se in pp d)
let (term_to_doc : FStarC_Syntax_Syntax.term -> FStarC_Pprint.document) =
  fun tm ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e = FStarC_Syntax_Resugar.resugar_term tm in
         FStarC_Parser_ToDocument.term_to_document e)
let (univ_to_doc : FStarC_Syntax_Syntax.universe -> FStarC_Pprint.document) =
  fun u ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e =
           FStarC_Syntax_Resugar.resugar_universe u
             FStarC_Compiler_Range_Type.dummyRange in
         FStarC_Parser_ToDocument.term_to_document e)
let (comp_to_doc : FStarC_Syntax_Syntax.comp -> FStarC_Pprint.document) =
  fun c ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e = FStarC_Syntax_Resugar.resugar_comp c in
         FStarC_Parser_ToDocument.term_to_document e)
let (sigelt_to_doc : FStarC_Syntax_Syntax.sigelt -> FStarC_Pprint.document) =
  fun se ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let uu___1 = FStarC_Syntax_Resugar.resugar_sigelt se in
         match uu___1 with
         | FStar_Pervasives_Native.None -> FStarC_Pprint.empty
         | FStar_Pervasives_Native.Some d ->
             FStarC_Parser_ToDocument.decl_to_document d)
let (term_to_string : FStarC_Syntax_Syntax.term -> Prims.string) =
  fun tm ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ -> let d = term_to_doc tm in pp d)
let (comp_to_string : FStarC_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e = FStarC_Syntax_Resugar.resugar_comp c in
         let d = FStarC_Parser_ToDocument.term_to_document e in pp d)
let (sigelt_to_string : FStarC_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let uu___1 = FStarC_Syntax_Resugar.resugar_sigelt se in
         match uu___1 with
         | FStar_Pervasives_Native.None -> ""
         | FStar_Pervasives_Native.Some d ->
             let d1 = FStarC_Parser_ToDocument.decl_to_document d in pp d1)
let (univ_to_string : FStarC_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e =
           FStarC_Syntax_Resugar.resugar_universe u
             FStarC_Compiler_Range_Type.dummyRange in
         let d = FStarC_Parser_ToDocument.term_to_document e in pp d)
let (tscheme_to_string : FStarC_Syntax_Syntax.tscheme -> Prims.string) =
  fun ts ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let d = FStarC_Syntax_Resugar.resugar_tscheme ts in
         let d1 = FStarC_Parser_ToDocument.decl_to_document d in pp d1)
let (pat_to_string : FStarC_Syntax_Syntax.pat -> Prims.string) =
  fun p ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e =
           let uu___1 =
             Obj.magic
               (FStarC_Class_Setlike.empty ()
                  (Obj.magic
                     (FStarC_Compiler_FlatSet.setlike_flat_set
                        FStarC_Syntax_Syntax.ord_bv)) ()) in
           FStarC_Syntax_Resugar.resugar_pat p uu___1 in
         let d = FStarC_Parser_ToDocument.pat_to_document e in pp d)
let (binder_to_string' :
  Prims.bool -> FStarC_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow ->
    fun b ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let e =
             FStarC_Syntax_Resugar.resugar_binder b
               FStarC_Compiler_Range_Type.dummyRange in
           let d = FStarC_Parser_ToDocument.binder_to_document e in pp d)
let (eff_decl_to_string : FStarC_Syntax_Syntax.eff_decl -> Prims.string) =
  fun ed ->
    FStarC_GenSym.with_frozen_gensym
      (fun uu___ ->
         let d = FStarC_Syntax_Resugar.resugar_eff_decl ed in
         let d1 = FStarC_Parser_ToDocument.decl_to_document d in pp d1)