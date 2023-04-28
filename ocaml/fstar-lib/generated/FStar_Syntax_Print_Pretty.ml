open Prims
let (rfrac : FStar_BaseTypes.float) =
  FStar_Compiler_Util.float_of_string "1.0"
let (width : Prims.int) = (Prims.of_int (100))
let (pp : FStar_Pprint.document -> Prims.string) =
  fun d -> FStar_Pprint.pretty_string rfrac width d
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun tm ->
      FStar_GenSym.with_frozen_gensym
        (fun uu___ ->
           let e = FStar_Syntax_Resugar.resugar_term' env tm in
           let d = FStar_Parser_ToDocument.term_to_document e in pp d)
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      FStar_GenSym.with_frozen_gensym
        (fun uu___ ->
           let e = FStar_Syntax_Resugar.resugar_comp' env c in
           let d = FStar_Parser_ToDocument.term_to_document e in pp d)
let (sigelt_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun env ->
    fun se ->
      FStar_GenSym.with_frozen_gensym
        (fun uu___ ->
           let uu___1 = FStar_Syntax_Resugar.resugar_sigelt' env se in
           match uu___1 with
           | FStar_Pervasives_Native.None -> ""
           | FStar_Pervasives_Native.Some d ->
               let d1 = FStar_Parser_ToDocument.decl_to_document d in pp d1)
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun tm ->
    FStar_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e = FStar_Syntax_Resugar.resugar_term tm in
         let d = FStar_Parser_ToDocument.term_to_document e in pp d)
let (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    FStar_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e = FStar_Syntax_Resugar.resugar_comp c in
         let d = FStar_Parser_ToDocument.term_to_document e in pp d)
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    FStar_GenSym.with_frozen_gensym
      (fun uu___ ->
         let uu___1 = FStar_Syntax_Resugar.resugar_sigelt se in
         match uu___1 with
         | FStar_Pervasives_Native.None -> ""
         | FStar_Pervasives_Native.Some d ->
             let d1 = FStar_Parser_ToDocument.decl_to_document d in pp d1)
let (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    FStar_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e =
           FStar_Syntax_Resugar.resugar_universe u
             FStar_Compiler_Range_Type.dummyRange in
         let d = FStar_Parser_ToDocument.term_to_document e in pp d)
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun ts ->
    FStar_GenSym.with_frozen_gensym
      (fun uu___ ->
         let d = FStar_Syntax_Resugar.resugar_tscheme ts in
         let d1 = FStar_Parser_ToDocument.decl_to_document d in pp d1)
let (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun p ->
    FStar_GenSym.with_frozen_gensym
      (fun uu___ ->
         let e =
           FStar_Syntax_Resugar.resugar_pat p FStar_Syntax_Syntax.no_names in
         let d = FStar_Parser_ToDocument.pat_to_document e in pp d)
let (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow ->
    fun b ->
      FStar_GenSym.with_frozen_gensym
        (fun uu___ ->
           let uu___1 =
             FStar_Syntax_Resugar.resugar_binder b
               FStar_Compiler_Range_Type.dummyRange in
           match uu___1 with
           | FStar_Pervasives_Native.None -> ""
           | FStar_Pervasives_Native.Some e ->
               let d = FStar_Parser_ToDocument.binder_to_document e in pp d)
let (eff_decl_to_string' :
  Prims.bool ->
    FStar_Compiler_Range_Type.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string)
  =
  fun for_free ->
    fun r ->
      fun q ->
        fun ed ->
          FStar_GenSym.with_frozen_gensym
            (fun uu___ ->
               let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed in
               let d1 = FStar_Parser_ToDocument.decl_to_document d in pp d1)