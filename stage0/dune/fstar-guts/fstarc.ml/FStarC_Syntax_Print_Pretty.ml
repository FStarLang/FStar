open Prims
let rfrac : FStarC_BaseTypes.float= FStarC_Util.float_of_string "1.0"
let width : Prims.int= (Prims.of_int (100))
let pp (d : FStar_Pprint.document) : Prims.string=
  FStarC_Pprint.pretty_string rfrac width d
let term_to_doc' (env : FStarC_Syntax_DsEnv.env)
  (tm : FStarC_Syntax_Syntax.term) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e = FStarC_Syntax_Resugar.resugar_term' env tm in
       FStarC_Parser_ToDocument.term_to_document e)
let univ_to_doc' (env : FStarC_Syntax_DsEnv.env)
  (u : FStarC_Syntax_Syntax.universe) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e =
         FStarC_Syntax_Resugar.resugar_universe' env u
           FStarC_Range_Type.dummyRange in
       FStarC_Parser_ToDocument.term_to_document e)
let term_to_string' (env : FStarC_Syntax_DsEnv.env)
  (tm : FStarC_Syntax_Syntax.term) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ -> let d = term_to_doc' env tm in pp d)
let univ_to_string' (env : FStarC_Syntax_DsEnv.env)
  (u : FStarC_Syntax_Syntax.universe) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ -> let d = univ_to_doc' env u in pp d)
let comp_to_doc' (env : FStarC_Syntax_DsEnv.env)
  (c : FStarC_Syntax_Syntax.comp) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e = FStarC_Syntax_Resugar.resugar_comp' env c in
       FStarC_Parser_ToDocument.term_to_document e)
let comp_to_string' (env : FStarC_Syntax_DsEnv.env)
  (c : FStarC_Syntax_Syntax.comp) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ -> let d = comp_to_doc' env c in pp d)
let sigelt_to_doc' (env : FStarC_Syntax_DsEnv.env)
  (se : FStarC_Syntax_Syntax.sigelt) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let uu___1 = FStarC_Syntax_Resugar.resugar_sigelt' env se in
       match uu___1 with
       | FStar_Pervasives_Native.None -> FStar_Pprint.empty
       | FStar_Pervasives_Native.Some d ->
           FStarC_Parser_ToDocument.decl_to_document d)
let sigelt_to_string' (env : FStarC_Syntax_DsEnv.env)
  (se : FStarC_Syntax_Syntax.sigelt) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ -> let d = sigelt_to_doc' env se in pp d)
let term_to_doc (tm : FStarC_Syntax_Syntax.term) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e = FStarC_Syntax_Resugar.resugar_term tm in
       FStarC_Parser_ToDocument.term_to_document e)
let univ_to_doc (u : FStarC_Syntax_Syntax.universe) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e =
         FStarC_Syntax_Resugar.resugar_universe u
           FStarC_Range_Type.dummyRange in
       FStarC_Parser_ToDocument.term_to_document e)
let comp_to_doc (c : FStarC_Syntax_Syntax.comp) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e = FStarC_Syntax_Resugar.resugar_comp c in
       FStarC_Parser_ToDocument.term_to_document e)
let sigelt_to_doc (se : FStarC_Syntax_Syntax.sigelt) : FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let uu___1 = FStarC_Syntax_Resugar.resugar_sigelt se in
       match uu___1 with
       | FStar_Pervasives_Native.None -> FStar_Pprint.empty
       | FStar_Pervasives_Native.Some d ->
           FStarC_Parser_ToDocument.decl_to_document d)
let term_to_string (tm : FStarC_Syntax_Syntax.term) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ -> let d = term_to_doc tm in pp d)
let comp_to_string (c : FStarC_Syntax_Syntax.comp) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e = FStarC_Syntax_Resugar.resugar_comp c in
       let d = FStarC_Parser_ToDocument.term_to_document e in pp d)
let sigelt_to_string (se : FStarC_Syntax_Syntax.sigelt) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let uu___1 = FStarC_Syntax_Resugar.resugar_sigelt se in
       match uu___1 with
       | FStar_Pervasives_Native.None -> ""
       | FStar_Pervasives_Native.Some d ->
           let d1 = FStarC_Parser_ToDocument.decl_to_document d in pp d1)
let univ_to_string (u : FStarC_Syntax_Syntax.universe) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e =
         FStarC_Syntax_Resugar.resugar_universe u
           FStarC_Range_Type.dummyRange in
       let d = FStarC_Parser_ToDocument.term_to_document e in pp d)
let tscheme_to_doc (ts : FStarC_Syntax_Syntax.tscheme) :
  FStar_Pprint.document=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let d = FStarC_Syntax_Resugar.resugar_tscheme ts in
       FStarC_Parser_ToDocument.decl_to_document d)
let tscheme_to_string (ts : FStarC_Syntax_Syntax.tscheme) : Prims.string=
  let uu___ = tscheme_to_doc ts in pp uu___
let pat_to_string (p : FStarC_Syntax_Syntax.pat) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e =
         let uu___1 =
           Obj.magic
             (FStarC_Class_Setlike.empty ()
                (Obj.magic
                   (FStarC_FlatSet.setlike_flat_set
                      FStarC_Syntax_Syntax.ord_bv)) ()) in
         FStarC_Syntax_Resugar.resugar_pat p uu___1 in
       let d = FStarC_Parser_ToDocument.pat_to_document e in pp d)
let binder_to_string' (is_arrow : Prims.bool)
  (b : FStarC_Syntax_Syntax.binder) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let e =
         FStarC_Syntax_Resugar.resugar_binder b FStarC_Range_Type.dummyRange in
       let d = FStarC_Parser_ToDocument.binder_to_document e in pp d)
let eff_decl_to_string (ed : FStarC_Syntax_Syntax.eff_decl) : Prims.string=
  FStarC_GenSym.with_frozen_gensym
    (fun uu___ ->
       let d = FStarC_Syntax_Resugar.resugar_eff_decl ed in
       let d1 = FStarC_Parser_ToDocument.decl_to_document d in pp d1)
