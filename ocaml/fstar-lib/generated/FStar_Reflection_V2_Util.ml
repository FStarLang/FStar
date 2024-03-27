open Prims
let (unfold_quotation :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.quoteinfo -> FStar_Syntax_Syntax.term)
  =
  fun qt ->
    fun qi ->
      match qi with
      | { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
          FStar_Syntax_Syntax.antiquotations = (shift, aqs);_} ->
          let uu___ = FStar_Reflection_V2_Builtins.inspect_ln qt in
          (match uu___ with
           | FStar_Reflection_V2_Data.Tv_BVar bv when
               bv.FStar_Syntax_Syntax.index < shift ->
               let tv' = FStar_Reflection_V2_Data.Tv_BVar bv in
               let tv =
                 let uu___1 =
                   FStar_Syntax_Embeddings_Base.embed
                     FStar_Reflection_V2_Embeddings.e_term_view tv' in
                 uu___1 qt.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None
                   FStar_Syntax_Embeddings_Base.id_norm_cb in
               let t =
                 let uu___1 =
                   let uu___2 = FStar_Syntax_Syntax.as_arg tv in [uu___2] in
                 FStar_Syntax_Util.mk_app
                   (FStar_Reflection_V2_Constants.refl_constant_term
                      FStar_Reflection_V2_Constants.fstar_refl_pack_ln)
                   uu___1 in
               t
           | FStar_Reflection_V2_Data.Tv_BVar bv ->
               let tm = FStar_Syntax_Syntax.lookup_aq bv (shift, aqs) in tm
           | tv ->
               let tv1 =
                 let uu___1 =
                   let uu___2 =
                     FStar_Reflection_V2_Embeddings.e_term_view_aq
                       (shift, aqs) in
                   FStar_Syntax_Embeddings_Base.embed uu___2 tv in
                 uu___1 qt.FStar_Syntax_Syntax.pos
                   FStar_Pervasives_Native.None
                   FStar_Syntax_Embeddings_Base.id_norm_cb in
               let t =
                 let uu___1 =
                   let uu___2 = FStar_Syntax_Syntax.as_arg tv1 in [uu___2] in
                 FStar_Syntax_Util.mk_app
                   (FStar_Reflection_V2_Constants.refl_constant_term
                      FStar_Reflection_V2_Constants.fstar_refl_pack_ln)
                   uu___1 in
               t)