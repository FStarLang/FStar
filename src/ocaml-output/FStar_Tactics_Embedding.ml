open Prims
type name = FStar_Syntax_Syntax.bv
let fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid =
  fun s  -> FStar_Syntax_Const.fstar_tactics_lid' s 
let lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____11 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_All.pipe_right uu____11 FStar_Syntax_Syntax.fv_to_tm
  
let mk_tactic_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____16 = fstar_tactics_lid' ["Effect"; s]  in lid_as_tm uu____16
  
let lid_as_data_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____21 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor)
       in
    FStar_Syntax_Syntax.fv_to_tm uu____21
  
let fstar_tactics_lid_as_data_tm : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____26 = fstar_tactics_lid' ["Effect"; s]  in
    lid_as_data_tm uu____26
  
let fstar_tactics_Failed : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Failed" 
let fstar_tactics_Success : FStar_Syntax_Syntax.term =
  fstar_tactics_lid_as_data_tm "Success" 
let pair_typ :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      let uu____37 =
        let uu____38 =
          let uu____39 = lid_as_tm FStar_Reflection_Basic.lid_tuple2  in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____39
            [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
           in
        let uu____40 =
          let uu____41 = FStar_Syntax_Syntax.as_arg t  in
          let uu____42 =
            let uu____44 = FStar_Syntax_Syntax.as_arg s  in [uu____44]  in
          uu____41 :: uu____42  in
        FStar_Syntax_Syntax.mk_Tm_app uu____38 uu____40  in
      uu____37 None FStar_Range.dummyRange
  
let embed_env :
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun env  -> FStar_Syntax_Util.mk_alien env "tactics_embed_env" None
  
let unembed_env :
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env
  =
  fun ps  ->
    fun t  ->
      let uu____65 = FStar_Syntax_Util.un_alien t  in
      FStar_All.pipe_right uu____65 FStar_Dyn.undyn
  
let embed_proofstate :
  FStar_Tactics_Basic.proofstate -> FStar_Syntax_Syntax.term =
  fun ps  -> FStar_Syntax_Util.mk_alien ps "tactics.embed_proofstate" None 
let unembed_proofstate :
  FStar_Tactics_Basic.proofstate ->
    FStar_Syntax_Syntax.term -> FStar_Tactics_Basic.proofstate
  =
  fun ps  ->
    fun t  ->
      let uu____78 = FStar_Syntax_Util.un_alien t  in
      FStar_All.pipe_right uu____78 FStar_Dyn.undyn
  
let embed_result ps res embed_a t_a =
  match res with
  | FStar_Tactics_Basic.Failed (msg,ps1) ->
      let uu____115 =
        let uu____116 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Failed
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____117 =
          let uu____118 = FStar_Syntax_Syntax.iarg t_a  in
          let uu____119 =
            let uu____121 =
              let uu____122 = FStar_Reflection_Basic.embed_string msg  in
              FStar_Syntax_Syntax.as_arg uu____122  in
            let uu____123 =
              let uu____125 =
                let uu____126 = embed_proofstate ps1  in
                FStar_Syntax_Syntax.as_arg uu____126  in
              [uu____125]  in
            uu____121 :: uu____123  in
          uu____118 :: uu____119  in
        FStar_Syntax_Syntax.mk_Tm_app uu____116 uu____117  in
      uu____115 None FStar_Range.dummyRange
  | FStar_Tactics_Basic.Success (a,ps1) ->
      let uu____133 =
        let uu____134 =
          FStar_Syntax_Syntax.mk_Tm_uinst fstar_tactics_Success
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____135 =
          let uu____136 = FStar_Syntax_Syntax.iarg t_a  in
          let uu____137 =
            let uu____139 =
              let uu____140 = embed_a a  in
              FStar_Syntax_Syntax.as_arg uu____140  in
            let uu____141 =
              let uu____143 =
                let uu____144 = embed_proofstate ps1  in
                FStar_Syntax_Syntax.as_arg uu____144  in
              [uu____143]  in
            uu____139 :: uu____141  in
          uu____136 :: uu____137  in
        FStar_Syntax_Syntax.mk_Tm_app uu____134 uu____135  in
      uu____133 None FStar_Range.dummyRange
  
let unembed_result ps res unembed_a =
  let res1 = FStar_Syntax_Util.unascribe res  in
  let uu____182 = FStar_Syntax_Util.head_and_args res1  in
  match uu____182 with
  | (hd1,args) ->
      let uu____214 =
        let uu____222 =
          let uu____223 = FStar_Syntax_Util.un_uinst hd1  in
          uu____223.FStar_Syntax_Syntax.n  in
        (uu____222, args)  in
      (match uu____214 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(a,uu____240)::(embedded_state,uu____242)::[]) when
           let uu____276 = fstar_tactics_lid' ["Effect"; "Success"]  in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____276 ->
           let uu____277 =
             let uu____280 = unembed_a a  in
             let uu____281 = unembed_proofstate ps embedded_state  in
             (uu____280, uu____281)  in
           FStar_Util.Inl uu____277
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(embedded_string,uu____289)::(embedded_state,uu____291)::[])
           when
           let uu____325 = fstar_tactics_lid' ["Effect"; "Failed"]  in
           FStar_Syntax_Syntax.fv_eq_lid fv uu____325 ->
           let uu____326 =
             let uu____329 =
               FStar_Reflection_Basic.unembed_string embedded_string  in
             let uu____330 = unembed_proofstate ps embedded_state  in
             (uu____329, uu____330)  in
           FStar_Util.Inr uu____326
       | uu____335 ->
           let uu____343 =
             let uu____344 = FStar_Syntax_Print.term_to_string res1  in
             FStar_Util.format1 "Not an embedded result: %s" uu____344  in
           failwith uu____343)
  