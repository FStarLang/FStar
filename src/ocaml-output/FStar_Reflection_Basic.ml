open Prims
let lid_as_tm : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____5 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
       in
    FStar_All.pipe_right uu____5 FStar_Syntax_Syntax.fv_to_tm
  
let fstar_refl_embed : FStar_Syntax_Syntax.term =
  lid_as_tm FStar_Parser_Const.fstar_refl_embed_lid 
let protect_embedded_term :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____16 =
        let uu____17 =
          let uu____18 = FStar_Syntax_Syntax.iarg t  in
          let uu____19 =
            let uu____22 = FStar_Syntax_Syntax.as_arg x  in [uu____22]  in
          uu____18 :: uu____19  in
        FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____17  in
      uu____16 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos
  
let un_protect_embedded_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____29 = FStar_Syntax_Util.head_and_args t  in
    match uu____29 with
    | (head1,args) ->
        let uu____66 =
          let uu____79 =
            let uu____80 = FStar_Syntax_Util.un_uinst head1  in
            uu____80.FStar_Syntax_Syntax.n  in
          (uu____79, args)  in
        (match uu____66 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____92::(x,uu____94)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> x
         | uu____131 ->
             let uu____144 =
               let uu____145 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____145
                in
             failwith uu____144)
  
let embed_unit : Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Util.exp_unit 
let unembed_unit : FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____153  -> () 
let embed_bool : Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Util.exp_true_bool
    else FStar_Syntax_Util.exp_false_bool
  
let unembed_bool : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____163 =
      let uu____164 = FStar_Syntax_Subst.compress t  in
      uu____164.FStar_Syntax_Syntax.n  in
    match uu____163 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____168 -> failwith "Not an embedded bool"
  
let embed_int : Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____173 = FStar_Util.string_of_int i  in
    FStar_Syntax_Util.exp_int uu____173
  
let unembed_int : FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____178 =
      let uu____179 = FStar_Syntax_Subst.compress t  in
      uu____179.FStar_Syntax_Syntax.n  in
    match uu____178 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____183))
        -> FStar_Util.int_of_string s
    | uu____196 -> failwith "Not an embedded int"
  
let embed_string : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s  in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let unembed_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____212)) -> FStar_Util.string_of_unicode bytes
    | uu____217 ->
        let uu____218 =
          let uu____219 =
            let uu____220 = FStar_Syntax_Print.term_to_string t1  in
            Prims.strcat uu____220 ")"  in
          Prims.strcat "Not an embedded string (" uu____219  in
        failwith uu____218
  
let lid_Mktuple2 : FStar_Ident.lident =
  FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
  
let lid_tuple2 : FStar_Ident.lident =
  FStar_Parser_Const.mk_tuple_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
  
let embed_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  ->
    FStar_Syntax_Util.mk_alien b "reflection.embed_binder"
      FStar_Pervasives_Native.None
  
let unembed_binder : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____229 = FStar_Syntax_Util.un_alien t  in
    FStar_All.pipe_right uu____229 FStar_Dyn.undyn
  
let rec embed_list :
  'a .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term -> 'a Prims.list -> FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun typ  ->
      fun l  ->
        match l with
        | [] ->
            let uu____260 =
              let uu____261 =
                let uu____262 =
                  FStar_Reflection_Data.lid_as_data_tm
                    FStar_Parser_Const.nil_lid
                   in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____262
                  [FStar_Syntax_Syntax.U_zero]
                 in
              let uu____263 =
                let uu____264 = FStar_Syntax_Syntax.iarg typ  in [uu____264]
                 in
              FStar_Syntax_Syntax.mk_Tm_app uu____261 uu____263  in
            uu____260 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | hd1::tl1 ->
            let uu____271 =
              let uu____272 =
                let uu____273 =
                  FStar_Reflection_Data.lid_as_data_tm
                    FStar_Parser_Const.cons_lid
                   in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____273
                  [FStar_Syntax_Syntax.U_zero]
                 in
              let uu____274 =
                let uu____275 = FStar_Syntax_Syntax.iarg typ  in
                let uu____276 =
                  let uu____279 =
                    let uu____280 = embed_a hd1  in
                    FStar_Syntax_Syntax.as_arg uu____280  in
                  let uu____281 =
                    let uu____284 =
                      let uu____285 = embed_list embed_a typ tl1  in
                      FStar_Syntax_Syntax.as_arg uu____285  in
                    [uu____284]  in
                  uu____279 :: uu____281  in
                uu____275 :: uu____276  in
              FStar_Syntax_Syntax.mk_Tm_app uu____272 uu____274  in
            uu____271 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let rec unembed_list :
  'a .
    (FStar_Syntax_Syntax.term -> 'a) ->
      FStar_Syntax_Syntax.term -> 'a Prims.list
  =
  fun unembed_a  ->
    fun l  ->
      let l1 = FStar_Syntax_Util.unascribe l  in
      let uu____311 = FStar_Syntax_Util.head_and_args l1  in
      match uu____311 with
      | (hd1,args) ->
          let uu____350 =
            let uu____363 =
              let uu____364 = FStar_Syntax_Util.un_uinst hd1  in
              uu____364.FStar_Syntax_Syntax.n  in
            (uu____363, args)  in
          (match uu____350 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____378) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               []
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,_t::(hd2,uu____398)::(tl1,uu____400)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____447 = unembed_a hd2  in
               let uu____448 = unembed_list unembed_a tl1  in uu____447 ::
                 uu____448
           | uu____451 ->
               let uu____464 =
                 let uu____465 = FStar_Syntax_Print.term_to_string l1  in
                 FStar_Util.format1 "Not an embedded list: %s" uu____465  in
               failwith uu____464)
  
let embed_binders :
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder l 
let unembed_binders :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list unembed_binder t 
let embed_string_list : Prims.string Prims.list -> FStar_Syntax_Syntax.term =
  fun ss  -> embed_list embed_string FStar_TypeChecker_Common.t_string ss 
let unembed_string_list : FStar_Syntax_Syntax.term -> Prims.string Prims.list
  = fun t  -> unembed_list unembed_string t 
let embed_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t 
let unembed_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t 
let embed_pair :
  'a 'b .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term ->
        ('b -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.term ->
            ('a,'b) FStar_Pervasives_Native.tuple2 ->
              FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun t_a  ->
      fun embed_b  ->
        fun t_b  ->
          fun x  ->
            let uu____558 =
              let uu____559 =
                let uu____560 =
                  FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2  in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____560
                  [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                 in
              let uu____561 =
                let uu____562 = FStar_Syntax_Syntax.iarg t_a  in
                let uu____563 =
                  let uu____566 = FStar_Syntax_Syntax.iarg t_b  in
                  let uu____567 =
                    let uu____570 =
                      let uu____571 = embed_a (FStar_Pervasives_Native.fst x)
                         in
                      FStar_Syntax_Syntax.as_arg uu____571  in
                    let uu____572 =
                      let uu____575 =
                        let uu____576 =
                          embed_b (FStar_Pervasives_Native.snd x)  in
                        FStar_Syntax_Syntax.as_arg uu____576  in
                      [uu____575]  in
                    uu____570 :: uu____572  in
                  uu____566 :: uu____567  in
                uu____562 :: uu____563  in
              FStar_Syntax_Syntax.mk_Tm_app uu____559 uu____561  in
            uu____558 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let unembed_pair :
  'a 'b .
    (FStar_Syntax_Syntax.term -> 'a) ->
      (FStar_Syntax_Syntax.term -> 'b) ->
        FStar_Syntax_Syntax.term -> ('a,'b) FStar_Pervasives_Native.tuple2
  =
  fun unembed_a  ->
    fun unembed_b  ->
      fun pair  ->
        let pairs = FStar_Syntax_Util.unascribe pair  in
        let uu____618 = FStar_Syntax_Util.head_and_args pair  in
        match uu____618 with
        | (hd1,args) ->
            let uu____659 =
              let uu____672 =
                let uu____673 = FStar_Syntax_Util.un_uinst hd1  in
                uu____673.FStar_Syntax_Syntax.n  in
              (uu____672, args)  in
            (match uu____659 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____689::uu____690::(a,uu____692)::(b,uu____694)::[])
                 when FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
                 let uu____753 = unembed_a a  in
                 let uu____754 = unembed_b b  in (uu____753, uu____754)
             | uu____755 -> failwith "Not an embedded pair")
  
let embed_option :
  'a .
    ('a -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term ->
        'a FStar_Pervasives_Native.option -> FStar_Syntax_Syntax.term
  =
  fun embed_a  ->
    fun typ  ->
      fun o  ->
        match o with
        | FStar_Pervasives_Native.None  ->
            let uu____802 =
              let uu____803 =
                let uu____804 =
                  FStar_Reflection_Data.lid_as_data_tm
                    FStar_Parser_Const.none_lid
                   in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____804
                  [FStar_Syntax_Syntax.U_zero]
                 in
              let uu____805 =
                let uu____806 = FStar_Syntax_Syntax.iarg typ  in [uu____806]
                 in
              FStar_Syntax_Syntax.mk_Tm_app uu____803 uu____805  in
            uu____802 FStar_Pervasives_Native.None FStar_Range.dummyRange
        | FStar_Pervasives_Native.Some a ->
            let uu____810 =
              let uu____811 =
                let uu____812 =
                  FStar_Reflection_Data.lid_as_data_tm
                    FStar_Parser_Const.some_lid
                   in
                FStar_Syntax_Syntax.mk_Tm_uinst uu____812
                  [FStar_Syntax_Syntax.U_zero]
                 in
              let uu____813 =
                let uu____814 = FStar_Syntax_Syntax.iarg typ  in
                let uu____815 =
                  let uu____818 =
                    let uu____819 = embed_a a  in
                    FStar_Syntax_Syntax.as_arg uu____819  in
                  [uu____818]  in
                uu____814 :: uu____815  in
              FStar_Syntax_Syntax.mk_Tm_app uu____811 uu____813  in
            uu____810 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let unembed_option :
  'a .
    (FStar_Syntax_Syntax.term -> 'a) ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun unembed_a  ->
    fun o  ->
      let uu____844 = FStar_Syntax_Util.head_and_args o  in
      match uu____844 with
      | (hd1,args) ->
          let uu____883 =
            let uu____896 =
              let uu____897 = FStar_Syntax_Util.un_uinst hd1  in
              uu____897.FStar_Syntax_Syntax.n  in
            (uu____896, args)  in
          (match uu____883 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____911) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.None
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____929::(a,uu____931)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid
               ->
               let uu____968 = unembed_a a  in
               FStar_Pervasives_Native.Some uu____968
           | uu____969 -> failwith "Not an embedded option")
  
let embed_fvar : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  ->
    FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar"
      FStar_Pervasives_Native.None
  
let unembed_fvar : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____992 = FStar_Syntax_Util.un_alien t  in
    FStar_All.pipe_right uu____992 FStar_Dyn.undyn
  
let embed_env : FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term =
  fun env  ->
    FStar_Syntax_Util.mk_alien env "tactics_embed_env"
      FStar_Pervasives_Native.None
  
let unembed_env : FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.env =
  fun t  ->
    let uu____1001 = FStar_Syntax_Util.un_alien t  in
    FStar_All.pipe_right uu____1001 FStar_Dyn.undyn
  
let embed_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int i ->
        let uu____1007 =
          let uu____1008 =
            let uu____1009 =
              let uu____1010 =
                let uu____1011 = FStar_Util.string_of_int i  in
                FStar_Syntax_Util.exp_int uu____1011  in
              FStar_Syntax_Syntax.as_arg uu____1010  in
            [uu____1009]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____1008
           in
        uu____1007 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.C_String s ->
        let uu____1015 =
          let uu____1016 =
            let uu____1017 =
              let uu____1018 = embed_string s  in
              FStar_Syntax_Syntax.as_arg uu____1018  in
            [uu____1017]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String
            uu____1016
           in
        uu____1015 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let unembed_const : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1026 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1026 with
    | (hd1,args) ->
        let uu____1063 =
          let uu____1076 =
            let uu____1077 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1077.FStar_Syntax_Syntax.n  in
          (uu____1076, args)  in
        (match uu____1063 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Unit_lid
             -> FStar_Reflection_Data.C_Unit
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_True_lid
             -> FStar_Reflection_Data.C_True
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_False_lid
             -> FStar_Reflection_Data.C_False
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____1135)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____1160 = unembed_int i  in
             FStar_Reflection_Data.C_Int uu____1160
         | (FStar_Syntax_Syntax.Tm_fvar fv,(s,uu____1163)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_String_lid
             ->
             let uu____1188 = unembed_string s  in
             FStar_Reflection_Data.C_String uu____1188
         | uu____1189 -> failwith "not an embedded vconst")
  
let rec embed_pattern :
  FStar_Reflection_Data.pattern -> FStar_Syntax_Syntax.term =
  fun p  ->
    match p with
    | FStar_Reflection_Data.Pat_Constant c ->
        let uu____1207 =
          let uu____1208 =
            let uu____1209 =
              let uu____1210 = embed_const c  in
              FStar_Syntax_Syntax.as_arg uu____1210  in
            [uu____1209]  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Pat_Constant uu____1208
           in
        uu____1207 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
        let uu____1219 =
          let uu____1220 =
            let uu____1221 =
              let uu____1222 = embed_fvar fv  in
              FStar_Syntax_Syntax.as_arg uu____1222  in
            let uu____1223 =
              let uu____1226 =
                let uu____1227 =
                  embed_list embed_pattern
                    FStar_Reflection_Data.fstar_refl_pattern ps
                   in
                FStar_Syntax_Syntax.as_arg uu____1227  in
              [uu____1226]  in
            uu____1221 :: uu____1223  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons
            uu____1220
           in
        uu____1219 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Var bv ->
        let uu____1231 =
          let uu____1232 =
            let uu____1233 =
              let uu____1234 =
                let uu____1235 = FStar_Syntax_Syntax.mk_binder bv  in
                embed_binder uu____1235  in
              FStar_Syntax_Syntax.as_arg uu____1234  in
            [uu____1233]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var
            uu____1232
           in
        uu____1231 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Pat_Wild bv ->
        let uu____1239 =
          let uu____1240 =
            let uu____1241 =
              let uu____1242 =
                let uu____1243 = FStar_Syntax_Syntax.mk_binder bv  in
                embed_binder uu____1243  in
              FStar_Syntax_Syntax.as_arg uu____1242  in
            [uu____1241]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild
            uu____1240
           in
        uu____1239 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let rec unembed_pattern :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.pattern =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1251 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1251 with
    | (hd1,args) ->
        let uu____1288 =
          let uu____1301 =
            let uu____1302 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1302.FStar_Syntax_Syntax.n  in
          (uu____1301, args)  in
        (match uu____1288 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1315)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Constant_lid
             ->
             let uu____1340 = unembed_const c  in
             FStar_Reflection_Data.Pat_Constant uu____1340
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(f,uu____1343)::(ps,uu____1345)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Cons_lid
             ->
             let uu____1380 =
               let uu____1387 = unembed_fvar f  in
               let uu____1388 = unembed_list unembed_pattern ps  in
               (uu____1387, uu____1388)  in
             FStar_Reflection_Data.Pat_Cons uu____1380
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1395)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Var_lid
             ->
             let uu____1420 =
               let uu____1421 = unembed_binder b  in
               FStar_Pervasives_Native.fst uu____1421  in
             FStar_Reflection_Data.Pat_Var uu____1420
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1428)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Pat_Wild_lid
             ->
             let uu____1453 =
               let uu____1454 = unembed_binder b  in
               FStar_Pervasives_Native.fst uu____1454  in
             FStar_Reflection_Data.Pat_Wild uu____1453
         | uu____1459 -> failwith "not an embedded pattern")
  
let embed_branch :
  (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term
  =
  embed_pair embed_pattern FStar_Reflection_Data.fstar_refl_pattern
    embed_term FStar_Reflection_Data.fstar_refl_term
  
let unembed_branch :
  FStar_Syntax_Syntax.term ->
    (FStar_Reflection_Data.pattern,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = unembed_pair unembed_pattern unembed_term 
let embed_term_view :
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____1491 =
          let uu____1492 =
            let uu____1493 =
              let uu____1494 = embed_fvar fv  in
              FStar_Syntax_Syntax.as_arg uu____1494  in
            [uu____1493]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____1492
           in
        uu____1491 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____1498 =
          let uu____1499 =
            let uu____1500 =
              let uu____1501 = embed_binder bv  in
              FStar_Syntax_Syntax.as_arg uu____1501  in
            [uu____1500]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____1499
           in
        uu____1498 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____1506 =
          let uu____1507 =
            let uu____1508 =
              let uu____1509 = embed_term hd1  in
              FStar_Syntax_Syntax.as_arg uu____1509  in
            let uu____1510 =
              let uu____1513 =
                let uu____1514 = embed_term a  in
                FStar_Syntax_Syntax.as_arg uu____1514  in
              [uu____1513]  in
            uu____1508 :: uu____1510  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____1507
           in
        uu____1506 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____1519 =
          let uu____1520 =
            let uu____1521 =
              let uu____1522 = embed_binder b  in
              FStar_Syntax_Syntax.as_arg uu____1522  in
            let uu____1523 =
              let uu____1526 =
                let uu____1527 = embed_term t1  in
                FStar_Syntax_Syntax.as_arg uu____1527  in
              [uu____1526]  in
            uu____1521 :: uu____1523  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____1520
           in
        uu____1519 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____1532 =
          let uu____1533 =
            let uu____1534 =
              let uu____1535 = embed_binder b  in
              FStar_Syntax_Syntax.as_arg uu____1535  in
            let uu____1536 =
              let uu____1539 =
                let uu____1540 = embed_term t1  in
                FStar_Syntax_Syntax.as_arg uu____1540  in
              [uu____1539]  in
            uu____1534 :: uu____1536  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____1533
           in
        uu____1532 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____1544 =
          let uu____1545 =
            let uu____1546 =
              let uu____1547 = embed_unit ()  in
              FStar_Syntax_Syntax.as_arg uu____1547  in
            [uu____1546]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____1545
           in
        uu____1544 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____1552 =
          let uu____1553 =
            let uu____1554 =
              let uu____1555 = embed_binder bv  in
              FStar_Syntax_Syntax.as_arg uu____1555  in
            let uu____1556 =
              let uu____1559 =
                let uu____1560 = embed_term t1  in
                FStar_Syntax_Syntax.as_arg uu____1560  in
              [uu____1559]  in
            uu____1554 :: uu____1556  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____1553
           in
        uu____1552 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1564 =
          let uu____1565 =
            let uu____1566 =
              let uu____1567 = embed_const c  in
              FStar_Syntax_Syntax.as_arg uu____1567  in
            [uu____1566]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____1565
           in
        uu____1564 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t1) ->
        let uu____1572 =
          let uu____1573 =
            let uu____1574 =
              let uu____1575 = embed_int u  in
              FStar_Syntax_Syntax.as_arg uu____1575  in
            let uu____1576 =
              let uu____1579 =
                let uu____1580 = embed_term t1  in
                FStar_Syntax_Syntax.as_arg uu____1580  in
              [uu____1579]  in
            uu____1574 :: uu____1576  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar
            uu____1573
           in
        uu____1572 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t1,brs) ->
        let uu____1589 =
          let uu____1590 =
            let uu____1591 =
              let uu____1592 = embed_term t1  in
              FStar_Syntax_Syntax.as_arg uu____1592  in
            let uu____1593 =
              let uu____1596 =
                let uu____1597 =
                  embed_list embed_branch
                    FStar_Reflection_Data.fstar_refl_branch brs
                   in
                FStar_Syntax_Syntax.as_arg uu____1597  in
              [uu____1596]  in
            uu____1591 :: uu____1593  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match
            uu____1590
           in
        uu____1589 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
  
let unembed_term_view :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1609 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1609 with
    | (hd1,args) ->
        let uu____1646 =
          let uu____1659 =
            let uu____1660 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1660.FStar_Syntax_Syntax.n  in
          (uu____1659, args)  in
        (match uu____1646 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1673)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1698 = unembed_binder b  in
             FStar_Reflection_Data.Tv_Var uu____1698
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1701)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1726 = unembed_fvar b  in
             FStar_Reflection_Data.Tv_FVar uu____1726
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1729)::(r,uu____1731)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1766 =
               let uu____1771 = unembed_term l  in
               let uu____1772 = unembed_term r  in (uu____1771, uu____1772)
                in
             FStar_Reflection_Data.Tv_App uu____1766
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1775)::(t2,uu____1777)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1812 =
               let uu____1817 = unembed_binder b  in
               let uu____1818 = unembed_term t2  in (uu____1817, uu____1818)
                in
             FStar_Reflection_Data.Tv_Abs uu____1812
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1821)::(t2,uu____1823)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1858 =
               let uu____1863 = unembed_binder b  in
               let uu____1864 = unembed_term t2  in (uu____1863, uu____1864)
                in
             FStar_Reflection_Data.Tv_Arrow uu____1858
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1867)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1895)::(t2,uu____1897)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1932 =
               let uu____1937 = unembed_binder b  in
               let uu____1938 = unembed_term t2  in (uu____1937, uu____1938)
                in
             FStar_Reflection_Data.Tv_Refine uu____1932
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1941)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1966 = unembed_const c  in
             FStar_Reflection_Data.Tv_Const uu____1966
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(u,uu____1969)::(t2,uu____1971)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Uvar_lid
             ->
             let uu____2006 =
               let uu____2011 = unembed_int u  in
               let uu____2012 = unembed_term t2  in (uu____2011, uu____2012)
                in
             FStar_Reflection_Data.Tv_Uvar uu____2006
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(t2,uu____2015)::(brs,uu____2017)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Match_lid
             ->
             let uu____2052 =
               let uu____2059 = unembed_term t2  in
               let uu____2060 = unembed_list unembed_branch brs  in
               (uu____2059, uu____2060)  in
             FStar_Reflection_Data.Tv_Match uu____2052
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____2092 -> failwith "not an embedded term_view")
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____2119::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____2145 = init xs  in x :: uu____2145
  
let inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____2156 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____2156
  
let pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____2165 = FStar_Parser_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____2165
      FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None
  
let inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b) 
let inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst =
  fun c  ->
    match c with
    | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s,uu____2175) ->
        let uu____2188 = FStar_Util.int_of_string s  in
        FStar_Reflection_Data.C_Int uu____2188
    | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (bs,uu____2190) ->
        FStar_Reflection_Data.C_String (FStar_Util.string_of_bytes bs)
    | uu____2195 ->
        let uu____2196 =
          let uu____2197 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "unknown constant: %s" uu____2197  in
        failwith uu____2196
  
let inspect : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____2204 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____2204
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____2247 = last args  in
        (match uu____2247 with
         | (a,uu____2261) ->
             let uu____2266 =
               let uu____2271 =
                 let uu____2274 =
                   let uu____2275 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____2275  in
                 uu____2274 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
                  in
               (uu____2271, a)  in
             FStar_Reflection_Data.Tv_App uu____2266)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____2288,uu____2289) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____2331 = FStar_Syntax_Subst.open_term bs t2  in
        (match uu____2331 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2358 =
                    let uu____2363 = FStar_Syntax_Util.abs bs2 t3 k  in
                    (b, uu____2363)  in
                  FStar_Reflection_Data.Tv_Abs uu____2358))
    | FStar_Syntax_Syntax.Tm_type uu____2368 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____2402 = FStar_Syntax_Subst.open_comp bs k  in
        (match uu____2402 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____2429 =
                    let uu____2434 = FStar_Syntax_Util.arrow bs2 k1  in
                    (b, uu____2434)  in
                  FStar_Reflection_Data.Tv_Arrow uu____2429))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____2450 = FStar_Syntax_Subst.open_term [b] t2  in
        (match uu____2450 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____2479 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____2489 = inspect_const c  in
        FStar_Reflection_Data.Tv_Const uu____2489
    | FStar_Syntax_Syntax.Tm_uvar (u,t2) ->
        let uu____2516 =
          let uu____2521 = FStar_Syntax_Unionfind.uvar_id u  in
          (uu____2521, t2)  in
        FStar_Reflection_Data.Tv_Uvar uu____2516
    | FStar_Syntax_Syntax.Tm_match (t2,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____2571 = inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____2571
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____2590 =
                let uu____2597 =
                  FStar_List.map
                    (fun uu____2609  ->
                       match uu____2609 with
                       | (p1,uu____2617) -> inspect_pat p1) ps
                   in
                (fv, uu____2597)  in
              FStar_Reflection_Data.Pat_Cons uu____2590
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term uu____2626 ->
              failwith "NYI: Pat_dot_term"
           in
        let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
        let brs2 =
          FStar_List.map
            (fun uu___76_2670  ->
               match uu___76_2670 with
               | (pat,uu____2692,t3) ->
                   let uu____2710 = inspect_pat pat  in (uu____2710, t3))
            brs1
           in
        FStar_Reflection_Data.Tv_Match (t2, brs2)
    | uu____2723 ->
        ((let uu____2725 = FStar_Syntax_Print.tag_of_term t1  in
          let uu____2726 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____2725 uu____2726);
         FStar_Reflection_Data.Tv_Unknown)
  
let pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____2732 =
          let uu____2743 = FStar_Util.string_of_int i  in
          (uu____2743, FStar_Pervasives_Native.None)  in
        FStar_Const.Const_int uu____2732
    | FStar_Reflection_Data.C_True  -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False  -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string
          ((FStar_Util.bytes_of_string s), FStar_Range.dummyRange)
  
let pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____2762) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____2766 =
          let uu____2775 = FStar_Syntax_Syntax.as_arg r  in [uu____2775]  in
        FStar_Syntax_Util.mk_app l uu____2766
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____2780 = FStar_Syntax_Syntax.mk_Total t  in
        FStar_Syntax_Util.arrow [b] uu____2780
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____2784),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____2791 =
          let uu____2794 =
            let uu____2795 = pack_const c  in
            FStar_Syntax_Syntax.Tm_constant uu____2795  in
          FStar_Syntax_Syntax.mk uu____2794  in
        uu____2791 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        FStar_Syntax_Util.uvar_from_id u t
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____2818 =
                let uu____2819 = pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____2819  in
              FStar_All.pipe_left wrap uu____2818
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____2828 =
                let uu____2829 =
                  let uu____2842 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____2856 = pack_pat p1  in (uu____2856, false))
                      ps
                     in
                  (fv, uu____2842)  in
                FStar_Syntax_Syntax.Pat_cons uu____2829  in
              FStar_All.pipe_left wrap uu____2828
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
           in
        let brs1 =
          FStar_List.map
            (fun uu___77_2902  ->
               match uu___77_2902 with
               | (pat,t1) ->
                   let uu____2919 = pack_pat pat  in
                   (uu____2919, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
          FStar_Pervasives_Native.None FStar_Range.dummyRange
    | uu____2931 -> failwith "pack: unexpected term view"
  
let embed_order : FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
  
let unembed_order : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2941 = FStar_Syntax_Util.head_and_args t1  in
    match uu____2941 with
    | (hd1,args) ->
        let uu____2978 =
          let uu____2991 =
            let uu____2992 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2992.FStar_Syntax_Syntax.n  in
          (uu____2991, args)  in
        (match uu____2978 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Lt_lid
             -> FStar_Reflection_Data.Lt
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Eq_lid
             -> FStar_Reflection_Data.Eq
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ord_Gt_lid
             -> FStar_Reflection_Data.Gt
         | uu____3048 -> failwith "not an embedded order")
  
let order_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Reflection_Data.order
  =
  fun x  ->
    fun y  ->
      let n1 =
        FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x)
          (FStar_Pervasives_Native.fst y)
         in
      if n1 < (Prims.parse_int "0")
      then FStar_Reflection_Data.Lt
      else
        if n1 = (Prims.parse_int "0")
        then FStar_Reflection_Data.Eq
        else FStar_Reflection_Data.Gt
  
let is_free :
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  ->
    fun t  -> FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t
  
let embed_norm_step :
  FStar_Reflection_Data.norm_step -> FStar_Syntax_Syntax.term =
  fun n1  ->
    match n1 with
    | FStar_Reflection_Data.Simpl  -> FStar_Reflection_Data.ref_Simpl
    | FStar_Reflection_Data.WHNF  -> FStar_Reflection_Data.ref_WHNF
    | FStar_Reflection_Data.Primops  -> FStar_Reflection_Data.ref_Primops
    | FStar_Reflection_Data.Delta  -> FStar_Reflection_Data.ref_Delta
  
let unembed_norm_step :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.norm_step =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3089 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3089 with
    | (hd1,args) ->
        let uu____3126 =
          let uu____3139 =
            let uu____3140 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3140.FStar_Syntax_Syntax.n  in
          (uu____3139, args)  in
        (match uu____3126 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Simpl_lid
             -> FStar_Reflection_Data.Simpl
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_WHNF_lid
             -> FStar_Reflection_Data.WHNF
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Primops_lid
             -> FStar_Reflection_Data.Primops
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Delta_lid
             -> FStar_Reflection_Data.Delta
         | uu____3211 -> failwith "not an embedded norm_step")
  
let lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list -> FStar_Reflection_Data.sigelt_view
  =
  fun env  ->
    fun ns  ->
      let lid = FStar_Parser_Const.p2l ns  in
      let res = FStar_TypeChecker_Env.lookup_qname env lid  in
      match res with
      | FStar_Pervasives_Native.None  -> FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____3276,rng) ->
          FStar_Reflection_Data.Unk
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               (lid1,us1,bs,t,uu____3377,dc_lids) ->
               let nm = FStar_Ident.path_of_lid lid1  in
               let ctor1 dc_lid =
                 let uu____3394 =
                   FStar_TypeChecker_Env.lookup_qname env dc_lid  in
                 match uu____3394 with
                 | FStar_Pervasives_Native.Some
                     (FStar_Util.Inr (se1,us2),rng1) ->
                     (match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid2,us3,t1,uu____3467,n1,uu____3469) ->
                          let uu____3474 =
                            let uu____3479 = FStar_Ident.path_of_lid lid2  in
                            (uu____3479, t1)  in
                          FStar_Reflection_Data.Ctor uu____3474
                      | uu____3484 -> failwith "wat 1")
                 | uu____3485 -> failwith "wat 2"  in
               let ctors = FStar_List.map ctor1 dc_lids  in
               FStar_Reflection_Data.Sg_Inductive (nm, bs, t, ctors)
           | uu____3513 -> FStar_Reflection_Data.Unk)
  
let embed_ctor : FStar_Reflection_Data.ctor -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.Ctor (nm,t) ->
        let uu____3520 =
          let uu____3521 =
            let uu____3522 =
              let uu____3523 = embed_string_list nm  in
              FStar_Syntax_Syntax.as_arg uu____3523  in
            let uu____3524 =
              let uu____3527 =
                let uu____3528 = embed_term t  in
                FStar_Syntax_Syntax.as_arg uu____3528  in
              [uu____3527]  in
            uu____3522 :: uu____3524  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor
            uu____3521
           in
        uu____3520 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let unembed_ctor : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.ctor =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3536 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3536 with
    | (hd1,args) ->
        let uu____3573 =
          let uu____3586 =
            let uu____3587 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3587.FStar_Syntax_Syntax.n  in
          (uu____3586, args)  in
        (match uu____3573 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3600)::(t2,uu____3602)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Ctor_lid
             ->
             let uu____3637 =
               let uu____3642 = unembed_string_list nm  in
               let uu____3645 = unembed_term t2  in (uu____3642, uu____3645)
                in
             FStar_Reflection_Data.Ctor uu____3637
         | uu____3648 -> failwith "not an embedded ctor")
  
let embed_sigelt_view :
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.term =
  fun sev  ->
    match sev with
    | FStar_Reflection_Data.Sg_Inductive (nm,bs,t,dcs) ->
        let uu____3677 =
          let uu____3678 =
            let uu____3679 =
              let uu____3680 = embed_string_list nm  in
              FStar_Syntax_Syntax.as_arg uu____3680  in
            let uu____3681 =
              let uu____3684 =
                let uu____3685 = embed_binders bs  in
                FStar_Syntax_Syntax.as_arg uu____3685  in
              let uu____3686 =
                let uu____3689 =
                  let uu____3690 = embed_term t  in
                  FStar_Syntax_Syntax.as_arg uu____3690  in
                let uu____3691 =
                  let uu____3694 =
                    let uu____3695 =
                      embed_list embed_ctor
                        FStar_Reflection_Data.fstar_refl_ctor dcs
                       in
                    FStar_Syntax_Syntax.as_arg uu____3695  in
                  [uu____3694]  in
                uu____3689 :: uu____3691  in
              uu____3684 :: uu____3686  in
            uu____3679 :: uu____3681  in
          FStar_Syntax_Syntax.mk_Tm_app
            FStar_Reflection_Data.ref_Sg_Inductive uu____3678
           in
        uu____3677 FStar_Pervasives_Native.None FStar_Range.dummyRange
    | FStar_Reflection_Data.Unk  -> FStar_Reflection_Data.ref_Unk
  
let unembed_sigelt_view :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.sigelt_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____3703 = FStar_Syntax_Util.head_and_args t1  in
    match uu____3703 with
    | (hd1,args) ->
        let uu____3740 =
          let uu____3753 =
            let uu____3754 = FStar_Syntax_Util.un_uinst hd1  in
            uu____3754.FStar_Syntax_Syntax.n  in
          (uu____3753, args)  in
        (match uu____3740 with
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(nm,uu____3767)::(bs,uu____3769)::(t2,uu____3771)::(dcs,uu____3773)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Sg_Inductive_lid
             ->
             let uu____3828 =
               let uu____3841 = unembed_string_list nm  in
               let uu____3844 = unembed_binders bs  in
               let uu____3847 = unembed_term t2  in
               let uu____3848 = unembed_list unembed_ctor dcs  in
               (uu____3841, uu____3844, uu____3847, uu____3848)  in
             FStar_Reflection_Data.Sg_Inductive uu____3828
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Unk_lid
             -> FStar_Reflection_Data.Unk
         | uu____3872 -> failwith "not an embedded sigelt_view")
  