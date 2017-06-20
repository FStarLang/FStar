open Prims
let protect_embedded_term :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____9 =
        let uu____10 =
          let uu____11 = FStar_Syntax_Syntax.iarg t  in
          let uu____12 =
            let uu____14 = FStar_Syntax_Syntax.as_arg x  in [uu____14]  in
          uu____11 :: uu____12  in
        FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Const.fstar_refl_embed
          uu____10
         in
      uu____9 None x.FStar_Syntax_Syntax.pos
  
let un_protect_embedded_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____22 = FStar_Syntax_Util.head_and_args t  in
    match uu____22 with
    | (head1,args) ->
        let uu____48 =
          let uu____56 =
            let uu____57 = FStar_Syntax_Util.un_uinst head1  in
            uu____57.FStar_Syntax_Syntax.n  in
          (uu____56, args)  in
        (match uu____48 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____66::(x,uu____68)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Syntax_Const.fstar_refl_embed_lid
             -> x
         | uu____94 ->
             let uu____102 =
               let uu____103 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____103
                in
             failwith uu____102)
  
let embed_unit : Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Const.exp_unit 
let unembed_unit : FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____109  -> () 
let embed_bool : Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
  
let unembed_bool : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____117 =
      let uu____118 = FStar_Syntax_Subst.compress t  in
      uu____118.FStar_Syntax_Syntax.n  in
    match uu____117 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____122 -> failwith "Not an embedded bool"
  
let embed_int : Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____126 = FStar_Util.string_of_int i  in
    FStar_Syntax_Const.exp_int uu____126
  
let unembed_int : FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____130 =
      let uu____131 = FStar_Syntax_Subst.compress t  in
      uu____131.FStar_Syntax_Syntax.n  in
    match uu____130 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____135))
        -> FStar_Util.int_of_string s
    | uu____142 -> failwith "Not an embedded int"
  
let embed_string :
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s  in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange))) None
      FStar_Range.dummyRange
  
let unembed_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____158)) -> FStar_Util.string_of_unicode bytes
    | uu____161 ->
        let uu____162 =
          let uu____163 =
            let uu____164 = FStar_Syntax_Print.term_to_string t1  in
            Prims.strcat uu____164 ")"  in
          Prims.strcat "Not an embedded string (" uu____163  in
        failwith uu____162
  
let lid_Mktuple2 : FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
  
let lid_tuple2 : FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange 
let embed_binder : FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term =
  fun b  -> FStar_Syntax_Util.mk_alien b "reflection.embed_binder" None 
let unembed_binder : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let uu____171 = FStar_Syntax_Util.un_alien t  in
    FStar_All.pipe_right uu____171 FStar_Dyn.undyn
  
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____196 =
        let uu____197 =
          let uu____198 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid
             in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____198
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____199 =
          let uu____200 = FStar_Syntax_Syntax.iarg typ  in [uu____200]  in
        FStar_Syntax_Syntax.mk_Tm_app uu____197 uu____199  in
      uu____196 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____208 =
        let uu____209 =
          let uu____210 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.cons_lid
             in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____210
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____211 =
          let uu____212 = FStar_Syntax_Syntax.iarg typ  in
          let uu____213 =
            let uu____215 =
              let uu____216 = embed_a hd1  in
              FStar_Syntax_Syntax.as_arg uu____216  in
            let uu____217 =
              let uu____219 =
                let uu____220 = embed_list embed_a typ tl1  in
                FStar_Syntax_Syntax.as_arg uu____220  in
              [uu____219]  in
            uu____215 :: uu____217  in
          uu____212 :: uu____213  in
        FStar_Syntax_Syntax.mk_Tm_app uu____209 uu____211  in
      uu____208 None FStar_Range.dummyRange
  
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l  in
  let uu____244 = FStar_Syntax_Util.head_and_args l1  in
  match uu____244 with
  | (hd1,args) ->
      let uu____271 =
        let uu____279 =
          let uu____280 = FStar_Syntax_Util.un_uinst hd1  in
          uu____280.FStar_Syntax_Syntax.n  in
        (uu____279, args)  in
      (match uu____271 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____290) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____304)::(tl1,uu____306)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____340 = unembed_a hd2  in
           let uu____341 = unembed_list unembed_a tl1  in uu____340 ::
             uu____341
       | uu____343 ->
           let uu____351 =
             let uu____352 = FStar_Syntax_Print.term_to_string l1  in
             FStar_Util.format1 "Not an embedded list: %s" uu____352  in
           failwith uu____351)
  
let embed_binders :
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder l 
let unembed_binders :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list unembed_binder t 
let embed_term :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t 
let unembed_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t 
let embed_pair embed_a t_a embed_b t_b x =
  let uu____412 =
    let uu____413 =
      let uu____414 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____414
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
       in
    let uu____415 =
      let uu____416 = FStar_Syntax_Syntax.iarg t_a  in
      let uu____417 =
        let uu____419 = FStar_Syntax_Syntax.iarg t_b  in
        let uu____420 =
          let uu____422 =
            let uu____423 = embed_a (fst x)  in
            FStar_Syntax_Syntax.as_arg uu____423  in
          let uu____424 =
            let uu____426 =
              let uu____427 = embed_b (snd x)  in
              FStar_Syntax_Syntax.as_arg uu____427  in
            [uu____426]  in
          uu____422 :: uu____424  in
        uu____419 :: uu____420  in
      uu____416 :: uu____417  in
    FStar_Syntax_Syntax.mk_Tm_app uu____413 uu____415  in
  uu____412 None FStar_Range.dummyRange 
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair  in
  let uu____464 = FStar_Syntax_Util.head_and_args pair  in
  match uu____464 with
  | (hd1,args) ->
      let uu____492 =
        let uu____500 =
          let uu____501 = FStar_Syntax_Util.un_uinst hd1  in
          uu____501.FStar_Syntax_Syntax.n  in
        (uu____500, args)  in
      (match uu____492 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____512::uu____513::(a,uu____515)::(b,uu____517)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____559 = unembed_a a  in
           let uu____560 = unembed_b b  in (uu____559, uu____560)
       | uu____561 -> failwith "Not an embedded pair")
  
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____595 =
        let uu____596 =
          let uu____597 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid
             in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____597
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____598 =
          let uu____599 = FStar_Syntax_Syntax.iarg typ  in [uu____599]  in
        FStar_Syntax_Syntax.mk_Tm_app uu____596 uu____598  in
      uu____595 None FStar_Range.dummyRange
  | Some a ->
      let uu____605 =
        let uu____606 =
          let uu____607 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid
             in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____607
            [FStar_Syntax_Syntax.U_zero]
           in
        let uu____608 =
          let uu____609 = FStar_Syntax_Syntax.iarg typ  in
          let uu____610 =
            let uu____612 =
              let uu____613 = embed_a a  in
              FStar_Syntax_Syntax.as_arg uu____613  in
            [uu____612]  in
          uu____609 :: uu____610  in
        FStar_Syntax_Syntax.mk_Tm_app uu____606 uu____608  in
      uu____605 None FStar_Range.dummyRange
  
let unembed_option unembed_a o =
  let uu____636 = FStar_Syntax_Util.head_and_args o  in
  match uu____636 with
  | (hd1,args) ->
      let uu____663 =
        let uu____671 =
          let uu____672 = FStar_Syntax_Util.un_uinst hd1  in
          uu____672.FStar_Syntax_Syntax.n  in
        (uu____671, args)  in
      (match uu____663 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____682) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____694::(a,uu____696)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____722 = unembed_a a  in Some uu____722
       | uu____723 -> failwith "Not an embedded option")
  
let embed_fvar : FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term =
  fun fv  -> FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar" None 
let unembed_fvar : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let uu____738 = FStar_Syntax_Util.un_alien t  in
    FStar_All.pipe_right uu____738 FStar_Dyn.undyn
  
let embed_const :
  FStar_Reflection_Data.vconst ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Reflection_Data.ref_C_Unit
    | FStar_Reflection_Data.C_True  -> FStar_Reflection_Data.ref_C_True
    | FStar_Reflection_Data.C_False  -> FStar_Reflection_Data.ref_C_False
    | FStar_Reflection_Data.C_Int s ->
        let uu____743 =
          let uu____744 =
            let uu____745 =
              let uu____746 = FStar_Syntax_Const.exp_int s  in
              FStar_Syntax_Syntax.as_arg uu____746  in
            [uu____745]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____744
           in
        uu____743 None FStar_Range.dummyRange
  
let embed_term_view :
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____755 =
          let uu____756 =
            let uu____757 =
              let uu____758 = embed_fvar fv  in
              FStar_Syntax_Syntax.as_arg uu____758  in
            [uu____757]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____756
           in
        uu____755 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____764 =
          let uu____765 =
            let uu____766 =
              let uu____767 = embed_binder bv  in
              FStar_Syntax_Syntax.as_arg uu____767  in
            [uu____766]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____765
           in
        uu____764 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____774 =
          let uu____775 =
            let uu____776 =
              let uu____777 = embed_term hd1  in
              FStar_Syntax_Syntax.as_arg uu____777  in
            let uu____778 =
              let uu____780 =
                let uu____781 = embed_term a  in
                FStar_Syntax_Syntax.as_arg uu____781  in
              [uu____780]  in
            uu____776 :: uu____778  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____775
           in
        uu____774 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____788 =
          let uu____789 =
            let uu____790 =
              let uu____791 = embed_binder b  in
              FStar_Syntax_Syntax.as_arg uu____791  in
            let uu____792 =
              let uu____794 =
                let uu____795 = embed_term t1  in
                FStar_Syntax_Syntax.as_arg uu____795  in
              [uu____794]  in
            uu____790 :: uu____792  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____789
           in
        uu____788 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____802 =
          let uu____803 =
            let uu____804 =
              let uu____805 = embed_binder b  in
              FStar_Syntax_Syntax.as_arg uu____805  in
            let uu____806 =
              let uu____808 =
                let uu____809 = embed_term t1  in
                FStar_Syntax_Syntax.as_arg uu____809  in
              [uu____808]  in
            uu____804 :: uu____806  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____803
           in
        uu____802 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____815 =
          let uu____816 =
            let uu____817 =
              let uu____818 = embed_unit ()  in
              FStar_Syntax_Syntax.as_arg uu____818  in
            [uu____817]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____816
           in
        uu____815 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____825 =
          let uu____826 =
            let uu____827 =
              let uu____828 = embed_binder bv  in
              FStar_Syntax_Syntax.as_arg uu____828  in
            let uu____829 =
              let uu____831 =
                let uu____832 = embed_term t1  in
                FStar_Syntax_Syntax.as_arg uu____832  in
              [uu____831]  in
            uu____827 :: uu____829  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____826
           in
        uu____825 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____838 =
          let uu____839 =
            let uu____840 =
              let uu____841 = embed_const c  in
              FStar_Syntax_Syntax.as_arg uu____841  in
            [uu____840]  in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____839
           in
        uu____838 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
  
let unembed_const : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst
  =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____850 = FStar_Syntax_Util.head_and_args t1  in
    match uu____850 with
    | (hd1,args) ->
        let uu____876 =
          let uu____884 =
            let uu____885 = FStar_Syntax_Util.un_uinst hd1  in
            uu____885.FStar_Syntax_Syntax.n  in
          (uu____884, args)  in
        (match uu____876 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____925)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____943 =
               let uu____944 = FStar_Syntax_Subst.compress i  in
               uu____944.FStar_Syntax_Syntax.n  in
             (match uu____943 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____948)) -> FStar_Reflection_Data.C_Int s
              | uu____955 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____956 -> failwith "not an embedded vconst")
  
let unembed_term_view :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____968 = FStar_Syntax_Util.head_and_args t1  in
    match uu____968 with
    | (hd1,args) ->
        let uu____994 =
          let uu____1002 =
            let uu____1003 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1003.FStar_Syntax_Syntax.n  in
          (uu____1002, args)  in
        (match uu____994 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1013)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1031 = unembed_binder b  in
             FStar_Reflection_Data.Tv_Var uu____1031
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1034)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1052 = unembed_fvar b  in
             FStar_Reflection_Data.Tv_FVar uu____1052
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1055)::(r,uu____1057)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1083 =
               let uu____1086 = unembed_term l  in
               let uu____1087 = unembed_term r  in (uu____1086, uu____1087)
                in
             FStar_Reflection_Data.Tv_App uu____1083
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1090)::(t2,uu____1092)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1118 =
               let uu____1121 = unembed_binder b  in
               let uu____1122 = unembed_term t2  in (uu____1121, uu____1122)
                in
             FStar_Reflection_Data.Tv_Abs uu____1118
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1125)::(t2,uu____1127)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1153 =
               let uu____1156 = unembed_binder b  in
               let uu____1157 = unembed_term t2  in (uu____1156, uu____1157)
                in
             FStar_Reflection_Data.Tv_Arrow uu____1153
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1160)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1181)::(t2,uu____1183)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1209 =
               let uu____1212 = unembed_binder b  in
               let uu____1213 = unembed_term t2  in (uu____1212, uu____1213)
                in
             FStar_Reflection_Data.Tv_Refine uu____1209
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1216)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1234 = unembed_const c  in
             FStar_Reflection_Data.Tv_Const uu____1234
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1245 -> failwith "not an embedded term_view")
  
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1263::xs -> last xs 
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1281 = init xs  in x :: uu____1281 
let inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1288 = FStar_Syntax_Syntax.lid_of_fv fv  in
    FStar_Ident.path_of_lid uu____1288
  
let pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1294 = FStar_Syntax_Const.p2l ns  in
    FStar_Syntax_Syntax.lid_as_fv uu____1294
      FStar_Syntax_Syntax.Delta_equational None
  
let inspect_bv : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b) 
let inspect : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1303 = FStar_Syntax_Syntax.mk_binder bv  in
        FStar_Reflection_Data.Tv_Var uu____1303
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1335 = last args  in
        (match uu____1335 with
         | (a,uu____1345) ->
             let uu____1350 =
               let uu____1353 =
                 let uu____1356 =
                   let uu____1357 = init args  in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1357  in
                 uu____1356 None t1.FStar_Syntax_Syntax.pos  in
               (uu____1353, a)  in
             FStar_Reflection_Data.Tv_App uu____1350)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1370,uu____1371) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1398 = FStar_Syntax_Subst.open_term bs t2  in
        (match uu____1398 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1414 =
                    let uu____1417 = FStar_Syntax_Util.abs bs2 t3 k  in
                    (b, uu____1417)  in
                  FStar_Reflection_Data.Tv_Abs uu____1414))
    | FStar_Syntax_Syntax.Tm_type uu____1420 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1443 = FStar_Syntax_Subst.open_comp bs k  in
        (match uu____1443 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1459 =
                    let uu____1462 = FStar_Syntax_Util.arrow bs2 k1  in
                    (b, uu____1462)  in
                  FStar_Reflection_Data.Tv_Arrow uu____1459))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____1476 = FStar_Syntax_Subst.open_term [b] t2  in
        (match uu____1476 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1493 -> failwith "impossible"  in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1501) ->
              FStar_Reflection_Data.C_Int s
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1508 ->
              let uu____1509 =
                let uu____1510 = FStar_Syntax_Print.const_to_string c  in
                FStar_Util.format1 "unknown constant: %s" uu____1510  in
              failwith uu____1509
           in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1511 ->
        ((let uu____1513 = FStar_Syntax_Print.tag_of_term t1  in
          let uu____1514 = FStar_Syntax_Print.term_to_string t1  in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1513 uu____1514);
         FStar_Reflection_Data.Tv_Unknown)
  
let pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Syntax_Const.exp_unit
    | FStar_Reflection_Data.C_Int s -> FStar_Syntax_Const.exp_int s
    | FStar_Reflection_Data.C_True  -> FStar_Syntax_Const.exp_true_bool
    | FStar_Reflection_Data.C_False  -> FStar_Syntax_Const.exp_false_bool
  
let pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1523) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1527 =
          let uu____1533 = FStar_Syntax_Syntax.as_arg r  in [uu____1533]  in
        FStar_Syntax_Util.mk_app l uu____1527
    | FStar_Reflection_Data.Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1538 = FStar_Syntax_Syntax.mk_Total t  in
        FStar_Syntax_Util.arrow [b] uu____1538
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1542),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | uu____1547 -> failwith "pack: unexpected term view"
  
let embed_order : FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
  
let unembed_order : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____1555 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1555 with
    | (hd1,args) ->
        let uu____1581 =
          let uu____1589 =
            let uu____1590 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1590.FStar_Syntax_Syntax.n  in
          (uu____1589, args)  in
        (match uu____1581 with
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
         | uu____1628 -> failwith "not an embedded order")
  
let order_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Reflection_Data.order
  =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y)  in
      if n1 < (Prims.parse_int "0")
      then FStar_Reflection_Data.Lt
      else
        if n1 = (Prims.parse_int "0")
        then FStar_Reflection_Data.Eq
        else FStar_Reflection_Data.Gt
  
let is_free :
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  -> fun t  -> FStar_Syntax_Util.is_free_in (fst x) t 
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
    let uu____1658 = FStar_Syntax_Util.head_and_args t1  in
    match uu____1658 with
    | (hd1,args) ->
        let uu____1684 =
          let uu____1692 =
            let uu____1693 = FStar_Syntax_Util.un_uinst hd1  in
            uu____1693.FStar_Syntax_Syntax.n  in
          (uu____1692, args)  in
        (match uu____1684 with
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
         | uu____1741 -> failwith "not an embedded norm_step")
  