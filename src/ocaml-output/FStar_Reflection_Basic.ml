open Prims
let protect_embedded_term:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun x  ->
      let uu____9 =
        let uu____10 =
          let uu____11 = FStar_Syntax_Syntax.iarg t in
          let uu____12 =
            let uu____14 = FStar_Syntax_Syntax.as_arg x in [uu____14] in
          uu____11 :: uu____12 in
        FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Const.fstar_refl_embed
          uu____10 in
      uu____9 None x.FStar_Syntax_Syntax.pos
let un_protect_embedded_term:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____22 = FStar_Syntax_Util.head_and_args t in
    match uu____22 with
    | (head1,args) ->
        let uu____48 =
          let uu____56 =
            let uu____57 = FStar_Syntax_Util.un_uinst head1 in
            uu____57.FStar_Syntax_Syntax.n in
          (uu____56, args) in
        (match uu____48 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____66::(x,uu____68)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Syntax_Const.fstar_refl_embed_lid
             -> x
         | uu____94 ->
             let uu____102 =
               let uu____103 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.format1 "Not a protected embedded term: %s"
                 uu____103 in
             failwith uu____102)
let embed_unit: Prims.unit -> FStar_Syntax_Syntax.term =
  fun u  -> FStar_Syntax_Const.exp_unit
let unembed_unit: FStar_Syntax_Syntax.term -> Prims.unit =
  fun uu____109  -> ()
let embed_bool: Prims.bool -> FStar_Syntax_Syntax.term =
  fun b  ->
    if b
    then FStar_Syntax_Const.exp_true_bool
    else FStar_Syntax_Const.exp_false_bool
let unembed_bool: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____117 =
      let uu____118 = FStar_Syntax_Subst.compress t in
      uu____118.FStar_Syntax_Syntax.n in
    match uu____117 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) -> b
    | uu____122 -> failwith "Not an embedded bool"
let embed_int: Prims.int -> FStar_Syntax_Syntax.term =
  fun i  ->
    let uu____126 = FStar_Util.string_of_int i in
    FStar_Syntax_Const.exp_int uu____126
let unembed_int: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    let uu____130 =
      let uu____131 = FStar_Syntax_Subst.compress t in
      uu____131.FStar_Syntax_Syntax.n in
    match uu____130 with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s,uu____135))
        -> FStar_Util.int_of_string s
    | uu____142 -> failwith "Not an embedded int"
let embed_string:
  Prims.string ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    let bytes = FStar_Util.unicode_of_string s in
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (bytes, FStar_Range.dummyRange))) None
      FStar_Range.dummyRange
let unembed_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (bytes,uu____158)) -> FStar_Util.string_of_unicode bytes
    | uu____161 ->
        let uu____162 =
          let uu____163 =
            let uu____164 = FStar_Syntax_Print.term_to_string t1 in
            Prims.strcat uu____164 ")" in
          Prims.strcat "Not an embedded string (" uu____163 in
        failwith uu____162
let lid_Mktuple2: FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2")
    FStar_Range.dummyRange
let lid_tuple2: FStar_Ident.lident =
  FStar_Syntax_Util.mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange
let embed_binder:
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    let uu____168 = FStar_Syntax_Syntax.bv_to_name (fst b) in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_binder uu____168
let unembed_binder: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Syntax_Syntax.mk_binder bv
    | uu____175 -> failwith "Not an embedded binder"
let rec embed_list embed_a typ l =
  match l with
  | [] ->
      let uu____200 =
        let uu____201 =
          let uu____202 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.nil_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____202
            [FStar_Syntax_Syntax.U_zero] in
        let uu____203 =
          let uu____204 = FStar_Syntax_Syntax.iarg typ in [uu____204] in
        FStar_Syntax_Syntax.mk_Tm_app uu____201 uu____203 in
      uu____200 None FStar_Range.dummyRange
  | hd1::tl1 ->
      let uu____212 =
        let uu____213 =
          let uu____214 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.cons_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____214
            [FStar_Syntax_Syntax.U_zero] in
        let uu____215 =
          let uu____216 = FStar_Syntax_Syntax.iarg typ in
          let uu____217 =
            let uu____219 =
              let uu____220 = embed_a hd1 in
              FStar_Syntax_Syntax.as_arg uu____220 in
            let uu____221 =
              let uu____223 =
                let uu____224 = embed_list embed_a typ tl1 in
                FStar_Syntax_Syntax.as_arg uu____224 in
              [uu____223] in
            uu____219 :: uu____221 in
          uu____216 :: uu____217 in
        FStar_Syntax_Syntax.mk_Tm_app uu____213 uu____215 in
      uu____212 None FStar_Range.dummyRange
let rec unembed_list unembed_a l =
  let l1 = FStar_Syntax_Util.unascribe l in
  let uu____248 = FStar_Syntax_Util.head_and_args l1 in
  match uu____248 with
  | (hd1,args) ->
      let uu____275 =
        let uu____283 =
          let uu____284 = FStar_Syntax_Util.un_uinst hd1 in
          uu____284.FStar_Syntax_Syntax.n in
        (uu____283, args) in
      (match uu____275 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____294) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid -> []
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,_t::(hd2,uu____308)::(tl1,uu____310)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
           let uu____344 = unembed_a hd2 in
           let uu____345 = unembed_list unembed_a tl1 in uu____344 ::
             uu____345
       | uu____347 ->
           let uu____355 =
             let uu____356 = FStar_Syntax_Print.term_to_string l1 in
             FStar_Util.format1 "Not an embedded list: %s" uu____356 in
           failwith uu____355)
let embed_binders:
  FStar_Syntax_Syntax.binder Prims.list -> FStar_Syntax_Syntax.term =
  fun l  -> embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder l
let unembed_binders:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binder Prims.list =
  fun t  -> unembed_list unembed_binder t
let embed_term:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> protect_embedded_term FStar_Reflection_Data.fstar_refl_term t
let unembed_term: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> un_protect_embedded_term t
let embed_pair embed_a t_a embed_b t_b x =
  let uu____416 =
    let uu____417 =
      let uu____418 = FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____418
        [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] in
    let uu____419 =
      let uu____420 = FStar_Syntax_Syntax.iarg t_a in
      let uu____421 =
        let uu____423 = FStar_Syntax_Syntax.iarg t_b in
        let uu____424 =
          let uu____426 =
            let uu____427 = embed_a (fst x) in
            FStar_Syntax_Syntax.as_arg uu____427 in
          let uu____428 =
            let uu____430 =
              let uu____431 = embed_b (snd x) in
              FStar_Syntax_Syntax.as_arg uu____431 in
            [uu____430] in
          uu____426 :: uu____428 in
        uu____423 :: uu____424 in
      uu____420 :: uu____421 in
    FStar_Syntax_Syntax.mk_Tm_app uu____417 uu____419 in
  uu____416 None FStar_Range.dummyRange
let unembed_pair unembed_a unembed_b pair =
  let pairs = FStar_Syntax_Util.unascribe pair in
  let uu____468 = FStar_Syntax_Util.head_and_args pair in
  match uu____468 with
  | (hd1,args) ->
      let uu____496 =
        let uu____504 =
          let uu____505 = FStar_Syntax_Util.un_uinst hd1 in
          uu____505.FStar_Syntax_Syntax.n in
        (uu____504, args) in
      (match uu____496 with
       | (FStar_Syntax_Syntax.Tm_fvar
          fv,uu____516::uu____517::(a,uu____519)::(b,uu____521)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2 ->
           let uu____563 = unembed_a a in
           let uu____564 = unembed_b b in (uu____563, uu____564)
       | uu____565 -> failwith "Not an embedded pair")
let embed_option embed_a typ o =
  match o with
  | None  ->
      let uu____599 =
        let uu____600 =
          let uu____601 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.none_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____601
            [FStar_Syntax_Syntax.U_zero] in
        let uu____602 =
          let uu____603 = FStar_Syntax_Syntax.iarg typ in [uu____603] in
        FStar_Syntax_Syntax.mk_Tm_app uu____600 uu____602 in
      uu____599 None FStar_Range.dummyRange
  | Some a ->
      let uu____609 =
        let uu____610 =
          let uu____611 =
            FStar_Reflection_Data.lid_as_data_tm FStar_Syntax_Const.some_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu____611
            [FStar_Syntax_Syntax.U_zero] in
        let uu____612 =
          let uu____613 = FStar_Syntax_Syntax.iarg typ in
          let uu____614 =
            let uu____616 =
              let uu____617 = embed_a a in
              FStar_Syntax_Syntax.as_arg uu____617 in
            [uu____616] in
          uu____613 :: uu____614 in
        FStar_Syntax_Syntax.mk_Tm_app uu____610 uu____612 in
      uu____609 None FStar_Range.dummyRange
let unembed_option unembed_a o =
  let uu____640 = FStar_Syntax_Util.head_and_args o in
  match uu____640 with
  | (hd1,args) ->
      let uu____667 =
        let uu____675 =
          let uu____676 = FStar_Syntax_Util.un_uinst hd1 in
          uu____676.FStar_Syntax_Syntax.n in
        (uu____675, args) in
      (match uu____667 with
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____686) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.none_lid ->
           None
       | (FStar_Syntax_Syntax.Tm_fvar fv,uu____698::(a,uu____700)::[]) when
           FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.some_lid ->
           let uu____726 = unembed_a a in Some uu____726
       | uu____727 -> failwith "Not an embedded option")
let embed_fvar:
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun fv  ->
    let uu____739 = FStar_Syntax_Syntax.fv_to_tm fv in
    protect_embedded_term FStar_Reflection_Data.fstar_refl_fvar uu____739
let unembed_fvar: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv =
  fun t  ->
    let t1 = un_protect_embedded_term t in
    let t2 = FStar_Syntax_Util.unascribe t1 in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____746 -> failwith "Not an embedded fv"
let embed_const:
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
        let uu____751 =
          let uu____752 =
            let uu____753 =
              let uu____754 = FStar_Syntax_Const.exp_int s in
              FStar_Syntax_Syntax.as_arg uu____754 in
            [uu____753] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int
            uu____752 in
        uu____751 None FStar_Range.dummyRange
let embed_term_view:
  FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun t  ->
    match t with
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____763 =
          let uu____764 =
            let uu____765 =
              let uu____766 = embed_fvar fv in
              FStar_Syntax_Syntax.as_arg uu____766 in
            [uu____765] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar
            uu____764 in
        uu____763 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____772 =
          let uu____773 =
            let uu____774 =
              let uu____775 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____775 in
            [uu____774] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var
            uu____773 in
        uu____772 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_App (hd1,a) ->
        let uu____782 =
          let uu____783 =
            let uu____784 =
              let uu____785 = embed_term hd1 in
              FStar_Syntax_Syntax.as_arg uu____785 in
            let uu____786 =
              let uu____788 =
                let uu____789 = embed_term a in
                FStar_Syntax_Syntax.as_arg uu____789 in
              [uu____788] in
            uu____784 :: uu____786 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App
            uu____783 in
        uu____782 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Abs (b,t1) ->
        let uu____796 =
          let uu____797 =
            let uu____798 =
              let uu____799 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____799 in
            let uu____800 =
              let uu____802 =
                let uu____803 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____803 in
              [uu____802] in
            uu____798 :: uu____800 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs
            uu____797 in
        uu____796 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Arrow (b,t1) ->
        let uu____810 =
          let uu____811 =
            let uu____812 =
              let uu____813 = embed_binder b in
              FStar_Syntax_Syntax.as_arg uu____813 in
            let uu____814 =
              let uu____816 =
                let uu____817 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____817 in
              [uu____816] in
            uu____812 :: uu____814 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow
            uu____811 in
        uu____810 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Type u ->
        let uu____823 =
          let uu____824 =
            let uu____825 =
              let uu____826 = embed_unit () in
              FStar_Syntax_Syntax.as_arg uu____826 in
            [uu____825] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type
            uu____824 in
        uu____823 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Refine (bv,t1) ->
        let uu____833 =
          let uu____834 =
            let uu____835 =
              let uu____836 = embed_binder bv in
              FStar_Syntax_Syntax.as_arg uu____836 in
            let uu____837 =
              let uu____839 =
                let uu____840 = embed_term t1 in
                FStar_Syntax_Syntax.as_arg uu____840 in
              [uu____839] in
            uu____835 :: uu____837 in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine
            uu____834 in
        uu____833 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____846 =
          let uu____847 =
            let uu____848 =
              let uu____849 = embed_const c in
              FStar_Syntax_Syntax.as_arg uu____849 in
            [uu____848] in
          FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const
            uu____847 in
        uu____846 None FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown  ->
        FStar_Reflection_Data.ref_Tv_Unknown
let unembed_const: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.vconst =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____858 = FStar_Syntax_Util.head_and_args t1 in
    match uu____858 with
    | (hd1,args) ->
        let uu____884 =
          let uu____892 =
            let uu____893 = FStar_Syntax_Util.un_uinst hd1 in
            uu____893.FStar_Syntax_Syntax.n in
          (uu____892, args) in
        (match uu____884 with
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
         | (FStar_Syntax_Syntax.Tm_fvar fv,(i,uu____933)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_C_Int_lid
             ->
             let uu____951 =
               let uu____952 = FStar_Syntax_Subst.compress i in
               uu____952.FStar_Syntax_Syntax.n in
             (match uu____951 with
              | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                  (s,uu____956)) -> FStar_Reflection_Data.C_Int s
              | uu____963 ->
                  failwith "unembed_const: unexpected arg for C_Int")
         | uu____964 -> failwith "not an embedded vconst")
let unembed_term_view:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____976 = FStar_Syntax_Util.head_and_args t1 in
    match uu____976 with
    | (hd1,args) ->
        let uu____1002 =
          let uu____1010 =
            let uu____1011 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1011.FStar_Syntax_Syntax.n in
          (uu____1010, args) in
        (match uu____1002 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1021)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Var_lid
             ->
             let uu____1039 = unembed_binder b in
             FStar_Reflection_Data.Tv_Var uu____1039
         | (FStar_Syntax_Syntax.Tm_fvar fv,(b,uu____1042)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_FVar_lid
             ->
             let uu____1060 = unembed_fvar b in
             FStar_Reflection_Data.Tv_FVar uu____1060
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(l,uu____1063)::(r,uu____1065)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_App_lid
             ->
             let uu____1091 =
               let uu____1094 = unembed_term l in
               let uu____1095 = unembed_term r in (uu____1094, uu____1095) in
             FStar_Reflection_Data.Tv_App uu____1091
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1098)::(t2,uu____1100)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Abs_lid
             ->
             let uu____1126 =
               let uu____1129 = unembed_binder b in
               let uu____1130 = unembed_term t2 in (uu____1129, uu____1130) in
             FStar_Reflection_Data.Tv_Abs uu____1126
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1133)::(t2,uu____1135)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Arrow_lid
             ->
             let uu____1161 =
               let uu____1164 = unembed_binder b in
               let uu____1165 = unembed_term t2 in (uu____1164, uu____1165) in
             FStar_Reflection_Data.Tv_Arrow uu____1161
         | (FStar_Syntax_Syntax.Tm_fvar fv,(u,uu____1168)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Type_lid
             -> (unembed_unit u; FStar_Reflection_Data.Tv_Type ())
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,(b,uu____1189)::(t2,uu____1191)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Refine_lid
             ->
             let uu____1217 =
               let uu____1220 = unembed_binder b in
               let uu____1221 = unembed_term t2 in (uu____1220, uu____1221) in
             FStar_Reflection_Data.Tv_Refine uu____1217
         | (FStar_Syntax_Syntax.Tm_fvar fv,(c,uu____1224)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Const_lid
             ->
             let uu____1242 = unembed_const c in
             FStar_Reflection_Data.Tv_Const uu____1242
         | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Reflection_Data.ref_Tv_Unknown_lid
             -> FStar_Reflection_Data.Tv_Unknown
         | uu____1253 -> failwith "not an embedded term_view")
let rec last l =
  match l with
  | [] -> failwith "last: empty list"
  | x::[] -> x
  | uu____1271::xs -> last xs
let rec init l =
  match l with
  | [] -> failwith "init: empty list"
  | x::[] -> []
  | x::xs -> let uu____1289 = init xs in x :: uu____1289
let inspect_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    let uu____1296 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____1296
let pack_fv: Prims.string Prims.list -> FStar_Syntax_Syntax.fv =
  fun ns  ->
    let uu____1302 = FStar_Syntax_Const.p2l ns in
    FStar_Syntax_Syntax.lid_as_fv uu____1302
      FStar_Syntax_Syntax.Delta_equational None
let inspect_bv: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> FStar_Syntax_Print.bv_to_string (fst b)
let inspect: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view =
  fun t  ->
    let t1 = FStar_Syntax_Util.un_uinst t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____1311 = FStar_Syntax_Syntax.mk_binder bv in
        FStar_Reflection_Data.Tv_Var uu____1311
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____1343 = last args in
        (match uu____1343 with
         | (a,uu____1353) ->
             let uu____1358 =
               let uu____1361 =
                 let uu____1364 =
                   let uu____1365 = init args in
                   FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1365 in
                 uu____1364 None t1.FStar_Syntax_Syntax.pos in
               (uu____1361, a) in
             FStar_Reflection_Data.Tv_App uu____1358)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____1378,uu____1379) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
        let uu____1426 = FStar_Syntax_Subst.open_term bs t2 in
        (match uu____1426 with
         | (bs1,t3) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1442 =
                    let uu____1445 = FStar_Syntax_Util.abs bs2 t3 k in
                    (b, uu____1445) in
                  FStar_Reflection_Data.Tv_Abs uu____1442))
    | FStar_Syntax_Syntax.Tm_type uu____1448 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
        let uu____1471 = FStar_Syntax_Subst.open_comp bs k in
        (match uu____1471 with
         | (bs1,k1) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____1487 =
                    let uu____1490 = FStar_Syntax_Util.arrow bs2 k1 in
                    (b, uu____1490) in
                  FStar_Reflection_Data.Tv_Arrow uu____1487))
    | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
        let b = FStar_Syntax_Syntax.mk_binder bv in
        let uu____1504 = FStar_Syntax_Subst.open_term [b] t2 in
        (match uu____1504 with
         | (b',t3) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____1521 -> failwith "impossible" in
             FStar_Reflection_Data.Tv_Refine (b1, t3))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let c1 =
          match c with
          | FStar_Const.Const_unit  -> FStar_Reflection_Data.C_Unit
          | FStar_Const.Const_int (s,uu____1529) ->
              FStar_Reflection_Data.C_Int s
          | FStar_Const.Const_bool (true ) -> FStar_Reflection_Data.C_True
          | FStar_Const.Const_bool (false ) -> FStar_Reflection_Data.C_False
          | uu____1536 ->
              let uu____1537 =
                let uu____1538 = FStar_Syntax_Print.const_to_string c in
                FStar_Util.format1 "unknown constant: %s" uu____1538 in
              failwith uu____1537 in
        FStar_Reflection_Data.Tv_Const c1
    | uu____1539 ->
        ((let uu____1541 = FStar_Syntax_Print.tag_of_term t1 in
          let uu____1542 = FStar_Syntax_Print.term_to_string t1 in
          FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n"
            uu____1541 uu____1542);
         FStar_Reflection_Data.Tv_Unknown)
let pack_const: FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.term =
  fun c  ->
    match c with
    | FStar_Reflection_Data.C_Unit  -> FStar_Syntax_Const.exp_unit
    | FStar_Reflection_Data.C_Int s -> FStar_Syntax_Const.exp_int s
    | FStar_Reflection_Data.C_True  -> FStar_Syntax_Const.exp_true_bool
    | FStar_Reflection_Data.C_False  -> FStar_Syntax_Const.exp_false_bool
let pack: FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var (bv,uu____1551) ->
        FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l,r) ->
        let uu____1555 =
          let uu____1561 = FStar_Syntax_Syntax.as_arg r in [uu____1561] in
        FStar_Syntax_Util.mk_app l uu____1555
    | FStar_Reflection_Data.Tv_Abs (b,t) -> FStar_Syntax_Util.abs [b] t None
    | FStar_Reflection_Data.Tv_Arrow (b,t) ->
        let uu____1571 = FStar_Syntax_Syntax.mk_Total t in
        FStar_Syntax_Util.arrow [b] uu____1571
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine ((bv,uu____1575),t) ->
        FStar_Syntax_Util.refine bv t
    | FStar_Reflection_Data.Tv_Const c -> pack_const c
    | uu____1580 -> failwith "pack: unexpected term view"
let embed_order: FStar_Reflection_Data.order -> FStar_Syntax_Syntax.term =
  fun o  ->
    match o with
    | FStar_Reflection_Data.Lt  -> FStar_Reflection_Data.ord_Lt
    | FStar_Reflection_Data.Eq  -> FStar_Reflection_Data.ord_Eq
    | FStar_Reflection_Data.Gt  -> FStar_Reflection_Data.ord_Gt
let unembed_order: FStar_Syntax_Syntax.term -> FStar_Reflection_Data.order =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1588 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1588 with
    | (hd1,args) ->
        let uu____1614 =
          let uu____1622 =
            let uu____1623 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1623.FStar_Syntax_Syntax.n in
          (uu____1622, args) in
        (match uu____1614 with
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
         | uu____1661 -> failwith "not an embedded order")
let order_binder:
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder -> FStar_Reflection_Data.order
  =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y) in
      if n1 < (Prims.parse_int "0")
      then FStar_Reflection_Data.Lt
      else
        if n1 = (Prims.parse_int "0")
        then FStar_Reflection_Data.Eq
        else FStar_Reflection_Data.Gt
let is_free:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun x  -> fun t  -> FStar_Syntax_Util.is_free_in (fst x) t
let embed_norm_step:
  FStar_Reflection_Data.norm_step -> FStar_Syntax_Syntax.term =
  fun n1  ->
    match n1 with
    | FStar_Reflection_Data.Simpl  -> FStar_Reflection_Data.ref_Simpl
    | FStar_Reflection_Data.WHNF  -> FStar_Reflection_Data.ref_WHNF
    | FStar_Reflection_Data.Primops  -> FStar_Reflection_Data.ref_Primops
    | FStar_Reflection_Data.Delta  -> FStar_Reflection_Data.ref_Delta
let unembed_norm_step:
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.norm_step =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1691 = FStar_Syntax_Util.head_and_args t1 in
    match uu____1691 with
    | (hd1,args) ->
        let uu____1717 =
          let uu____1725 =
            let uu____1726 = FStar_Syntax_Util.un_uinst hd1 in
            uu____1726.FStar_Syntax_Syntax.n in
          (uu____1725, args) in
        (match uu____1717 with
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
         | uu____1774 -> failwith "not an embedded norm_step")