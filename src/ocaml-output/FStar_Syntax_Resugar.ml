open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.of_int (100)) doc
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t ->
    let uu____10 = FStar_Parser_ToDocument.term_to_document t in
    doc_to_string uu____10
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t ->
    let uu____16 = FStar_Parser_ToDocument.pat_to_document t in
    doc_to_string uu____16
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t -> FStar_Syntax_Util.tts t
let map_opt :
  'uuuuuu30 'uuuuuu31 .
    unit ->
      ('uuuuuu30 -> 'uuuuuu31 FStar_Pervasives_Native.option) ->
        'uuuuuu30 Prims.list -> 'uuuuuu31 Prims.list
  = fun uu____48 -> FStar_List.filter_map
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x ->
    let unique_name =
      let uu____55 =
        (let uu____58 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
         FStar_Util.starts_with FStar_Ident.reserved_prefix uu____58) ||
          (FStar_Options.print_real_names ()) in
      if uu____55
      then
        let uu____59 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
        let uu____60 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.op_Hat uu____59 uu____60
      else FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
    let uu____62 =
      let uu____67 = FStar_Ident.range_of_id x.FStar_Syntax_Syntax.ppname in
      (unique_name, uu____67) in
    FStar_Ident.mk_ident uu____62
let filter_imp :
  'uuuuuu72 .
    ('uuuuuu72 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu72 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_127 ->
            match uu___0_127 with
            | (uu____134, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta
               (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____140, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____141)) -> false
            | (uu____144, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____145)) -> false
            | uu____148 -> true))
let filter_pattern_imp :
  'uuuuuu159 .
    ('uuuuuu159 * Prims.bool) Prims.list ->
      ('uuuuuu159 * Prims.bool) Prims.list
  =
  fun xs ->
    FStar_List.filter
      (fun uu____190 ->
         match uu____190 with
         | (uu____195, is_implicit) -> Prims.op_Negation is_implicit) xs
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s ->
    fun t ->
      if s = ""
      then t
      else
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (t, s, true))
          t.FStar_Parser_AST.range FStar_Parser_AST.Un
let rec (universe_to_int :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe))
  =
  fun n ->
    fun u ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n + Prims.int_one) u1
      | uu____227 -> (n, u)
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs ->
    let uu____237 = FStar_Options.print_universes () in
    if uu____237
    then
      let uu____238 =
        FStar_List.map (fun x -> FStar_Ident.string_of_id x) univs in
      FStar_All.pipe_right uu____238 (FStar_String.concat ", ")
    else ""
let rec (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u ->
    fun r ->
      let mk a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un in
      match u with
      | FStar_Syntax_Syntax.U_zero ->
          mk
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____277 ->
          let uu____278 = universe_to_int Prims.int_zero u in
          (match uu____278 with
           | (n, u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero ->
                    let uu____285 =
                      let uu____286 =
                        let uu____287 =
                          let uu____298 = FStar_Util.string_of_int n in
                          (uu____298, FStar_Pervasives_Native.None) in
                        FStar_Const.Const_int uu____287 in
                      FStar_Parser_AST.Const uu____286 in
                    mk uu____285 r
                | uu____309 ->
                    let e1 =
                      let uu____311 =
                        let uu____312 =
                          let uu____313 =
                            let uu____324 = FStar_Util.string_of_int n in
                            (uu____324, FStar_Pervasives_Native.None) in
                          FStar_Const.Const_int uu____313 in
                        FStar_Parser_AST.Const uu____312 in
                      mk uu____311 r in
                    let e2 = resugar_universe u1 r in
                    let uu____336 =
                      let uu____337 =
                        let uu____344 = FStar_Ident.id_of_text "+" in
                        (uu____344, [e1; e2]) in
                      FStar_Parser_AST.Op uu____337 in
                    mk uu____336 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____350 ->
               let t =
                 let uu____354 =
                   let uu____355 = FStar_Ident.lid_of_path ["max"] r in
                   FStar_Parser_AST.Var uu____355 in
                 mk uu____354 r in
               FStar_List.fold_left
                 (fun acc ->
                    fun x ->
                      let uu____361 =
                        let uu____362 =
                          let uu____369 = resugar_universe x r in
                          (acc, uu____369, FStar_Parser_AST.Nothing) in
                        FStar_Parser_AST.App uu____362 in
                      mk uu____361 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____371 -> mk FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id =
            let uu____384 =
              let uu____389 =
                let uu____390 = FStar_Util.string_of_int x in
                FStar_Util.strcat "uu__univ_bvar_" uu____390 in
              (uu____389, r) in
            FStar_Ident.mk_ident uu____384 in
          mk (FStar_Parser_AST.Uvar id) r
      | FStar_Syntax_Syntax.U_unknown -> mk FStar_Parser_AST.Wild r
let (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env -> fun u -> fun r -> resugar_universe u r
let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s ->
    let name_of_op uu___1_432 =
      match uu___1_432 with
      | "Amp" ->
          FStar_Pervasives_Native.Some ("&", FStar_Pervasives_Native.None)
      | "At" ->
          FStar_Pervasives_Native.Some ("@", FStar_Pervasives_Native.None)
      | "Plus" ->
          FStar_Pervasives_Native.Some ("+", FStar_Pervasives_Native.None)
      | "Minus" ->
          FStar_Pervasives_Native.Some ("-", FStar_Pervasives_Native.None)
      | "Subtraction" ->
          FStar_Pervasives_Native.Some
            ("-", (FStar_Pervasives_Native.Some (Prims.of_int (2))))
      | "Tilde" ->
          FStar_Pervasives_Native.Some ("~", FStar_Pervasives_Native.None)
      | "Slash" ->
          FStar_Pervasives_Native.Some ("/", FStar_Pervasives_Native.None)
      | "Backslash" ->
          FStar_Pervasives_Native.Some ("\\", FStar_Pervasives_Native.None)
      | "Less" ->
          FStar_Pervasives_Native.Some ("<", FStar_Pervasives_Native.None)
      | "Equals" ->
          FStar_Pervasives_Native.Some ("=", FStar_Pervasives_Native.None)
      | "Greater" ->
          FStar_Pervasives_Native.Some (">", FStar_Pervasives_Native.None)
      | "Underscore" ->
          FStar_Pervasives_Native.Some ("_", FStar_Pervasives_Native.None)
      | "Bar" ->
          FStar_Pervasives_Native.Some ("|", FStar_Pervasives_Native.None)
      | "Bang" ->
          FStar_Pervasives_Native.Some ("!", FStar_Pervasives_Native.None)
      | "Hat" ->
          FStar_Pervasives_Native.Some ("^", FStar_Pervasives_Native.None)
      | "Percent" ->
          FStar_Pervasives_Native.Some ("%", FStar_Pervasives_Native.None)
      | "Star" ->
          FStar_Pervasives_Native.Some ("*", FStar_Pervasives_Native.None)
      | "Question" ->
          FStar_Pervasives_Native.Some ("?", FStar_Pervasives_Native.None)
      | "Colon" ->
          FStar_Pervasives_Native.Some (":", FStar_Pervasives_Native.None)
      | "Dollar" ->
          FStar_Pervasives_Native.Some ("$", FStar_Pervasives_Native.None)
      | "Dot" ->
          FStar_Pervasives_Native.Some (".", FStar_Pervasives_Native.None)
      | uu____609 -> FStar_Pervasives_Native.None in
    match s with
    | "op_String_Assignment" ->
        FStar_Pervasives_Native.Some (".[]<-", FStar_Pervasives_Native.None)
    | "op_Array_Assignment" ->
        FStar_Pervasives_Native.Some (".()<-", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".[||]<-", FStar_Pervasives_Native.None)
    | "op_Lens_Assignment" ->
        FStar_Pervasives_Native.Some
          (".(||)<-", FStar_Pervasives_Native.None)
    | "op_String_Access" ->
        FStar_Pervasives_Native.Some (".[]", FStar_Pervasives_Native.None)
    | "op_Array_Access" ->
        FStar_Pervasives_Native.Some (".()", FStar_Pervasives_Native.None)
    | "op_Brack_Lens_Access" ->
        FStar_Pervasives_Native.Some (".[||]", FStar_Pervasives_Native.None)
    | "op_Lens_Access" ->
        FStar_Pervasives_Native.Some (".(||)", FStar_Pervasives_Native.None)
    | uu____688 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____700 =
              FStar_Util.substring_from s (FStar_String.length "op_") in
            FStar_Util.split uu____700 "_" in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____710 ->
               let maybeop =
                 let uu____716 = FStar_List.map name_of_op s1 in
                 FStar_List.fold_left
                   (fun acc ->
                      fun x ->
                        match acc with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some acc1 ->
                            (match x with
                             | FStar_Pervasives_Native.Some (op, uu____765)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (Prims.op_Hat acc1 op)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None))
                   (FStar_Pervasives_Native.Some "") uu____716 in
               FStar_Util.map_opt maybeop
                 (fun o -> (o, FStar_Pervasives_Native.None)))
        else FStar_Pervasives_Native.None
type expected_arity = Prims.int FStar_Pervasives_Native.option
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string * expected_arity) FStar_Pervasives_Native.option)
  =
  fun t ->
    let infix_prim_ops =
      [(FStar_Parser_Const.op_Addition, "+");
      (FStar_Parser_Const.op_Subtraction, "-");
      (FStar_Parser_Const.op_Minus, "-");
      (FStar_Parser_Const.op_Multiply, "*");
      (FStar_Parser_Const.op_Division, "/");
      (FStar_Parser_Const.op_Modulus, "%");
      (FStar_Parser_Const.read_lid, "!");
      (FStar_Parser_Const.list_append_lid, "@");
      (FStar_Parser_Const.list_tot_append_lid, "@");
      (FStar_Parser_Const.pipe_right_lid, "|>");
      (FStar_Parser_Const.pipe_left_lid, "<|");
      (FStar_Parser_Const.op_Eq, "=");
      (FStar_Parser_Const.op_ColonEq, ":=");
      (FStar_Parser_Const.op_notEq, "<>");
      (FStar_Parser_Const.not_lid, "~");
      (FStar_Parser_Const.op_And, "&&");
      (FStar_Parser_Const.op_Or, "||");
      (FStar_Parser_Const.op_LTE, "<=");
      (FStar_Parser_Const.op_GTE, ">=");
      (FStar_Parser_Const.op_LT, "<");
      (FStar_Parser_Const.op_GT, ">");
      (FStar_Parser_Const.op_Modulus, "mod");
      (FStar_Parser_Const.and_lid, "/\\");
      (FStar_Parser_Const.or_lid, "\\/");
      (FStar_Parser_Const.imp_lid, "==>");
      (FStar_Parser_Const.iff_lid, "<==>");
      (FStar_Parser_Const.precedes_lid, "<<");
      (FStar_Parser_Const.eq2_lid, "==");
      (FStar_Parser_Const.eq3_lid, "===");
      (FStar_Parser_Const.forall_lid, "forall");
      (FStar_Parser_Const.exists_lid, "exists");
      (FStar_Parser_Const.salloc_lid, "alloc");
      (FStar_Parser_Const.calc_finish_lid, "calc_finish")] in
    let fallback fv =
      let uu____975 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d))) in
      match uu____975 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1029 ->
          let length =
            let uu____1037 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_String.length uu____1037 in
          let str =
            if length = Prims.int_zero
            then
              FStar_Ident.string_of_lid
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            else
              (let uu____1040 =
                 FStar_Ident.string_of_lid
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_Util.substring_from uu____1040 (length + Prims.int_one)) in
          let uu____1041 =
            (FStar_Util.starts_with str "dtuple") &&
              (let uu____1043 =
                 let uu____1046 =
                   FStar_Util.substring_from str (Prims.of_int (6)) in
                 FStar_Util.safe_int_of_string uu____1046 in
               FStar_Option.isSome uu____1043) in
          if uu____1041
          then
            let uu____1055 =
              let uu____1062 =
                let uu____1065 =
                  FStar_Util.substring_from str (Prims.of_int (6)) in
                FStar_Util.safe_int_of_string uu____1065 in
              ("dtuple", uu____1062) in
            FStar_Pervasives_Native.Some uu____1055
          else
            (let uu____1075 =
               (FStar_Util.starts_with str "tuple") &&
                 (let uu____1077 =
                    let uu____1080 =
                      FStar_Util.substring_from str (Prims.of_int (5)) in
                    FStar_Util.safe_int_of_string uu____1080 in
                  FStar_Option.isSome uu____1077) in
             if uu____1075
             then
               let uu____1089 =
                 let uu____1096 =
                   let uu____1099 =
                     FStar_Util.substring_from str (Prims.of_int (5)) in
                   FStar_Util.safe_int_of_string uu____1099 in
                 ("tuple", uu____1096) in
               FStar_Pervasives_Native.Some uu____1089
             else
               if FStar_Util.starts_with str "try_with"
               then
                 FStar_Pervasives_Native.Some
                   ("try_with", FStar_Pervasives_Native.None)
               else
                 (let uu____1126 =
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.sread_lid in
                  if uu____1126
                  then
                    let uu____1135 =
                      let uu____1142 =
                        FStar_Ident.string_of_lid
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                      (uu____1142, FStar_Pervasives_Native.None) in
                    FStar_Pervasives_Native.Some uu____1135
                  else FStar_Pervasives_Native.None)) in
    let uu____1158 =
      let uu____1159 = FStar_Syntax_Subst.compress t in
      uu____1159.FStar_Syntax_Syntax.n in
    match uu____1158 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length =
          let uu____1170 =
            FStar_Ident.nsstr
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_String.length uu____1170 in
        let s =
          if length = Prims.int_zero
          then
            FStar_Ident.string_of_lid
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          else
            (let uu____1173 =
               FStar_Ident.string_of_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             FStar_Util.substring_from uu____1173 (length + Prims.int_one)) in
        let uu____1174 = string_to_op s in
        (match uu____1174 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1206 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e, us) -> resugar_term_as_op e
    | uu____1221 -> FStar_Pervasives_Native.None
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) ->
        true
    | uu____1231 -> false
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1237 -> true
    | uu____1238 -> false
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    let uu____1249 = FStar_Ident.string_of_lid lid in
    match uu____1249 with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1250 ->
        let uu____1251 = is_tuple_constructor_lid lid in
        Prims.op_Negation uu____1251
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____1263 = may_shorten lid in
      if uu____1263 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env ->
    fun t ->
      let mk a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un in
      let name a r =
        let uu____1412 = FStar_Ident.lid_of_path [a] r in
        FStar_Parser_AST.Name uu____1412 in
      let uu____1413 =
        let uu____1414 = FStar_Syntax_Subst.compress t in
        uu____1414.FStar_Syntax_Syntax.n in
      match uu____1413 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1417 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1433 = FStar_Syntax_Util.unfold_lazy i in
          resugar_term' env uu____1433
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1436 =
              let uu____1437 = bv_as_unique_ident x in [uu____1437] in
            FStar_Ident.lid_of_ids uu____1436 in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1440 =
              let uu____1441 = bv_as_unique_ident x in [uu____1441] in
            FStar_Ident.lid_of_ids uu____1440 in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let length =
            let uu____1445 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_String.length uu____1445 in
          let s =
            if length = Prims.int_zero
            then FStar_Ident.string_of_lid a
            else
              (let uu____1448 = FStar_Ident.string_of_lid a in
               FStar_Util.substring_from uu____1448 (length + Prims.int_one)) in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_" in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix) in
            let uu____1451 =
              let uu____1452 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
              FStar_Parser_AST.Discrim uu____1452 in
            mk uu____1451
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
            then
              (let rest =
                 FStar_Util.substring_from s
                   (FStar_String.length
                      FStar_Syntax_Util.field_projector_prefix) in
               let r =
                 FStar_Util.split rest FStar_Syntax_Util.field_projector_sep in
               match r with
               | fst::snd::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst] t.FStar_Syntax_Syntax.pos in
                   let r1 =
                     FStar_Ident.mk_ident (snd, (t.FStar_Syntax_Syntax.pos)) in
                   mk (FStar_Parser_AST.Projector (l, r1))
               | uu____1462 -> failwith "wrong projector format")
            else
              (let uu____1466 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid in
               if uu____1466
               then
                 let uu____1467 =
                   let uu____1468 =
                     let uu____1469 =
                       let uu____1474 = FStar_Ident.range_of_lid a in
                       ("SMTPat", uu____1474) in
                     FStar_Ident.mk_ident uu____1469 in
                   FStar_Parser_AST.Tvar uu____1468 in
                 mk uu____1467
               else
                 (let uu____1476 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid in
                  if uu____1476
                  then
                    let uu____1477 =
                      let uu____1478 =
                        let uu____1479 =
                          let uu____1484 = FStar_Ident.range_of_lid a in
                          ("SMTPatOr", uu____1484) in
                        FStar_Ident.mk_ident uu____1479 in
                      FStar_Parser_AST.Tvar uu____1478 in
                    mk uu____1477
                  else
                    (let uu____1486 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____1489 =
                            let uu____1490 =
                              FStar_String.get s Prims.int_zero in
                            FStar_Char.uppercase uu____1490 in
                          let uu____1491 = FStar_String.get s Prims.int_zero in
                          uu____1489 <> uu____1491) in
                     if uu____1486
                     then
                       let uu____1492 =
                         let uu____1493 = maybe_shorten_fv env fv in
                         FStar_Parser_AST.Var uu____1493 in
                       mk uu____1492
                     else
                       (let uu____1495 =
                          let uu____1496 =
                            let uu____1507 = maybe_shorten_fv env fv in
                            (uu____1507, []) in
                          FStar_Parser_AST.Construct uu____1496 in
                        mk uu____1495))))
      | FStar_Syntax_Syntax.Tm_uinst (e, universes) ->
          let e1 = resugar_term' env e in
          let uu____1525 = FStar_Options.print_universes () in
          if uu____1525
          then
            let univs =
              FStar_List.map
                (fun x -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd, args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____1554 =
                     FStar_List.map (fun u -> (u, FStar_Parser_AST.UnivApp))
                       univs in
                   FStar_List.append args uu____1554 in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd, args1)) r l
             | uu____1577 ->
                 FStar_List.fold_left
                   (fun acc ->
                      fun u ->
                        mk
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1584 = FStar_Syntax_Syntax.is_teff t in
          if uu____1584
          then
            let uu____1585 = name "Effect" t.FStar_Syntax_Syntax.pos in
            mk uu____1585
          else mk (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1588 =
            match u with
            | FStar_Syntax_Syntax.U_zero -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown -> ("Type", false)
            | uu____1597 -> ("Type", true) in
          (match uu____1588 with
           | (nm, needs_app) ->
               let typ =
                 let uu____1601 = name nm t.FStar_Syntax_Syntax.pos in
                 mk uu____1601 in
               let uu____1602 =
                 needs_app && (FStar_Options.print_universes ()) in
               if uu____1602
               then
                 let uu____1603 =
                   let uu____1604 =
                     let uu____1611 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos in
                     (typ, uu____1611, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1604 in
                 mk uu____1603
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs, body, uu____1615) ->
          let uu____1640 = FStar_Syntax_Subst.open_term xs body in
          (match uu____1640 with
           | (xs1, body1) ->
               let xs2 =
                 let uu____1656 = FStar_Options.print_implicits () in
                 if uu____1656 then xs1 else filter_imp xs1 in
               let body_bv = FStar_Syntax_Free.names body1 in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1691 ->
                         match uu____1691 with
                         | (x, qual) -> resugar_bv_as_pat env x qual body_bv)) in
               let body2 = resugar_term' env body1 in
               mk (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow uu____1709 ->
          let uu____1724 =
            let uu____1729 =
              let uu____1730 =
                let uu____1733 = FStar_Syntax_Util.canon_arrow t in
                FStar_Syntax_Subst.compress uu____1733 in
              uu____1730.FStar_Syntax_Syntax.n in
            match uu____1729 with
            | FStar_Syntax_Syntax.Tm_arrow (xs, body) -> (xs, body)
            | uu____1760 -> failwith "impossible: Tm_arrow in resugar_term" in
          (match uu____1724 with
           | (xs, body) ->
               let uu____1767 = FStar_Syntax_Subst.open_comp xs body in
               (match uu____1767 with
                | (xs1, body1) ->
                    let xs2 =
                      let uu____1777 = FStar_Options.print_implicits () in
                      if uu____1777 then xs1 else filter_imp xs1 in
                    let body2 = resugar_comp' env body1 in
                    let xs3 =
                      let uu____1785 =
                        FStar_All.pipe_right xs2
                          ((map_opt ())
                             (fun b ->
                                resugar_binder' env b
                                  t.FStar_Syntax_Syntax.pos)) in
                      FStar_All.pipe_right uu____1785 FStar_List.rev in
                    let rec aux body3 uu___2_1810 =
                      match uu___2_1810 with
                      | [] -> body3
                      | hd::tl ->
                          let body4 =
                            mk (FStar_Parser_AST.Product ([hd], body3)) in
                          aux body4 tl in
                    aux body2 xs3))
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu____1826 =
            let uu____1831 =
              let uu____1832 = FStar_Syntax_Syntax.mk_binder x in
              [uu____1832] in
            FStar_Syntax_Subst.open_term uu____1831 phi in
          (match uu____1826 with
           | (x1, phi1) ->
               let b =
                 let uu____1854 =
                   let uu____1857 = FStar_List.hd x1 in
                   resugar_binder' env uu____1857 t.FStar_Syntax_Syntax.pos in
                 FStar_Util.must uu____1854 in
               let uu____1864 =
                 let uu____1865 =
                   let uu____1870 = resugar_term' env phi1 in (b, uu____1870) in
                 FStar_Parser_AST.Refine uu____1865 in
               mk uu____1864)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1872;
             FStar_Syntax_Syntax.vars = uu____1873;_},
           (e, uu____1875)::[])
          when
          (let uu____1916 = FStar_Options.print_implicits () in
           Prims.op_Negation uu____1916) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e, args) ->
          let rec last uu___3_1964 =
            match uu___3_1964 with
            | hd::[] -> [hd]
            | hd::tl -> last tl
            | uu____2034 -> failwith "last of an empty list" in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2119, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2120))::tl ->
                  drop_implicits tl
              | uu____2138 -> args2 in
            let uu____2147 = drop_implicits args1 in
            match uu____2147 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2178::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2207 -> [a1; a2] in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2307 ->
                   match uu____2307 with
                   | (e2, qual) ->
                       let uu____2324 = resugar_term' env e2 in
                       let uu____2325 = resugar_imp env qual in
                       (uu____2324, uu____2325)) args1 in
            let uu____2326 = resugar_term' env e1 in
            match uu____2326 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd, previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc ->
                     fun uu____2363 ->
                       match uu____2363 with
                       | (x, qual) ->
                           mk (FStar_Parser_AST.App (acc, x, qual))) e2 args2 in
          let args1 =
            let uu____2379 = FStar_Options.print_implicits () in
            if uu____2379 then args else filter_imp args in
          let uu____2391 = resugar_term_as_op e in
          (match uu____2391 with
           | FStar_Pervasives_Native.None -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("calc_finish", uu____2402) ->
               let uu____2407 = resugar_calc env t in
               (match uu____2407 with
                | FStar_Pervasives_Native.Some r -> r
                | uu____2411 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("tuple", uu____2414) ->
               let out =
                 FStar_List.fold_left
                   (fun out ->
                      fun uu____2436 ->
                        match uu____2436 with
                        | (x, uu____2448) ->
                            let x1 = resugar_term' env x in
                            (match out with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix ->
                                 let uu____2457 =
                                   let uu____2458 =
                                     let uu____2459 =
                                       let uu____2466 =
                                         FStar_Ident.id_of_text "*" in
                                       (uu____2466, [prefix; x1]) in
                                     FStar_Parser_AST.Op uu____2459 in
                                   mk uu____2458 in
                                 FStar_Pervasives_Native.Some uu____2457))
                   FStar_Pervasives_Native.None args1 in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple", uu____2469) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last args1 in
               let body =
                 match args2 with
                 | (b, uu____2491)::[] -> b
                 | uu____2508 -> failwith "wrong arguments to dtuple" in
               let uu____2517 =
                 let uu____2518 = FStar_Syntax_Subst.compress body in
                 uu____2518.FStar_Syntax_Syntax.n in
               (match uu____2517 with
                | FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2523) ->
                    let uu____2548 = FStar_Syntax_Subst.open_term xs body1 in
                    (match uu____2548 with
                     | (xs1, body2) ->
                         let xs2 =
                           let uu____2558 = FStar_Options.print_implicits () in
                           if uu____2558 then xs1 else filter_imp xs1 in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos)) in
                         let body3 = resugar_term' env body2 in
                         let uu____2572 =
                           let uu____2573 =
                             let uu____2584 =
                               FStar_List.map
                                 (fun uu____2595 -> FStar_Util.Inl uu____2595)
                                 xs3 in
                             (uu____2584, body3) in
                           FStar_Parser_AST.Sum uu____2573 in
                         mk uu____2572)
                | uu____2602 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2625 ->
                              match uu____2625 with
                              | (e1, qual) -> resugar_term' env e1)) in
                    let e1 = resugar_term' env e in
                    FStar_List.fold_left
                      (fun acc ->
                         fun x ->
                           mk
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple", uu____2643) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read, uu____2649) when
               let uu____2654 =
                 FStar_Ident.string_of_lid FStar_Parser_Const.sread_lid in
               ref_read = uu____2654 ->
               let uu____2655 = FStar_List.hd args1 in
               (match uu____2655 with
                | (t1, uu____2669) ->
                    let uu____2674 =
                      let uu____2675 = FStar_Syntax_Subst.compress t1 in
                      uu____2675.FStar_Syntax_Syntax.n in
                    (match uu____2674 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         let uu____2679 =
                           FStar_Ident.string_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                         FStar_Syntax_Util.field_projector_contains_constructor
                           uu____2679
                         ->
                         let f =
                           let uu____2681 =
                             let uu____2682 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             [uu____2682] in
                           FStar_Ident.lid_of_path uu____2681
                             t1.FStar_Syntax_Syntax.pos in
                         let uu____2683 =
                           let uu____2684 =
                             let uu____2689 = resugar_term' env t1 in
                             (uu____2689, f) in
                           FStar_Parser_AST.Project uu____2684 in
                         mk uu____2683
                     | uu____2690 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with", uu____2691) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___441_2714 ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1 in
                         let uu____2724 =
                           match new_args with
                           | (a1, uu____2734)::(a2, uu____2736)::[] ->
                               (a1, a2)
                           | uu____2763 ->
                               failwith "wrong arguments to try_with" in
                         (match uu____2724 with
                          | (body, handler) ->
                              let decomp term =
                                let uu____2784 =
                                  let uu____2785 =
                                    FStar_Syntax_Subst.compress term in
                                  uu____2785.FStar_Syntax_Syntax.n in
                                match uu____2784 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x, e1, uu____2790) ->
                                    let uu____2815 =
                                      FStar_Syntax_Subst.open_term x e1 in
                                    (match uu____2815 with | (x1, e2) -> e2)
                                | uu____2822 ->
                                    let uu____2823 =
                                      let uu____2824 =
                                        let uu____2825 =
                                          resugar_term' env term in
                                        FStar_Parser_AST.term_to_string
                                          uu____2825 in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____2824 in
                                    failwith uu____2823 in
                              let body1 =
                                let uu____2827 = decomp body in
                                resugar_term' env uu____2827 in
                              let handler1 =
                                let uu____2829 = decomp handler in
                                resugar_term' env uu____2829 in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1, (uu____2837, uu____2838, b)::[]) ->
                                    b
                                | FStar_Parser_AST.Let
                                    (uu____2870, uu____2871, b) -> b
                                | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                                    let uu____2908 =
                                      let uu____2909 =
                                        let uu____2918 = resugar_body t11 in
                                        (uu____2918, t2, t3) in
                                      FStar_Parser_AST.Ascribed uu____2909 in
                                    mk uu____2908
                                | uu____2921 ->
                                    failwith
                                      "unexpected body format to try_with" in
                              let e1 = resugar_body body1 in
                              let rec resugar_branches t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match (e2, branches) ->
                                    branches
                                | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                                    resugar_branches t11
                                | uu____2978 -> [] in
                              let branches = resugar_branches handler1 in
                              mk (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____3011 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with", uu____3012) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op, uu____3018) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op, uu____3024) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs', (uu____3082, pats'), body)
                     ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs', (uu____3114, pats'), body)
                     ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3145 -> (xs, pats, t1) in
               let resugar_forall_body body =
                 let uu____3158 =
                   let uu____3159 = FStar_Syntax_Subst.compress body in
                   uu____3159.FStar_Syntax_Syntax.n in
                 match uu____3158 with
                 | FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____3164) ->
                     let uu____3189 = FStar_Syntax_Subst.open_term xs body1 in
                     (match uu____3189 with
                      | (xs1, body2) ->
                          let xs2 =
                            let uu____3199 = FStar_Options.print_implicits () in
                            if uu____3199 then xs1 else filter_imp xs1 in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos)) in
                          let uu____3212 =
                            let uu____3221 =
                              let uu____3222 =
                                FStar_Syntax_Subst.compress body2 in
                              uu____3222.FStar_Syntax_Syntax.n in
                            match uu____3221 with
                            | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
                                let body3 = resugar_term' env e1 in
                                let uu____3240 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3257, pats) ->
                                      let uu____3291 =
                                        FStar_List.map
                                          (fun es ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3335 ->
                                                     match uu____3335 with
                                                     | (e2, uu____3343) ->
                                                         resugar_term' env e2)))
                                          pats in
                                      (uu____3291, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled
                                      (s, r, p) ->
                                      let uu____3355 =
                                        mk
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p)) in
                                      ([], uu____3355)
                                  | uu____3362 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists" in
                                (match uu____3240 with
                                 | (pats, body4) -> (pats, body4))
                            | uu____3393 ->
                                let uu____3394 = resugar_term' env body2 in
                                ([], uu____3394) in
                          (match uu____3212 with
                           | (pats, body3) ->
                               let uu____3411 = uncurry xs3 pats body3 in
                               (match uu____3411 with
                                | (xs4, pats1, body4) ->
                                    if op = "forall"
                                    then
                                      let uu____3439 =
                                        let uu____3440 =
                                          let uu____3459 =
                                            let uu____3470 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos in
                                            (uu____3470, pats1) in
                                          (xs4, uu____3459, body4) in
                                        FStar_Parser_AST.QForall uu____3440 in
                                      mk uu____3439
                                    else
                                      (let uu____3492 =
                                         let uu____3493 =
                                           let uu____3512 =
                                             let uu____3523 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos in
                                             (uu____3523, pats1) in
                                           (xs4, uu____3512, body4) in
                                         FStar_Parser_AST.QExists uu____3493 in
                                       mk uu____3492))))
                 | uu____3544 ->
                     if op = "forall"
                     then
                       let uu____3545 =
                         let uu____3546 =
                           let uu____3565 = resugar_term' env body in
                           ([], ([], []), uu____3565) in
                         FStar_Parser_AST.QForall uu____3546 in
                       mk uu____3545
                     else
                       (let uu____3587 =
                          let uu____3588 =
                            let uu____3607 = resugar_term' env body in
                            ([], ([], []), uu____3607) in
                          FStar_Parser_AST.QExists uu____3588 in
                        mk uu____3587) in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last args1 in
                 (match args2 with
                  | (b, uu____3644)::[] -> resugar_forall_body b
                  | uu____3661 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc", uu____3671) ->
               let uu____3676 = FStar_List.hd args1 in
               (match uu____3676 with
                | (e1, uu____3690) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op, expected_arity1) ->
               let op1 = FStar_Ident.id_of_text op in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3759 ->
                         match uu____3759 with
                         | (e1, qual) ->
                             let uu____3776 = resugar_term' env e1 in
                             let uu____3777 = resugar_imp env qual in
                             (uu____3776, uu____3777))) in
               (match expected_arity1 with
                | FStar_Pervasives_Native.None ->
                    let resugared_args = resugar args1 in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1 in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3790 =
                        FStar_Util.first_N expect_n resugared_args in
                      (match uu____3790 with
                       | (op_args, rest) ->
                           let head =
                             let uu____3838 =
                               let uu____3839 =
                                 let uu____3846 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args in
                                 (op1, uu____3846) in
                               FStar_Parser_AST.Op uu____3839 in
                             mk uu____3838 in
                           FStar_List.fold_left
                             (fun head1 ->
                                fun uu____3864 ->
                                  match uu____3864 with
                                  | (arg, qual) ->
                                      mk
                                        (FStar_Parser_AST.App
                                           (head1, arg, qual))) head rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n when
                    (FStar_List.length args1) = n ->
                    let uu____3879 =
                      let uu____3880 =
                        let uu____3887 =
                          let uu____3890 = resugar args1 in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3890 in
                        (op1, uu____3887) in
                      FStar_Parser_AST.Op uu____3880 in
                    mk uu____3879
                | uu____3903 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e, (pat, wopt, t1)::[]) ->
          let uu____3972 = FStar_Syntax_Subst.open_branch (pat, wopt, t1) in
          (match uu____3972 with
           | (pat1, wopt1, t2) ->
               let branch_bv = FStar_Syntax_Free.names t2 in
               let bnds =
                 let uu____4018 =
                   let uu____4031 =
                     let uu____4036 = resugar_pat' env pat1 branch_bv in
                     let uu____4037 = resugar_term' env e in
                     (uu____4036, uu____4037) in
                   (FStar_Pervasives_Native.None, uu____4031) in
                 [uu____4018] in
               let body = resugar_term' env t2 in
               mk
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e, (pat1, uu____4089, t1)::(pat2, uu____4092, t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4188 =
            let uu____4189 =
              let uu____4196 = resugar_term' env e in
              let uu____4197 = resugar_term' env t1 in
              let uu____4198 = resugar_term' env t2 in
              (uu____4196, uu____4197, uu____4198) in
            FStar_Parser_AST.If uu____4189 in
          mk uu____4188
      | FStar_Syntax_Syntax.Tm_match (e, branches) ->
          let resugar_branch uu____4264 =
            match uu____4264 with
            | (pat, wopt, b) ->
                let uu____4306 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b) in
                (match uu____4306 with
                 | (pat1, wopt1, b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1 in
                     let pat2 = resugar_pat' env pat1 branch_bv in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4358 = resugar_term' env e1 in
                           FStar_Pervasives_Native.Some uu____4358 in
                     let b2 = resugar_term' env b1 in (pat2, wopt2, b2)) in
          let uu____4362 =
            let uu____4363 =
              let uu____4378 = resugar_term' env e in
              let uu____4379 = FStar_List.map resugar_branch branches in
              (uu____4378, uu____4379) in
            FStar_Parser_AST.Match uu____4363 in
          mk uu____4362
      | FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____4425) ->
          let term =
            match asc with
            | FStar_Util.Inl n -> resugar_term' env n
            | FStar_Util.Inr n -> resugar_comp' env n in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt in
          let uu____4494 =
            let uu____4495 =
              let uu____4504 = resugar_term' env e in
              (uu____4504, term, tac_opt1) in
            FStar_Parser_AST.Ascribed uu____4495 in
          mk uu____4494
      | FStar_Syntax_Syntax.Tm_let ((is_rec, source_lbs), body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
          let uu____4530 = FStar_Syntax_Subst.open_let_rec source_lbs body in
          (match uu____4530 with
           | (source_lbs1, body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4583 =
                         FStar_List.map (resugar_term' env) tms in
                       FStar_Pervasives_Native.Some uu____4583 in
                 let uu____4590 =
                   let uu____4595 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4595 in
                 match uu____4590 with
                 | (univs, td) ->
                     let uu____4614 =
                       let uu____4621 =
                         let uu____4622 = FStar_Syntax_Subst.compress td in
                         uu____4622.FStar_Syntax_Syntax.n in
                       match uu____4621 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4631,
                            (t1, uu____4633)::(d, uu____4635)::[])
                           -> (t1, d)
                       | uu____4692 -> failwith "wrong let binding format" in
                     (match uu____4614 with
                      | (typ, def) ->
                          let uu____4721 =
                            let uu____4736 =
                              let uu____4737 =
                                FStar_Syntax_Subst.compress def in
                              uu____4737.FStar_Syntax_Syntax.n in
                            match uu____4736 with
                            | FStar_Syntax_Syntax.Tm_abs (b, t1, uu____4756)
                                ->
                                let uu____4781 =
                                  FStar_Syntax_Subst.open_term b t1 in
                                (match uu____4781 with
                                 | (b1, t2) ->
                                     let b2 =
                                       let uu____4811 =
                                         FStar_Options.print_implicits () in
                                       if uu____4811
                                       then b1
                                       else filter_imp b1 in
                                     (b2, t2, true))
                            | uu____4829 -> ([], def, false) in
                          (match uu____4721 with
                           | (binders, term, is_pat_app) ->
                               let uu____4879 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4890 =
                                       let uu____4891 =
                                         let uu____4892 =
                                           let uu____4899 =
                                             bv_as_unique_ident bv in
                                           (uu____4899,
                                             FStar_Pervasives_Native.None) in
                                         FStar_Parser_AST.PatVar uu____4892 in
                                       mk_pat uu____4891 in
                                     (uu____4890, term) in
                               (match uu____4879 with
                                | (pat, term1) ->
                                    let uu____4920 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4960 ->
                                                  match uu____4960 with
                                                  | (bv, q) ->
                                                      let uu____4975 =
                                                        resugar_arg_qual env
                                                          q in
                                                      FStar_Util.map_opt
                                                        uu____4975
                                                        (fun q1 ->
                                                           let uu____4987 =
                                                             let uu____4988 =
                                                               let uu____4995
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv in
                                                               (uu____4995,
                                                                 q1) in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4988 in
                                                           mk_pat uu____4987))) in
                                        let uu____4998 =
                                          let uu____5003 =
                                            resugar_term' env term1 in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____5003) in
                                        let uu____5006 =
                                          universe_to_string univs in
                                        (uu____4998, uu____5006)
                                      else
                                        (let uu____5012 =
                                           let uu____5017 =
                                             resugar_term' env term1 in
                                           (pat, uu____5017) in
                                         let uu____5018 =
                                           universe_to_string univs in
                                         (uu____5012, uu____5018)) in
                                    (attrs_opt, uu____4920)))) in
               let r = FStar_List.map resugar_one_binding source_lbs1 in
               let bnds =
                 let f uu____5118 =
                   match uu____5118 with
                   | (attrs, (pb, univs)) ->
                       let uu____5174 =
                         let uu____5175 = FStar_Options.print_universes () in
                         Prims.op_Negation uu____5175 in
                       if uu____5174
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs (FStar_Pervasives_Native.snd pb)))) in
                 FStar_List.map f r in
               let body2 = resugar_term' env body1 in
               mk
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u, uu____5250) ->
          let s =
            let uu____5268 =
              let uu____5269 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head in
              FStar_All.pipe_right uu____5269 FStar_Util.string_of_int in
            Prims.op_Hat "?u" uu____5268 in
          let uu____5270 = mk FStar_Parser_AST.Wild in label s uu____5270
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic -> FStar_Parser_AST.Dynamic in
          let uu____5278 =
            let uu____5279 =
              let uu____5284 = resugar_term' env tm in (uu____5284, qi1) in
            FStar_Parser_AST.Quote uu____5279 in
          mk uu____5278
      | FStar_Syntax_Syntax.Tm_meta (e, m) ->
          let resugar_meta_desugared uu___4_5296 =
            match uu___4_5296 with
            | FStar_Syntax_Syntax.Sequence ->
                let term = resugar_term' env e in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5304, (uu____5305, (p, t11))::[], t2) ->
                      mk (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                      let uu____5366 =
                        let uu____5367 =
                          let uu____5376 = resugar_seq t11 in
                          (uu____5376, t2, t3) in
                        FStar_Parser_AST.Ascribed uu____5367 in
                      mk uu____5366
                  | uu____5379 -> t1 in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat -> resugar_term' env e in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____5380, pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5444 ->
                         match uu____5444 with
                         | (x, uu____5452) -> resugar_term' env x)) in
               mk (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____5457 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____5466, t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift
               (uu____5472, uu____5473, t1) -> resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown -> mk FStar_Parser_AST.Wild
and (resugar_calc :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Parser_AST.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t0 ->
      let mk a =
        FStar_Parser_AST.mk_term a t0.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un in
      let resugar_calc_finish t =
        let uu____5507 = FStar_Syntax_Util.head_and_args t in
        match uu____5507 with
        | (hd, args) ->
            let uu____5556 =
              let uu____5571 =
                let uu____5572 =
                  let uu____5575 = FStar_Syntax_Util.un_uinst hd in
                  FStar_Syntax_Subst.compress uu____5575 in
                uu____5572.FStar_Syntax_Syntax.n in
              (uu____5571, args) in
            (match uu____5556 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____5593, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5594))::(rel,
                                                              FStar_Pervasives_Native.None)::
                (uu____5596, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5597))::(uu____5598,
                                                              FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Syntax.Implicit
                                                              uu____5599))::
                (pf, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_finish_lid
                 ->
                 let pf1 = FStar_Syntax_Util.unthunk pf in
                 FStar_Pervasives_Native.Some (rel, pf1)
             | uu____5694 -> FStar_Pervasives_Native.None) in
      let un_eta_rel rel =
        let bv_eq_tm b t =
          let uu____5734 =
            let uu____5735 = FStar_Syntax_Subst.compress t in
            uu____5735.FStar_Syntax_Syntax.n in
          match uu____5734 with
          | FStar_Syntax_Syntax.Tm_name b' when
              FStar_Syntax_Syntax.bv_eq b b' -> true
          | uu____5739 -> false in
        let uu____5740 =
          let uu____5741 = FStar_Syntax_Subst.compress rel in
          uu____5741.FStar_Syntax_Syntax.n in
        match uu____5740 with
        | FStar_Syntax_Syntax.Tm_abs (b1::b2::[], body, uu____5749) ->
            let uu____5796 = FStar_Syntax_Subst.open_term [b1; b2] body in
            (match uu____5796 with
             | (b11::b21::[], body1) ->
                 let body2 = FStar_Syntax_Util.unascribe body1 in
                 let body3 =
                   let uu____5856 = FStar_Syntax_Util.unb2t body2 in
                   match uu____5856 with
                   | FStar_Pervasives_Native.Some body3 -> body3
                   | FStar_Pervasives_Native.None -> body2 in
                 let uu____5860 =
                   let uu____5861 = FStar_Syntax_Subst.compress body3 in
                   uu____5861.FStar_Syntax_Syntax.n in
                 (match uu____5860 with
                  | FStar_Syntax_Syntax.Tm_app (e, args) when
                      (FStar_List.length args) >= (Prims.of_int (2)) ->
                      (match FStar_List.rev args with
                       | (a1, FStar_Pervasives_Native.None)::(a2,
                                                              FStar_Pervasives_Native.None)::rest
                           ->
                           let uu____5951 =
                             (bv_eq_tm (FStar_Pervasives_Native.fst b11) a2)
                               &&
                               (bv_eq_tm (FStar_Pervasives_Native.fst b21) a1) in
                           if uu____5951
                           then
                             let uu____5958 =
                               FStar_Syntax_Util.mk_app e
                                 (FStar_List.rev rest) in
                             FStar_All.pipe_left
                               (fun uu____5969 ->
                                  FStar_Pervasives_Native.Some uu____5969)
                               uu____5958
                           else FStar_Pervasives_Native.Some rel
                       | uu____5971 -> FStar_Pervasives_Native.Some rel)
                  | uu____5982 -> FStar_Pervasives_Native.Some rel))
        | uu____5983 -> FStar_Pervasives_Native.Some rel in
      let resugar_step pack =
        let uu____6010 = FStar_Syntax_Util.head_and_args pack in
        match uu____6010 with
        | (hd, args) ->
            let uu____6063 =
              let uu____6078 =
                let uu____6079 =
                  let uu____6082 = FStar_Syntax_Util.un_uinst hd in
                  FStar_Syntax_Subst.compress uu____6082 in
                uu____6079.FStar_Syntax_Syntax.n in
              (uu____6078, args) in
            (match uu____6063 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____6104, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6105))::(uu____6106,
                                                              FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Syntax.Implicit
                                                              uu____6107))::
                (uu____6108, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6109))::(rel,
                                                              FStar_Pervasives_Native.None)::
                (z, FStar_Pervasives_Native.None)::(pf,
                                                    FStar_Pervasives_Native.None)::
                (j, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_step_lid
                 ->
                 let pf1 = FStar_Syntax_Util.unthunk pf in
                 let j1 = FStar_Syntax_Util.unthunk j in
                 FStar_Pervasives_Native.Some (z, rel, j1, pf1)
             | uu____6240 -> FStar_Pervasives_Native.None) in
      let resugar_init pack =
        let uu____6273 = FStar_Syntax_Util.head_and_args pack in
        match uu____6273 with
        | (hd, args) ->
            let uu____6318 =
              let uu____6333 =
                let uu____6334 =
                  let uu____6337 = FStar_Syntax_Util.un_uinst hd in
                  FStar_Syntax_Subst.compress uu____6337 in
                uu____6334.FStar_Syntax_Syntax.n in
              (uu____6333, args) in
            (match uu____6318 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____6351, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6352))::(x,
                                                              FStar_Pervasives_Native.None)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_init_lid
                 -> FStar_Pervasives_Native.Some x
             | uu____6400 -> FStar_Pervasives_Native.None) in
      let rec resugar_all_steps pack =
        let uu____6449 = resugar_step pack in
        match uu____6449 with
        | FStar_Pervasives_Native.Some (t, r, j, k) ->
            let uu____6486 = resugar_all_steps k in
            FStar_Util.bind_opt uu____6486
              (fun uu____6528 ->
                 match uu____6528 with
                 | (steps, k1) ->
                     FStar_Pervasives_Native.Some (((t, r, j) :: steps), k1))
        | FStar_Pervasives_Native.None ->
            FStar_Pervasives_Native.Some ([], pack) in
      let resugar_rel rel =
        let rel1 =
          let uu____6640 = un_eta_rel rel in
          match uu____6640 with
          | FStar_Pervasives_Native.Some rel1 -> rel1
          | FStar_Pervasives_Native.None -> rel in
        let fallback uu____6649 =
          let uu____6650 =
            let uu____6651 = resugar_term' env rel1 in
            FStar_Parser_AST.Paren uu____6651 in
          mk uu____6650 in
        let uu____6652 = FStar_Syntax_Util.head_and_args rel1 in
        match uu____6652 with
        | (hd, args) ->
            let uu____6695 =
              (FStar_Options.print_implicits ()) &&
                (FStar_List.existsb
                   (fun uu____6705 ->
                      match uu____6705 with
                      | (uu____6712, q) -> FStar_Syntax_Syntax.is_implicit q)
                   args) in
            if uu____6695
            then fallback ()
            else
              (let uu____6719 = resugar_term_as_op hd in
               match uu____6719 with
               | FStar_Pervasives_Native.Some
                   (s, FStar_Pervasives_Native.None) ->
                   let uu____6731 =
                     let uu____6732 =
                       let uu____6739 = FStar_Ident.id_of_text s in
                       (uu____6739, []) in
                     FStar_Parser_AST.Op uu____6732 in
                   mk uu____6731
               | FStar_Pervasives_Native.Some
                   (s, FStar_Pervasives_Native.Some uu____6747) when
                   uu____6747 = (Prims.of_int (2)) ->
                   let uu____6748 =
                     let uu____6749 =
                       let uu____6756 = FStar_Ident.id_of_text s in
                       (uu____6756, []) in
                     FStar_Parser_AST.Op uu____6749 in
                   mk uu____6748
               | uu____6759 -> fallback ()) in
      let build_calc rel x0 steps =
        let r = resugar_term' env in
        let uu____6803 =
          let uu____6804 =
            let uu____6813 = resugar_rel rel in
            let uu____6814 = r x0 in
            let uu____6815 =
              FStar_List.map
                (fun uu____6829 ->
                   match uu____6829 with
                   | (z, rel1, j) ->
                       let uu____6839 =
                         let uu____6846 = resugar_rel rel1 in
                         let uu____6847 = r j in
                         let uu____6848 = r z in
                         (uu____6846, uu____6847, uu____6848) in
                       FStar_Parser_AST.CalcStep uu____6839) steps in
            (uu____6813, uu____6814, uu____6815) in
          FStar_Parser_AST.CalcProof uu____6804 in
        mk uu____6803 in
      let uu____6851 = resugar_calc_finish t0 in
      FStar_Util.bind_opt uu____6851
        (fun uu____6866 ->
           match uu____6866 with
           | (rel, pack) ->
               let uu____6875 = resugar_all_steps pack in
               FStar_Util.bind_opt uu____6875
                 (fun uu____6906 ->
                    match uu____6906 with
                    | (steps, k) ->
                        let uu____6939 = resugar_init k in
                        FStar_Util.bind_opt uu____6939
                          (fun x0 ->
                             let uu____6945 =
                               build_calc rel x0 (FStar_List.rev steps) in
                             FStar_All.pipe_left
                               (fun uu____6954 ->
                                  FStar_Pervasives_Native.Some uu____6954)
                               uu____6945)))
and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env ->
    fun c ->
      let mk a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ, u) ->
          let t = resugar_term' env typ in
          (match u with
           | FStar_Pervasives_Native.None ->
               mk
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____6989 = FStar_Options.print_universes () in
               if uu____6989
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.GTotal (typ, u) ->
          let t = resugar_term' env typ in
          (match u with
           | FStar_Pervasives_Native.None ->
               mk
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____7050 = FStar_Options.print_universes () in
               if uu____7050
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos in
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.Comp c1 ->
          let result =
            let uu____7091 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ in
            (uu____7091, FStar_Parser_AST.Nothing) in
          let uu____7092 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid) in
          if uu____7092
          then
            let universe =
              FStar_List.map (fun u -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs in
            let args =
              let uu____7113 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid in
              if uu____7113
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____7196 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post) in
                      (uu____7196, (FStar_Pervasives_Native.snd post)) in
                    let uu____7207 =
                      let uu____7216 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre) in
                      if uu____7216 then [] else [pre] in
                    let uu____7248 =
                      let uu____7257 =
                        let uu____7266 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats) in
                        if uu____7266 then [] else [pats] in
                      FStar_List.append [post1] uu____7257 in
                    FStar_List.append uu____7207 uu____7248
                | uu____7322 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args in
            let args1 =
              FStar_List.map
                (fun uu____7355 ->
                   match uu____7355 with
                   | (e, uu____7367) ->
                       let uu____7372 = resugar_term' env e in
                       (uu____7372, FStar_Parser_AST.Nothing)) args in
            let rec aux l uu___5_7397 =
              match uu___5_7397 with
              | [] -> l
              | hd::tl ->
                  (match hd with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____7430 = resugar_term' env e in
                         (uu____7430, FStar_Parser_AST.Nothing) in
                       aux (e1 :: l) tl
                   | uu____7435 -> aux l tl) in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags in
            mk
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name), [result]))
and (resugar_binder' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env ->
    fun b ->
      fun r ->
        let uu____7481 = b in
        match uu____7481 with
        | (x, aq) ->
            let uu____7490 = resugar_arg_qual env aq in
            FStar_Util.map_opt uu____7490
              (fun imp ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild ->
                     let uu____7504 =
                       let uu____7505 = bv_as_unique_ident x in
                       FStar_Parser_AST.Variable uu____7505 in
                     FStar_Parser_AST.mk_binder uu____7504 r
                       FStar_Parser_AST.Type_level imp
                 | uu____7506 ->
                     let uu____7507 = FStar_Syntax_Syntax.is_null_bv x in
                     if uu____7507
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____7509 =
                          let uu____7510 =
                            let uu____7515 = bv_as_unique_ident x in
                            (uu____7515, e) in
                          FStar_Parser_AST.Annotated uu____7510 in
                        FStar_Parser_AST.mk_binder uu____7509 r
                          FStar_Parser_AST.Type_level imp))
and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env ->
    fun v ->
      fun aqual ->
        fun body_bv ->
          fun typ_opt ->
            let mk a =
              let uu____7535 = FStar_Syntax_Syntax.range_of_bv v in
              FStar_Parser_AST.mk_pattern a uu____7535 in
            let used = FStar_Util.set_mem v body_bv in
            let pat =
              let uu____7538 =
                if used
                then
                  let uu____7539 =
                    let uu____7546 = bv_as_unique_ident v in
                    (uu____7546, aqual) in
                  FStar_Parser_AST.PatVar uu____7539
                else FStar_Parser_AST.PatWild aqual in
              mk uu____7538 in
            match typ_opt with
            | FStar_Pervasives_Native.None -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown;
                  FStar_Syntax_Syntax.pos = uu____7552;
                  FStar_Syntax_Syntax.vars = uu____7553;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____7563 = FStar_Options.print_bound_var_types () in
                if uu____7563
                then
                  let uu____7564 =
                    let uu____7565 =
                      let uu____7576 =
                        let uu____7583 = resugar_term' env typ in
                        (uu____7583, FStar_Pervasives_Native.None) in
                      (pat, uu____7576) in
                    FStar_Parser_AST.PatAscribed uu____7565 in
                  mk uu____7564
                else pat
and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env ->
    fun x ->
      fun qual ->
        fun body_bv ->
          let uu____7603 = resugar_arg_qual env qual in
          FStar_Util.map_opt uu____7603
            (fun aqual ->
               let uu____7615 =
                 let uu____7620 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
                 FStar_All.pipe_left
                   (fun uu____7631 -> FStar_Pervasives_Native.Some uu____7631)
                   uu____7620 in
               resugar_bv_as_pat' env x aqual body_bv uu____7615)
and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env ->
    fun p ->
      fun branch_bv ->
        let mk a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None) in
        let may_drop_implicits args =
          (let uu____7684 = FStar_Options.print_implicits () in
           Prims.op_Negation uu____7684) &&
            (let uu____7686 =
               FStar_List.existsML
                 (fun uu____7697 ->
                    match uu____7697 with
                    | (pattern, is_implicit) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv, uu____7713)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____7718 -> false
                          | uu____7719 -> true in
                        is_implicit && might_be_used) args in
             Prims.op_Negation uu____7686) in
        let resugar_plain_pat_cons' fv args =
          mk
            (FStar_Parser_AST.PatApp
               ((mk
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args)) in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____7782 = may_drop_implicits args in
            if uu____7782 then filter_pattern_imp args else args in
          let args2 =
            FStar_List.map
              (fun uu____7802 ->
                 match uu____7802 with
                 | (p1, b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1 in
          resugar_plain_pat_cons' fv args2
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv, []) ->
              mk
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv, args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____7848 =
                  let uu____7849 =
                    let uu____7850 = filter_pattern_imp args in
                    FStar_List.isEmpty uu____7850 in
                  Prims.op_Negation uu____7849 in
                if uu____7848
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv, args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____7886 = filter_pattern_imp args in
              (match uu____7886 with
               | (hd, false)::(tl, false)::[] ->
                   let hd' = aux hd (FStar_Pervasives_Native.Some false) in
                   let uu____7926 =
                     aux tl (FStar_Pervasives_Native.Some false) in
                   (match uu____7926 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7942 =
                       let uu____7947 =
                         let uu____7948 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args') in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7948 in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7947) in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7942);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv, args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7991 ->
                        match uu____7991 with
                        | (p2, is_implicit) ->
                            if is_implicit
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____8003 =
                                 aux p2 (FStar_Pervasives_Native.Some false) in
                               FStar_Pervasives_Native.Some uu____8003))) in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              mk (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____8007;
                 FStar_Syntax_Syntax.fv_delta = uu____8008;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name, fields));_},
               args)
              ->
              let fields1 =
                let uu____8035 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f -> FStar_Ident.lid_of_ids [f])) in
                FStar_All.pipe_right uu____8035 FStar_List.rev in
              let args1 =
                let uu____8051 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____8069 ->
                          match uu____8069 with
                          | (p2, b) ->
                              aux p2 (FStar_Pervasives_Native.Some b))) in
                FStar_All.pipe_right uu____8051 FStar_List.rev in
              let rec map2 l1 l2 =
                match (l1, l2) with
                | ([], []) -> []
                | ([], hd::tl) -> []
                | (hd::tl, []) ->
                    let uu____8143 = map2 tl [] in
                    (hd,
                      (mk
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____8143
                | (hd1::tl1, hd2::tl2) ->
                    let uu____8166 = map2 tl1 tl2 in (hd1, hd2) :: uu____8166 in
              let args2 =
                let uu____8184 = map2 fields1 args1 in
                FStar_All.pipe_right uu____8184 FStar_List.rev in
              mk (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv, args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v ->
              let uu____8226 =
                let uu____8235 =
                  FStar_Ident.string_of_id v.FStar_Syntax_Syntax.ppname in
                string_to_op uu____8235 in
              (match uu____8226 with
               | FStar_Pervasives_Native.Some (op, uu____8237) ->
                   let uu____8248 =
                     let uu____8249 =
                       let uu____8250 =
                         let uu____8255 =
                           FStar_Ident.range_of_id
                             v.FStar_Syntax_Syntax.ppname in
                         (op, uu____8255) in
                       FStar_Ident.mk_ident uu____8250 in
                     FStar_Parser_AST.PatOp uu____8249 in
                   mk uu____8248
               | FStar_Pervasives_Native.None ->
                   let uu____8262 = to_arg_qual imp_opt in
                   resugar_bv_as_pat' env v uu____8262 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____8267 ->
              let uu____8268 =
                let uu____8269 = to_arg_qual imp_opt in
                FStar_Parser_AST.PatWild uu____8269 in
              mk uu____8268
          | FStar_Syntax_Syntax.Pat_dot_term (bv, term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term) in
        aux p FStar_Pervasives_Native.None
and (resugar_arg_qual :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun q ->
      match q with
      | FStar_Pervasives_Native.None ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
          if b
          then FStar_Pervasives_Native.None
          else
            FStar_Pervasives_Native.Some
              (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____8305 =
            let uu____8308 =
              let uu____8309 =
                let uu____8310 = resugar_term' env t in
                FStar_Parser_AST.Arg_qualifier_meta_tac uu____8310 in
              FStar_Parser_AST.Meta uu____8309 in
            FStar_Pervasives_Native.Some uu____8308 in
          FStar_Pervasives_Native.Some uu____8305
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____8316 =
            let uu____8319 =
              let uu____8320 =
                let uu____8321 = resugar_term' env t in
                FStar_Parser_AST.Arg_qualifier_meta_attr uu____8321 in
              FStar_Parser_AST.Meta uu____8320 in
            FStar_Pervasives_Native.Some uu____8319 in
          FStar_Pervasives_Native.Some uu____8316
and (resugar_imp :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.imp)
  =
  fun env ->
    fun q ->
      match q with
      | FStar_Pervasives_Native.None -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false))
          -> FStar_Parser_AST.Hash
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
          FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) ->
          FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta uu____8328) ->
          FStar_Parser_AST.Nothing
let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_8335 ->
    match uu___6_8335 with
    | FStar_Syntax_Syntax.Assumption ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Irreducible ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Inline_for_extraction ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Reifiable ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____8342 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____8343 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____8344 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____8349 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____8358 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____8367 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName -> FStar_Pervasives_Native.None
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_8372 ->
    match uu___7_8372 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions -> FStar_Parser_AST.PopOptions
    | FStar_Syntax_Syntax.RestartSolver -> FStar_Parser_AST.RestartSolver
    | FStar_Syntax_Syntax.LightOff -> FStar_Parser_AST.LightOff
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon))
  =
  fun env ->
    fun datacon_ses ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid, uvs, bs, t, uu____8411, datacons) ->
            let uu____8421 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1 ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____8448, uu____8449, uu____8450, inductive_lid,
                           uu____8452, uu____8453)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____8458 -> failwith "unexpected")) in
            (match uu____8421 with
             | (current_datacons, other_datacons) ->
                 let bs1 =
                   let uu____8477 = FStar_Options.print_implicits () in
                   if uu____8477 then bs else filter_imp bs in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos)) in
                 let tyc =
                   let uu____8491 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_8496 ->
                             match uu___8_8496 with
                             | FStar_Syntax_Syntax.RecordType uu____8497 ->
                                 true
                             | uu____8506 -> false)) in
                   if uu____8491
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____8542, univs, term, uu____8545, num,
                            uu____8547)
                           ->
                           let uu____8552 =
                             let uu____8553 =
                               FStar_Syntax_Subst.compress term in
                             uu____8553.FStar_Syntax_Syntax.n in
                           (match uu____8552 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3, uu____8563)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____8620 ->
                                          match uu____8620 with
                                          | (b, qual) ->
                                              let uu____8637 =
                                                bv_as_unique_ident b in
                                              let uu____8638 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort in
                                              (uu____8637, uu____8638))) in
                                FStar_List.append mfields fields
                            | uu____8643 -> failwith "unexpected")
                       | uu____8650 -> failwith "unexpected" in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons in
                     let uu____8674 =
                       let uu____8693 = FStar_Ident.ident_of_lid tylid in
                       (uu____8693, bs2, FStar_Pervasives_Native.None,
                         fields) in
                     FStar_Parser_AST.TyconRecord uu____8674
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l, univs, term, uu____8759, num, uu____8761) ->
                            let c =
                              let uu____8775 = FStar_Ident.ident_of_lid l in
                              let uu____8776 =
                                let uu____8779 = resugar_term' env term in
                                FStar_Pervasives_Native.Some uu____8779 in
                              (uu____8775, uu____8776, false) in
                            c :: constructors
                        | uu____8790 -> failwith "unexpected" in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons in
                      let uu____8830 =
                        let uu____8853 = FStar_Ident.ident_of_lid tylid in
                        (uu____8853, bs2, FStar_Pervasives_Native.None,
                          constructors) in
                      FStar_Parser_AST.TyconVariant uu____8830) in
                 (other_datacons, tyc))
        | uu____8868 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r ->
    fun q ->
      fun d' ->
        let uu____8892 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8892;
          FStar_Parser_AST.attrs = []
        }
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se ->
    fun d' ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env ->
    fun name ->
      fun ts ->
        let uu____8918 = ts in
        match uu____8918 with
        | (univs, typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
            let uu____8930 =
              let uu____8931 =
                let uu____8940 =
                  let uu____8943 =
                    let uu____8944 =
                      let uu____8957 = resugar_term' env typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____8957) in
                    FStar_Parser_AST.TyconAbbrev uu____8944 in
                  [uu____8943] in
                (false, false, uu____8940) in
              FStar_Parser_AST.Tycon uu____8931 in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8930
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env -> fun ts -> resugar_tscheme'' env "tscheme" ts
let (resugar_wp_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.wp_eff_combinators ->
        FStar_Parser_AST.decl Prims.list)
  =
  fun env ->
    fun for_free ->
      fun combs ->
        let resugar_opt name tsopt =
          match tsopt with
          | FStar_Pervasives_Native.Some ts ->
              let uu____9011 = resugar_tscheme'' env name ts in [uu____9011]
          | FStar_Pervasives_Native.None -> [] in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____9024 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp in
           let uu____9025 =
             let uu____9028 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp in
             let uu____9029 =
               let uu____9032 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger in
               let uu____9033 =
                 let uu____9036 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else in
                 let uu____9037 =
                   let uu____9040 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp in
                   let uu____9041 =
                     let uu____9044 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp in
                     let uu____9045 =
                       let uu____9048 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial in
                       uu____9048 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr)) in
                     uu____9044 :: uu____9045 in
                   uu____9040 :: uu____9041 in
                 uu____9036 :: uu____9037 in
               uu____9032 :: uu____9033 in
             uu____9028 :: uu____9029 in
           uu____9024 :: uu____9025)
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env ->
    fun combs ->
      let resugar name uu____9075 =
        match uu____9075 with
        | (ts, uu____9081) -> resugar_tscheme'' env name ts in
      let uu____9082 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr in
      let uu____9083 =
        let uu____9086 = resugar "return" combs.FStar_Syntax_Syntax.l_return in
        let uu____9087 =
          let uu____9090 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind in
          let uu____9091 =
            let uu____9094 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp in
            let uu____9095 =
              let uu____9098 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else in
              [uu____9098] in
            uu____9094 :: uu____9095 in
          uu____9090 :: uu____9091 in
        uu____9086 :: uu____9087 in
      uu____9082 :: uu____9083
let (resugar_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.eff_combinators -> FStar_Parser_AST.decl Prims.list)
  =
  fun env ->
    fun combs ->
      match combs with
      | FStar_Syntax_Syntax.Primitive_eff combs1 ->
          resugar_wp_eff_combinators env false combs1
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          resugar_wp_eff_combinators env true combs1
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          resugar_layered_eff_combinators env combs1
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env ->
    fun r ->
      fun q ->
        fun ed ->
          let resugar_action d for_free =
            let action_params =
              FStar_Syntax_Subst.open_binders
                d.FStar_Syntax_Syntax.action_params in
            let uu____9152 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____9152 with
            | (bs, action_defn) ->
                let uu____9159 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____9159 with
                 | (bs1, action_typ) ->
                     let action_params1 =
                       let uu____9169 = FStar_Options.print_implicits () in
                       if uu____9169
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____9176 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b -> resugar_binder' env b r)) in
                       FStar_All.pipe_right uu____9176 FStar_List.rev in
                     let action_defn1 = resugar_term' env action_defn in
                     let action_typ1 = resugar_term' env action_typ in
                     if for_free
                     then
                       let a =
                         let uu____9192 =
                           let uu____9203 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____9203,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____9192 in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un in
                       let uu____9223 =
                         let uu____9224 =
                           let uu____9233 =
                             let uu____9236 =
                               let uu____9237 =
                                 let uu____9250 =
                                   FStar_Ident.ident_of_lid
                                     d.FStar_Syntax_Syntax.action_name in
                                 (uu____9250, action_params2,
                                   FStar_Pervasives_Native.None, t) in
                               FStar_Parser_AST.TyconAbbrev uu____9237 in
                             [uu____9236] in
                           (false, false, uu____9233) in
                         FStar_Parser_AST.Tycon uu____9224 in
                       mk_decl r q uu____9223
                     else
                       (let uu____9258 =
                          let uu____9259 =
                            let uu____9268 =
                              let uu____9271 =
                                let uu____9272 =
                                  let uu____9285 =
                                    FStar_Ident.ident_of_lid
                                      d.FStar_Syntax_Syntax.action_name in
                                  (uu____9285, action_params2,
                                    FStar_Pervasives_Native.None,
                                    action_defn1) in
                                FStar_Parser_AST.TyconAbbrev uu____9272 in
                              [uu____9271] in
                            (false, false, uu____9268) in
                          FStar_Parser_AST.Tycon uu____9259 in
                        mk_decl r q uu____9258)) in
          let eff_name =
            FStar_Ident.ident_of_lid ed.FStar_Syntax_Syntax.mname in
          let uu____9293 =
            let uu____9298 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____9298 in
          match uu____9293 with
          | (eff_binders, eff_typ) ->
              let eff_binders1 =
                let uu____9316 = FStar_Options.print_implicits () in
                if uu____9316 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____9323 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b -> resugar_binder' env b r)) in
                FStar_All.pipe_right uu____9323 FStar_List.rev in
              let eff_typ1 = resugar_term' env eff_typ in
              let mandatory_members_decls =
                resugar_combinators env ed.FStar_Syntax_Syntax.combinators in
              let actions =
                FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                  (FStar_List.map (fun a -> resugar_action a false)) in
              let decls = FStar_List.append mandatory_members_decls actions in
              mk_decl r q
                (FStar_Parser_AST.NewEffect
                   (FStar_Parser_AST.DefineEffect
                      (eff_name, eff_binders2, eff_typ1, decls)))
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9371) ->
          let uu____9380 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1 ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____9402 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____9419 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____9426 -> false
                    | uu____9441 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
          (match uu____9380 with
           | (decl_typ_ses, datacon_ses) ->
               let retrieve_datacons_and_resugar uu____9477 se1 =
                 match uu____9477 with
                 | (datacon_ses1, tycons) ->
                     let uu____9503 = resugar_typ env datacon_ses1 se1 in
                     (match uu____9503 with
                      | (datacon_ses2, tyc) ->
                          (datacon_ses2, (tyc :: tycons))) in
               let uu____9518 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses in
               (match uu____9518 with
                | (leftover_datacons, tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____9553 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons)) in
                         FStar_Pervasives_Native.Some uu____9553
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l, uu____9560, uu____9561, uu____9562,
                               uu____9563, uu____9564)
                              ->
                              let uu____9569 =
                                let uu____9570 =
                                  let uu____9571 =
                                    let uu____9578 =
                                      FStar_Ident.ident_of_lid l in
                                    (uu____9578,
                                      FStar_Pervasives_Native.None) in
                                  FStar_Parser_AST.Exception uu____9571 in
                                decl'_to_decl se1 uu____9570 in
                              FStar_Pervasives_Native.Some uu____9569
                          | uu____9581 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____9584 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____9589 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____9601) ->
          let uu____9606 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_9612 ->
                    match uu___9_9612 with
                    | FStar_Syntax_Syntax.Projector (uu____9613, uu____9614)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9615 -> true
                    | uu____9616 -> false)) in
          if uu____9606
          then FStar_Pervasives_Native.None
          else
            (let mk e =
               FStar_Syntax_Syntax.mk e se.FStar_Syntax_Syntax.sigrng in
             let dummy = mk FStar_Syntax_Syntax.Tm_unknown in
             let desugared_let = mk (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
             let t = resugar_term' env desugared_let in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec, lets, uu____9647) ->
                 let uu____9676 =
                   let uu____9677 =
                     let uu____9678 =
                       let uu____9689 =
                         FStar_List.map FStar_Pervasives_Native.snd lets in
                       (isrec, uu____9689) in
                     FStar_Parser_AST.TopLevelLet uu____9678 in
                   decl'_to_decl se uu____9677 in
                 FStar_Pervasives_Native.Some uu____9676
             | uu____9726 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid, uu____9730, fml) ->
          let uu____9732 =
            let uu____9733 =
              let uu____9734 =
                let uu____9739 = FStar_Ident.ident_of_lid lid in
                let uu____9740 = resugar_term' env fml in
                (uu____9739, uu____9740) in
              FStar_Parser_AST.Assume uu____9734 in
            decl'_to_decl se uu____9733 in
          FStar_Pervasives_Native.Some uu____9732
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9742 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed in
          FStar_Pervasives_Native.Some uu____9742
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source in
          let dst = e.FStar_Syntax_Syntax.target in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9751, t) ->
                let uu____9761 = resugar_term' env t in
                FStar_Pervasives_Native.Some uu____9761
            | uu____9762 -> FStar_Pervasives_Native.None in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9770, t) ->
                let uu____9780 = resugar_term' env t in
                FStar_Pervasives_Native.Some uu____9780
            | uu____9781 -> FStar_Pervasives_Native.None in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t, FStar_Pervasives_Native.None)
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp, FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9805 -> failwith "Should not happen hopefully" in
          let uu____9814 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 }) in
          FStar_Pervasives_Native.Some uu____9814
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags) ->
          let uu____9824 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____9824 with
           | (bs1, c1) ->
               let bs2 =
                 let uu____9836 = FStar_Options.print_implicits () in
                 if uu____9836 then bs1 else filter_imp bs1 in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng)) in
               let uu____9849 =
                 let uu____9850 =
                   let uu____9851 =
                     let uu____9860 =
                       let uu____9863 =
                         let uu____9864 =
                           let uu____9877 = FStar_Ident.ident_of_lid lid in
                           let uu____9878 = resugar_comp' env c1 in
                           (uu____9877, bs3, FStar_Pervasives_Native.None,
                             uu____9878) in
                         FStar_Parser_AST.TyconAbbrev uu____9864 in
                       [uu____9863] in
                     (false, false, uu____9860) in
                   FStar_Parser_AST.Tycon uu____9851 in
                 decl'_to_decl se uu____9850 in
               FStar_Pervasives_Native.Some uu____9849)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9886 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
          FStar_Pervasives_Native.Some uu____9886
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
          let uu____9890 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9896 ->
                    match uu___10_9896 with
                    | FStar_Syntax_Syntax.Projector (uu____9897, uu____9898)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9899 -> true
                    | uu____9900 -> false)) in
          if uu____9890
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9905 =
                 (let uu____9908 = FStar_Options.print_universes () in
                  Prims.op_Negation uu____9908) || (FStar_List.isEmpty uvs) in
               if uu____9905
               then resugar_term' env t
               else
                 (let uu____9910 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____9910 with
                  | (uvs1, t1) ->
                      let universes = universe_to_string uvs1 in
                      let uu____9918 = resugar_term' env t1 in
                      label universes uu____9918) in
             let uu____9919 =
               let uu____9920 =
                 let uu____9921 =
                   let uu____9926 = FStar_Ident.ident_of_lid lid in
                   (uu____9926, t') in
                 FStar_Parser_AST.Val uu____9921 in
               decl'_to_decl se uu____9920 in
             FStar_Pervasives_Native.Some uu____9919)
      | FStar_Syntax_Syntax.Sig_splice (ids, t) ->
          let uu____9933 =
            let uu____9934 =
              let uu____9935 =
                let uu____9942 =
                  FStar_List.map (fun l -> FStar_Ident.ident_of_lid l) ids in
                let uu____9947 = resugar_term' env t in
                (uu____9942, uu____9947) in
              FStar_Parser_AST.Splice uu____9935 in
            decl'_to_decl se uu____9934 in
          FStar_Pervasives_Native.Some uu____9933
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9950 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9967 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m, n, p, (uu____9985, t), uu____9987) ->
          let uu____9996 =
            let uu____9997 =
              let uu____9998 =
                let uu____10007 = resugar_term' env t in
                (m, n, p, uu____10007) in
              FStar_Parser_AST.Polymonadic_bind uu____9998 in
            decl'_to_decl se uu____9997 in
          FStar_Pervasives_Native.Some uu____9996
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          (m, n, (uu____10010, t), uu____10012) ->
          let uu____10021 =
            let uu____10022 =
              let uu____10023 =
                let uu____10030 = resugar_term' env t in (m, n, uu____10030) in
              FStar_Parser_AST.Polymonadic_subcomp uu____10023 in
            decl'_to_decl se uu____10022 in
          FStar_Pervasives_Native.Some uu____10021
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f -> f empty_env
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t -> let uu____10051 = noenv resugar_term' in uu____10051 t
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se -> let uu____10068 = noenv resugar_sigelt' in uu____10068 se
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c -> let uu____10085 = noenv resugar_comp' in uu____10085 c
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p ->
    fun branch_bv ->
      let uu____10107 = noenv resugar_pat' in uu____10107 p branch_bv
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b ->
    fun r -> let uu____10140 = noenv resugar_binder' in uu____10140 b r
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts -> let uu____10164 = noenv resugar_tscheme' in uu____10164 ts
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r ->
    fun q ->
      fun ed ->
        let uu____10191 = noenv resugar_eff_decl' in uu____10191 r q ed