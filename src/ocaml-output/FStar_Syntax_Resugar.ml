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
          if FStar_Util.starts_with str "dtuple"
          then
            FStar_Pervasives_Native.Some
              ("dtuple", FStar_Pervasives_Native.None)
          else
            if FStar_Util.starts_with str "tuple"
            then
              FStar_Pervasives_Native.Some
                ("tuple", FStar_Pervasives_Native.None)
            else
              if FStar_Util.starts_with str "try_with"
              then
                FStar_Pervasives_Native.Some
                  ("try_with", FStar_Pervasives_Native.None)
              else
                (let uu____1092 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid in
                 if uu____1092
                 then
                   let uu____1101 =
                     let uu____1108 =
                       FStar_Ident.string_of_lid
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                     (uu____1108, FStar_Pervasives_Native.None) in
                   FStar_Pervasives_Native.Some uu____1101
                 else FStar_Pervasives_Native.None) in
    let uu____1124 =
      let uu____1125 = FStar_Syntax_Subst.compress t in
      uu____1125.FStar_Syntax_Syntax.n in
    match uu____1124 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length =
          let uu____1136 =
            FStar_Ident.nsstr
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_String.length uu____1136 in
        let s =
          if length = Prims.int_zero
          then
            FStar_Ident.string_of_lid
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          else
            (let uu____1139 =
               FStar_Ident.string_of_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             FStar_Util.substring_from uu____1139 (length + Prims.int_one)) in
        let uu____1140 = string_to_op s in
        (match uu____1140 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____1172 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e, us) -> resugar_term_as_op e
    | uu____1187 -> FStar_Pervasives_Native.None
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) ->
        true
    | uu____1197 -> false
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____1203 -> true
    | uu____1204 -> false
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    let uu____1215 = FStar_Ident.string_of_lid lid in
    match uu____1215 with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____1216 ->
        let uu____1217 = is_tuple_constructor_lid lid in
        Prims.op_Negation uu____1217
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let uu____1229 = may_shorten lid in
      if uu____1229 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env ->
    fun t ->
      let mk a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un in
      let name a r =
        let uu____1378 = FStar_Ident.lid_of_path [a] r in
        FStar_Parser_AST.Name uu____1378 in
      let uu____1379 =
        let uu____1380 = FStar_Syntax_Subst.compress t in
        uu____1380.FStar_Syntax_Syntax.n in
      match uu____1379 with
      | FStar_Syntax_Syntax.Tm_delayed uu____1383 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____1399 = FStar_Syntax_Util.unfold_lazy i in
          resugar_term' env uu____1399
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____1402 =
              let uu____1403 = bv_as_unique_ident x in [uu____1403] in
            FStar_Ident.lid_of_ids uu____1402 in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____1406 =
              let uu____1407 = bv_as_unique_ident x in [uu____1407] in
            FStar_Ident.lid_of_ids uu____1406 in
          mk (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let length =
            let uu____1411 =
              FStar_Ident.nsstr
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_String.length uu____1411 in
          let s =
            if length = Prims.int_zero
            then FStar_Ident.string_of_lid a
            else
              (let uu____1414 = FStar_Ident.string_of_lid a in
               FStar_Util.substring_from uu____1414 (length + Prims.int_one)) in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_" in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix) in
            let uu____1417 =
              let uu____1418 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos in
              FStar_Parser_AST.Discrim uu____1418 in
            mk uu____1417
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
               | uu____1428 -> failwith "wrong projector format")
            else
              (let uu____1432 =
                 FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid in
               if uu____1432
               then
                 let uu____1433 =
                   let uu____1434 =
                     let uu____1435 =
                       let uu____1440 = FStar_Ident.range_of_lid a in
                       ("SMTPat", uu____1440) in
                     FStar_Ident.mk_ident uu____1435 in
                   FStar_Parser_AST.Tvar uu____1434 in
                 mk uu____1433
               else
                 (let uu____1442 =
                    FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid in
                  if uu____1442
                  then
                    let uu____1443 =
                      let uu____1444 =
                        let uu____1445 =
                          let uu____1450 = FStar_Ident.range_of_lid a in
                          ("SMTPatOr", uu____1450) in
                        FStar_Ident.mk_ident uu____1445 in
                      FStar_Parser_AST.Tvar uu____1444 in
                    mk uu____1443
                  else
                    (let uu____1452 =
                       ((FStar_Ident.lid_equals a
                           FStar_Parser_Const.assert_lid)
                          ||
                          (FStar_Ident.lid_equals a
                             FStar_Parser_Const.assume_lid))
                         ||
                         (let uu____1455 =
                            let uu____1456 =
                              FStar_String.get s Prims.int_zero in
                            FStar_Char.uppercase uu____1456 in
                          let uu____1457 = FStar_String.get s Prims.int_zero in
                          uu____1455 <> uu____1457) in
                     if uu____1452
                     then
                       let uu____1458 =
                         let uu____1459 = maybe_shorten_fv env fv in
                         FStar_Parser_AST.Var uu____1459 in
                       mk uu____1458
                     else
                       (let uu____1461 =
                          let uu____1462 =
                            let uu____1473 = maybe_shorten_fv env fv in
                            (uu____1473, []) in
                          FStar_Parser_AST.Construct uu____1462 in
                        mk uu____1461))))
      | FStar_Syntax_Syntax.Tm_uinst (e, universes) ->
          let e1 = resugar_term' env e in
          let uu____1491 = FStar_Options.print_universes () in
          if uu____1491
          then
            let univs =
              FStar_List.map
                (fun x -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd, args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____1520 =
                     FStar_List.map (fun u -> (u, FStar_Parser_AST.UnivApp))
                       univs in
                   FStar_List.append args uu____1520 in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd, args1)) r l
             | uu____1543 ->
                 FStar_List.fold_left
                   (fun acc ->
                      fun u ->
                        mk
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____1550 = FStar_Syntax_Syntax.is_teff t in
          if uu____1550
          then
            let uu____1551 = name "Effect" t.FStar_Syntax_Syntax.pos in
            mk uu____1551
          else mk (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____1554 =
            match u with
            | FStar_Syntax_Syntax.U_zero -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown -> ("Type", false)
            | uu____1563 -> ("Type", true) in
          (match uu____1554 with
           | (nm, needs_app) ->
               let typ =
                 let uu____1567 = name nm t.FStar_Syntax_Syntax.pos in
                 mk uu____1567 in
               let uu____1568 =
                 needs_app && (FStar_Options.print_universes ()) in
               if uu____1568
               then
                 let uu____1569 =
                   let uu____1570 =
                     let uu____1577 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos in
                     (typ, uu____1577, FStar_Parser_AST.UnivApp) in
                   FStar_Parser_AST.App uu____1570 in
                 mk uu____1569
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs, body, uu____1581) ->
          let uu____1606 = FStar_Syntax_Subst.open_term xs body in
          (match uu____1606 with
           | (xs1, body1) ->
               let xs2 =
                 let uu____1622 = FStar_Options.print_implicits () in
                 if uu____1622 then xs1 else filter_imp xs1 in
               let body_bv = FStar_Syntax_Free.names body1 in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____1657 ->
                         match uu____1657 with
                         | (x, qual) -> resugar_bv_as_pat env x qual body_bv)) in
               let body2 = resugar_term' env body1 in
               mk (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs, body) ->
          let uu____1697 = FStar_Syntax_Subst.open_comp xs body in
          (match uu____1697 with
           | (xs1, body1) ->
               let xs2 =
                 let uu____1707 = FStar_Options.print_implicits () in
                 if uu____1707 then xs1 else filter_imp xs1 in
               let body2 = resugar_comp' env body1 in
               let xs3 =
                 let uu____1715 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos)) in
                 FStar_All.pipe_right uu____1715 FStar_List.rev in
               let rec aux body3 uu___2_1740 =
                 match uu___2_1740 with
                 | [] -> body3
                 | hd::tl ->
                     let body4 = mk (FStar_Parser_AST.Product ([hd], body3)) in
                     aux body4 tl in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu____1756 =
            let uu____1761 =
              let uu____1762 = FStar_Syntax_Syntax.mk_binder x in
              [uu____1762] in
            FStar_Syntax_Subst.open_term uu____1761 phi in
          (match uu____1756 with
           | (x1, phi1) ->
               let b =
                 let uu____1784 =
                   let uu____1787 = FStar_List.hd x1 in
                   resugar_binder' env uu____1787 t.FStar_Syntax_Syntax.pos in
                 FStar_Util.must uu____1784 in
               let uu____1794 =
                 let uu____1795 =
                   let uu____1800 = resugar_term' env phi1 in (b, uu____1800) in
                 FStar_Parser_AST.Refine uu____1795 in
               mk uu____1794)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____1802;
             FStar_Syntax_Syntax.vars = uu____1803;_},
           (e, uu____1805)::[])
          when
          (let uu____1846 = FStar_Options.print_implicits () in
           Prims.op_Negation uu____1846) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e, args) ->
          let rec last uu___3_1894 =
            match uu___3_1894 with
            | hd::[] -> [hd]
            | hd::tl -> last tl
            | uu____1964 -> failwith "last of an empty list" in
          let first_two_explicit args1 =
            let rec drop_implicits args2 =
              match args2 with
              | (uu____2049, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____2050))::tl ->
                  drop_implicits tl
              | uu____2068 -> args2 in
            let uu____2077 = drop_implicits args1 in
            match uu____2077 with
            | [] -> failwith "not_enough explicit_arguments"
            | uu____2108::[] -> failwith "not_enough explicit_arguments"
            | a1::a2::uu____2137 -> [a1; a2] in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____2237 ->
                   match uu____2237 with
                   | (e2, qual) ->
                       let uu____2254 = resugar_term' env e2 in
                       let uu____2255 = resugar_imp env qual in
                       (uu____2254, uu____2255)) args1 in
            let uu____2256 = resugar_term' env e1 in
            match uu____2256 with
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
                     fun uu____2293 ->
                       match uu____2293 with
                       | (x, qual) ->
                           mk (FStar_Parser_AST.App (acc, x, qual))) e2 args2 in
          let args1 =
            let uu____2309 = FStar_Options.print_implicits () in
            if uu____2309 then args else filter_imp args in
          let uu____2321 = resugar_term_as_op e in
          (match uu____2321 with
           | FStar_Pervasives_Native.None -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("calc_finish", uu____2332) ->
               let uu____2337 = resugar_calc env t in
               (match uu____2337 with
                | FStar_Pervasives_Native.Some r -> r
                | uu____2341 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("tuple", uu____2344) ->
               let out =
                 FStar_List.fold_left
                   (fun out ->
                      fun uu____2366 ->
                        match uu____2366 with
                        | (x, uu____2378) ->
                            let x1 = resugar_term' env x in
                            (match out with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix ->
                                 let uu____2387 =
                                   let uu____2388 =
                                     let uu____2389 =
                                       let uu____2396 =
                                         FStar_Ident.id_of_text "*" in
                                       (uu____2396, [prefix; x1]) in
                                     FStar_Parser_AST.Op uu____2389 in
                                   mk uu____2388 in
                                 FStar_Pervasives_Native.Some uu____2387))
                   FStar_Pervasives_Native.None args1 in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple", uu____2399) when
               (FStar_List.length args1) > Prims.int_zero ->
               let args2 = last args1 in
               let body =
                 match args2 with
                 | (b, uu____2421)::[] -> b
                 | uu____2438 -> failwith "wrong arguments to dtuple" in
               let uu____2447 =
                 let uu____2448 = FStar_Syntax_Subst.compress body in
                 uu____2448.FStar_Syntax_Syntax.n in
               (match uu____2447 with
                | FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2453) ->
                    let uu____2478 = FStar_Syntax_Subst.open_term xs body1 in
                    (match uu____2478 with
                     | (xs1, body2) ->
                         let xs2 =
                           let uu____2488 = FStar_Options.print_implicits () in
                           if uu____2488 then xs1 else filter_imp xs1 in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos)) in
                         let body3 = resugar_term' env body2 in
                         let uu____2502 =
                           let uu____2503 =
                             let uu____2514 =
                               FStar_List.map
                                 (fun uu____2525 -> FStar_Util.Inl uu____2525)
                                 xs3 in
                             (uu____2514, body3) in
                           FStar_Parser_AST.Sum uu____2503 in
                         mk uu____2502)
                | uu____2532 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____2555 ->
                              match uu____2555 with
                              | (e1, qual) -> resugar_term' env e1)) in
                    let e1 = resugar_term' env e in
                    FStar_List.fold_left
                      (fun acc ->
                         fun x ->
                           mk
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple", uu____2573) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read, uu____2579) when
               let uu____2584 =
                 FStar_Ident.string_of_lid FStar_Parser_Const.sread_lid in
               ref_read = uu____2584 ->
               let uu____2585 = FStar_List.hd args1 in
               (match uu____2585 with
                | (t1, uu____2599) ->
                    let uu____2604 =
                      let uu____2605 = FStar_Syntax_Subst.compress t1 in
                      uu____2605.FStar_Syntax_Syntax.n in
                    (match uu____2604 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         let uu____2609 =
                           FStar_Ident.string_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                         FStar_Syntax_Util.field_projector_contains_constructor
                           uu____2609
                         ->
                         let f =
                           let uu____2611 =
                             let uu____2612 =
                               FStar_Ident.string_of_lid
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             [uu____2612] in
                           FStar_Ident.lid_of_path uu____2611
                             t1.FStar_Syntax_Syntax.pos in
                         let uu____2613 =
                           let uu____2614 =
                             let uu____2619 = resugar_term' env t1 in
                             (uu____2619, f) in
                           FStar_Parser_AST.Project uu____2614 in
                         mk uu____2613
                     | uu____2620 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with", uu____2621) when
               (FStar_List.length args1) > Prims.int_one ->
               (try
                  (fun uu___435_2644 ->
                     match () with
                     | () ->
                         let new_args = first_two_explicit args1 in
                         let uu____2654 =
                           match new_args with
                           | (a1, uu____2664)::(a2, uu____2666)::[] ->
                               (a1, a2)
                           | uu____2693 ->
                               failwith "wrong arguments to try_with" in
                         (match uu____2654 with
                          | (body, handler) ->
                              let decomp term =
                                let uu____2714 =
                                  let uu____2715 =
                                    FStar_Syntax_Subst.compress term in
                                  uu____2715.FStar_Syntax_Syntax.n in
                                match uu____2714 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (x, e1, uu____2720) ->
                                    let uu____2745 =
                                      FStar_Syntax_Subst.open_term x e1 in
                                    (match uu____2745 with | (x1, e2) -> e2)
                                | uu____2752 ->
                                    let uu____2753 =
                                      let uu____2754 =
                                        let uu____2755 =
                                          resugar_term' env term in
                                        FStar_Parser_AST.term_to_string
                                          uu____2755 in
                                      Prims.op_Hat
                                        "wrong argument format to try_with: "
                                        uu____2754 in
                                    failwith uu____2753 in
                              let body1 =
                                let uu____2757 = decomp body in
                                resugar_term' env uu____2757 in
                              let handler1 =
                                let uu____2759 = decomp handler in
                                resugar_term' env uu____2759 in
                              let rec resugar_body t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match
                                    (e1, (uu____2767, uu____2768, b)::[]) ->
                                    b
                                | FStar_Parser_AST.Let
                                    (uu____2800, uu____2801, b) -> b
                                | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                                    let uu____2838 =
                                      let uu____2839 =
                                        let uu____2848 = resugar_body t11 in
                                        (uu____2848, t2, t3) in
                                      FStar_Parser_AST.Ascribed uu____2839 in
                                    mk uu____2838
                                | uu____2851 ->
                                    failwith
                                      "unexpected body format to try_with" in
                              let e1 = resugar_body body1 in
                              let rec resugar_branches t1 =
                                match t1.FStar_Parser_AST.tm with
                                | FStar_Parser_AST.Match (e2, branches) ->
                                    branches
                                | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                                    resugar_branches t11
                                | uu____2908 -> [] in
                              let branches = resugar_branches handler1 in
                              mk (FStar_Parser_AST.TryWith (e1, branches))))
                    ()
                with | uu____2941 -> resugar_as_app e args1)
           | FStar_Pervasives_Native.Some ("try_with", uu____2942) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op, uu____2948) when
               (((((((op = "=") || (op = "==")) || (op = "===")) ||
                     (op = "@"))
                    || (op = ":="))
                   || (op = "|>"))
                  || (op = "<<"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op, uu____2954) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pats t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (xs', (uu____3012, pats'), body)
                     ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | FStar_Parser_AST.QForall (xs', (uu____3044, pats'), body)
                     ->
                     uncurry (FStar_List.append xs xs')
                       (FStar_List.append pats pats') body
                 | uu____3075 -> (xs, pats, t1) in
               let resugar_forall_body body =
                 let uu____3088 =
                   let uu____3089 = FStar_Syntax_Subst.compress body in
                   uu____3089.FStar_Syntax_Syntax.n in
                 match uu____3088 with
                 | FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____3094) ->
                     let uu____3119 = FStar_Syntax_Subst.open_term xs body1 in
                     (match uu____3119 with
                      | (xs1, body2) ->
                          let xs2 =
                            let uu____3129 = FStar_Options.print_implicits () in
                            if uu____3129 then xs1 else filter_imp xs1 in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos)) in
                          let uu____3142 =
                            let uu____3151 =
                              let uu____3152 =
                                FStar_Syntax_Subst.compress body2 in
                              uu____3152.FStar_Syntax_Syntax.n in
                            match uu____3151 with
                            | FStar_Syntax_Syntax.Tm_meta (e1, m) ->
                                let body3 = resugar_term' env e1 in
                                let uu____3170 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____3187, pats) ->
                                      let uu____3221 =
                                        FStar_List.map
                                          (fun es ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____3265 ->
                                                     match uu____3265 with
                                                     | (e2, uu____3273) ->
                                                         resugar_term' env e2)))
                                          pats in
                                      (uu____3221, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled
                                      (s, r, p) ->
                                      let uu____3285 =
                                        mk
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p)) in
                                      ([], uu____3285)
                                  | uu____3292 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists" in
                                (match uu____3170 with
                                 | (pats, body4) -> (pats, body4))
                            | uu____3323 ->
                                let uu____3324 = resugar_term' env body2 in
                                ([], uu____3324) in
                          (match uu____3142 with
                           | (pats, body3) ->
                               let uu____3341 = uncurry xs3 pats body3 in
                               (match uu____3341 with
                                | (xs4, pats1, body4) ->
                                    if op = "forall"
                                    then
                                      let uu____3369 =
                                        let uu____3370 =
                                          let uu____3389 =
                                            let uu____3400 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs4 t.FStar_Syntax_Syntax.pos in
                                            (uu____3400, pats1) in
                                          (xs4, uu____3389, body4) in
                                        FStar_Parser_AST.QForall uu____3370 in
                                      mk uu____3369
                                    else
                                      (let uu____3422 =
                                         let uu____3423 =
                                           let uu____3442 =
                                             let uu____3453 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs4
                                                 t.FStar_Syntax_Syntax.pos in
                                             (uu____3453, pats1) in
                                           (xs4, uu____3442, body4) in
                                         FStar_Parser_AST.QExists uu____3423 in
                                       mk uu____3422))))
                 | uu____3474 ->
                     if op = "forall"
                     then
                       let uu____3475 =
                         let uu____3476 =
                           let uu____3495 = resugar_term' env body in
                           ([], ([], []), uu____3495) in
                         FStar_Parser_AST.QForall uu____3476 in
                       mk uu____3475
                     else
                       (let uu____3517 =
                          let uu____3518 =
                            let uu____3537 = resugar_term' env body in
                            ([], ([], []), uu____3537) in
                          FStar_Parser_AST.QExists uu____3518 in
                        mk uu____3517) in
               if (FStar_List.length args1) > Prims.int_zero
               then
                 let args2 = last args1 in
                 (match args2 with
                  | (b, uu____3574)::[] -> resugar_forall_body b
                  | uu____3591 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc", uu____3601) ->
               let uu____3606 = FStar_List.hd args1 in
               (match uu____3606 with
                | (e1, uu____3620) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op, expected_arity1) ->
               let op1 = FStar_Ident.id_of_text op in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____3689 ->
                         match uu____3689 with
                         | (e1, qual) ->
                             let uu____3706 = resugar_term' env e1 in
                             let uu____3707 = resugar_imp env qual in
                             (uu____3706, uu____3707))) in
               (match expected_arity1 with
                | FStar_Pervasives_Native.None ->
                    let resugared_args = resugar args1 in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1 in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____3720 =
                        FStar_Util.first_N expect_n resugared_args in
                      (match uu____3720 with
                       | (op_args, rest) ->
                           let head =
                             let uu____3768 =
                               let uu____3769 =
                                 let uu____3776 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args in
                                 (op1, uu____3776) in
                               FStar_Parser_AST.Op uu____3769 in
                             mk uu____3768 in
                           FStar_List.fold_left
                             (fun head1 ->
                                fun uu____3794 ->
                                  match uu____3794 with
                                  | (arg, qual) ->
                                      mk
                                        (FStar_Parser_AST.App
                                           (head1, arg, qual))) head rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n when
                    (FStar_List.length args1) = n ->
                    let uu____3809 =
                      let uu____3810 =
                        let uu____3817 =
                          let uu____3820 = resugar args1 in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____3820 in
                        (op1, uu____3817) in
                      FStar_Parser_AST.Op uu____3810 in
                    mk uu____3809
                | uu____3833 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e, (pat, wopt, t1)::[]) ->
          let uu____3902 = FStar_Syntax_Subst.open_branch (pat, wopt, t1) in
          (match uu____3902 with
           | (pat1, wopt1, t2) ->
               let branch_bv = FStar_Syntax_Free.names t2 in
               let bnds =
                 let uu____3948 =
                   let uu____3961 =
                     let uu____3966 = resugar_pat' env pat1 branch_bv in
                     let uu____3967 = resugar_term' env e in
                     (uu____3966, uu____3967) in
                   (FStar_Pervasives_Native.None, uu____3961) in
                 [uu____3948] in
               let body = resugar_term' env t2 in
               mk
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e, (pat1, uu____4019, t1)::(pat2, uu____4022, t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____4118 =
            let uu____4119 =
              let uu____4126 = resugar_term' env e in
              let uu____4127 = resugar_term' env t1 in
              let uu____4128 = resugar_term' env t2 in
              (uu____4126, uu____4127, uu____4128) in
            FStar_Parser_AST.If uu____4119 in
          mk uu____4118
      | FStar_Syntax_Syntax.Tm_match (e, branches) ->
          let resugar_branch uu____4194 =
            match uu____4194 with
            | (pat, wopt, b) ->
                let uu____4236 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b) in
                (match uu____4236 with
                 | (pat1, wopt1, b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1 in
                     let pat2 = resugar_pat' env pat1 branch_bv in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____4288 = resugar_term' env e1 in
                           FStar_Pervasives_Native.Some uu____4288 in
                     let b2 = resugar_term' env b1 in (pat2, wopt2, b2)) in
          let uu____4292 =
            let uu____4293 =
              let uu____4308 = resugar_term' env e in
              let uu____4309 = FStar_List.map resugar_branch branches in
              (uu____4308, uu____4309) in
            FStar_Parser_AST.Match uu____4293 in
          mk uu____4292
      | FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____4355) ->
          let term =
            match asc with
            | FStar_Util.Inl n -> resugar_term' env n
            | FStar_Util.Inr n -> resugar_comp' env n in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt in
          let uu____4424 =
            let uu____4425 =
              let uu____4434 = resugar_term' env e in
              (uu____4434, term, tac_opt1) in
            FStar_Parser_AST.Ascribed uu____4425 in
          mk uu____4424
      | FStar_Syntax_Syntax.Tm_let ((is_rec, source_lbs), body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos in
          let uu____4460 = FStar_Syntax_Subst.open_let_rec source_lbs body in
          (match uu____4460 with
           | (source_lbs1, body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____4513 =
                         FStar_List.map (resugar_term' env) tms in
                       FStar_Pervasives_Native.Some uu____4513 in
                 let uu____4520 =
                   let uu____4525 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____4525 in
                 match uu____4520 with
                 | (univs, td) ->
                     let uu____4544 =
                       let uu____4551 =
                         let uu____4552 = FStar_Syntax_Subst.compress td in
                         uu____4552.FStar_Syntax_Syntax.n in
                       match uu____4551 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____4561,
                            (t1, uu____4563)::(d, uu____4565)::[])
                           -> (t1, d)
                       | uu____4622 -> failwith "wrong let binding format" in
                     (match uu____4544 with
                      | (typ, def) ->
                          let uu____4651 =
                            let uu____4666 =
                              let uu____4667 =
                                FStar_Syntax_Subst.compress def in
                              uu____4667.FStar_Syntax_Syntax.n in
                            match uu____4666 with
                            | FStar_Syntax_Syntax.Tm_abs (b, t1, uu____4686)
                                ->
                                let uu____4711 =
                                  FStar_Syntax_Subst.open_term b t1 in
                                (match uu____4711 with
                                 | (b1, t2) ->
                                     let b2 =
                                       let uu____4741 =
                                         FStar_Options.print_implicits () in
                                       if uu____4741
                                       then b1
                                       else filter_imp b1 in
                                     (b2, t2, true))
                            | uu____4759 -> ([], def, false) in
                          (match uu____4651 with
                           | (binders, term, is_pat_app) ->
                               let uu____4809 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____4820 =
                                       let uu____4821 =
                                         let uu____4822 =
                                           let uu____4829 =
                                             bv_as_unique_ident bv in
                                           (uu____4829,
                                             FStar_Pervasives_Native.None) in
                                         FStar_Parser_AST.PatVar uu____4822 in
                                       mk_pat uu____4821 in
                                     (uu____4820, term) in
                               (match uu____4809 with
                                | (pat, term1) ->
                                    let uu____4850 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____4890 ->
                                                  match uu____4890 with
                                                  | (bv, q) ->
                                                      let uu____4905 =
                                                        resugar_arg_qual env
                                                          q in
                                                      FStar_Util.map_opt
                                                        uu____4905
                                                        (fun q1 ->
                                                           let uu____4917 =
                                                             let uu____4918 =
                                                               let uu____4925
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv in
                                                               (uu____4925,
                                                                 q1) in
                                                             FStar_Parser_AST.PatVar
                                                               uu____4918 in
                                                           mk_pat uu____4917))) in
                                        let uu____4928 =
                                          let uu____4933 =
                                            resugar_term' env term1 in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____4933) in
                                        let uu____4936 =
                                          universe_to_string univs in
                                        (uu____4928, uu____4936)
                                      else
                                        (let uu____4942 =
                                           let uu____4947 =
                                             resugar_term' env term1 in
                                           (pat, uu____4947) in
                                         let uu____4948 =
                                           universe_to_string univs in
                                         (uu____4942, uu____4948)) in
                                    (attrs_opt, uu____4850)))) in
               let r = FStar_List.map resugar_one_binding source_lbs1 in
               let bnds =
                 let f uu____5048 =
                   match uu____5048 with
                   | (attrs, (pb, univs)) ->
                       let uu____5104 =
                         let uu____5105 = FStar_Options.print_universes () in
                         Prims.op_Negation uu____5105 in
                       if uu____5104
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
      | FStar_Syntax_Syntax.Tm_uvar (u, uu____5180) ->
          let s =
            let uu____5198 =
              let uu____5199 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head in
              FStar_All.pipe_right uu____5199 FStar_Util.string_of_int in
            Prims.op_Hat "?u" uu____5198 in
          let uu____5200 = mk FStar_Parser_AST.Wild in label s uu____5200
      | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic -> FStar_Parser_AST.Dynamic in
          let uu____5208 =
            let uu____5209 =
              let uu____5214 = resugar_term' env tm in (uu____5214, qi1) in
            FStar_Parser_AST.Quote uu____5209 in
          mk uu____5208
      | FStar_Syntax_Syntax.Tm_meta (e, m) ->
          let resugar_meta_desugared uu___4_5226 =
            match uu___4_5226 with
            | FStar_Syntax_Syntax.Sequence ->
                let term = resugar_term' env e in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____5234, (uu____5235, (p, t11))::[], t2) ->
                      mk (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11, t2, t3) ->
                      let uu____5296 =
                        let uu____5297 =
                          let uu____5306 = resugar_seq t11 in
                          (uu____5306, t2, t3) in
                        FStar_Parser_AST.Ascribed uu____5297 in
                      mk uu____5296
                  | uu____5309 -> t1 in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat -> resugar_term' env e in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____5310, pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____5374 ->
                         match uu____5374 with
                         | (x, uu____5382) -> resugar_term' env x)) in
               mk (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____5387 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (uu____5396, t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift
               (uu____5402, uu____5403, t1) -> resugar_term' env e)
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
        let uu____5437 = FStar_Syntax_Util.head_and_args t in
        match uu____5437 with
        | (hd, args) ->
            let uu____5486 =
              let uu____5501 =
                let uu____5502 =
                  let uu____5505 = FStar_Syntax_Util.un_uinst hd in
                  FStar_Syntax_Subst.compress uu____5505 in
                uu____5502.FStar_Syntax_Syntax.n in
              (uu____5501, args) in
            (match uu____5486 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____5523, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5524))::(rel,
                                                              FStar_Pervasives_Native.None)::
                (uu____5526, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5527))::(uu____5528,
                                                              FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Syntax.Implicit
                                                              uu____5529))::
                (pf, FStar_Pervasives_Native.None)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_finish_lid
                 ->
                 let pf1 = FStar_Syntax_Util.unthunk pf in
                 FStar_Pervasives_Native.Some (rel, pf1)
             | uu____5624 -> FStar_Pervasives_Native.None) in
      let un_eta_rel rel =
        let bv_eq_tm b t =
          let uu____5664 =
            let uu____5665 = FStar_Syntax_Subst.compress t in
            uu____5665.FStar_Syntax_Syntax.n in
          match uu____5664 with
          | FStar_Syntax_Syntax.Tm_name b' when
              FStar_Syntax_Syntax.bv_eq b b' -> true
          | uu____5669 -> false in
        let uu____5670 =
          let uu____5671 = FStar_Syntax_Subst.compress rel in
          uu____5671.FStar_Syntax_Syntax.n in
        match uu____5670 with
        | FStar_Syntax_Syntax.Tm_abs (b1::b2::[], body, uu____5679) ->
            let uu____5726 = FStar_Syntax_Subst.open_term [b1; b2] body in
            (match uu____5726 with
             | (b11::b21::[], body1) ->
                 let body2 = FStar_Syntax_Util.unascribe body1 in
                 let body3 =
                   let uu____5786 = FStar_Syntax_Util.unb2t body2 in
                   match uu____5786 with
                   | FStar_Pervasives_Native.Some body3 -> body3
                   | FStar_Pervasives_Native.None -> body2 in
                 let uu____5790 =
                   let uu____5791 = FStar_Syntax_Subst.compress body3 in
                   uu____5791.FStar_Syntax_Syntax.n in
                 (match uu____5790 with
                  | FStar_Syntax_Syntax.Tm_app (e, args) when
                      (FStar_List.length args) >= (Prims.of_int (2)) ->
                      (match FStar_List.rev args with
                       | (a1, FStar_Pervasives_Native.None)::(a2,
                                                              FStar_Pervasives_Native.None)::rest
                           ->
                           let uu____5881 =
                             (bv_eq_tm (FStar_Pervasives_Native.fst b11) a2)
                               &&
                               (bv_eq_tm (FStar_Pervasives_Native.fst b21) a1) in
                           if uu____5881
                           then
                             let uu____5888 =
                               FStar_Syntax_Util.mk_app e
                                 (FStar_List.rev rest) in
                             FStar_All.pipe_left
                               (fun uu____5899 ->
                                  FStar_Pervasives_Native.Some uu____5899)
                               uu____5888
                           else FStar_Pervasives_Native.Some rel
                       | uu____5901 -> FStar_Pervasives_Native.Some rel)
                  | uu____5912 -> FStar_Pervasives_Native.Some rel))
        | uu____5913 -> FStar_Pervasives_Native.Some rel in
      let resugar_step pack =
        let uu____5940 = FStar_Syntax_Util.head_and_args pack in
        match uu____5940 with
        | (hd, args) ->
            let uu____5993 =
              let uu____6008 =
                let uu____6009 =
                  let uu____6012 = FStar_Syntax_Util.un_uinst hd in
                  FStar_Syntax_Subst.compress uu____6012 in
                uu____6009.FStar_Syntax_Syntax.n in
              (uu____6008, args) in
            (match uu____5993 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____6034, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6035))::(uu____6036,
                                                              FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Syntax.Implicit
                                                              uu____6037))::
                (uu____6038, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6039))::(rel,
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
             | uu____6170 -> FStar_Pervasives_Native.None) in
      let resugar_init pack =
        let uu____6203 = FStar_Syntax_Util.head_and_args pack in
        match uu____6203 with
        | (hd, args) ->
            let uu____6248 =
              let uu____6263 =
                let uu____6264 =
                  let uu____6267 = FStar_Syntax_Util.un_uinst hd in
                  FStar_Syntax_Subst.compress uu____6267 in
                uu____6264.FStar_Syntax_Syntax.n in
              (uu____6263, args) in
            (match uu____6248 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____6281, FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6282))::(x,
                                                              FStar_Pervasives_Native.None)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.calc_init_lid
                 -> FStar_Pervasives_Native.Some x
             | uu____6330 -> FStar_Pervasives_Native.None) in
      let rec resugar_all_steps pack =
        let uu____6379 = resugar_step pack in
        match uu____6379 with
        | FStar_Pervasives_Native.Some (t, r, j, k) ->
            let uu____6416 = resugar_all_steps k in
            FStar_Util.bind_opt uu____6416
              (fun uu____6458 ->
                 match uu____6458 with
                 | (steps, k1) ->
                     FStar_Pervasives_Native.Some (((t, r, j) :: steps), k1))
        | FStar_Pervasives_Native.None ->
            FStar_Pervasives_Native.Some ([], pack) in
      let resugar_rel rel =
        let rel1 =
          let uu____6570 = un_eta_rel rel in
          match uu____6570 with
          | FStar_Pervasives_Native.Some rel1 -> rel1
          | FStar_Pervasives_Native.None -> rel in
        let fallback uu____6579 =
          let uu____6580 =
            let uu____6581 = resugar_term' env rel1 in
            FStar_Parser_AST.Paren uu____6581 in
          mk uu____6580 in
        let uu____6582 = FStar_Syntax_Util.head_and_args rel1 in
        match uu____6582 with
        | (hd, args) ->
            let uu____6625 =
              (FStar_Options.print_implicits ()) &&
                (FStar_List.existsb
                   (fun uu____6635 ->
                      match uu____6635 with
                      | (uu____6642, q) -> FStar_Syntax_Syntax.is_implicit q)
                   args) in
            if uu____6625
            then fallback ()
            else
              (let uu____6649 = resugar_term_as_op hd in
               match uu____6649 with
               | FStar_Pervasives_Native.Some
                   (s, FStar_Pervasives_Native.None) ->
                   let uu____6661 =
                     let uu____6662 =
                       let uu____6669 = FStar_Ident.id_of_text s in
                       (uu____6669, []) in
                     FStar_Parser_AST.Op uu____6662 in
                   mk uu____6661
               | FStar_Pervasives_Native.Some
                   (s, FStar_Pervasives_Native.Some uu____6677) when
                   uu____6677 = (Prims.of_int (2)) ->
                   let uu____6678 =
                     let uu____6679 =
                       let uu____6686 = FStar_Ident.id_of_text s in
                       (uu____6686, []) in
                     FStar_Parser_AST.Op uu____6679 in
                   mk uu____6678
               | uu____6689 -> fallback ()) in
      let build_calc rel x0 steps =
        let r = resugar_term' env in
        let uu____6733 =
          let uu____6734 =
            let uu____6743 = resugar_rel rel in
            let uu____6744 = r x0 in
            let uu____6745 =
              FStar_List.map
                (fun uu____6759 ->
                   match uu____6759 with
                   | (z, rel1, j) ->
                       let uu____6769 =
                         let uu____6776 = resugar_rel rel1 in
                         let uu____6777 = r j in
                         let uu____6778 = r z in
                         (uu____6776, uu____6777, uu____6778) in
                       FStar_Parser_AST.CalcStep uu____6769) steps in
            (uu____6743, uu____6744, uu____6745) in
          FStar_Parser_AST.CalcProof uu____6734 in
        mk uu____6733 in
      let uu____6781 = resugar_calc_finish t0 in
      FStar_Util.bind_opt uu____6781
        (fun uu____6796 ->
           match uu____6796 with
           | (rel, pack) ->
               let uu____6805 = resugar_all_steps pack in
               FStar_Util.bind_opt uu____6805
                 (fun uu____6836 ->
                    match uu____6836 with
                    | (steps, k) ->
                        let uu____6869 = resugar_init k in
                        FStar_Util.bind_opt uu____6869
                          (fun x0 ->
                             let uu____6875 =
                               build_calc rel x0 (FStar_List.rev steps) in
                             FStar_All.pipe_left
                               (fun uu____6884 ->
                                  FStar_Pervasives_Native.Some uu____6884)
                               uu____6875)))
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
               let uu____6919 = FStar_Options.print_universes () in
               if uu____6919
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
               let uu____6980 = FStar_Options.print_universes () in
               if uu____6980
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
            let uu____7021 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ in
            (uu____7021, FStar_Parser_AST.Nothing) in
          let uu____7022 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid) in
          if uu____7022
          then
            let universe =
              FStar_List.map (fun u -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs in
            let args =
              let uu____7043 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid in
              if uu____7043
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____7126 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post) in
                      (uu____7126, (FStar_Pervasives_Native.snd post)) in
                    let uu____7137 =
                      let uu____7146 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre) in
                      if uu____7146 then [] else [pre] in
                    let uu____7178 =
                      let uu____7187 =
                        let uu____7196 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats) in
                        if uu____7196 then [] else [pats] in
                      FStar_List.append [post1] uu____7187 in
                    FStar_List.append uu____7137 uu____7178
                | uu____7252 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args in
            let args1 =
              FStar_List.map
                (fun uu____7285 ->
                   match uu____7285 with
                   | (e, uu____7297) ->
                       let uu____7302 = resugar_term' env e in
                       (uu____7302, FStar_Parser_AST.Nothing)) args in
            let rec aux l uu___5_7327 =
              match uu___5_7327 with
              | [] -> l
              | hd::tl ->
                  (match hd with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____7360 = resugar_term' env e in
                         (uu____7360, FStar_Parser_AST.Nothing) in
                       aux (e1 :: l) tl
                   | uu____7365 -> aux l tl) in
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
        let uu____7411 = b in
        match uu____7411 with
        | (x, aq) ->
            let uu____7420 = resugar_arg_qual env aq in
            FStar_Util.map_opt uu____7420
              (fun imp ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild ->
                     let uu____7434 =
                       let uu____7435 = bv_as_unique_ident x in
                       FStar_Parser_AST.Variable uu____7435 in
                     FStar_Parser_AST.mk_binder uu____7434 r
                       FStar_Parser_AST.Type_level imp
                 | uu____7436 ->
                     let uu____7437 = FStar_Syntax_Syntax.is_null_bv x in
                     if uu____7437
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____7439 =
                          let uu____7440 =
                            let uu____7445 = bv_as_unique_ident x in
                            (uu____7445, e) in
                          FStar_Parser_AST.Annotated uu____7440 in
                        FStar_Parser_AST.mk_binder uu____7439 r
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
              let uu____7465 = FStar_Syntax_Syntax.range_of_bv v in
              FStar_Parser_AST.mk_pattern a uu____7465 in
            let used = FStar_Util.set_mem v body_bv in
            let pat =
              let uu____7468 =
                if used
                then
                  let uu____7469 =
                    let uu____7476 = bv_as_unique_ident v in
                    (uu____7476, aqual) in
                  FStar_Parser_AST.PatVar uu____7469
                else FStar_Parser_AST.PatWild aqual in
              mk uu____7468 in
            match typ_opt with
            | FStar_Pervasives_Native.None -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown;
                  FStar_Syntax_Syntax.pos = uu____7482;
                  FStar_Syntax_Syntax.vars = uu____7483;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____7493 = FStar_Options.print_bound_var_types () in
                if uu____7493
                then
                  let uu____7494 =
                    let uu____7495 =
                      let uu____7506 =
                        let uu____7513 = resugar_term' env typ in
                        (uu____7513, FStar_Pervasives_Native.None) in
                      (pat, uu____7506) in
                    FStar_Parser_AST.PatAscribed uu____7495 in
                  mk uu____7494
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
          let uu____7533 = resugar_arg_qual env qual in
          FStar_Util.map_opt uu____7533
            (fun aqual ->
               let uu____7545 =
                 let uu____7550 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort in
                 FStar_All.pipe_left
                   (fun uu____7561 -> FStar_Pervasives_Native.Some uu____7561)
                   uu____7550 in
               resugar_bv_as_pat' env x aqual body_bv uu____7545)
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
          (let uu____7614 = FStar_Options.print_implicits () in
           Prims.op_Negation uu____7614) &&
            (let uu____7616 =
               FStar_List.existsML
                 (fun uu____7627 ->
                    match uu____7627 with
                    | (pattern, is_implicit) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv, uu____7643)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____7648 -> false
                          | uu____7649 -> true in
                        is_implicit && might_be_used) args in
             Prims.op_Negation uu____7616) in
        let resugar_plain_pat_cons' fv args =
          mk
            (FStar_Parser_AST.PatApp
               ((mk
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args)) in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____7712 = may_drop_implicits args in
            if uu____7712 then filter_pattern_imp args else args in
          let args2 =
            FStar_List.map
              (fun uu____7732 ->
                 match uu____7732 with
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
              ((let uu____7778 =
                  let uu____7779 =
                    let uu____7780 = filter_pattern_imp args in
                    FStar_List.isEmpty uu____7780 in
                  Prims.op_Negation uu____7779 in
                if uu____7778
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
              let uu____7816 = filter_pattern_imp args in
              (match uu____7816 with
               | (hd, false)::(tl, false)::[] ->
                   let hd' = aux hd (FStar_Pervasives_Native.Some false) in
                   let uu____7856 =
                     aux tl (FStar_Pervasives_Native.Some false) in
                   (match uu____7856 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____7872 =
                       let uu____7877 =
                         let uu____7878 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args') in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____7878 in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____7877) in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____7872);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv, args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____7921 ->
                        match uu____7921 with
                        | (p2, is_implicit) ->
                            if is_implicit
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____7933 =
                                 aux p2 (FStar_Pervasives_Native.Some false) in
                               FStar_Pervasives_Native.Some uu____7933))) in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              mk (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____7937;
                 FStar_Syntax_Syntax.fv_delta = uu____7938;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name, fields));_},
               args)
              ->
              let fields1 =
                let uu____7965 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f -> FStar_Ident.lid_of_ids [f])) in
                FStar_All.pipe_right uu____7965 FStar_List.rev in
              let args1 =
                let uu____7981 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____7999 ->
                          match uu____7999 with
                          | (p2, b) ->
                              aux p2 (FStar_Pervasives_Native.Some b))) in
                FStar_All.pipe_right uu____7981 FStar_List.rev in
              let rec map2 l1 l2 =
                match (l1, l2) with
                | ([], []) -> []
                | ([], hd::tl) -> []
                | (hd::tl, []) ->
                    let uu____8073 = map2 tl [] in
                    (hd,
                      (mk
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____8073
                | (hd1::tl1, hd2::tl2) ->
                    let uu____8096 = map2 tl1 tl2 in (hd1, hd2) :: uu____8096 in
              let args2 =
                let uu____8114 = map2 fields1 args1 in
                FStar_All.pipe_right uu____8114 FStar_List.rev in
              mk (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv, args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v ->
              let uu____8156 =
                let uu____8165 =
                  FStar_Ident.string_of_id v.FStar_Syntax_Syntax.ppname in
                string_to_op uu____8165 in
              (match uu____8156 with
               | FStar_Pervasives_Native.Some (op, uu____8167) ->
                   let uu____8178 =
                     let uu____8179 =
                       let uu____8180 =
                         let uu____8185 =
                           FStar_Ident.range_of_id
                             v.FStar_Syntax_Syntax.ppname in
                         (op, uu____8185) in
                       FStar_Ident.mk_ident uu____8180 in
                     FStar_Parser_AST.PatOp uu____8179 in
                   mk uu____8178
               | FStar_Pervasives_Native.None ->
                   let uu____8192 = to_arg_qual imp_opt in
                   resugar_bv_as_pat' env v uu____8192 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____8197 ->
              let uu____8198 =
                let uu____8199 = to_arg_qual imp_opt in
                FStar_Parser_AST.PatWild uu____8199 in
              mk uu____8198
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
          let uu____8235 =
            let uu____8238 =
              let uu____8239 =
                let uu____8240 = resugar_term' env t in
                FStar_Parser_AST.Arg_qualifier_meta_tac uu____8240 in
              FStar_Parser_AST.Meta uu____8239 in
            FStar_Pervasives_Native.Some uu____8238 in
          FStar_Pervasives_Native.Some uu____8235
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____8246 =
            let uu____8249 =
              let uu____8250 =
                let uu____8251 = resugar_term' env t in
                FStar_Parser_AST.Arg_qualifier_meta_attr uu____8251 in
              FStar_Parser_AST.Meta uu____8250 in
            FStar_Pervasives_Native.Some uu____8249 in
          FStar_Pervasives_Native.Some uu____8246
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
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta uu____8258) ->
          FStar_Parser_AST.Nothing
let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___6_8265 ->
    match uu___6_8265 with
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
    | FStar_Syntax_Syntax.Reflectable uu____8272 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____8273 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____8274 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____8279 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____8288 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____8297 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName -> FStar_Pervasives_Native.None
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___7_8302 ->
    match uu___7_8302 with
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
            (tylid, uvs, bs, t, uu____8341, datacons) ->
            let uu____8351 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1 ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____8378, uu____8379, uu____8380, inductive_lid,
                           uu____8382, uu____8383)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____8388 -> failwith "unexpected")) in
            (match uu____8351 with
             | (current_datacons, other_datacons) ->
                 let bs1 =
                   let uu____8407 = FStar_Options.print_implicits () in
                   if uu____8407 then bs else filter_imp bs in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos)) in
                 let tyc =
                   let uu____8421 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___8_8426 ->
                             match uu___8_8426 with
                             | FStar_Syntax_Syntax.RecordType uu____8427 ->
                                 true
                             | uu____8436 -> false)) in
                   if uu____8421
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____8472, univs, term, uu____8475, num,
                            uu____8477)
                           ->
                           let uu____8482 =
                             let uu____8483 =
                               FStar_Syntax_Subst.compress term in
                             uu____8483.FStar_Syntax_Syntax.n in
                           (match uu____8482 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3, uu____8493)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____8550 ->
                                          match uu____8550 with
                                          | (b, qual) ->
                                              let uu____8567 =
                                                bv_as_unique_ident b in
                                              let uu____8568 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort in
                                              (uu____8567, uu____8568))) in
                                FStar_List.append mfields fields
                            | uu____8573 -> failwith "unexpected")
                       | uu____8580 -> failwith "unexpected" in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons in
                     let uu____8604 =
                       let uu____8623 = FStar_Ident.ident_of_lid tylid in
                       (uu____8623, bs2, FStar_Pervasives_Native.None,
                         fields) in
                     FStar_Parser_AST.TyconRecord uu____8604
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l, univs, term, uu____8689, num, uu____8691) ->
                            let c =
                              let uu____8705 = FStar_Ident.ident_of_lid l in
                              let uu____8706 =
                                let uu____8709 = resugar_term' env term in
                                FStar_Pervasives_Native.Some uu____8709 in
                              (uu____8705, uu____8706, false) in
                            c :: constructors
                        | uu____8720 -> failwith "unexpected" in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons in
                      let uu____8760 =
                        let uu____8783 = FStar_Ident.ident_of_lid tylid in
                        (uu____8783, bs2, FStar_Pervasives_Native.None,
                          constructors) in
                      FStar_Parser_AST.TyconVariant uu____8760) in
                 (other_datacons, tyc))
        | uu____8798 ->
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
        let uu____8822 = FStar_List.choose resugar_qualifier q in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.quals = uu____8822;
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
        let uu____8848 = ts in
        match uu____8848 with
        | (univs, typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos)) in
            let uu____8860 =
              let uu____8861 =
                let uu____8870 =
                  let uu____8873 =
                    let uu____8874 =
                      let uu____8887 = resugar_term' env typ in
                      (name1, [], FStar_Pervasives_Native.None, uu____8887) in
                    FStar_Parser_AST.TyconAbbrev uu____8874 in
                  [uu____8873] in
                (false, false, uu____8870) in
              FStar_Parser_AST.Tycon uu____8861 in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8860
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
              let uu____8941 = resugar_tscheme'' env name ts in [uu____8941]
          | FStar_Pervasives_Native.None -> [] in
        let repr = resugar_opt "repr" combs.FStar_Syntax_Syntax.repr in
        let return_repr =
          resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr in
        let bind_repr =
          resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr in
        if for_free
        then FStar_List.append repr (FStar_List.append return_repr bind_repr)
        else
          (let uu____8954 =
             resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp in
           let uu____8955 =
             let uu____8958 =
               resugar_tscheme'' env "bind_wp"
                 combs.FStar_Syntax_Syntax.bind_wp in
             let uu____8959 =
               let uu____8962 =
                 resugar_tscheme'' env "stronger"
                   combs.FStar_Syntax_Syntax.stronger in
               let uu____8963 =
                 let uu____8966 =
                   resugar_tscheme'' env "if_then_else"
                     combs.FStar_Syntax_Syntax.if_then_else in
                 let uu____8967 =
                   let uu____8970 =
                     resugar_tscheme'' env "ite_wp"
                       combs.FStar_Syntax_Syntax.ite_wp in
                   let uu____8971 =
                     let uu____8974 =
                       resugar_tscheme'' env "close_wp"
                         combs.FStar_Syntax_Syntax.close_wp in
                     let uu____8975 =
                       let uu____8978 =
                         resugar_tscheme'' env "trivial"
                           combs.FStar_Syntax_Syntax.trivial in
                       uu____8978 ::
                         (FStar_List.append repr
                            (FStar_List.append return_repr bind_repr)) in
                     uu____8974 :: uu____8975 in
                   uu____8970 :: uu____8971 in
                 uu____8966 :: uu____8967 in
               uu____8962 :: uu____8963 in
             uu____8958 :: uu____8959 in
           uu____8954 :: uu____8955)
let (resugar_layered_eff_combinators :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Parser_AST.decl Prims.list)
  =
  fun env ->
    fun combs ->
      let resugar name uu____9005 =
        match uu____9005 with
        | (ts, uu____9011) -> resugar_tscheme'' env name ts in
      let uu____9012 = resugar "repr" combs.FStar_Syntax_Syntax.l_repr in
      let uu____9013 =
        let uu____9016 = resugar "return" combs.FStar_Syntax_Syntax.l_return in
        let uu____9017 =
          let uu____9020 = resugar "bind" combs.FStar_Syntax_Syntax.l_bind in
          let uu____9021 =
            let uu____9024 =
              resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp in
            let uu____9025 =
              let uu____9028 =
                resugar "if_then_else"
                  combs.FStar_Syntax_Syntax.l_if_then_else in
              [uu____9028] in
            uu____9024 :: uu____9025 in
          uu____9020 :: uu____9021 in
        uu____9016 :: uu____9017 in
      uu____9012 :: uu____9013
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
            let uu____9082 =
              FStar_Syntax_Subst.open_term action_params
                d.FStar_Syntax_Syntax.action_defn in
            match uu____9082 with
            | (bs, action_defn) ->
                let uu____9089 =
                  FStar_Syntax_Subst.open_term action_params
                    d.FStar_Syntax_Syntax.action_typ in
                (match uu____9089 with
                 | (bs1, action_typ) ->
                     let action_params1 =
                       let uu____9099 = FStar_Options.print_implicits () in
                       if uu____9099
                       then action_params
                       else filter_imp action_params in
                     let action_params2 =
                       let uu____9106 =
                         FStar_All.pipe_right action_params1
                           ((map_opt ()) (fun b -> resugar_binder' env b r)) in
                       FStar_All.pipe_right uu____9106 FStar_List.rev in
                     let action_defn1 = resugar_term' env action_defn in
                     let action_typ1 = resugar_term' env action_typ in
                     if for_free
                     then
                       let a =
                         let uu____9122 =
                           let uu____9133 =
                             FStar_Ident.lid_of_str "construct" in
                           (uu____9133,
                             [(action_defn1, FStar_Parser_AST.Nothing);
                             (action_typ1, FStar_Parser_AST.Nothing)]) in
                         FStar_Parser_AST.Construct uu____9122 in
                       let t =
                         FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un in
                       let uu____9153 =
                         let uu____9154 =
                           let uu____9163 =
                             let uu____9166 =
                               let uu____9167 =
                                 let uu____9180 =
                                   FStar_Ident.ident_of_lid
                                     d.FStar_Syntax_Syntax.action_name in
                                 (uu____9180, action_params2,
                                   FStar_Pervasives_Native.None, t) in
                               FStar_Parser_AST.TyconAbbrev uu____9167 in
                             [uu____9166] in
                           (false, false, uu____9163) in
                         FStar_Parser_AST.Tycon uu____9154 in
                       mk_decl r q uu____9153
                     else
                       (let uu____9188 =
                          let uu____9189 =
                            let uu____9198 =
                              let uu____9201 =
                                let uu____9202 =
                                  let uu____9215 =
                                    FStar_Ident.ident_of_lid
                                      d.FStar_Syntax_Syntax.action_name in
                                  (uu____9215, action_params2,
                                    FStar_Pervasives_Native.None,
                                    action_defn1) in
                                FStar_Parser_AST.TyconAbbrev uu____9202 in
                              [uu____9201] in
                            (false, false, uu____9198) in
                          FStar_Parser_AST.Tycon uu____9189 in
                        mk_decl r q uu____9188)) in
          let eff_name =
            FStar_Ident.ident_of_lid ed.FStar_Syntax_Syntax.mname in
          let uu____9223 =
            let uu____9228 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature
                FStar_Pervasives_Native.snd in
            FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
              uu____9228 in
          match uu____9223 with
          | (eff_binders, eff_typ) ->
              let eff_binders1 =
                let uu____9246 = FStar_Options.print_implicits () in
                if uu____9246 then eff_binders else filter_imp eff_binders in
              let eff_binders2 =
                let uu____9253 =
                  FStar_All.pipe_right eff_binders1
                    ((map_opt ()) (fun b -> resugar_binder' env b r)) in
                FStar_All.pipe_right uu____9253 FStar_List.rev in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9301) ->
          let uu____9310 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1 ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____9332 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____9349 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____9356 -> false
                    | uu____9371 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")) in
          (match uu____9310 with
           | (decl_typ_ses, datacon_ses) ->
               let retrieve_datacons_and_resugar uu____9407 se1 =
                 match uu____9407 with
                 | (datacon_ses1, tycons) ->
                     let uu____9433 = resugar_typ env datacon_ses1 se1 in
                     (match uu____9433 with
                      | (datacon_ses2, tyc) ->
                          (datacon_ses2, (tyc :: tycons))) in
               let uu____9448 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses in
               (match uu____9448 with
                | (leftover_datacons, tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____9483 =
                           decl'_to_decl se
                             (FStar_Parser_AST.Tycon (false, false, tycons)) in
                         FStar_Pervasives_Native.Some uu____9483
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l, uu____9490, uu____9491, uu____9492,
                               uu____9493, uu____9494)
                              ->
                              let uu____9499 =
                                let uu____9500 =
                                  let uu____9501 =
                                    let uu____9508 =
                                      FStar_Ident.ident_of_lid l in
                                    (uu____9508,
                                      FStar_Pervasives_Native.None) in
                                  FStar_Parser_AST.Exception uu____9501 in
                                decl'_to_decl se1 uu____9500 in
                              FStar_Pervasives_Native.Some uu____9499
                          | uu____9511 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____9514 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_fail uu____9519 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____9531) ->
          let uu____9536 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___9_9542 ->
                    match uu___9_9542 with
                    | FStar_Syntax_Syntax.Projector (uu____9543, uu____9544)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9545 -> true
                    | uu____9546 -> false)) in
          if uu____9536
          then FStar_Pervasives_Native.None
          else
            (let mk e =
               FStar_Syntax_Syntax.mk e se.FStar_Syntax_Syntax.sigrng in
             let dummy = mk FStar_Syntax_Syntax.Tm_unknown in
             let desugared_let = mk (FStar_Syntax_Syntax.Tm_let (lbs, dummy)) in
             let t = resugar_term' env desugared_let in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec, lets, uu____9577) ->
                 let uu____9606 =
                   let uu____9607 =
                     let uu____9608 =
                       let uu____9619 =
                         FStar_List.map FStar_Pervasives_Native.snd lets in
                       (isrec, uu____9619) in
                     FStar_Parser_AST.TopLevelLet uu____9608 in
                   decl'_to_decl se uu____9607 in
                 FStar_Pervasives_Native.Some uu____9606
             | uu____9656 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid, uu____9660, fml) ->
          let uu____9662 =
            let uu____9663 =
              let uu____9664 =
                let uu____9669 = FStar_Ident.ident_of_lid lid in
                let uu____9670 = resugar_term' env fml in
                (uu____9669, uu____9670) in
              FStar_Parser_AST.Assume uu____9664 in
            decl'_to_decl se uu____9663 in
          FStar_Pervasives_Native.Some uu____9662
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9672 =
            resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed in
          FStar_Pervasives_Native.Some uu____9672
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source in
          let dst = e.FStar_Syntax_Syntax.target in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____9681, t) ->
                let uu____9691 = resugar_term' env t in
                FStar_Pervasives_Native.Some uu____9691
            | uu____9692 -> FStar_Pervasives_Native.None in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____9700, t) ->
                let uu____9710 = resugar_term' env t in
                FStar_Pervasives_Native.Some uu____9710
            | uu____9711 -> FStar_Pervasives_Native.None in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t, FStar_Pervasives_Native.None)
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp, FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____9735 -> failwith "Should not happen hopefully" in
          let uu____9744 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 }) in
          FStar_Pervasives_Native.Some uu____9744
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags) ->
          let uu____9754 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____9754 with
           | (bs1, c1) ->
               let bs2 =
                 let uu____9766 = FStar_Options.print_implicits () in
                 if uu____9766 then bs1 else filter_imp bs1 in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng)) in
               let uu____9779 =
                 let uu____9780 =
                   let uu____9781 =
                     let uu____9790 =
                       let uu____9793 =
                         let uu____9794 =
                           let uu____9807 = FStar_Ident.ident_of_lid lid in
                           let uu____9808 = resugar_comp' env c1 in
                           (uu____9807, bs3, FStar_Pervasives_Native.None,
                             uu____9808) in
                         FStar_Parser_AST.TyconAbbrev uu____9794 in
                       [uu____9793] in
                     (false, false, uu____9790) in
                   FStar_Parser_AST.Tycon uu____9781 in
                 decl'_to_decl se uu____9780 in
               FStar_Pervasives_Native.Some uu____9779)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____9816 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p)) in
          FStar_Pervasives_Native.Some uu____9816
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
          let uu____9820 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_9826 ->
                    match uu___10_9826 with
                    | FStar_Syntax_Syntax.Projector (uu____9827, uu____9828)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____9829 -> true
                    | uu____9830 -> false)) in
          if uu____9820
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____9835 =
                 (let uu____9838 = FStar_Options.print_universes () in
                  Prims.op_Negation uu____9838) || (FStar_List.isEmpty uvs) in
               if uu____9835
               then resugar_term' env t
               else
                 (let uu____9840 = FStar_Syntax_Subst.open_univ_vars uvs t in
                  match uu____9840 with
                  | (uvs1, t1) ->
                      let universes = universe_to_string uvs1 in
                      let uu____9848 = resugar_term' env t1 in
                      label universes uu____9848) in
             let uu____9849 =
               let uu____9850 =
                 let uu____9851 =
                   let uu____9856 = FStar_Ident.ident_of_lid lid in
                   (uu____9856, t') in
                 FStar_Parser_AST.Val uu____9851 in
               decl'_to_decl se uu____9850 in
             FStar_Pervasives_Native.Some uu____9849)
      | FStar_Syntax_Syntax.Sig_splice (ids, t) ->
          let uu____9863 =
            let uu____9864 =
              let uu____9865 =
                let uu____9872 =
                  FStar_List.map (fun l -> FStar_Ident.ident_of_lid l) ids in
                let uu____9877 = resugar_term' env t in
                (uu____9872, uu____9877) in
              FStar_Parser_AST.Splice uu____9865 in
            decl'_to_decl se uu____9864 in
          FStar_Pervasives_Native.Some uu____9863
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____9880 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____9897 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m, n, p, (uu____9915, t), uu____9917) ->
          let uu____9926 =
            let uu____9927 =
              let uu____9928 =
                let uu____9937 = resugar_term' env t in (m, n, p, uu____9937) in
              FStar_Parser_AST.Polymonadic_bind uu____9928 in
            decl'_to_decl se uu____9927 in
          FStar_Pervasives_Native.Some uu____9926
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          (m, n, (uu____9940, t), uu____9942) ->
          let uu____9951 =
            let uu____9952 =
              let uu____9953 =
                let uu____9960 = resugar_term' env t in (m, n, uu____9960) in
              FStar_Parser_AST.Polymonadic_subcomp uu____9953 in
            decl'_to_decl se uu____9952 in
          FStar_Pervasives_Native.Some uu____9951
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f -> f empty_env
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t -> let uu____9981 = noenv resugar_term' in uu____9981 t
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se -> let uu____9998 = noenv resugar_sigelt' in uu____9998 se
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c -> let uu____10015 = noenv resugar_comp' in uu____10015 c
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p ->
    fun branch_bv ->
      let uu____10037 = noenv resugar_pat' in uu____10037 p branch_bv
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b ->
    fun r -> let uu____10070 = noenv resugar_binder' in uu____10070 b r
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts -> let uu____10094 = noenv resugar_tscheme' in uu____10094 ts
let (resugar_eff_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun r ->
    fun q ->
      fun ed ->
        let uu____10121 = noenv resugar_eff_decl' in uu____10121 r q ed