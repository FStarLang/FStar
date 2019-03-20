open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____51306 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____51306
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____51314 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____51314
  
let map_opt :
  'Auu____51324 'Auu____51325 .
    unit ->
      ('Auu____51324 -> 'Auu____51325 FStar_Pervasives_Native.option) ->
        'Auu____51324 Prims.list -> 'Auu____51325 Prims.list
  = fun uu____51341  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____51350 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____51350
      then
        let uu____51354 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____51354
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____51364 .
    ('Auu____51364 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51364 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_51419  ->
            match uu___429_51419 with
            | (uu____51427,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____51434,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____51435)) -> false
            | (uu____51440,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____51441)) -> false
            | uu____51447 -> true))
  
let filter_pattern_imp :
  'Auu____51460 .
    ('Auu____51460 * Prims.bool) Prims.list ->
      ('Auu____51460 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____51495  ->
         match uu____51495 with
         | (uu____51502,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
let (label : Prims.string -> FStar_Parser_AST.term -> FStar_Parser_AST.term)
  =
  fun s  ->
    fun t  ->
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
  fun n1  ->
    fun u  ->
      match u with
      | FStar_Syntax_Syntax.U_succ u1 ->
          universe_to_int (n1 + (Prims.parse_int "1")) u1
      | uu____51552 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____51565 = FStar_Options.print_universes ()  in
    if uu____51565
    then
      let uu____51569 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____51569 (FStar_String.concat ", ")
    else ""
  
let rec (resugar_universe' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Range.range -> FStar_Parser_AST.term)
  = fun env  -> fun u  -> fun r  -> resugar_universe u r

and (resugar_universe :
  FStar_Syntax_Syntax.universe -> FStar_Range.range -> FStar_Parser_AST.term)
  =
  fun u  ->
    fun r  ->
      let mk1 a r1 = FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un  in
      match u with
      | FStar_Syntax_Syntax.U_zero  ->
          mk1
            (FStar_Parser_AST.Const
               (FStar_Const.Const_int ("0", FStar_Pervasives_Native.None))) r
      | FStar_Syntax_Syntax.U_succ uu____51633 ->
          let uu____51634 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____51634 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____51645 =
                      let uu____51646 =
                        let uu____51647 =
                          let uu____51659 = FStar_Util.string_of_int n1  in
                          (uu____51659, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____51647  in
                      FStar_Parser_AST.Const uu____51646  in
                    mk1 uu____51645 r
                | uu____51672 ->
                    let e1 =
                      let uu____51674 =
                        let uu____51675 =
                          let uu____51676 =
                            let uu____51688 = FStar_Util.string_of_int n1  in
                            (uu____51688, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____51676  in
                        FStar_Parser_AST.Const uu____51675  in
                      mk1 uu____51674 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____51702 =
                      let uu____51703 =
                        let uu____51710 = FStar_Ident.id_of_text "+"  in
                        (uu____51710, [e1; e2])  in
                      FStar_Parser_AST.Op uu____51703  in
                    mk1 uu____51702 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____51718 ->
               let t =
                 let uu____51722 =
                   let uu____51723 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____51723  in
                 mk1 uu____51722 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____51732 =
                        let uu____51733 =
                          let uu____51740 = resugar_universe x r  in
                          (acc, uu____51740, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____51733  in
                      mk1 uu____51732 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____51742 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____51754 =
              let uu____51760 =
                let uu____51762 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____51762  in
              (uu____51760, r)  in
            FStar_Ident.mk_ident uu____51754  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_51800 =
      match uu___430_51800 with
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
            ("-", (FStar_Pervasives_Native.Some (Prims.parse_int "2")))
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
      | uu____52128 -> FStar_Pervasives_Native.None  in
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
    | uu____52268 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____52286 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____52286 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____52304 ->
               let op =
                 let uu____52310 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____52364) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____52310
                  in
               FStar_Pervasives_Native.Some
                 (op, FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
  
type expected_arity = Prims.int FStar_Pervasives_Native.option
let rec (resugar_term_as_op :
  FStar_Syntax_Syntax.term ->
    (Prims.string * expected_arity) FStar_Pervasives_Native.option)
  =
  fun t  ->
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
      (FStar_Parser_Const.salloc_lid, "alloc")]  in
    let fallback fv =
      let uu____52691 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____52691 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____52761 ->
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let str =
            if length1 = (Prims.parse_int "0")
            then
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
            else
              FStar_Util.substring_from
                ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
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
                (let uu____52863 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____52863
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____52899 =
      let uu____52900 = FStar_Syntax_Subst.compress t  in
      uu____52900.FStar_Syntax_Syntax.n  in
    match uu____52899 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let length1 =
          FStar_String.length
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
           in
        let s =
          if length1 = (Prims.parse_int "0")
          then
            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          else
            FStar_Util.substring_from
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
              (length1 + (Prims.parse_int "1"))
           in
        let uu____52921 = string_to_op s  in
        (match uu____52921 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____52961 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____52978 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____52995 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____53006 -> true
    | uu____53008 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____53029 ->
        let uu____53031 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____53031
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____53045 = may_shorten lid  in
      if uu____53045 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
let rec (resugar_term' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun t  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      let name a r =
        let uu____53190 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____53190  in
      let uu____53193 =
        let uu____53194 = FStar_Syntax_Subst.compress t  in
        uu____53194.FStar_Syntax_Syntax.n  in
      match uu____53193 with
      | FStar_Syntax_Syntax.Tm_delayed uu____53197 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____53222 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____53222
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____53225 =
              let uu____53228 = bv_as_unique_ident x  in [uu____53228]  in
            FStar_Ident.lid_of_ids uu____53225  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____53231 =
              let uu____53234 = bv_as_unique_ident x  in [uu____53234]  in
            FStar_Ident.lid_of_ids uu____53231  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let a = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let length1 =
            FStar_String.length
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
             in
          let s =
            if length1 = (Prims.parse_int "0")
            then a.FStar_Ident.str
            else
              FStar_Util.substring_from a.FStar_Ident.str
                (length1 + (Prims.parse_int "1"))
             in
          let is_prefix = Prims.op_Hat FStar_Ident.reserved_prefix "is_"  in
          if FStar_Util.starts_with s is_prefix
          then
            let rest =
              FStar_Util.substring_from s (FStar_String.length is_prefix)  in
            let uu____53253 =
              let uu____53254 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____53254  in
            mk1 uu____53253
          else
            if
              FStar_Util.starts_with s
                FStar_Syntax_Util.field_projector_prefix
            then
              (let rest =
                 FStar_Util.substring_from s
                   (FStar_String.length
                      FStar_Syntax_Util.field_projector_prefix)
                  in
               let r =
                 FStar_Util.split rest FStar_Syntax_Util.field_projector_sep
                  in
               match r with
               | fst1::snd1::[] ->
                   let l =
                     FStar_Ident.lid_of_path [fst1] t.FStar_Syntax_Syntax.pos
                      in
                   let r1 =
                     FStar_Ident.mk_ident (snd1, (t.FStar_Syntax_Syntax.pos))
                      in
                   mk1 (FStar_Parser_AST.Projector (l, r1))
               | uu____53278 -> failwith "wrong projector format")
            else
              (let uu____53285 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____53289 =
                      let uu____53291 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____53291  in
                    let uu____53294 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____53289 <> uu____53294)
                  in
               if uu____53285
               then
                 let uu____53299 =
                   let uu____53300 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____53300  in
                 mk1 uu____53299
               else
                 (let uu____53303 =
                    let uu____53304 =
                      let uu____53315 = maybe_shorten_fv env fv  in
                      (uu____53315, [])  in
                    FStar_Parser_AST.Construct uu____53304  in
                  mk1 uu____53303))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____53333 = FStar_Options.print_universes ()  in
          if uu____53333
          then
            let univs1 =
              FStar_List.map
                (fun x  -> resugar_universe x t.FStar_Syntax_Syntax.pos)
                universes
               in
            (match e1 with
             | { FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1,args);
                 FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                 let args1 =
                   let uu____53364 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____53364  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____53387 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____53395 = FStar_Syntax_Syntax.is_teff t  in
          if uu____53395
          then
            let uu____53398 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____53398
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____53403 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____53424 -> ("Type", true)  in
          (match uu____53403 with
           | (nm,needs_app) ->
               let typ =
                 let uu____53436 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____53436  in
               let uu____53437 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____53437
               then
                 let uu____53440 =
                   let uu____53441 =
                     let uu____53448 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____53448, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____53441  in
                 mk1 uu____53440
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____53453) ->
          let uu____53478 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____53478 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53494 = FStar_Options.print_implicits ()  in
                 if uu____53494 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____53532  ->
                         match uu____53532 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____53572 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____53572 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53582 = FStar_Options.print_implicits ()  in
                 if uu____53582 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____53593 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____53593 FStar_List.rev  in
               let rec aux body3 uu___431_53618 =
                 match uu___431_53618 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____53634 =
            let uu____53639 =
              let uu____53640 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____53640]  in
            FStar_Syntax_Subst.open_term uu____53639 phi  in
          (match uu____53634 with
           | (x1,phi1) ->
               let b =
                 let uu____53662 =
                   let uu____53665 = FStar_List.hd x1  in
                   resugar_binder' env uu____53665 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____53662  in
               let uu____53672 =
                 let uu____53673 =
                   let uu____53678 = resugar_term' env phi1  in
                   (b, uu____53678)  in
                 FStar_Parser_AST.Refine uu____53673  in
               mk1 uu____53672)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____53680;
             FStar_Syntax_Syntax.vars = uu____53681;_},(e,uu____53683)::[])
          when
          (let uu____53724 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____53724) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_53773 =
            match uu___432_53773 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____53843 -> failwith "last of an empty list"  in
          let rec last_two uu___433_53882 =
            match uu___433_53882 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____53914::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____53992::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____54063  ->
                   match uu____54063 with
                   | (e2,qual) ->
                       let uu____54080 = resugar_term' env e2  in
                       let uu____54081 = resugar_imp env qual  in
                       (uu____54080, uu____54081)) args1
               in
            let uu____54082 = resugar_term' env e1  in
            match uu____54082 with
            | {
                FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                  (hd1,previous_args);
                FStar_Parser_AST.range = r; FStar_Parser_AST.level = l;_} ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Construct
                     (hd1, (FStar_List.append previous_args args2))) r l
            | e2 ->
                FStar_List.fold_left
                  (fun acc  ->
                     fun uu____54119  ->
                       match uu____54119 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____54135 = FStar_Options.print_implicits ()  in
            if uu____54135 then args else filter_imp args  in
          let uu____54150 = resugar_term_as_op e  in
          (match uu____54150 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____54163) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____54188  ->
                        match uu____54188 with
                        | (x,uu____54200) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____54209 =
                                   let uu____54210 =
                                     let uu____54211 =
                                       let uu____54218 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____54218, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____54211  in
                                   mk1 uu____54210  in
                                 FStar_Pervasives_Native.Some uu____54209))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____54222) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____54248)::[] -> b
                 | uu____54265 -> failwith "wrong arguments to dtuple"  in
               let uu____54275 =
                 let uu____54276 = FStar_Syntax_Subst.compress body  in
                 uu____54276.FStar_Syntax_Syntax.n  in
               (match uu____54275 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54281) ->
                    let uu____54306 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____54306 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____54316 = FStar_Options.print_implicits ()
                              in
                           if uu____54316 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____54333 =
                           let uu____54334 =
                             let uu____54345 =
                               FStar_List.map
                                 (fun _54356  -> FStar_Util.Inl _54356) xs3
                                in
                             (uu____54345, body3)  in
                           FStar_Parser_AST.Sum uu____54334  in
                         mk1 uu____54333)
                | uu____54363 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____54386  ->
                              match uu____54386 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____54404) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____54413) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____54422 = FStar_List.hd args1  in
               (match uu____54422 with
                | (t1,uu____54436) ->
                    let uu____54441 =
                      let uu____54442 = FStar_Syntax_Subst.compress t1  in
                      uu____54442.FStar_Syntax_Syntax.n  in
                    (match uu____54441 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____54449 =
                           let uu____54450 =
                             let uu____54455 = resugar_term' env t1  in
                             (uu____54455, f)  in
                           FStar_Parser_AST.Project uu____54450  in
                         mk1 uu____54449
                     | uu____54456 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____54457) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____54481 =
                 match new_args with
                 | (a1,uu____54491)::(a2,uu____54493)::[] -> (a1, a2)
                 | uu____54520 -> failwith "wrong arguments to try_with"  in
               (match uu____54481 with
                | (body,handler) ->
                    let decomp term =
                      let uu____54542 =
                        let uu____54543 = FStar_Syntax_Subst.compress term
                           in
                        uu____54543.FStar_Syntax_Syntax.n  in
                      match uu____54542 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____54548) ->
                          let uu____54573 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____54573 with | (x1,e2) -> e2)
                      | uu____54580 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____54583 = decomp body  in
                      resugar_term' env uu____54583  in
                    let handler1 =
                      let uu____54585 = decomp handler  in
                      resugar_term' env uu____54585  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____54593,uu____54594,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____54626,uu____54627,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____54664 =
                            let uu____54665 =
                              let uu____54674 = resugar_body t11  in
                              (uu____54674, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____54665  in
                          mk1 uu____54664
                      | uu____54677 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____54735 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____54765) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54774) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54795) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____54893 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____54906 =
                   let uu____54907 = FStar_Syntax_Subst.compress body  in
                   uu____54907.FStar_Syntax_Syntax.n  in
                 match uu____54906 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54912) ->
                     let uu____54937 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____54937 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____54947 =
                              FStar_Options.print_implicits ()  in
                            if uu____54947 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____54963 =
                            let uu____54972 =
                              let uu____54973 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____54973.FStar_Syntax_Syntax.n  in
                            match uu____54972 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____54991 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____55021 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____55065  ->
                                                     match uu____55065 with
                                                     | (e2,uu____55073) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____55021, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____55089 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____55089)
                                  | uu____55098 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____54991 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____55130 ->
                                let uu____55131 = resugar_term' env body2  in
                                ([], uu____55131)
                             in
                          (match uu____54963 with
                           | (pats,body3) ->
                               let uu____55148 = uncurry xs3 pats body3  in
                               (match uu____55148 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      mk1
                                        (FStar_Parser_AST.QForall
                                           (xs5, pats1, body4))
                                    else
                                      mk1
                                        (FStar_Parser_AST.QExists
                                           (xs5, pats1, body4)))))
                 | uu____55200 ->
                     if op = "forall"
                     then
                       let uu____55204 =
                         let uu____55205 =
                           let uu____55218 = resugar_term' env body  in
                           ([], [[]], uu____55218)  in
                         FStar_Parser_AST.QForall uu____55205  in
                       mk1 uu____55204
                     else
                       (let uu____55231 =
                          let uu____55232 =
                            let uu____55245 = resugar_term' env body  in
                            ([], [[]], uu____55245)  in
                          FStar_Parser_AST.QExists uu____55232  in
                        mk1 uu____55231)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____55274)::[] -> resugar b
                  | uu____55291 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____55303) ->
               let uu____55311 = FStar_List.hd args1  in
               (match uu____55311 with
                | (e1,uu____55325) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____55397  ->
                         match uu____55397 with
                         | (e1,qual) ->
                             let uu____55414 = resugar_term' env e1  in
                             let uu____55415 = resugar_imp env qual  in
                             (uu____55414, uu____55415)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____55431 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____55431 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____55479 =
                               let uu____55480 =
                                 let uu____55487 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____55487)  in
                               FStar_Parser_AST.Op uu____55480  in
                             mk1 uu____55479  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____55505  ->
                                  match uu____55505 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____55524 =
                      let uu____55525 =
                        let uu____55532 =
                          let uu____55535 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____55535
                           in
                        (op1, uu____55532)  in
                      FStar_Parser_AST.Op uu____55525  in
                    mk1 uu____55524
                | uu____55548 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____55617 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____55617 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____55663 =
                   let uu____55676 =
                     let uu____55681 = resugar_pat' env pat1 branch_bv  in
                     let uu____55682 = resugar_term' env e  in
                     (uu____55681, uu____55682)  in
                   (FStar_Pervasives_Native.None, uu____55676)  in
                 [uu____55663]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____55734,t1)::(pat2,uu____55737,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____55833 =
            let uu____55834 =
              let uu____55841 = resugar_term' env e  in
              let uu____55842 = resugar_term' env t1  in
              let uu____55843 = resugar_term' env t2  in
              (uu____55841, uu____55842, uu____55843)  in
            FStar_Parser_AST.If uu____55834  in
          mk1 uu____55833
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____55909 =
            match uu____55909 with
            | (pat,wopt,b) ->
                let uu____55951 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____55951 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____56003 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____56003
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____56007 =
            let uu____56008 =
              let uu____56023 = resugar_term' env e  in
              let uu____56024 = FStar_List.map resugar_branch branches  in
              (uu____56023, uu____56024)  in
            FStar_Parser_AST.Match uu____56008  in
          mk1 uu____56007
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____56070) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____56139 =
            let uu____56140 =
              let uu____56149 = resugar_term' env e  in
              (uu____56149, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____56140  in
          mk1 uu____56139
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____56178 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____56178 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____56232 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____56232
                    in
                 let uu____56239 =
                   let uu____56244 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____56244
                    in
                 match uu____56239 with
                 | (univs1,td) ->
                     let uu____56264 =
                       let uu____56271 =
                         let uu____56272 = FStar_Syntax_Subst.compress td  in
                         uu____56272.FStar_Syntax_Syntax.n  in
                       match uu____56271 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____56281,(t1,uu____56283)::(d,uu____56285)::[])
                           -> (t1, d)
                       | uu____56342 -> failwith "wrong let binding format"
                        in
                     (match uu____56264 with
                      | (typ,def) ->
                          let uu____56373 =
                            let uu____56389 =
                              let uu____56390 =
                                FStar_Syntax_Subst.compress def  in
                              uu____56390.FStar_Syntax_Syntax.n  in
                            match uu____56389 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____56410)
                                ->
                                let uu____56435 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____56435 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____56466 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____56466
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____56489 -> ([], def, false)  in
                          (match uu____56373 with
                           | (binders,term,is_pat_app) ->
                               let uu____56544 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____56555 =
                                       let uu____56556 =
                                         let uu____56557 =
                                           let uu____56564 =
                                             bv_as_unique_ident bv  in
                                           (uu____56564,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____56557
                                          in
                                       mk_pat uu____56556  in
                                     (uu____56555, term)
                                  in
                               (match uu____56544 with
                                | (pat,term1) ->
                                    let uu____56586 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____56629  ->
                                                  match uu____56629 with
                                                  | (bv,q) ->
                                                      let uu____56644 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____56644
                                                        (fun q1  ->
                                                           let uu____56656 =
                                                             let uu____56657
                                                               =
                                                               let uu____56664
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____56664,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____56657
                                                              in
                                                           mk_pat uu____56656)))
                                           in
                                        let uu____56667 =
                                          let uu____56672 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____56672)
                                           in
                                        let uu____56675 =
                                          universe_to_string univs1  in
                                        (uu____56667, uu____56675)
                                      else
                                        (let uu____56684 =
                                           let uu____56689 =
                                             resugar_term' env term1  in
                                           (pat, uu____56689)  in
                                         let uu____56690 =
                                           universe_to_string univs1  in
                                         (uu____56684, uu____56690))
                                       in
                                    (attrs_opt, uu____56586))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____56796 =
                   match uu____56796 with
                   | (attrs,(pb,univs1)) ->
                       let uu____56856 =
                         let uu____56858 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____56858  in
                       if uu____56856
                       then (attrs, pb)
                       else
                         (attrs,
                           ((FStar_Pervasives_Native.fst pb),
                             (label univs1 (FStar_Pervasives_Native.snd pb))))
                    in
                 FStar_List.map f r  in
               let body2 = resugar_term' env body1  in
               mk1
                 (FStar_Parser_AST.Let
                    ((if is_rec
                      then FStar_Parser_AST.Rec
                      else FStar_Parser_AST.NoLetQualifier), bnds, body2)))
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____56939) ->
          let s =
            let uu____56958 =
              let uu____56960 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____56960 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____56958  in
          let uu____56965 = mk1 FStar_Parser_AST.Wild  in label s uu____56965
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____56973 =
            let uu____56974 =
              let uu____56979 = resugar_term' env tm  in (uu____56979, qi1)
               in
            FStar_Parser_AST.Quote uu____56974  in
          mk1 uu____56973
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_56991 =
            match uu___434_56991 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____56999,(uu____57000,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____57061 =
                        let uu____57062 =
                          let uu____57071 = resugar_seq t11  in
                          (uu____57071, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____57062  in
                      mk1 uu____57061
                  | uu____57074 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____57118  ->
                         match uu____57118 with
                         | (x,uu____57126) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____57131 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____57149,t1) ->
               resugar_term' env e)
      | FStar_Syntax_Syntax.Tm_unknown  -> mk1 FStar_Parser_AST.Wild

and (resugar_comp' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term)
  =
  fun env  ->
    fun c  ->
      let mk1 a =
        FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos
          FStar_Parser_AST.Un
         in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_Tot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____57189 = FStar_Options.print_universes ()  in
               if uu____57189
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_Tot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.GTotal (typ,u) ->
          let t = resugar_term' env typ  in
          (match u with
           | FStar_Pervasives_Native.None  ->
               mk1
                 (FStar_Parser_AST.Construct
                    (FStar_Parser_Const.effect_GTot_lid,
                      [(t, FStar_Parser_AST.Nothing)]))
           | FStar_Pervasives_Native.Some u1 ->
               let uu____57253 = FStar_Options.print_universes ()  in
               if uu____57253
               then
                 let u2 = resugar_universe u1 c.FStar_Syntax_Syntax.pos  in
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(u2, FStar_Parser_AST.UnivApp);
                        (t, FStar_Parser_AST.Nothing)]))
               else
                 mk1
                   (FStar_Parser_AST.Construct
                      (FStar_Parser_Const.effect_GTot_lid,
                        [(t, FStar_Parser_AST.Nothing)])))
      | FStar_Syntax_Syntax.Comp c1 ->
          let result =
            let uu____57297 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____57297, FStar_Parser_AST.Nothing)  in
          let uu____57298 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____57298
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____57321 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____57321
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____57406 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____57406, (FStar_Pervasives_Native.snd post))  in
                    let uu____57417 =
                      let uu____57426 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____57426 then [] else [pre]  in
                    let uu____57461 =
                      let uu____57470 =
                        let uu____57479 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____57479 then [] else [pats]  in
                      FStar_List.append [post1] uu____57470  in
                    FStar_List.append uu____57417 uu____57461
                | uu____57538 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____57572  ->
                   match uu____57572 with
                   | (e,uu____57584) ->
                       let uu____57589 = resugar_term' env e  in
                       (uu____57589, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_57614 =
              match uu___435_57614 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____57647 = resugar_term' env e  in
                         (uu____57647, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____57652 -> aux l tl1)
               in
            let decrease = aux [] c1.FStar_Syntax_Syntax.flags  in
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name),
                   (FStar_List.append (result :: decrease) args1)))
          else
            mk1
              (FStar_Parser_AST.Construct
                 ((c1.FStar_Syntax_Syntax.effect_name), [result]))

and (resugar_binder' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Range.range ->
        FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun b  ->
      fun r  ->
        let uu____57699 = b  in
        match uu____57699 with
        | (x,aq) ->
            let uu____57708 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____57708
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____57722 =
                       let uu____57723 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____57723  in
                     FStar_Parser_AST.mk_binder uu____57722 r
                       FStar_Parser_AST.Type_level imp
                 | uu____57724 ->
                     let uu____57725 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____57725
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____57730 =
                          let uu____57731 =
                            let uu____57736 = bv_as_unique_ident x  in
                            (uu____57736, e)  in
                          FStar_Parser_AST.Annotated uu____57731  in
                        FStar_Parser_AST.mk_binder uu____57730 r
                          FStar_Parser_AST.Type_level imp))

and (resugar_bv_as_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun v1  ->
      fun aqual  ->
        fun body_bv  ->
          fun typ_opt  ->
            let mk1 a =
              let uu____57756 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____57756  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____57760 =
                if used
                then
                  let uu____57762 =
                    let uu____57769 = bv_as_unique_ident v1  in
                    (uu____57769, aqual)  in
                  FStar_Parser_AST.PatVar uu____57762
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____57760  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____57776;
                  FStar_Syntax_Syntax.vars = uu____57777;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____57787 = FStar_Options.print_bound_var_types ()  in
                if uu____57787
                then
                  let uu____57790 =
                    let uu____57791 =
                      let uu____57802 =
                        let uu____57809 = resugar_term' env typ  in
                        (uu____57809, FStar_Pervasives_Native.None)  in
                      (pat, uu____57802)  in
                    FStar_Parser_AST.PatAscribed uu____57791  in
                  mk1 uu____57790
                else pat

and (resugar_bv_as_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.bv FStar_Util.set ->
          FStar_Parser_AST.pattern FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun x  ->
      fun qual  ->
        fun body_bv  ->
          let uu____57830 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____57830
            (fun aqual  ->
               let uu____57842 =
                 let uu____57847 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _57858  -> FStar_Pervasives_Native.Some _57858)
                   uu____57847
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____57842)

and (resugar_pat' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun env  ->
    fun p  ->
      fun branch_bv  ->
        let mk1 a = FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p  in
        let to_arg_qual bopt =
          FStar_Util.bind_opt bopt
            (fun b  ->
               if b
               then FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit
               else FStar_Pervasives_Native.None)
           in
        let may_drop_implicits args =
          (let uu____57920 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____57920) &&
            (let uu____57923 =
               FStar_List.existsML
                 (fun uu____57936  ->
                    match uu____57936 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____57958)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____57963 -> false
                          | uu____57965 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____57923)
           in
        let resugar_plain_pat_cons' fv args =
          mk1
            (FStar_Parser_AST.PatApp
               ((mk1
                   (FStar_Parser_AST.PatName
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                 args))
           in
        let rec resugar_plain_pat_cons fv args =
          let args1 =
            let uu____58033 = may_drop_implicits args  in
            if uu____58033 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____58058  ->
                 match uu____58058 with
                 | (p1,b) -> aux p1 (FStar_Pervasives_Native.Some b)) args1
             in
          resugar_plain_pat_cons' fv args2
        
        and aux p1 imp_opt =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              mk1 (FStar_Parser_AST.PatConst c)
          | FStar_Syntax_Syntax.Pat_cons (fv,[]) ->
              mk1
                (FStar_Parser_AST.PatName
                   ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.nil_lid)
                && (may_drop_implicits args)
              ->
              ((let uu____58113 =
                  let uu____58115 =
                    let uu____58117 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____58117  in
                  Prims.op_Negation uu____58115  in
                if uu____58113
                then
                  FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                    (FStar_Errors.Warning_NilGivenExplicitArgs,
                      "Prims.Nil given explicit arguments")
                else ());
               mk1 (FStar_Parser_AST.PatList []))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (FStar_Ident.lid_equals
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 FStar_Parser_Const.cons_lid)
                && (may_drop_implicits args)
              ->
              let uu____58161 = filter_pattern_imp args  in
              (match uu____58161 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____58211 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____58211 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____58230 =
                       let uu____58236 =
                         let uu____58238 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____58238
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____58236)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____58230);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____58291  ->
                        match uu____58291 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____58308 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____58308)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____58316;
                 FStar_Syntax_Syntax.fv_delta = uu____58317;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____58346 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____58346 FStar_List.rev  in
              let args1 =
                let uu____58362 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____58382  ->
                          match uu____58382 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____58362 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____58460 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____58460
                | (hd1::tl1,hd2::tl2) ->
                    let uu____58483 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____58483
                 in
              let args2 =
                let uu____58501 = map21 fields1 args1  in
                FStar_All.pipe_right uu____58501 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____58545 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____58545 with
               | FStar_Pervasives_Native.Some (op,uu____58557) ->
                   let uu____58574 =
                     let uu____58575 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____58575  in
                   mk1 uu____58574
               | FStar_Pervasives_Native.None  ->
                   let uu____58585 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____58585 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____58590 ->
              let uu____58591 =
                let uu____58592 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____58592  in
              mk1 uu____58591
          | FStar_Syntax_Syntax.Pat_dot_term (bv,term) ->
              resugar_bv_as_pat' env bv
                (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                branch_bv (FStar_Pervasives_Native.Some term)
         in aux p FStar_Pervasives_Native.None

and (resugar_arg_qual :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b) ->
          if b
          then FStar_Pervasives_Native.None
          else
            FStar_Pervasives_Native.Some
              (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Pervasives_Native.Some
            (FStar_Pervasives_Native.Some FStar_Parser_AST.Equality)
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____58632 =
            let uu____58635 =
              let uu____58636 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____58636  in
            FStar_Pervasives_Native.Some uu____58635  in
          FStar_Pervasives_Native.Some uu____58632

and (resugar_imp :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Parser_AST.imp)
  =
  fun env  ->
    fun q  ->
      match q with
      | FStar_Pervasives_Native.None  -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> FStar_Parser_AST.Hash
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> FStar_Parser_AST.Nothing
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____58648 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____58648

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_58656  ->
    match uu___436_58656 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Assumption
    | FStar_Syntax_Syntax.New  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.New
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
        FStar_Pervasives_Native.Some
          FStar_Parser_AST.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Irreducible  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Irreducible
    | FStar_Syntax_Syntax.Abstract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Abstract
    | FStar_Syntax_Syntax.Inline_for_extraction  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.NoExtract
    | FStar_Syntax_Syntax.Noeq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Noeq
    | FStar_Syntax_Syntax.Unopteq  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Unopteq
    | FStar_Syntax_Syntax.TotalEffect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.TotalEffect
    | FStar_Syntax_Syntax.Logic  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Reifiable  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reifiable
    | FStar_Syntax_Syntax.Reflectable uu____58663 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____58664 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____58665 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____58670 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____58679 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____58688 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_58694  ->
    match uu___437_58694 with
    | FStar_Syntax_Syntax.SetOptions s -> FStar_Parser_AST.SetOptions s
    | FStar_Syntax_Syntax.ResetOptions s -> FStar_Parser_AST.ResetOptions s
    | FStar_Syntax_Syntax.PushOptions s -> FStar_Parser_AST.PushOptions s
    | FStar_Syntax_Syntax.PopOptions  -> FStar_Parser_AST.PopOptions
    | FStar_Syntax_Syntax.LightOff  -> FStar_Parser_AST.LightOff
  
let (resugar_typ :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon))
  =
  fun env  ->
    fun datacon_ses  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (tylid,uvs,bs,t,uu____58737,datacons) ->
            let uu____58747 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____58775,uu____58776,uu____58777,inductive_lid,uu____58779,uu____58780)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____58787 -> failwith "unexpected"))
               in
            (match uu____58747 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____58808 = FStar_Options.print_implicits ()  in
                   if uu____58808 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____58825 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_58832  ->
                             match uu___438_58832 with
                             | FStar_Syntax_Syntax.RecordType uu____58834 ->
                                 true
                             | uu____58844 -> false))
                      in
                   if uu____58825
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____58898,univs1,term,uu____58901,num,uu____58903)
                           ->
                           let uu____58910 =
                             let uu____58911 =
                               FStar_Syntax_Subst.compress term  in
                             uu____58911.FStar_Syntax_Syntax.n  in
                           (match uu____58910 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____58925)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____58994  ->
                                          match uu____58994 with
                                          | (b,qual) ->
                                              let uu____59015 =
                                                bv_as_unique_ident b  in
                                              let uu____59016 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____59015, uu____59016,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____59027 -> failwith "unexpected")
                       | uu____59039 -> failwith "unexpected"  in
                     let fields =
                       FStar_List.fold_left resugar_datacon_as_fields []
                         current_datacons
                        in
                     FStar_Parser_AST.TyconRecord
                       ((tylid.FStar_Ident.ident), bs2,
                         FStar_Pervasives_Native.None, fields)
                   else
                     (let resugar_datacon constructors se1 =
                        match se1.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_datacon
                            (l,univs1,term,uu____59170,num,uu____59172) ->
                            let c =
                              let uu____59193 =
                                let uu____59196 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____59196  in
                              ((l.FStar_Ident.ident), uu____59193,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____59216 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____59296 ->
            failwith
              "Impossible : only Sig_inductive_typ can be resugared as types"
  
let (mk_decl :
  FStar_Range.range ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun r  ->
    fun q  ->
      fun d'  ->
        let uu____59322 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____59322;
          FStar_Parser_AST.attrs = []
        }
  
let (decl'_to_decl :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl' -> FStar_Parser_AST.decl)
  =
  fun se  ->
    fun d'  ->
      mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals
        d'
  
let (resugar_tscheme'' :
  FStar_Syntax_DsEnv.env ->
    Prims.string -> FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun name  ->
      fun ts  ->
        let uu____59352 = ts  in
        match uu____59352 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____59365 =
              let uu____59366 =
                let uu____59383 =
                  let uu____59392 =
                    let uu____59399 =
                      let uu____59400 =
                        let uu____59413 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____59413)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____59400  in
                    (uu____59399, FStar_Pervasives_Native.None)  in
                  [uu____59392]  in
                (false, false, uu____59383)  in
              FStar_Parser_AST.Tycon uu____59366  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____59365
  
let (resugar_tscheme' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun env  -> fun ts  -> resugar_tscheme'' env "tscheme" ts 
let (resugar_eff_decl' :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun env  ->
    fun for_free  ->
      fun r  ->
        fun q  ->
          fun ed  ->
            let resugar_action d for_free1 =
              let action_params =
                FStar_Syntax_Subst.open_binders
                  d.FStar_Syntax_Syntax.action_params
                 in
              let uu____59502 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____59502 with
              | (bs,action_defn) ->
                  let uu____59509 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____59509 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____59519 = FStar_Options.print_implicits ()
                            in
                         if uu____59519
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____59529 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____59529 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____59546 =
                             let uu____59557 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____59557,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____59546  in
                         let t =
                           FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un
                            in
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None, t)),
                                   FStar_Pervasives_Native.None)]))
                       else
                         mk_decl r q
                           (FStar_Parser_AST.Tycon
                              (false, false,
                                [((FStar_Parser_AST.TyconAbbrev
                                     (((d.FStar_Syntax_Syntax.action_name).FStar_Ident.ident),
                                       action_params2,
                                       FStar_Pervasives_Native.None,
                                       action_defn1)),
                                   FStar_Pervasives_Native.None)])))
               in
            let eff_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident
               in
            let uu____59641 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____59641 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____59651 = FStar_Options.print_implicits ()  in
                  if uu____59651 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____59661 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____59661 FStar_List.rev  in
                let eff_typ1 = resugar_term' env eff_typ  in
                let ret_wp =
                  resugar_tscheme'' env "ret_wp"
                    ed.FStar_Syntax_Syntax.ret_wp
                   in
                let bind_wp =
                  resugar_tscheme'' env "bind_wp"
                    ed.FStar_Syntax_Syntax.bind_wp
                   in
                let if_then_else1 =
                  resugar_tscheme'' env "if_then_else"
                    ed.FStar_Syntax_Syntax.if_then_else
                   in
                let ite_wp =
                  resugar_tscheme'' env "ite_wp"
                    ed.FStar_Syntax_Syntax.ite_wp
                   in
                let stronger =
                  resugar_tscheme'' env "stronger"
                    ed.FStar_Syntax_Syntax.stronger
                   in
                let close_wp =
                  resugar_tscheme'' env "close_wp"
                    ed.FStar_Syntax_Syntax.close_wp
                   in
                let assert_p =
                  resugar_tscheme'' env "assert_p"
                    ed.FStar_Syntax_Syntax.assert_p
                   in
                let assume_p =
                  resugar_tscheme'' env "assume_p"
                    ed.FStar_Syntax_Syntax.assume_p
                   in
                let null_wp =
                  resugar_tscheme'' env "null_wp"
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let trivial =
                  resugar_tscheme'' env "trivial"
                    ed.FStar_Syntax_Syntax.trivial
                   in
                let repr =
                  resugar_tscheme'' env "repr"
                    ([], (ed.FStar_Syntax_Syntax.repr))
                   in
                let return_repr =
                  resugar_tscheme'' env "return_repr"
                    ed.FStar_Syntax_Syntax.return_repr
                   in
                let bind_repr =
                  resugar_tscheme'' env "bind_repr"
                    ed.FStar_Syntax_Syntax.bind_repr
                   in
                let mandatory_members_decls =
                  if for_free
                  then [repr; return_repr; bind_repr]
                  else
                    [repr;
                    return_repr;
                    bind_repr;
                    ret_wp;
                    bind_wp;
                    if_then_else1;
                    ite_wp;
                    stronger;
                    close_wp;
                    assert_p;
                    assume_p;
                    null_wp;
                    trivial]
                   in
                let actions =
                  FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions
                    (FStar_List.map (fun a  -> resugar_action a false))
                   in
                let decls = FStar_List.append mandatory_members_decls actions
                   in
                mk_decl r q
                  (FStar_Parser_AST.NewEffect
                     (FStar_Parser_AST.DefineEffect
                        (eff_name, eff_binders2, eff_typ1, decls)))
  
let (resugar_sigelt' :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59746) ->
          let uu____59755 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____59778 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____59796 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____59804 -> false
                    | uu____59821 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____59755 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____59859 se1 =
                 match uu____59859 with
                 | (datacon_ses1,tycons) ->
                     let uu____59885 = resugar_typ env datacon_ses1 se1  in
                     (match uu____59885 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____59900 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____59900 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____59935 =
                           let uu____59936 =
                             let uu____59937 =
                               let uu____59954 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____59954)  in
                             FStar_Parser_AST.Tycon uu____59937  in
                           decl'_to_decl se uu____59936  in
                         FStar_Pervasives_Native.Some uu____59935
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____59989,uu____59990,uu____59991,uu____59992,uu____59993)
                              ->
                              let uu____60000 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____60000
                          | uu____60003 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____60007 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60014) ->
          let uu____60019 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_60027  ->
                    match uu___439_60027 with
                    | FStar_Syntax_Syntax.Projector (uu____60029,uu____60030)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60032 -> true
                    | uu____60034 -> false))
             in
          if uu____60019
          then FStar_Pervasives_Native.None
          else
            (let mk1 e =
               FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
                 se.FStar_Syntax_Syntax.sigrng
                in
             let dummy = mk1 FStar_Syntax_Syntax.Tm_unknown  in
             let desugared_let =
               mk1 (FStar_Syntax_Syntax.Tm_let (lbs, dummy))  in
             let t = resugar_term' env desugared_let  in
             match t.FStar_Parser_AST.tm with
             | FStar_Parser_AST.Let (isrec,lets,uu____60069) ->
                 let uu____60098 =
                   let uu____60099 =
                     let uu____60100 =
                       let uu____60111 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____60111)  in
                     FStar_Parser_AST.TopLevelLet uu____60100  in
                   decl'_to_decl se uu____60099  in
                 FStar_Pervasives_Native.Some uu____60098
             | uu____60148 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____60153,fml) ->
          let uu____60155 =
            let uu____60156 =
              let uu____60157 =
                let uu____60162 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____60162)  in
              FStar_Parser_AST.Assume uu____60157  in
            decl'_to_decl se uu____60156  in
          FStar_Pervasives_Native.Some uu____60155
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____60164 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60164
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____60167 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60167
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____60177,t) ->
                let uu____60187 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60187
            | uu____60188 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____60196,t) ->
                let uu____60206 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60206
            | uu____60207 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____60231 -> failwith "Should not happen hopefully"  in
          let uu____60241 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____60241
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____60251 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____60251 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____60263 = FStar_Options.print_implicits ()  in
                 if uu____60263 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____60279 =
                 let uu____60280 =
                   let uu____60281 =
                     let uu____60298 =
                       let uu____60307 =
                         let uu____60314 =
                           let uu____60315 =
                             let uu____60328 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____60328)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____60315  in
                         (uu____60314, FStar_Pervasives_Native.None)  in
                       [uu____60307]  in
                     (false, false, uu____60298)  in
                   FStar_Parser_AST.Tycon uu____60281  in
                 decl'_to_decl se uu____60280  in
               FStar_Pervasives_Native.Some uu____60279)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____60360 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____60360
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____60364 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_60372  ->
                    match uu___440_60372 with
                    | FStar_Syntax_Syntax.Projector (uu____60374,uu____60375)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60377 -> true
                    | uu____60379 -> false))
             in
          if uu____60364
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____60387 =
                 (let uu____60391 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____60391) || (FStar_List.isEmpty uvs)
                  in
               if uu____60387
               then resugar_term' env t
               else
                 (let uu____60396 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____60396 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____60405 = resugar_term' env t1  in
                      label universes uu____60405)
                in
             let uu____60406 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____60406)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____60413 =
            let uu____60414 =
              let uu____60415 =
                let uu____60422 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____60427 = resugar_term' env t  in
                (uu____60422, uu____60427)  in
              FStar_Parser_AST.Splice uu____60415  in
            decl'_to_decl se uu____60414  in
          FStar_Pervasives_Native.Some uu____60413
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____60430 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____60447 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____60463 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____60487 = noenv resugar_term'  in uu____60487 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____60505 = noenv resugar_sigelt'  in uu____60505 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____60523 = noenv resugar_comp'  in uu____60523 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____60546 = noenv resugar_pat'  in uu____60546 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____60580 = noenv resugar_binder'  in uu____60580 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____60605 = noenv resugar_tscheme'  in uu____60605 ts 
let (resugar_eff_decl :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Parser_AST.decl)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____60640 = noenv resugar_eff_decl'  in
          uu____60640 for_free r q ed
  