open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____51325 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____51325
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____51333 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____51333
  
let map_opt :
  'Auu____51343 'Auu____51344 .
    unit ->
      ('Auu____51343 -> 'Auu____51344 FStar_Pervasives_Native.option) ->
        'Auu____51343 Prims.list -> 'Auu____51344 Prims.list
  = fun uu____51360  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____51369 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____51369
      then
        let uu____51373 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____51373
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____51383 .
    ('Auu____51383 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51383 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_51438  ->
            match uu___429_51438 with
            | (uu____51446,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____51453,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____51454)) -> false
            | (uu____51459,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____51460)) -> false
            | uu____51466 -> true))
  
let filter_pattern_imp :
  'Auu____51479 .
    ('Auu____51479 * Prims.bool) Prims.list ->
      ('Auu____51479 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____51514  ->
         match uu____51514 with
         | (uu____51521,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____51571 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____51584 = FStar_Options.print_universes ()  in
    if uu____51584
    then
      let uu____51588 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____51588 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____51652 ->
          let uu____51653 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____51653 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____51664 =
                      let uu____51665 =
                        let uu____51666 =
                          let uu____51678 = FStar_Util.string_of_int n1  in
                          (uu____51678, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____51666  in
                      FStar_Parser_AST.Const uu____51665  in
                    mk1 uu____51664 r
                | uu____51691 ->
                    let e1 =
                      let uu____51693 =
                        let uu____51694 =
                          let uu____51695 =
                            let uu____51707 = FStar_Util.string_of_int n1  in
                            (uu____51707, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____51695  in
                        FStar_Parser_AST.Const uu____51694  in
                      mk1 uu____51693 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____51721 =
                      let uu____51722 =
                        let uu____51729 = FStar_Ident.id_of_text "+"  in
                        (uu____51729, [e1; e2])  in
                      FStar_Parser_AST.Op uu____51722  in
                    mk1 uu____51721 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____51737 ->
               let t =
                 let uu____51741 =
                   let uu____51742 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____51742  in
                 mk1 uu____51741 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____51751 =
                        let uu____51752 =
                          let uu____51759 = resugar_universe x r  in
                          (acc, uu____51759, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____51752  in
                      mk1 uu____51751 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____51761 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____51773 =
              let uu____51779 =
                let uu____51781 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____51781  in
              (uu____51779, r)  in
            FStar_Ident.mk_ident uu____51773  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_51819 =
      match uu___430_51819 with
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
      | uu____52147 -> FStar_Pervasives_Native.None  in
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
    | uu____52287 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____52305 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____52305 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____52323 ->
               let op =
                 let uu____52329 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____52383) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____52329
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
      let uu____52710 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____52710 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____52780 ->
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
                (let uu____52882 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____52882
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____52918 =
      let uu____52919 = FStar_Syntax_Subst.compress t  in
      uu____52919.FStar_Syntax_Syntax.n  in
    match uu____52918 with
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
        let uu____52940 = string_to_op s  in
        (match uu____52940 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____52980 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____52997 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____53014 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____53025 -> true
    | uu____53027 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____53048 ->
        let uu____53050 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____53050
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____53064 = may_shorten lid  in
      if uu____53064 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____53209 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____53209  in
      let uu____53212 =
        let uu____53213 = FStar_Syntax_Subst.compress t  in
        uu____53213.FStar_Syntax_Syntax.n  in
      match uu____53212 with
      | FStar_Syntax_Syntax.Tm_delayed uu____53216 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____53241 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____53241
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____53244 =
              let uu____53247 = bv_as_unique_ident x  in [uu____53247]  in
            FStar_Ident.lid_of_ids uu____53244  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____53250 =
              let uu____53253 = bv_as_unique_ident x  in [uu____53253]  in
            FStar_Ident.lid_of_ids uu____53250  in
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
            let uu____53272 =
              let uu____53273 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____53273  in
            mk1 uu____53272
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
               | uu____53297 -> failwith "wrong projector format")
            else
              (let uu____53304 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____53308 =
                      let uu____53310 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____53310  in
                    let uu____53313 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____53308 <> uu____53313)
                  in
               if uu____53304
               then
                 let uu____53318 =
                   let uu____53319 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____53319  in
                 mk1 uu____53318
               else
                 (let uu____53322 =
                    let uu____53323 =
                      let uu____53334 = maybe_shorten_fv env fv  in
                      (uu____53334, [])  in
                    FStar_Parser_AST.Construct uu____53323  in
                  mk1 uu____53322))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____53352 = FStar_Options.print_universes ()  in
          if uu____53352
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
                   let uu____53383 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____53383  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____53406 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____53414 = FStar_Syntax_Syntax.is_teff t  in
          if uu____53414
          then
            let uu____53417 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____53417
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____53422 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____53443 -> ("Type", true)  in
          (match uu____53422 with
           | (nm,needs_app) ->
               let typ =
                 let uu____53455 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____53455  in
               let uu____53456 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____53456
               then
                 let uu____53459 =
                   let uu____53460 =
                     let uu____53467 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____53467, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____53460  in
                 mk1 uu____53459
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____53472) ->
          let uu____53497 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____53497 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53513 = FStar_Options.print_implicits ()  in
                 if uu____53513 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____53551  ->
                         match uu____53551 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____53591 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____53591 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53601 = FStar_Options.print_implicits ()  in
                 if uu____53601 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____53612 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____53612 FStar_List.rev  in
               let rec aux body3 uu___431_53637 =
                 match uu___431_53637 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____53653 =
            let uu____53658 =
              let uu____53659 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____53659]  in
            FStar_Syntax_Subst.open_term uu____53658 phi  in
          (match uu____53653 with
           | (x1,phi1) ->
               let b =
                 let uu____53681 =
                   let uu____53684 = FStar_List.hd x1  in
                   resugar_binder' env uu____53684 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____53681  in
               let uu____53691 =
                 let uu____53692 =
                   let uu____53697 = resugar_term' env phi1  in
                   (b, uu____53697)  in
                 FStar_Parser_AST.Refine uu____53692  in
               mk1 uu____53691)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____53699;
             FStar_Syntax_Syntax.vars = uu____53700;_},(e,uu____53702)::[])
          when
          (let uu____53743 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____53743) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_53792 =
            match uu___432_53792 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____53862 -> failwith "last of an empty list"  in
          let rec last_two uu___433_53901 =
            match uu___433_53901 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____53933::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____54011::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____54082  ->
                   match uu____54082 with
                   | (e2,qual) ->
                       let uu____54099 = resugar_term' env e2  in
                       let uu____54100 = resugar_imp env qual  in
                       (uu____54099, uu____54100)) args1
               in
            let uu____54101 = resugar_term' env e1  in
            match uu____54101 with
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
                     fun uu____54138  ->
                       match uu____54138 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____54154 = FStar_Options.print_implicits ()  in
            if uu____54154 then args else filter_imp args  in
          let uu____54169 = resugar_term_as_op e  in
          (match uu____54169 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____54182) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____54207  ->
                        match uu____54207 with
                        | (x,uu____54219) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____54228 =
                                   let uu____54229 =
                                     let uu____54230 =
                                       let uu____54237 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____54237, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____54230  in
                                   mk1 uu____54229  in
                                 FStar_Pervasives_Native.Some uu____54228))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____54241) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____54267)::[] -> b
                 | uu____54284 -> failwith "wrong arguments to dtuple"  in
               let uu____54294 =
                 let uu____54295 = FStar_Syntax_Subst.compress body  in
                 uu____54295.FStar_Syntax_Syntax.n  in
               (match uu____54294 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54300) ->
                    let uu____54325 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____54325 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____54335 = FStar_Options.print_implicits ()
                              in
                           if uu____54335 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____54352 =
                           let uu____54353 =
                             let uu____54364 =
                               FStar_List.map
                                 (fun _54375  -> FStar_Util.Inl _54375) xs3
                                in
                             (uu____54364, body3)  in
                           FStar_Parser_AST.Sum uu____54353  in
                         mk1 uu____54352)
                | uu____54382 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____54405  ->
                              match uu____54405 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____54423) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____54432) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____54441 = FStar_List.hd args1  in
               (match uu____54441 with
                | (t1,uu____54455) ->
                    let uu____54460 =
                      let uu____54461 = FStar_Syntax_Subst.compress t1  in
                      uu____54461.FStar_Syntax_Syntax.n  in
                    (match uu____54460 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____54468 =
                           let uu____54469 =
                             let uu____54474 = resugar_term' env t1  in
                             (uu____54474, f)  in
                           FStar_Parser_AST.Project uu____54469  in
                         mk1 uu____54468
                     | uu____54475 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____54476) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____54500 =
                 match new_args with
                 | (a1,uu____54510)::(a2,uu____54512)::[] -> (a1, a2)
                 | uu____54539 -> failwith "wrong arguments to try_with"  in
               (match uu____54500 with
                | (body,handler) ->
                    let decomp term =
                      let uu____54561 =
                        let uu____54562 = FStar_Syntax_Subst.compress term
                           in
                        uu____54562.FStar_Syntax_Syntax.n  in
                      match uu____54561 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____54567) ->
                          let uu____54592 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____54592 with | (x1,e2) -> e2)
                      | uu____54599 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____54602 = decomp body  in
                      resugar_term' env uu____54602  in
                    let handler1 =
                      let uu____54604 = decomp handler  in
                      resugar_term' env uu____54604  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____54612,uu____54613,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____54645,uu____54646,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____54683 =
                            let uu____54684 =
                              let uu____54693 = resugar_body t11  in
                              (uu____54693, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____54684  in
                          mk1 uu____54683
                      | uu____54696 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____54754 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____54784) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54793) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54814) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____54912 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____54925 =
                   let uu____54926 = FStar_Syntax_Subst.compress body  in
                   uu____54926.FStar_Syntax_Syntax.n  in
                 match uu____54925 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54931) ->
                     let uu____54956 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____54956 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____54966 =
                              FStar_Options.print_implicits ()  in
                            if uu____54966 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____54982 =
                            let uu____54991 =
                              let uu____54992 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____54992.FStar_Syntax_Syntax.n  in
                            match uu____54991 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____55010 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____55040 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____55084  ->
                                                     match uu____55084 with
                                                     | (e2,uu____55092) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____55040, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____55108 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____55108)
                                  | uu____55117 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____55010 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____55149 ->
                                let uu____55150 = resugar_term' env body2  in
                                ([], uu____55150)
                             in
                          (match uu____54982 with
                           | (pats,body3) ->
                               let uu____55167 = uncurry xs3 pats body3  in
                               (match uu____55167 with
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
                 | uu____55219 ->
                     if op = "forall"
                     then
                       let uu____55223 =
                         let uu____55224 =
                           let uu____55237 = resugar_term' env body  in
                           ([], [[]], uu____55237)  in
                         FStar_Parser_AST.QForall uu____55224  in
                       mk1 uu____55223
                     else
                       (let uu____55250 =
                          let uu____55251 =
                            let uu____55264 = resugar_term' env body  in
                            ([], [[]], uu____55264)  in
                          FStar_Parser_AST.QExists uu____55251  in
                        mk1 uu____55250)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____55293)::[] -> resugar b
                  | uu____55310 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____55322) ->
               let uu____55330 = FStar_List.hd args1  in
               (match uu____55330 with
                | (e1,uu____55344) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____55416  ->
                         match uu____55416 with
                         | (e1,qual) ->
                             let uu____55433 = resugar_term' env e1  in
                             let uu____55434 = resugar_imp env qual  in
                             (uu____55433, uu____55434)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____55450 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____55450 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____55498 =
                               let uu____55499 =
                                 let uu____55506 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____55506)  in
                               FStar_Parser_AST.Op uu____55499  in
                             mk1 uu____55498  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____55524  ->
                                  match uu____55524 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____55543 =
                      let uu____55544 =
                        let uu____55551 =
                          let uu____55554 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____55554
                           in
                        (op1, uu____55551)  in
                      FStar_Parser_AST.Op uu____55544  in
                    mk1 uu____55543
                | uu____55567 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____55636 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____55636 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____55682 =
                   let uu____55695 =
                     let uu____55700 = resugar_pat' env pat1 branch_bv  in
                     let uu____55701 = resugar_term' env e  in
                     (uu____55700, uu____55701)  in
                   (FStar_Pervasives_Native.None, uu____55695)  in
                 [uu____55682]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____55753,t1)::(pat2,uu____55756,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____55852 =
            let uu____55853 =
              let uu____55860 = resugar_term' env e  in
              let uu____55861 = resugar_term' env t1  in
              let uu____55862 = resugar_term' env t2  in
              (uu____55860, uu____55861, uu____55862)  in
            FStar_Parser_AST.If uu____55853  in
          mk1 uu____55852
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____55928 =
            match uu____55928 with
            | (pat,wopt,b) ->
                let uu____55970 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____55970 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____56022 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____56022
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____56026 =
            let uu____56027 =
              let uu____56042 = resugar_term' env e  in
              let uu____56043 = FStar_List.map resugar_branch branches  in
              (uu____56042, uu____56043)  in
            FStar_Parser_AST.Match uu____56027  in
          mk1 uu____56026
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____56089) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____56158 =
            let uu____56159 =
              let uu____56168 = resugar_term' env e  in
              (uu____56168, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____56159  in
          mk1 uu____56158
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____56197 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____56197 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____56251 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____56251
                    in
                 let uu____56258 =
                   let uu____56263 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____56263
                    in
                 match uu____56258 with
                 | (univs1,td) ->
                     let uu____56283 =
                       let uu____56290 =
                         let uu____56291 = FStar_Syntax_Subst.compress td  in
                         uu____56291.FStar_Syntax_Syntax.n  in
                       match uu____56290 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____56300,(t1,uu____56302)::(d,uu____56304)::[])
                           -> (t1, d)
                       | uu____56361 -> failwith "wrong let binding format"
                        in
                     (match uu____56283 with
                      | (typ,def) ->
                          let uu____56392 =
                            let uu____56408 =
                              let uu____56409 =
                                FStar_Syntax_Subst.compress def  in
                              uu____56409.FStar_Syntax_Syntax.n  in
                            match uu____56408 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____56429)
                                ->
                                let uu____56454 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____56454 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____56485 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____56485
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____56508 -> ([], def, false)  in
                          (match uu____56392 with
                           | (binders,term,is_pat_app) ->
                               let uu____56563 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____56574 =
                                       let uu____56575 =
                                         let uu____56576 =
                                           let uu____56583 =
                                             bv_as_unique_ident bv  in
                                           (uu____56583,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____56576
                                          in
                                       mk_pat uu____56575  in
                                     (uu____56574, term)
                                  in
                               (match uu____56563 with
                                | (pat,term1) ->
                                    let uu____56605 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____56648  ->
                                                  match uu____56648 with
                                                  | (bv,q) ->
                                                      let uu____56663 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____56663
                                                        (fun q1  ->
                                                           let uu____56675 =
                                                             let uu____56676
                                                               =
                                                               let uu____56683
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____56683,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____56676
                                                              in
                                                           mk_pat uu____56675)))
                                           in
                                        let uu____56686 =
                                          let uu____56691 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____56691)
                                           in
                                        let uu____56694 =
                                          universe_to_string univs1  in
                                        (uu____56686, uu____56694)
                                      else
                                        (let uu____56703 =
                                           let uu____56708 =
                                             resugar_term' env term1  in
                                           (pat, uu____56708)  in
                                         let uu____56709 =
                                           universe_to_string univs1  in
                                         (uu____56703, uu____56709))
                                       in
                                    (attrs_opt, uu____56605))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____56815 =
                   match uu____56815 with
                   | (attrs,(pb,univs1)) ->
                       let uu____56875 =
                         let uu____56877 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____56877  in
                       if uu____56875
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____56958) ->
          let s =
            let uu____56977 =
              let uu____56979 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____56979 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____56977  in
          let uu____56984 = mk1 FStar_Parser_AST.Wild  in label s uu____56984
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____56992 =
            let uu____56993 =
              let uu____56998 = resugar_term' env tm  in (uu____56998, qi1)
               in
            FStar_Parser_AST.Quote uu____56993  in
          mk1 uu____56992
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_57010 =
            match uu___434_57010 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____57018,(uu____57019,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____57080 =
                        let uu____57081 =
                          let uu____57090 = resugar_seq t11  in
                          (uu____57090, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____57081  in
                      mk1 uu____57080
                  | uu____57093 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____57137  ->
                         match uu____57137 with
                         | (x,uu____57145) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____57150 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____57168,t1) ->
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
               let uu____57208 = FStar_Options.print_universes ()  in
               if uu____57208
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
               let uu____57272 = FStar_Options.print_universes ()  in
               if uu____57272
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
            let uu____57316 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____57316, FStar_Parser_AST.Nothing)  in
          let uu____57317 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____57317
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____57340 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____57340
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____57425 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____57425, (FStar_Pervasives_Native.snd post))  in
                    let uu____57436 =
                      let uu____57445 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____57445 then [] else [pre]  in
                    let uu____57480 =
                      let uu____57489 =
                        let uu____57498 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____57498 then [] else [pats]  in
                      FStar_List.append [post1] uu____57489  in
                    FStar_List.append uu____57436 uu____57480
                | uu____57557 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____57591  ->
                   match uu____57591 with
                   | (e,uu____57603) ->
                       let uu____57608 = resugar_term' env e  in
                       (uu____57608, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_57633 =
              match uu___435_57633 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____57666 = resugar_term' env e  in
                         (uu____57666, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____57671 -> aux l tl1)
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
        let uu____57718 = b  in
        match uu____57718 with
        | (x,aq) ->
            let uu____57727 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____57727
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____57741 =
                       let uu____57742 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____57742  in
                     FStar_Parser_AST.mk_binder uu____57741 r
                       FStar_Parser_AST.Type_level imp
                 | uu____57743 ->
                     let uu____57744 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____57744
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____57749 =
                          let uu____57750 =
                            let uu____57755 = bv_as_unique_ident x  in
                            (uu____57755, e)  in
                          FStar_Parser_AST.Annotated uu____57750  in
                        FStar_Parser_AST.mk_binder uu____57749 r
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
              let uu____57775 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____57775  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____57779 =
                if used
                then
                  let uu____57781 =
                    let uu____57788 = bv_as_unique_ident v1  in
                    (uu____57788, aqual)  in
                  FStar_Parser_AST.PatVar uu____57781
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____57779  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____57795;
                  FStar_Syntax_Syntax.vars = uu____57796;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____57806 = FStar_Options.print_bound_var_types ()  in
                if uu____57806
                then
                  let uu____57809 =
                    let uu____57810 =
                      let uu____57821 =
                        let uu____57828 = resugar_term' env typ  in
                        (uu____57828, FStar_Pervasives_Native.None)  in
                      (pat, uu____57821)  in
                    FStar_Parser_AST.PatAscribed uu____57810  in
                  mk1 uu____57809
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
          let uu____57849 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____57849
            (fun aqual  ->
               let uu____57861 =
                 let uu____57866 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _57877  -> FStar_Pervasives_Native.Some _57877)
                   uu____57866
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____57861)

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
          (let uu____57939 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____57939) &&
            (let uu____57942 =
               FStar_List.existsML
                 (fun uu____57955  ->
                    match uu____57955 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____57977)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____57982 -> false
                          | uu____57984 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____57942)
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
            let uu____58052 = may_drop_implicits args  in
            if uu____58052 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____58077  ->
                 match uu____58077 with
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
              ((let uu____58132 =
                  let uu____58134 =
                    let uu____58136 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____58136  in
                  Prims.op_Negation uu____58134  in
                if uu____58132
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
              let uu____58180 = filter_pattern_imp args  in
              (match uu____58180 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____58230 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____58230 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____58249 =
                       let uu____58255 =
                         let uu____58257 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____58257
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____58255)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____58249);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____58310  ->
                        match uu____58310 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____58327 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____58327)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____58335;
                 FStar_Syntax_Syntax.fv_delta = uu____58336;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____58365 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____58365 FStar_List.rev  in
              let args1 =
                let uu____58381 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____58401  ->
                          match uu____58401 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____58381 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____58479 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____58479
                | (hd1::tl1,hd2::tl2) ->
                    let uu____58502 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____58502
                 in
              let args2 =
                let uu____58520 = map21 fields1 args1  in
                FStar_All.pipe_right uu____58520 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____58564 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____58564 with
               | FStar_Pervasives_Native.Some (op,uu____58576) ->
                   let uu____58593 =
                     let uu____58594 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____58594  in
                   mk1 uu____58593
               | FStar_Pervasives_Native.None  ->
                   let uu____58604 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____58604 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____58609 ->
              let uu____58610 =
                let uu____58611 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____58611  in
              mk1 uu____58610
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
          let uu____58651 =
            let uu____58654 =
              let uu____58655 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____58655  in
            FStar_Pervasives_Native.Some uu____58654  in
          FStar_Pervasives_Native.Some uu____58651

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
          let uu____58667 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____58667

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_58675  ->
    match uu___436_58675 with
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
    | FStar_Syntax_Syntax.Reflectable uu____58682 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____58683 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____58684 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____58689 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____58698 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____58707 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_58713  ->
    match uu___437_58713 with
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
            (tylid,uvs,bs,t,uu____58756,datacons) ->
            let uu____58766 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____58794,uu____58795,uu____58796,inductive_lid,uu____58798,uu____58799)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____58806 -> failwith "unexpected"))
               in
            (match uu____58766 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____58827 = FStar_Options.print_implicits ()  in
                   if uu____58827 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____58844 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_58851  ->
                             match uu___438_58851 with
                             | FStar_Syntax_Syntax.RecordType uu____58853 ->
                                 true
                             | uu____58863 -> false))
                      in
                   if uu____58844
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____58917,univs1,term,uu____58920,num,uu____58922)
                           ->
                           let uu____58929 =
                             let uu____58930 =
                               FStar_Syntax_Subst.compress term  in
                             uu____58930.FStar_Syntax_Syntax.n  in
                           (match uu____58929 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____58944)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____59013  ->
                                          match uu____59013 with
                                          | (b,qual) ->
                                              let uu____59034 =
                                                bv_as_unique_ident b  in
                                              let uu____59035 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____59034, uu____59035,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____59046 -> failwith "unexpected")
                       | uu____59058 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____59189,num,uu____59191) ->
                            let c =
                              let uu____59212 =
                                let uu____59215 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____59215  in
                              ((l.FStar_Ident.ident), uu____59212,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____59235 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____59315 ->
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
        let uu____59341 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____59341;
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
        let uu____59371 = ts  in
        match uu____59371 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____59384 =
              let uu____59385 =
                let uu____59402 =
                  let uu____59411 =
                    let uu____59418 =
                      let uu____59419 =
                        let uu____59432 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____59432)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____59419  in
                    (uu____59418, FStar_Pervasives_Native.None)  in
                  [uu____59411]  in
                (false, false, uu____59402)  in
              FStar_Parser_AST.Tycon uu____59385  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____59384
  
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
              let uu____59521 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____59521 with
              | (bs,action_defn) ->
                  let uu____59528 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____59528 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____59538 = FStar_Options.print_implicits ()
                            in
                         if uu____59538
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____59548 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____59548 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____59565 =
                             let uu____59576 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____59576,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____59565  in
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
            let uu____59660 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____59660 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____59670 = FStar_Options.print_implicits ()  in
                  if uu____59670 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____59680 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____59680 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59765) ->
          let uu____59774 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____59797 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____59815 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____59823 -> false
                    | uu____59840 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____59774 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____59878 se1 =
                 match uu____59878 with
                 | (datacon_ses1,tycons) ->
                     let uu____59904 = resugar_typ env datacon_ses1 se1  in
                     (match uu____59904 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____59919 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____59919 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____59954 =
                           let uu____59955 =
                             let uu____59956 =
                               let uu____59973 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____59973)  in
                             FStar_Parser_AST.Tycon uu____59956  in
                           decl'_to_decl se uu____59955  in
                         FStar_Pervasives_Native.Some uu____59954
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____60008,uu____60009,uu____60010,uu____60011,uu____60012)
                              ->
                              let uu____60019 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____60019
                          | uu____60022 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____60026 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60033) ->
          let uu____60038 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_60046  ->
                    match uu___439_60046 with
                    | FStar_Syntax_Syntax.Projector (uu____60048,uu____60049)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60051 -> true
                    | uu____60053 -> false))
             in
          if uu____60038
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
             | FStar_Parser_AST.Let (isrec,lets,uu____60088) ->
                 let uu____60117 =
                   let uu____60118 =
                     let uu____60119 =
                       let uu____60130 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____60130)  in
                     FStar_Parser_AST.TopLevelLet uu____60119  in
                   decl'_to_decl se uu____60118  in
                 FStar_Pervasives_Native.Some uu____60117
             | uu____60167 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____60172,fml) ->
          let uu____60174 =
            let uu____60175 =
              let uu____60176 =
                let uu____60181 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____60181)  in
              FStar_Parser_AST.Assume uu____60176  in
            decl'_to_decl se uu____60175  in
          FStar_Pervasives_Native.Some uu____60174
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____60183 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60183
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____60186 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60186
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____60196,t) ->
                let uu____60206 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60206
            | uu____60207 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____60215,t) ->
                let uu____60225 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60225
            | uu____60226 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____60250 -> failwith "Should not happen hopefully"  in
          let uu____60260 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____60260
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____60270 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____60270 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____60282 = FStar_Options.print_implicits ()  in
                 if uu____60282 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____60298 =
                 let uu____60299 =
                   let uu____60300 =
                     let uu____60317 =
                       let uu____60326 =
                         let uu____60333 =
                           let uu____60334 =
                             let uu____60347 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____60347)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____60334  in
                         (uu____60333, FStar_Pervasives_Native.None)  in
                       [uu____60326]  in
                     (false, false, uu____60317)  in
                   FStar_Parser_AST.Tycon uu____60300  in
                 decl'_to_decl se uu____60299  in
               FStar_Pervasives_Native.Some uu____60298)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____60379 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____60379
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____60383 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_60391  ->
                    match uu___440_60391 with
                    | FStar_Syntax_Syntax.Projector (uu____60393,uu____60394)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60396 -> true
                    | uu____60398 -> false))
             in
          if uu____60383
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____60406 =
                 (let uu____60410 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____60410) || (FStar_List.isEmpty uvs)
                  in
               if uu____60406
               then resugar_term' env t
               else
                 (let uu____60415 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____60415 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____60424 = resugar_term' env t1  in
                      label universes uu____60424)
                in
             let uu____60425 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____60425)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____60432 =
            let uu____60433 =
              let uu____60434 =
                let uu____60441 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____60446 = resugar_term' env t  in
                (uu____60441, uu____60446)  in
              FStar_Parser_AST.Splice uu____60434  in
            decl'_to_decl se uu____60433  in
          FStar_Pervasives_Native.Some uu____60432
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____60449 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____60466 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____60482 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____60506 = noenv resugar_term'  in uu____60506 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____60524 = noenv resugar_sigelt'  in uu____60524 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____60542 = noenv resugar_comp'  in uu____60542 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____60565 = noenv resugar_pat'  in uu____60565 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____60599 = noenv resugar_binder'  in uu____60599 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____60624 = noenv resugar_tscheme'  in uu____60624 ts 
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
          let uu____60659 = noenv resugar_eff_decl'  in
          uu____60659 for_free r q ed
  