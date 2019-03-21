open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____51326 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____51326
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____51334 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____51334
  
let map_opt :
  'Auu____51344 'Auu____51345 .
    unit ->
      ('Auu____51344 -> 'Auu____51345 FStar_Pervasives_Native.option) ->
        'Auu____51344 Prims.list -> 'Auu____51345 Prims.list
  = fun uu____51361  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____51370 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____51370
      then
        let uu____51374 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____51374
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____51384 .
    ('Auu____51384 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51384 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_51439  ->
            match uu___429_51439 with
            | (uu____51447,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____51454,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____51455)) -> false
            | (uu____51460,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____51461)) -> false
            | uu____51467 -> true))
  
let filter_pattern_imp :
  'Auu____51480 .
    ('Auu____51480 * Prims.bool) Prims.list ->
      ('Auu____51480 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____51515  ->
         match uu____51515 with
         | (uu____51522,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____51572 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____51585 = FStar_Options.print_universes ()  in
    if uu____51585
    then
      let uu____51589 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____51589 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____51653 ->
          let uu____51654 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____51654 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____51665 =
                      let uu____51666 =
                        let uu____51667 =
                          let uu____51679 = FStar_Util.string_of_int n1  in
                          (uu____51679, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____51667  in
                      FStar_Parser_AST.Const uu____51666  in
                    mk1 uu____51665 r
                | uu____51692 ->
                    let e1 =
                      let uu____51694 =
                        let uu____51695 =
                          let uu____51696 =
                            let uu____51708 = FStar_Util.string_of_int n1  in
                            (uu____51708, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____51696  in
                        FStar_Parser_AST.Const uu____51695  in
                      mk1 uu____51694 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____51722 =
                      let uu____51723 =
                        let uu____51730 = FStar_Ident.id_of_text "+"  in
                        (uu____51730, [e1; e2])  in
                      FStar_Parser_AST.Op uu____51723  in
                    mk1 uu____51722 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____51738 ->
               let t =
                 let uu____51742 =
                   let uu____51743 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____51743  in
                 mk1 uu____51742 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____51752 =
                        let uu____51753 =
                          let uu____51760 = resugar_universe x r  in
                          (acc, uu____51760, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____51753  in
                      mk1 uu____51752 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____51762 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____51774 =
              let uu____51780 =
                let uu____51782 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____51782  in
              (uu____51780, r)  in
            FStar_Ident.mk_ident uu____51774  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_51820 =
      match uu___430_51820 with
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
      | uu____52148 -> FStar_Pervasives_Native.None  in
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
    | uu____52288 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____52306 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____52306 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____52324 ->
               let op =
                 let uu____52330 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____52384) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____52330
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
      let uu____52711 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____52711 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____52781 ->
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
                (let uu____52883 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____52883
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____52919 =
      let uu____52920 = FStar_Syntax_Subst.compress t  in
      uu____52920.FStar_Syntax_Syntax.n  in
    match uu____52919 with
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
        let uu____52941 = string_to_op s  in
        (match uu____52941 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____52981 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____52998 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____53015 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____53026 -> true
    | uu____53028 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____53049 ->
        let uu____53051 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____53051
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____53065 = may_shorten lid  in
      if uu____53065 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____53210 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____53210  in
      let uu____53213 =
        let uu____53214 = FStar_Syntax_Subst.compress t  in
        uu____53214.FStar_Syntax_Syntax.n  in
      match uu____53213 with
      | FStar_Syntax_Syntax.Tm_delayed uu____53217 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____53242 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____53242
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____53245 =
              let uu____53248 = bv_as_unique_ident x  in [uu____53248]  in
            FStar_Ident.lid_of_ids uu____53245  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____53251 =
              let uu____53254 = bv_as_unique_ident x  in [uu____53254]  in
            FStar_Ident.lid_of_ids uu____53251  in
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
            let uu____53273 =
              let uu____53274 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____53274  in
            mk1 uu____53273
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
               | uu____53298 -> failwith "wrong projector format")
            else
              (let uu____53305 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____53309 =
                      let uu____53311 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____53311  in
                    let uu____53314 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____53309 <> uu____53314)
                  in
               if uu____53305
               then
                 let uu____53319 =
                   let uu____53320 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____53320  in
                 mk1 uu____53319
               else
                 (let uu____53323 =
                    let uu____53324 =
                      let uu____53335 = maybe_shorten_fv env fv  in
                      (uu____53335, [])  in
                    FStar_Parser_AST.Construct uu____53324  in
                  mk1 uu____53323))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____53353 = FStar_Options.print_universes ()  in
          if uu____53353
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
                   let uu____53384 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____53384  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____53407 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____53415 = FStar_Syntax_Syntax.is_teff t  in
          if uu____53415
          then
            let uu____53418 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____53418
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____53423 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____53444 -> ("Type", true)  in
          (match uu____53423 with
           | (nm,needs_app) ->
               let typ =
                 let uu____53456 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____53456  in
               let uu____53457 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____53457
               then
                 let uu____53460 =
                   let uu____53461 =
                     let uu____53468 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____53468, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____53461  in
                 mk1 uu____53460
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____53473) ->
          let uu____53498 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____53498 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53514 = FStar_Options.print_implicits ()  in
                 if uu____53514 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____53552  ->
                         match uu____53552 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____53592 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____53592 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____53602 = FStar_Options.print_implicits ()  in
                 if uu____53602 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____53613 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____53613 FStar_List.rev  in
               let rec aux body3 uu___431_53638 =
                 match uu___431_53638 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____53654 =
            let uu____53659 =
              let uu____53660 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____53660]  in
            FStar_Syntax_Subst.open_term uu____53659 phi  in
          (match uu____53654 with
           | (x1,phi1) ->
               let b =
                 let uu____53682 =
                   let uu____53685 = FStar_List.hd x1  in
                   resugar_binder' env uu____53685 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____53682  in
               let uu____53692 =
                 let uu____53693 =
                   let uu____53698 = resugar_term' env phi1  in
                   (b, uu____53698)  in
                 FStar_Parser_AST.Refine uu____53693  in
               mk1 uu____53692)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____53700;
             FStar_Syntax_Syntax.vars = uu____53701;_},(e,uu____53703)::[])
          when
          (let uu____53744 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____53744) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_53793 =
            match uu___432_53793 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____53863 -> failwith "last of an empty list"  in
          let rec last_two uu___433_53902 =
            match uu___433_53902 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____53934::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____54012::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____54083  ->
                   match uu____54083 with
                   | (e2,qual) ->
                       let uu____54100 = resugar_term' env e2  in
                       let uu____54101 = resugar_imp env qual  in
                       (uu____54100, uu____54101)) args1
               in
            let uu____54102 = resugar_term' env e1  in
            match uu____54102 with
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
                     fun uu____54139  ->
                       match uu____54139 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____54155 = FStar_Options.print_implicits ()  in
            if uu____54155 then args else filter_imp args  in
          let uu____54170 = resugar_term_as_op e  in
          (match uu____54170 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____54183) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____54208  ->
                        match uu____54208 with
                        | (x,uu____54220) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____54229 =
                                   let uu____54230 =
                                     let uu____54231 =
                                       let uu____54238 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____54238, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____54231  in
                                   mk1 uu____54230  in
                                 FStar_Pervasives_Native.Some uu____54229))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____54242) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____54268)::[] -> b
                 | uu____54285 -> failwith "wrong arguments to dtuple"  in
               let uu____54295 =
                 let uu____54296 = FStar_Syntax_Subst.compress body  in
                 uu____54296.FStar_Syntax_Syntax.n  in
               (match uu____54295 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54301) ->
                    let uu____54326 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____54326 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____54336 = FStar_Options.print_implicits ()
                              in
                           if uu____54336 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____54353 =
                           let uu____54354 =
                             let uu____54365 =
                               FStar_List.map
                                 (fun _54376  -> FStar_Util.Inl _54376) xs3
                                in
                             (uu____54365, body3)  in
                           FStar_Parser_AST.Sum uu____54354  in
                         mk1 uu____54353)
                | uu____54383 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____54406  ->
                              match uu____54406 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____54424) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____54433) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____54442 = FStar_List.hd args1  in
               (match uu____54442 with
                | (t1,uu____54456) ->
                    let uu____54461 =
                      let uu____54462 = FStar_Syntax_Subst.compress t1  in
                      uu____54462.FStar_Syntax_Syntax.n  in
                    (match uu____54461 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____54469 =
                           let uu____54470 =
                             let uu____54475 = resugar_term' env t1  in
                             (uu____54475, f)  in
                           FStar_Parser_AST.Project uu____54470  in
                         mk1 uu____54469
                     | uu____54476 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____54477) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____54501 =
                 match new_args with
                 | (a1,uu____54511)::(a2,uu____54513)::[] -> (a1, a2)
                 | uu____54540 -> failwith "wrong arguments to try_with"  in
               (match uu____54501 with
                | (body,handler) ->
                    let decomp term =
                      let uu____54562 =
                        let uu____54563 = FStar_Syntax_Subst.compress term
                           in
                        uu____54563.FStar_Syntax_Syntax.n  in
                      match uu____54562 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____54568) ->
                          let uu____54593 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____54593 with | (x1,e2) -> e2)
                      | uu____54600 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____54603 = decomp body  in
                      resugar_term' env uu____54603  in
                    let handler1 =
                      let uu____54605 = decomp handler  in
                      resugar_term' env uu____54605  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____54613,uu____54614,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____54646,uu____54647,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____54684 =
                            let uu____54685 =
                              let uu____54694 = resugar_body t11  in
                              (uu____54694, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____54685  in
                          mk1 uu____54684
                      | uu____54697 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____54755 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____54785) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54794) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____54815) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____54913 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____54926 =
                   let uu____54927 = FStar_Syntax_Subst.compress body  in
                   uu____54927.FStar_Syntax_Syntax.n  in
                 match uu____54926 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____54932) ->
                     let uu____54957 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____54957 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____54967 =
                              FStar_Options.print_implicits ()  in
                            if uu____54967 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____54983 =
                            let uu____54992 =
                              let uu____54993 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____54993.FStar_Syntax_Syntax.n  in
                            match uu____54992 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____55011 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____55041 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____55085  ->
                                                     match uu____55085 with
                                                     | (e2,uu____55093) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____55041, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____55109 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____55109)
                                  | uu____55118 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____55011 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____55150 ->
                                let uu____55151 = resugar_term' env body2  in
                                ([], uu____55151)
                             in
                          (match uu____54983 with
                           | (pats,body3) ->
                               let uu____55168 = uncurry xs3 pats body3  in
                               (match uu____55168 with
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
                 | uu____55220 ->
                     if op = "forall"
                     then
                       let uu____55224 =
                         let uu____55225 =
                           let uu____55238 = resugar_term' env body  in
                           ([], [[]], uu____55238)  in
                         FStar_Parser_AST.QForall uu____55225  in
                       mk1 uu____55224
                     else
                       (let uu____55251 =
                          let uu____55252 =
                            let uu____55265 = resugar_term' env body  in
                            ([], [[]], uu____55265)  in
                          FStar_Parser_AST.QExists uu____55252  in
                        mk1 uu____55251)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____55294)::[] -> resugar b
                  | uu____55311 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____55323) ->
               let uu____55331 = FStar_List.hd args1  in
               (match uu____55331 with
                | (e1,uu____55345) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____55417  ->
                         match uu____55417 with
                         | (e1,qual) ->
                             let uu____55434 = resugar_term' env e1  in
                             let uu____55435 = resugar_imp env qual  in
                             (uu____55434, uu____55435)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____55451 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____55451 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____55499 =
                               let uu____55500 =
                                 let uu____55507 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____55507)  in
                               FStar_Parser_AST.Op uu____55500  in
                             mk1 uu____55499  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____55525  ->
                                  match uu____55525 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____55544 =
                      let uu____55545 =
                        let uu____55552 =
                          let uu____55555 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____55555
                           in
                        (op1, uu____55552)  in
                      FStar_Parser_AST.Op uu____55545  in
                    mk1 uu____55544
                | uu____55568 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____55637 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____55637 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____55683 =
                   let uu____55696 =
                     let uu____55701 = resugar_pat' env pat1 branch_bv  in
                     let uu____55702 = resugar_term' env e  in
                     (uu____55701, uu____55702)  in
                   (FStar_Pervasives_Native.None, uu____55696)  in
                 [uu____55683]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____55754,t1)::(pat2,uu____55757,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____55853 =
            let uu____55854 =
              let uu____55861 = resugar_term' env e  in
              let uu____55862 = resugar_term' env t1  in
              let uu____55863 = resugar_term' env t2  in
              (uu____55861, uu____55862, uu____55863)  in
            FStar_Parser_AST.If uu____55854  in
          mk1 uu____55853
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____55929 =
            match uu____55929 with
            | (pat,wopt,b) ->
                let uu____55971 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____55971 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____56023 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____56023
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____56027 =
            let uu____56028 =
              let uu____56043 = resugar_term' env e  in
              let uu____56044 = FStar_List.map resugar_branch branches  in
              (uu____56043, uu____56044)  in
            FStar_Parser_AST.Match uu____56028  in
          mk1 uu____56027
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____56090) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____56159 =
            let uu____56160 =
              let uu____56169 = resugar_term' env e  in
              (uu____56169, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____56160  in
          mk1 uu____56159
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____56198 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____56198 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____56252 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____56252
                    in
                 let uu____56259 =
                   let uu____56264 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____56264
                    in
                 match uu____56259 with
                 | (univs1,td) ->
                     let uu____56284 =
                       let uu____56291 =
                         let uu____56292 = FStar_Syntax_Subst.compress td  in
                         uu____56292.FStar_Syntax_Syntax.n  in
                       match uu____56291 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____56301,(t1,uu____56303)::(d,uu____56305)::[])
                           -> (t1, d)
                       | uu____56362 -> failwith "wrong let binding format"
                        in
                     (match uu____56284 with
                      | (typ,def) ->
                          let uu____56393 =
                            let uu____56409 =
                              let uu____56410 =
                                FStar_Syntax_Subst.compress def  in
                              uu____56410.FStar_Syntax_Syntax.n  in
                            match uu____56409 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____56430)
                                ->
                                let uu____56455 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____56455 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____56486 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____56486
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____56509 -> ([], def, false)  in
                          (match uu____56393 with
                           | (binders,term,is_pat_app) ->
                               let uu____56564 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____56575 =
                                       let uu____56576 =
                                         let uu____56577 =
                                           let uu____56584 =
                                             bv_as_unique_ident bv  in
                                           (uu____56584,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____56577
                                          in
                                       mk_pat uu____56576  in
                                     (uu____56575, term)
                                  in
                               (match uu____56564 with
                                | (pat,term1) ->
                                    let uu____56606 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____56649  ->
                                                  match uu____56649 with
                                                  | (bv,q) ->
                                                      let uu____56664 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____56664
                                                        (fun q1  ->
                                                           let uu____56676 =
                                                             let uu____56677
                                                               =
                                                               let uu____56684
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____56684,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____56677
                                                              in
                                                           mk_pat uu____56676)))
                                           in
                                        let uu____56687 =
                                          let uu____56692 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____56692)
                                           in
                                        let uu____56695 =
                                          universe_to_string univs1  in
                                        (uu____56687, uu____56695)
                                      else
                                        (let uu____56704 =
                                           let uu____56709 =
                                             resugar_term' env term1  in
                                           (pat, uu____56709)  in
                                         let uu____56710 =
                                           universe_to_string univs1  in
                                         (uu____56704, uu____56710))
                                       in
                                    (attrs_opt, uu____56606))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____56816 =
                   match uu____56816 with
                   | (attrs,(pb,univs1)) ->
                       let uu____56876 =
                         let uu____56878 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____56878  in
                       if uu____56876
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____56959) ->
          let s =
            let uu____56978 =
              let uu____56980 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____56980 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____56978  in
          let uu____56985 = mk1 FStar_Parser_AST.Wild  in label s uu____56985
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____56993 =
            let uu____56994 =
              let uu____56999 = resugar_term' env tm  in (uu____56999, qi1)
               in
            FStar_Parser_AST.Quote uu____56994  in
          mk1 uu____56993
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_57011 =
            match uu___434_57011 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____57019,(uu____57020,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____57081 =
                        let uu____57082 =
                          let uu____57091 = resugar_seq t11  in
                          (uu____57091, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____57082  in
                      mk1 uu____57081
                  | uu____57094 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____57138  ->
                         match uu____57138 with
                         | (x,uu____57146) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____57151 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____57169,t1) ->
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
               let uu____57209 = FStar_Options.print_universes ()  in
               if uu____57209
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
               let uu____57273 = FStar_Options.print_universes ()  in
               if uu____57273
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
            let uu____57317 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____57317, FStar_Parser_AST.Nothing)  in
          let uu____57318 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____57318
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____57341 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____57341
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____57426 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____57426, (FStar_Pervasives_Native.snd post))  in
                    let uu____57437 =
                      let uu____57446 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____57446 then [] else [pre]  in
                    let uu____57481 =
                      let uu____57490 =
                        let uu____57499 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____57499 then [] else [pats]  in
                      FStar_List.append [post1] uu____57490  in
                    FStar_List.append uu____57437 uu____57481
                | uu____57558 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____57592  ->
                   match uu____57592 with
                   | (e,uu____57604) ->
                       let uu____57609 = resugar_term' env e  in
                       (uu____57609, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_57634 =
              match uu___435_57634 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____57667 = resugar_term' env e  in
                         (uu____57667, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____57672 -> aux l tl1)
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
        let uu____57719 = b  in
        match uu____57719 with
        | (x,aq) ->
            let uu____57728 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____57728
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____57742 =
                       let uu____57743 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____57743  in
                     FStar_Parser_AST.mk_binder uu____57742 r
                       FStar_Parser_AST.Type_level imp
                 | uu____57744 ->
                     let uu____57745 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____57745
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____57750 =
                          let uu____57751 =
                            let uu____57756 = bv_as_unique_ident x  in
                            (uu____57756, e)  in
                          FStar_Parser_AST.Annotated uu____57751  in
                        FStar_Parser_AST.mk_binder uu____57750 r
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
              let uu____57776 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____57776  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____57780 =
                if used
                then
                  let uu____57782 =
                    let uu____57789 = bv_as_unique_ident v1  in
                    (uu____57789, aqual)  in
                  FStar_Parser_AST.PatVar uu____57782
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____57780  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____57796;
                  FStar_Syntax_Syntax.vars = uu____57797;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____57807 = FStar_Options.print_bound_var_types ()  in
                if uu____57807
                then
                  let uu____57810 =
                    let uu____57811 =
                      let uu____57822 =
                        let uu____57829 = resugar_term' env typ  in
                        (uu____57829, FStar_Pervasives_Native.None)  in
                      (pat, uu____57822)  in
                    FStar_Parser_AST.PatAscribed uu____57811  in
                  mk1 uu____57810
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
          let uu____57850 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____57850
            (fun aqual  ->
               let uu____57862 =
                 let uu____57867 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _57878  -> FStar_Pervasives_Native.Some _57878)
                   uu____57867
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____57862)

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
          (let uu____57940 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____57940) &&
            (let uu____57943 =
               FStar_List.existsML
                 (fun uu____57956  ->
                    match uu____57956 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____57978)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____57983 -> false
                          | uu____57985 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____57943)
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
            let uu____58053 = may_drop_implicits args  in
            if uu____58053 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____58078  ->
                 match uu____58078 with
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
              ((let uu____58133 =
                  let uu____58135 =
                    let uu____58137 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____58137  in
                  Prims.op_Negation uu____58135  in
                if uu____58133
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
              let uu____58181 = filter_pattern_imp args  in
              (match uu____58181 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____58231 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____58231 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____58250 =
                       let uu____58256 =
                         let uu____58258 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____58258
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____58256)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____58250);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____58311  ->
                        match uu____58311 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____58328 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____58328)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____58336;
                 FStar_Syntax_Syntax.fv_delta = uu____58337;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____58366 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____58366 FStar_List.rev  in
              let args1 =
                let uu____58382 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____58402  ->
                          match uu____58402 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____58382 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____58480 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____58480
                | (hd1::tl1,hd2::tl2) ->
                    let uu____58503 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____58503
                 in
              let args2 =
                let uu____58521 = map21 fields1 args1  in
                FStar_All.pipe_right uu____58521 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____58565 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____58565 with
               | FStar_Pervasives_Native.Some (op,uu____58577) ->
                   let uu____58594 =
                     let uu____58595 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____58595  in
                   mk1 uu____58594
               | FStar_Pervasives_Native.None  ->
                   let uu____58605 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____58605 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____58610 ->
              let uu____58611 =
                let uu____58612 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____58612  in
              mk1 uu____58611
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
          let uu____58652 =
            let uu____58655 =
              let uu____58656 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____58656  in
            FStar_Pervasives_Native.Some uu____58655  in
          FStar_Pervasives_Native.Some uu____58652

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
          let uu____58668 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____58668

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_58676  ->
    match uu___436_58676 with
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
    | FStar_Syntax_Syntax.Reflectable uu____58683 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____58684 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____58685 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____58690 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____58699 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____58708 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_58714  ->
    match uu___437_58714 with
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
            (tylid,uvs,bs,t,uu____58757,datacons) ->
            let uu____58767 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____58795,uu____58796,uu____58797,inductive_lid,uu____58799,uu____58800)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____58807 -> failwith "unexpected"))
               in
            (match uu____58767 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____58828 = FStar_Options.print_implicits ()  in
                   if uu____58828 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____58845 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_58852  ->
                             match uu___438_58852 with
                             | FStar_Syntax_Syntax.RecordType uu____58854 ->
                                 true
                             | uu____58864 -> false))
                      in
                   if uu____58845
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____58918,univs1,term,uu____58921,num,uu____58923)
                           ->
                           let uu____58930 =
                             let uu____58931 =
                               FStar_Syntax_Subst.compress term  in
                             uu____58931.FStar_Syntax_Syntax.n  in
                           (match uu____58930 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____58945)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____59014  ->
                                          match uu____59014 with
                                          | (b,qual) ->
                                              let uu____59035 =
                                                bv_as_unique_ident b  in
                                              let uu____59036 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____59035, uu____59036,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____59047 -> failwith "unexpected")
                       | uu____59059 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____59190,num,uu____59192) ->
                            let c =
                              let uu____59213 =
                                let uu____59216 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____59216  in
                              ((l.FStar_Ident.ident), uu____59213,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____59236 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____59316 ->
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
        let uu____59342 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____59342;
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
        let uu____59372 = ts  in
        match uu____59372 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____59385 =
              let uu____59386 =
                let uu____59403 =
                  let uu____59412 =
                    let uu____59419 =
                      let uu____59420 =
                        let uu____59433 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____59433)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____59420  in
                    (uu____59419, FStar_Pervasives_Native.None)  in
                  [uu____59412]  in
                (false, false, uu____59403)  in
              FStar_Parser_AST.Tycon uu____59386  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____59385
  
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
              let uu____59522 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____59522 with
              | (bs,action_defn) ->
                  let uu____59529 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____59529 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____59539 = FStar_Options.print_implicits ()
                            in
                         if uu____59539
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____59549 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____59549 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____59566 =
                             let uu____59577 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____59577,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____59566  in
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
            let uu____59661 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____59661 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____59671 = FStar_Options.print_implicits ()  in
                  if uu____59671 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____59681 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____59681 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59766) ->
          let uu____59775 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____59798 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____59816 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____59824 -> false
                    | uu____59841 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____59775 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____59879 se1 =
                 match uu____59879 with
                 | (datacon_ses1,tycons) ->
                     let uu____59905 = resugar_typ env datacon_ses1 se1  in
                     (match uu____59905 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____59920 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____59920 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____59955 =
                           let uu____59956 =
                             let uu____59957 =
                               let uu____59974 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____59974)  in
                             FStar_Parser_AST.Tycon uu____59957  in
                           decl'_to_decl se uu____59956  in
                         FStar_Pervasives_Native.Some uu____59955
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____60009,uu____60010,uu____60011,uu____60012,uu____60013)
                              ->
                              let uu____60020 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____60020
                          | uu____60023 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____60027 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60034) ->
          let uu____60039 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_60047  ->
                    match uu___439_60047 with
                    | FStar_Syntax_Syntax.Projector (uu____60049,uu____60050)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60052 -> true
                    | uu____60054 -> false))
             in
          if uu____60039
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
             | FStar_Parser_AST.Let (isrec,lets,uu____60089) ->
                 let uu____60118 =
                   let uu____60119 =
                     let uu____60120 =
                       let uu____60131 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____60131)  in
                     FStar_Parser_AST.TopLevelLet uu____60120  in
                   decl'_to_decl se uu____60119  in
                 FStar_Pervasives_Native.Some uu____60118
             | uu____60168 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____60173,fml) ->
          let uu____60175 =
            let uu____60176 =
              let uu____60177 =
                let uu____60182 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____60182)  in
              FStar_Parser_AST.Assume uu____60177  in
            decl'_to_decl se uu____60176  in
          FStar_Pervasives_Native.Some uu____60175
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____60184 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60184
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____60187 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____60187
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____60197,t) ->
                let uu____60207 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60207
            | uu____60208 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____60216,t) ->
                let uu____60226 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____60226
            | uu____60227 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____60251 -> failwith "Should not happen hopefully"  in
          let uu____60261 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____60261
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____60271 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____60271 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____60283 = FStar_Options.print_implicits ()  in
                 if uu____60283 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____60299 =
                 let uu____60300 =
                   let uu____60301 =
                     let uu____60318 =
                       let uu____60327 =
                         let uu____60334 =
                           let uu____60335 =
                             let uu____60348 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____60348)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____60335  in
                         (uu____60334, FStar_Pervasives_Native.None)  in
                       [uu____60327]  in
                     (false, false, uu____60318)  in
                   FStar_Parser_AST.Tycon uu____60301  in
                 decl'_to_decl se uu____60300  in
               FStar_Pervasives_Native.Some uu____60299)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____60380 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____60380
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____60384 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_60392  ->
                    match uu___440_60392 with
                    | FStar_Syntax_Syntax.Projector (uu____60394,uu____60395)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____60397 -> true
                    | uu____60399 -> false))
             in
          if uu____60384
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____60407 =
                 (let uu____60411 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____60411) || (FStar_List.isEmpty uvs)
                  in
               if uu____60407
               then resugar_term' env t
               else
                 (let uu____60416 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____60416 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____60425 = resugar_term' env t1  in
                      label universes uu____60425)
                in
             let uu____60426 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____60426)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____60433 =
            let uu____60434 =
              let uu____60435 =
                let uu____60442 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____60447 = resugar_term' env t  in
                (uu____60442, uu____60447)  in
              FStar_Parser_AST.Splice uu____60435  in
            decl'_to_decl se uu____60434  in
          FStar_Pervasives_Native.Some uu____60433
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____60450 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____60467 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____60483 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____60507 = noenv resugar_term'  in uu____60507 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____60525 = noenv resugar_sigelt'  in uu____60525 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____60543 = noenv resugar_comp'  in uu____60543 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____60566 = noenv resugar_pat'  in uu____60566 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____60600 = noenv resugar_binder'  in uu____60600 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____60625 = noenv resugar_tscheme'  in uu____60625 ts 
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
          let uu____60660 = noenv resugar_eff_decl'  in
          uu____60660 for_free r q ed
  