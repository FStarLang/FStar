open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____55850 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____55850
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____55858 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____55858
  
let map_opt :
  'Auu____55868 'Auu____55869 .
    unit ->
      ('Auu____55868 -> 'Auu____55869 FStar_Pervasives_Native.option) ->
        'Auu____55868 Prims.list -> 'Auu____55869 Prims.list
  = fun uu____55885  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____55894 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____55894
      then
        let uu____55898 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____55898
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____55908 .
    ('Auu____55908 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____55908 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_55963  ->
            match uu___429_55963 with
            | (uu____55971,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____55978,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____55979)) -> false
            | (uu____55984,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____55985)) -> false
            | uu____55991 -> true))
  
let filter_pattern_imp :
  'Auu____56004 .
    ('Auu____56004 * Prims.bool) Prims.list ->
      ('Auu____56004 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____56039  ->
         match uu____56039 with
         | (uu____56046,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____56096 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____56109 = FStar_Options.print_universes ()  in
    if uu____56109
    then
      let uu____56113 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____56113 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____56177 ->
          let uu____56178 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____56178 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____56189 =
                      let uu____56190 =
                        let uu____56191 =
                          let uu____56203 = FStar_Util.string_of_int n1  in
                          (uu____56203, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____56191  in
                      FStar_Parser_AST.Const uu____56190  in
                    mk1 uu____56189 r
                | uu____56216 ->
                    let e1 =
                      let uu____56218 =
                        let uu____56219 =
                          let uu____56220 =
                            let uu____56232 = FStar_Util.string_of_int n1  in
                            (uu____56232, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____56220  in
                        FStar_Parser_AST.Const uu____56219  in
                      mk1 uu____56218 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____56246 =
                      let uu____56247 =
                        let uu____56254 = FStar_Ident.id_of_text "+"  in
                        (uu____56254, [e1; e2])  in
                      FStar_Parser_AST.Op uu____56247  in
                    mk1 uu____56246 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____56262 ->
               let t =
                 let uu____56266 =
                   let uu____56267 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____56267  in
                 mk1 uu____56266 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____56276 =
                        let uu____56277 =
                          let uu____56284 = resugar_universe x r  in
                          (acc, uu____56284, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____56277  in
                      mk1 uu____56276 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____56286 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____56298 =
              let uu____56304 =
                let uu____56306 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____56306  in
              (uu____56304, r)  in
            FStar_Ident.mk_ident uu____56298  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_56344 =
      match uu___430_56344 with
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
      | uu____56672 -> FStar_Pervasives_Native.None  in
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
    | uu____56812 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____56830 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____56830 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____56848 ->
               let op =
                 let uu____56854 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____56908) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____56854
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
      let uu____57235 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____57235 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____57305 ->
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
                (let uu____57417 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____57417
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____57453 =
      let uu____57454 = FStar_Syntax_Subst.compress t  in
      uu____57454.FStar_Syntax_Syntax.n  in
    match uu____57453 with
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
        let uu____57485 = string_to_op s  in
        (match uu____57485 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____57525 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____57542 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____57559 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____57570 -> true
    | uu____57572 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____57593 ->
        let uu____57595 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____57595
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____57609 = may_shorten lid  in
      if uu____57609 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____57754 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____57754  in
      let uu____57757 =
        let uu____57758 = FStar_Syntax_Subst.compress t  in
        uu____57758.FStar_Syntax_Syntax.n  in
      match uu____57757 with
      | FStar_Syntax_Syntax.Tm_delayed uu____57761 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____57786 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____57786
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____57789 =
              let uu____57792 = bv_as_unique_ident x  in [uu____57792]  in
            FStar_Ident.lid_of_ids uu____57789  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____57795 =
              let uu____57798 = bv_as_unique_ident x  in [uu____57798]  in
            FStar_Ident.lid_of_ids uu____57795  in
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
            let uu____57827 =
              let uu____57828 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____57828  in
            mk1 uu____57827
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
               | uu____57852 -> failwith "wrong projector format")
            else
              (let uu____57859 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____57863 =
                      let uu____57865 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____57865  in
                    let uu____57868 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____57863 <> uu____57868)
                  in
               if uu____57859
               then
                 let uu____57873 =
                   let uu____57874 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____57874  in
                 mk1 uu____57873
               else
                 (let uu____57877 =
                    let uu____57878 =
                      let uu____57889 = maybe_shorten_fv env fv  in
                      (uu____57889, [])  in
                    FStar_Parser_AST.Construct uu____57878  in
                  mk1 uu____57877))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____57907 = FStar_Options.print_universes ()  in
          if uu____57907
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
                   let uu____57938 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____57938  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____57961 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____57969 = FStar_Syntax_Syntax.is_teff t  in
          if uu____57969
          then
            let uu____57972 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____57972
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____57977 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____57998 -> ("Type", true)  in
          (match uu____57977 with
           | (nm,needs_app) ->
               let typ =
                 let uu____58010 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____58010  in
               let uu____58011 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____58011
               then
                 let uu____58014 =
                   let uu____58015 =
                     let uu____58022 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____58022, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____58015  in
                 mk1 uu____58014
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____58027) ->
          let uu____58052 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____58052 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58068 = FStar_Options.print_implicits ()  in
                 if uu____58068 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____58106  ->
                         match uu____58106 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____58146 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____58146 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58156 = FStar_Options.print_implicits ()  in
                 if uu____58156 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____58167 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____58167 FStar_List.rev  in
               let rec aux body3 uu___431_58192 =
                 match uu___431_58192 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____58208 =
            let uu____58213 =
              let uu____58214 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____58214]  in
            FStar_Syntax_Subst.open_term uu____58213 phi  in
          (match uu____58208 with
           | (x1,phi1) ->
               let b =
                 let uu____58236 =
                   let uu____58239 = FStar_List.hd x1  in
                   resugar_binder' env uu____58239 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____58236  in
               let uu____58246 =
                 let uu____58247 =
                   let uu____58252 = resugar_term' env phi1  in
                   (b, uu____58252)  in
                 FStar_Parser_AST.Refine uu____58247  in
               mk1 uu____58246)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____58254;
             FStar_Syntax_Syntax.vars = uu____58255;_},(e,uu____58257)::[])
          when
          (let uu____58298 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____58298) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_58347 =
            match uu___432_58347 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____58417 -> failwith "last of an empty list"  in
          let rec last_two uu___433_58456 =
            match uu___433_58456 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____58488::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____58566::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____58637  ->
                   match uu____58637 with
                   | (e2,qual) ->
                       let uu____58654 = resugar_term' env e2  in
                       let uu____58655 = resugar_imp env qual  in
                       (uu____58654, uu____58655)) args1
               in
            let uu____58656 = resugar_term' env e1  in
            match uu____58656 with
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
                     fun uu____58693  ->
                       match uu____58693 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____58709 = FStar_Options.print_implicits ()  in
            if uu____58709 then args else filter_imp args  in
          let uu____58724 = resugar_term_as_op e  in
          (match uu____58724 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____58737) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____58762  ->
                        match uu____58762 with
                        | (x,uu____58774) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____58783 =
                                   let uu____58784 =
                                     let uu____58785 =
                                       let uu____58792 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____58792, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____58785  in
                                   mk1 uu____58784  in
                                 FStar_Pervasives_Native.Some uu____58783))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____58796) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____58822)::[] -> b
                 | uu____58839 -> failwith "wrong arguments to dtuple"  in
               let uu____58849 =
                 let uu____58850 = FStar_Syntax_Subst.compress body  in
                 uu____58850.FStar_Syntax_Syntax.n  in
               (match uu____58849 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____58855) ->
                    let uu____58880 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____58880 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____58890 = FStar_Options.print_implicits ()
                              in
                           if uu____58890 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____58907 =
                           let uu____58908 =
                             let uu____58919 =
                               FStar_List.map
                                 (fun _58930  -> FStar_Util.Inl _58930) xs3
                                in
                             (uu____58919, body3)  in
                           FStar_Parser_AST.Sum uu____58908  in
                         mk1 uu____58907)
                | uu____58937 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____58960  ->
                              match uu____58960 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____58978) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____58987) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____58996 = FStar_List.hd args1  in
               (match uu____58996 with
                | (t1,uu____59010) ->
                    let uu____59015 =
                      let uu____59016 = FStar_Syntax_Subst.compress t1  in
                      uu____59016.FStar_Syntax_Syntax.n  in
                    (match uu____59015 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____59023 =
                           let uu____59024 =
                             let uu____59029 = resugar_term' env t1  in
                             (uu____59029, f)  in
                           FStar_Parser_AST.Project uu____59024  in
                         mk1 uu____59023
                     | uu____59030 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____59031) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____59055 =
                 match new_args with
                 | (a1,uu____59065)::(a2,uu____59067)::[] -> (a1, a2)
                 | uu____59094 -> failwith "wrong arguments to try_with"  in
               (match uu____59055 with
                | (body,handler) ->
                    let decomp term =
                      let uu____59116 =
                        let uu____59117 = FStar_Syntax_Subst.compress term
                           in
                        uu____59117.FStar_Syntax_Syntax.n  in
                      match uu____59116 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____59122) ->
                          let uu____59147 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____59147 with | (x1,e2) -> e2)
                      | uu____59154 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____59157 = decomp body  in
                      resugar_term' env uu____59157  in
                    let handler1 =
                      let uu____59159 = decomp handler  in
                      resugar_term' env uu____59159  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____59167,uu____59168,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____59200,uu____59201,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____59238 =
                            let uu____59239 =
                              let uu____59248 = resugar_body t11  in
                              (uu____59248, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____59239  in
                          mk1 uu____59238
                      | uu____59251 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____59309 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____59339) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59348) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59369) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____59467 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____59480 =
                   let uu____59481 = FStar_Syntax_Subst.compress body  in
                   uu____59481.FStar_Syntax_Syntax.n  in
                 match uu____59480 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____59486) ->
                     let uu____59511 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____59511 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____59521 =
                              FStar_Options.print_implicits ()  in
                            if uu____59521 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____59537 =
                            let uu____59546 =
                              let uu____59547 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____59547.FStar_Syntax_Syntax.n  in
                            match uu____59546 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____59565 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____59595 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____59639  ->
                                                     match uu____59639 with
                                                     | (e2,uu____59647) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____59595, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____59663 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____59663)
                                  | uu____59672 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____59565 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____59704 ->
                                let uu____59705 = resugar_term' env body2  in
                                ([], uu____59705)
                             in
                          (match uu____59537 with
                           | (pats,body3) ->
                               let uu____59722 = uncurry xs3 pats body3  in
                               (match uu____59722 with
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
                 | uu____59774 ->
                     if op = "forall"
                     then
                       let uu____59778 =
                         let uu____59779 =
                           let uu____59792 = resugar_term' env body  in
                           ([], [[]], uu____59792)  in
                         FStar_Parser_AST.QForall uu____59779  in
                       mk1 uu____59778
                     else
                       (let uu____59805 =
                          let uu____59806 =
                            let uu____59819 = resugar_term' env body  in
                            ([], [[]], uu____59819)  in
                          FStar_Parser_AST.QExists uu____59806  in
                        mk1 uu____59805)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____59848)::[] -> resugar b
                  | uu____59865 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____59877) ->
               let uu____59885 = FStar_List.hd args1  in
               (match uu____59885 with
                | (e1,uu____59899) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____59971  ->
                         match uu____59971 with
                         | (e1,qual) ->
                             let uu____59988 = resugar_term' env e1  in
                             let uu____59989 = resugar_imp env qual  in
                             (uu____59988, uu____59989)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____60005 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____60005 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____60053 =
                               let uu____60054 =
                                 let uu____60061 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____60061)  in
                               FStar_Parser_AST.Op uu____60054  in
                             mk1 uu____60053  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____60079  ->
                                  match uu____60079 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____60098 =
                      let uu____60099 =
                        let uu____60106 =
                          let uu____60109 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____60109
                           in
                        (op1, uu____60106)  in
                      FStar_Parser_AST.Op uu____60099  in
                    mk1 uu____60098
                | uu____60122 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____60191 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____60191 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____60237 =
                   let uu____60250 =
                     let uu____60255 = resugar_pat' env pat1 branch_bv  in
                     let uu____60256 = resugar_term' env e  in
                     (uu____60255, uu____60256)  in
                   (FStar_Pervasives_Native.None, uu____60250)  in
                 [uu____60237]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____60308,t1)::(pat2,uu____60311,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____60407 =
            let uu____60408 =
              let uu____60415 = resugar_term' env e  in
              let uu____60416 = resugar_term' env t1  in
              let uu____60417 = resugar_term' env t2  in
              (uu____60415, uu____60416, uu____60417)  in
            FStar_Parser_AST.If uu____60408  in
          mk1 uu____60407
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____60483 =
            match uu____60483 with
            | (pat,wopt,b) ->
                let uu____60525 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____60525 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____60577 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____60577
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____60581 =
            let uu____60582 =
              let uu____60597 = resugar_term' env e  in
              let uu____60598 = FStar_List.map resugar_branch branches  in
              (uu____60597, uu____60598)  in
            FStar_Parser_AST.Match uu____60582  in
          mk1 uu____60581
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____60644) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____60713 =
            let uu____60714 =
              let uu____60723 = resugar_term' env e  in
              (uu____60723, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____60714  in
          mk1 uu____60713
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____60752 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____60752 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____60806 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____60806
                    in
                 let uu____60813 =
                   let uu____60818 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____60818
                    in
                 match uu____60813 with
                 | (univs1,td) ->
                     let uu____60838 =
                       let uu____60845 =
                         let uu____60846 = FStar_Syntax_Subst.compress td  in
                         uu____60846.FStar_Syntax_Syntax.n  in
                       match uu____60845 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____60855,(t1,uu____60857)::(d,uu____60859)::[])
                           -> (t1, d)
                       | uu____60916 -> failwith "wrong let binding format"
                        in
                     (match uu____60838 with
                      | (typ,def) ->
                          let uu____60947 =
                            let uu____60963 =
                              let uu____60964 =
                                FStar_Syntax_Subst.compress def  in
                              uu____60964.FStar_Syntax_Syntax.n  in
                            match uu____60963 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____60984)
                                ->
                                let uu____61009 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____61009 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____61040 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____61040
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____61063 -> ([], def, false)  in
                          (match uu____60947 with
                           | (binders,term,is_pat_app) ->
                               let uu____61118 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____61129 =
                                       let uu____61130 =
                                         let uu____61131 =
                                           let uu____61138 =
                                             bv_as_unique_ident bv  in
                                           (uu____61138,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____61131
                                          in
                                       mk_pat uu____61130  in
                                     (uu____61129, term)
                                  in
                               (match uu____61118 with
                                | (pat,term1) ->
                                    let uu____61160 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____61203  ->
                                                  match uu____61203 with
                                                  | (bv,q) ->
                                                      let uu____61218 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____61218
                                                        (fun q1  ->
                                                           let uu____61230 =
                                                             let uu____61231
                                                               =
                                                               let uu____61238
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____61238,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____61231
                                                              in
                                                           mk_pat uu____61230)))
                                           in
                                        let uu____61241 =
                                          let uu____61246 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____61246)
                                           in
                                        let uu____61249 =
                                          universe_to_string univs1  in
                                        (uu____61241, uu____61249)
                                      else
                                        (let uu____61258 =
                                           let uu____61263 =
                                             resugar_term' env term1  in
                                           (pat, uu____61263)  in
                                         let uu____61264 =
                                           universe_to_string univs1  in
                                         (uu____61258, uu____61264))
                                       in
                                    (attrs_opt, uu____61160))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____61370 =
                   match uu____61370 with
                   | (attrs,(pb,univs1)) ->
                       let uu____61430 =
                         let uu____61432 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____61432  in
                       if uu____61430
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____61513) ->
          let s =
            let uu____61532 =
              let uu____61534 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____61534 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____61532  in
          let uu____61539 = mk1 FStar_Parser_AST.Wild  in label s uu____61539
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____61547 =
            let uu____61548 =
              let uu____61553 = resugar_term' env tm  in (uu____61553, qi1)
               in
            FStar_Parser_AST.Quote uu____61548  in
          mk1 uu____61547
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_61565 =
            match uu___434_61565 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____61573,(uu____61574,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____61635 =
                        let uu____61636 =
                          let uu____61645 = resugar_seq t11  in
                          (uu____61645, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____61636  in
                      mk1 uu____61635
                  | uu____61648 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____61692  ->
                         match uu____61692 with
                         | (x,uu____61700) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____61705 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____61723,t1) ->
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
               let uu____61763 = FStar_Options.print_universes ()  in
               if uu____61763
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
               let uu____61827 = FStar_Options.print_universes ()  in
               if uu____61827
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
            let uu____61871 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____61871, FStar_Parser_AST.Nothing)  in
          let uu____61872 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____61872
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____61895 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____61895
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____61980 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____61980, (FStar_Pervasives_Native.snd post))  in
                    let uu____61991 =
                      let uu____62000 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____62000 then [] else [pre]  in
                    let uu____62035 =
                      let uu____62044 =
                        let uu____62053 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____62053 then [] else [pats]  in
                      FStar_List.append [post1] uu____62044  in
                    FStar_List.append uu____61991 uu____62035
                | uu____62112 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____62146  ->
                   match uu____62146 with
                   | (e,uu____62158) ->
                       let uu____62163 = resugar_term' env e  in
                       (uu____62163, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_62188 =
              match uu___435_62188 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____62221 = resugar_term' env e  in
                         (uu____62221, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____62226 -> aux l tl1)
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
        let uu____62273 = b  in
        match uu____62273 with
        | (x,aq) ->
            let uu____62282 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____62282
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____62296 =
                       let uu____62297 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____62297  in
                     FStar_Parser_AST.mk_binder uu____62296 r
                       FStar_Parser_AST.Type_level imp
                 | uu____62298 ->
                     let uu____62299 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____62299
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____62304 =
                          let uu____62305 =
                            let uu____62310 = bv_as_unique_ident x  in
                            (uu____62310, e)  in
                          FStar_Parser_AST.Annotated uu____62305  in
                        FStar_Parser_AST.mk_binder uu____62304 r
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
              let uu____62330 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____62330  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____62334 =
                if used
                then
                  let uu____62336 =
                    let uu____62343 = bv_as_unique_ident v1  in
                    (uu____62343, aqual)  in
                  FStar_Parser_AST.PatVar uu____62336
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____62334  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____62350;
                  FStar_Syntax_Syntax.vars = uu____62351;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____62361 = FStar_Options.print_bound_var_types ()  in
                if uu____62361
                then
                  let uu____62364 =
                    let uu____62365 =
                      let uu____62376 =
                        let uu____62383 = resugar_term' env typ  in
                        (uu____62383, FStar_Pervasives_Native.None)  in
                      (pat, uu____62376)  in
                    FStar_Parser_AST.PatAscribed uu____62365  in
                  mk1 uu____62364
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
          let uu____62404 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____62404
            (fun aqual  ->
               let uu____62416 =
                 let uu____62421 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _62432  -> FStar_Pervasives_Native.Some _62432)
                   uu____62421
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____62416)

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
          (let uu____62494 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____62494) &&
            (let uu____62497 =
               FStar_List.existsML
                 (fun uu____62510  ->
                    match uu____62510 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____62532)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____62537 -> false
                          | uu____62539 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____62497)
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
            let uu____62607 = may_drop_implicits args  in
            if uu____62607 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____62632  ->
                 match uu____62632 with
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
              ((let uu____62687 =
                  let uu____62689 =
                    let uu____62691 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____62691  in
                  Prims.op_Negation uu____62689  in
                if uu____62687
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
              let uu____62735 = filter_pattern_imp args  in
              (match uu____62735 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____62785 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____62785 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____62804 =
                       let uu____62810 =
                         let uu____62812 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____62812
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____62810)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____62804);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____62865  ->
                        match uu____62865 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____62882 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____62882)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____62890;
                 FStar_Syntax_Syntax.fv_delta = uu____62891;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____62920 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____62920 FStar_List.rev  in
              let args1 =
                let uu____62936 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____62956  ->
                          match uu____62956 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____62936 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____63034 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____63034
                | (hd1::tl1,hd2::tl2) ->
                    let uu____63057 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____63057
                 in
              let args2 =
                let uu____63075 = map21 fields1 args1  in
                FStar_All.pipe_right uu____63075 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____63119 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____63119 with
               | FStar_Pervasives_Native.Some (op,uu____63131) ->
                   let uu____63148 =
                     let uu____63149 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____63149  in
                   mk1 uu____63148
               | FStar_Pervasives_Native.None  ->
                   let uu____63159 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____63159 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____63164 ->
              let uu____63165 =
                let uu____63166 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____63166  in
              mk1 uu____63165
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
          let uu____63206 =
            let uu____63209 =
              let uu____63210 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____63210  in
            FStar_Pervasives_Native.Some uu____63209  in
          FStar_Pervasives_Native.Some uu____63206

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
          let uu____63222 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____63222

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_63230  ->
    match uu___436_63230 with
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
    | FStar_Syntax_Syntax.Reflectable uu____63237 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____63238 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____63239 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____63244 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____63253 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____63262 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_63268  ->
    match uu___437_63268 with
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
            (tylid,uvs,bs,t,uu____63311,datacons) ->
            let uu____63321 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____63349,uu____63350,uu____63351,inductive_lid,uu____63353,uu____63354)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____63361 -> failwith "unexpected"))
               in
            (match uu____63321 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____63382 = FStar_Options.print_implicits ()  in
                   if uu____63382 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____63399 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_63406  ->
                             match uu___438_63406 with
                             | FStar_Syntax_Syntax.RecordType uu____63408 ->
                                 true
                             | uu____63418 -> false))
                      in
                   if uu____63399
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____63472,univs1,term,uu____63475,num,uu____63477)
                           ->
                           let uu____63484 =
                             let uu____63485 =
                               FStar_Syntax_Subst.compress term  in
                             uu____63485.FStar_Syntax_Syntax.n  in
                           (match uu____63484 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____63499)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____63568  ->
                                          match uu____63568 with
                                          | (b,qual) ->
                                              let uu____63589 =
                                                bv_as_unique_ident b  in
                                              let uu____63590 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____63589, uu____63590,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____63601 -> failwith "unexpected")
                       | uu____63613 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____63744,num,uu____63746) ->
                            let c =
                              let uu____63767 =
                                let uu____63770 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____63770  in
                              ((l.FStar_Ident.ident), uu____63767,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____63790 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____63870 ->
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
        let uu____63896 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____63896;
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
        let uu____63926 = ts  in
        match uu____63926 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____63939 =
              let uu____63940 =
                let uu____63957 =
                  let uu____63966 =
                    let uu____63973 =
                      let uu____63974 =
                        let uu____63987 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____63987)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____63974  in
                    (uu____63973, FStar_Pervasives_Native.None)  in
                  [uu____63966]  in
                (false, false, uu____63957)  in
              FStar_Parser_AST.Tycon uu____63940  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____63939
  
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
              let uu____64076 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____64076 with
              | (bs,action_defn) ->
                  let uu____64083 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____64083 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____64093 = FStar_Options.print_implicits ()
                            in
                         if uu____64093
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____64103 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____64103 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____64120 =
                             let uu____64131 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____64131,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____64120  in
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
            let uu____64215 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____64215 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____64225 = FStar_Options.print_implicits ()  in
                  if uu____64225 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____64235 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____64235 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____64320) ->
          let uu____64329 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____64352 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____64370 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____64378 -> false
                    | uu____64395 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____64329 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____64433 se1 =
                 match uu____64433 with
                 | (datacon_ses1,tycons) ->
                     let uu____64459 = resugar_typ env datacon_ses1 se1  in
                     (match uu____64459 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____64474 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____64474 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____64509 =
                           let uu____64510 =
                             let uu____64511 =
                               let uu____64528 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____64528)  in
                             FStar_Parser_AST.Tycon uu____64511  in
                           decl'_to_decl se uu____64510  in
                         FStar_Pervasives_Native.Some uu____64509
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____64563,uu____64564,uu____64565,uu____64566,uu____64567)
                              ->
                              let uu____64574 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____64574
                          | uu____64577 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____64581 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____64588) ->
          let uu____64593 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_64601  ->
                    match uu___439_64601 with
                    | FStar_Syntax_Syntax.Projector (uu____64603,uu____64604)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____64606 -> true
                    | uu____64608 -> false))
             in
          if uu____64593
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
             | FStar_Parser_AST.Let (isrec,lets,uu____64643) ->
                 let uu____64672 =
                   let uu____64673 =
                     let uu____64674 =
                       let uu____64685 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____64685)  in
                     FStar_Parser_AST.TopLevelLet uu____64674  in
                   decl'_to_decl se uu____64673  in
                 FStar_Pervasives_Native.Some uu____64672
             | uu____64722 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____64727,fml) ->
          let uu____64729 =
            let uu____64730 =
              let uu____64731 =
                let uu____64736 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____64736)  in
              FStar_Parser_AST.Assume uu____64731  in
            decl'_to_decl se uu____64730  in
          FStar_Pervasives_Native.Some uu____64729
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____64738 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64738
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____64741 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64741
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____64751,t) ->
                let uu____64761 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64761
            | uu____64762 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____64770,t) ->
                let uu____64780 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64780
            | uu____64781 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____64805 -> failwith "Should not happen hopefully"  in
          let uu____64815 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____64815
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____64825 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____64825 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____64837 = FStar_Options.print_implicits ()  in
                 if uu____64837 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____64853 =
                 let uu____64854 =
                   let uu____64855 =
                     let uu____64872 =
                       let uu____64881 =
                         let uu____64888 =
                           let uu____64889 =
                             let uu____64902 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____64902)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____64889  in
                         (uu____64888, FStar_Pervasives_Native.None)  in
                       [uu____64881]  in
                     (false, false, uu____64872)  in
                   FStar_Parser_AST.Tycon uu____64855  in
                 decl'_to_decl se uu____64854  in
               FStar_Pervasives_Native.Some uu____64853)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____64934 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____64934
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____64938 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_64946  ->
                    match uu___440_64946 with
                    | FStar_Syntax_Syntax.Projector (uu____64948,uu____64949)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____64951 -> true
                    | uu____64953 -> false))
             in
          if uu____64938
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____64961 =
                 (let uu____64965 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____64965) || (FStar_List.isEmpty uvs)
                  in
               if uu____64961
               then resugar_term' env t
               else
                 (let uu____64970 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____64970 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____64979 = resugar_term' env t1  in
                      label universes uu____64979)
                in
             let uu____64980 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____64980)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____64987 =
            let uu____64988 =
              let uu____64989 =
                let uu____64996 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____65001 = resugar_term' env t  in
                (uu____64996, uu____65001)  in
              FStar_Parser_AST.Splice uu____64989  in
            decl'_to_decl se uu____64988  in
          FStar_Pervasives_Native.Some uu____64987
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____65004 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____65021 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____65037 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____65061 = noenv resugar_term'  in uu____65061 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____65079 = noenv resugar_sigelt'  in uu____65079 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____65097 = noenv resugar_comp'  in uu____65097 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____65120 = noenv resugar_pat'  in uu____65120 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____65154 = noenv resugar_binder'  in uu____65154 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____65179 = noenv resugar_tscheme'  in uu____65179 ts 
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
          let uu____65214 = noenv resugar_eff_decl'  in
          uu____65214 for_free r q ed
  