open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____55855 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____55855
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____55863 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____55863
  
let map_opt :
  'Auu____55873 'Auu____55874 .
    unit ->
      ('Auu____55873 -> 'Auu____55874 FStar_Pervasives_Native.option) ->
        'Auu____55873 Prims.list -> 'Auu____55874 Prims.list
  = fun uu____55890  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____55899 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____55899
      then
        let uu____55903 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____55903
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____55913 .
    ('Auu____55913 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____55913 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_55968  ->
            match uu___429_55968 with
            | (uu____55976,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____55983,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____55984)) -> false
            | (uu____55989,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____55990)) -> false
            | uu____55996 -> true))
  
let filter_pattern_imp :
  'Auu____56009 .
    ('Auu____56009 * Prims.bool) Prims.list ->
      ('Auu____56009 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____56044  ->
         match uu____56044 with
         | (uu____56051,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____56101 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____56114 = FStar_Options.print_universes ()  in
    if uu____56114
    then
      let uu____56118 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____56118 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____56182 ->
          let uu____56183 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____56183 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____56194 =
                      let uu____56195 =
                        let uu____56196 =
                          let uu____56208 = FStar_Util.string_of_int n1  in
                          (uu____56208, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____56196  in
                      FStar_Parser_AST.Const uu____56195  in
                    mk1 uu____56194 r
                | uu____56221 ->
                    let e1 =
                      let uu____56223 =
                        let uu____56224 =
                          let uu____56225 =
                            let uu____56237 = FStar_Util.string_of_int n1  in
                            (uu____56237, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____56225  in
                        FStar_Parser_AST.Const uu____56224  in
                      mk1 uu____56223 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____56251 =
                      let uu____56252 =
                        let uu____56259 = FStar_Ident.id_of_text "+"  in
                        (uu____56259, [e1; e2])  in
                      FStar_Parser_AST.Op uu____56252  in
                    mk1 uu____56251 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____56267 ->
               let t =
                 let uu____56271 =
                   let uu____56272 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____56272  in
                 mk1 uu____56271 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____56281 =
                        let uu____56282 =
                          let uu____56289 = resugar_universe x r  in
                          (acc, uu____56289, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____56282  in
                      mk1 uu____56281 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____56291 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____56303 =
              let uu____56309 =
                let uu____56311 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____56311  in
              (uu____56309, r)  in
            FStar_Ident.mk_ident uu____56303  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_56349 =
      match uu___430_56349 with
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
      | uu____56677 -> FStar_Pervasives_Native.None  in
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
    | uu____56817 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____56835 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____56835 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____56853 ->
               let op =
                 let uu____56859 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____56913) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____56859
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
      let uu____57240 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____57240 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____57310 ->
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
                (let uu____57422 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____57422
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____57458 =
      let uu____57459 = FStar_Syntax_Subst.compress t  in
      uu____57459.FStar_Syntax_Syntax.n  in
    match uu____57458 with
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
        let uu____57490 = string_to_op s  in
        (match uu____57490 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____57530 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____57547 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____57564 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____57575 -> true
    | uu____57577 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____57598 ->
        let uu____57600 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____57600
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____57614 = may_shorten lid  in
      if uu____57614 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____57759 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____57759  in
      let uu____57762 =
        let uu____57763 = FStar_Syntax_Subst.compress t  in
        uu____57763.FStar_Syntax_Syntax.n  in
      match uu____57762 with
      | FStar_Syntax_Syntax.Tm_delayed uu____57766 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____57791 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____57791
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____57794 =
              let uu____57797 = bv_as_unique_ident x  in [uu____57797]  in
            FStar_Ident.lid_of_ids uu____57794  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____57800 =
              let uu____57803 = bv_as_unique_ident x  in [uu____57803]  in
            FStar_Ident.lid_of_ids uu____57800  in
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
            let uu____57832 =
              let uu____57833 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____57833  in
            mk1 uu____57832
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
               | uu____57857 -> failwith "wrong projector format")
            else
              (let uu____57864 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____57868 =
                      let uu____57870 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____57870  in
                    let uu____57873 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____57868 <> uu____57873)
                  in
               if uu____57864
               then
                 let uu____57878 =
                   let uu____57879 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____57879  in
                 mk1 uu____57878
               else
                 (let uu____57882 =
                    let uu____57883 =
                      let uu____57894 = maybe_shorten_fv env fv  in
                      (uu____57894, [])  in
                    FStar_Parser_AST.Construct uu____57883  in
                  mk1 uu____57882))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____57912 = FStar_Options.print_universes ()  in
          if uu____57912
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
                   let uu____57943 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____57943  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____57966 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____57974 = FStar_Syntax_Syntax.is_teff t  in
          if uu____57974
          then
            let uu____57977 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____57977
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____57982 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____58003 -> ("Type", true)  in
          (match uu____57982 with
           | (nm,needs_app) ->
               let typ =
                 let uu____58015 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____58015  in
               let uu____58016 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____58016
               then
                 let uu____58019 =
                   let uu____58020 =
                     let uu____58027 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____58027, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____58020  in
                 mk1 uu____58019
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____58032) ->
          let uu____58057 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____58057 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58073 = FStar_Options.print_implicits ()  in
                 if uu____58073 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____58111  ->
                         match uu____58111 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____58151 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____58151 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58161 = FStar_Options.print_implicits ()  in
                 if uu____58161 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____58172 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____58172 FStar_List.rev  in
               let rec aux body3 uu___431_58197 =
                 match uu___431_58197 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____58213 =
            let uu____58218 =
              let uu____58219 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____58219]  in
            FStar_Syntax_Subst.open_term uu____58218 phi  in
          (match uu____58213 with
           | (x1,phi1) ->
               let b =
                 let uu____58241 =
                   let uu____58244 = FStar_List.hd x1  in
                   resugar_binder' env uu____58244 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____58241  in
               let uu____58251 =
                 let uu____58252 =
                   let uu____58257 = resugar_term' env phi1  in
                   (b, uu____58257)  in
                 FStar_Parser_AST.Refine uu____58252  in
               mk1 uu____58251)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____58259;
             FStar_Syntax_Syntax.vars = uu____58260;_},(e,uu____58262)::[])
          when
          (let uu____58303 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____58303) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_58352 =
            match uu___432_58352 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____58422 -> failwith "last of an empty list"  in
          let rec last_two uu___433_58461 =
            match uu___433_58461 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____58493::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____58571::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____58642  ->
                   match uu____58642 with
                   | (e2,qual) ->
                       let uu____58659 = resugar_term' env e2  in
                       let uu____58660 = resugar_imp env qual  in
                       (uu____58659, uu____58660)) args1
               in
            let uu____58661 = resugar_term' env e1  in
            match uu____58661 with
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
                     fun uu____58698  ->
                       match uu____58698 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____58714 = FStar_Options.print_implicits ()  in
            if uu____58714 then args else filter_imp args  in
          let uu____58729 = resugar_term_as_op e  in
          (match uu____58729 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____58742) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____58767  ->
                        match uu____58767 with
                        | (x,uu____58779) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____58788 =
                                   let uu____58789 =
                                     let uu____58790 =
                                       let uu____58797 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____58797, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____58790  in
                                   mk1 uu____58789  in
                                 FStar_Pervasives_Native.Some uu____58788))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____58801) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____58827)::[] -> b
                 | uu____58844 -> failwith "wrong arguments to dtuple"  in
               let uu____58854 =
                 let uu____58855 = FStar_Syntax_Subst.compress body  in
                 uu____58855.FStar_Syntax_Syntax.n  in
               (match uu____58854 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____58860) ->
                    let uu____58885 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____58885 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____58895 = FStar_Options.print_implicits ()
                              in
                           if uu____58895 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____58912 =
                           let uu____58913 =
                             let uu____58924 =
                               FStar_List.map
                                 (fun _58935  -> FStar_Util.Inl _58935) xs3
                                in
                             (uu____58924, body3)  in
                           FStar_Parser_AST.Sum uu____58913  in
                         mk1 uu____58912)
                | uu____58942 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____58965  ->
                              match uu____58965 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____58983) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____58992) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____59001 = FStar_List.hd args1  in
               (match uu____59001 with
                | (t1,uu____59015) ->
                    let uu____59020 =
                      let uu____59021 = FStar_Syntax_Subst.compress t1  in
                      uu____59021.FStar_Syntax_Syntax.n  in
                    (match uu____59020 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____59028 =
                           let uu____59029 =
                             let uu____59034 = resugar_term' env t1  in
                             (uu____59034, f)  in
                           FStar_Parser_AST.Project uu____59029  in
                         mk1 uu____59028
                     | uu____59035 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____59036) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____59060 =
                 match new_args with
                 | (a1,uu____59070)::(a2,uu____59072)::[] -> (a1, a2)
                 | uu____59099 -> failwith "wrong arguments to try_with"  in
               (match uu____59060 with
                | (body,handler) ->
                    let decomp term =
                      let uu____59121 =
                        let uu____59122 = FStar_Syntax_Subst.compress term
                           in
                        uu____59122.FStar_Syntax_Syntax.n  in
                      match uu____59121 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____59127) ->
                          let uu____59152 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____59152 with | (x1,e2) -> e2)
                      | uu____59159 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____59162 = decomp body  in
                      resugar_term' env uu____59162  in
                    let handler1 =
                      let uu____59164 = decomp handler  in
                      resugar_term' env uu____59164  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____59172,uu____59173,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____59205,uu____59206,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____59243 =
                            let uu____59244 =
                              let uu____59253 = resugar_body t11  in
                              (uu____59253, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____59244  in
                          mk1 uu____59243
                      | uu____59256 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____59314 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____59344) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59353) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59374) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____59472 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____59485 =
                   let uu____59486 = FStar_Syntax_Subst.compress body  in
                   uu____59486.FStar_Syntax_Syntax.n  in
                 match uu____59485 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____59491) ->
                     let uu____59516 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____59516 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____59526 =
                              FStar_Options.print_implicits ()  in
                            if uu____59526 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____59542 =
                            let uu____59551 =
                              let uu____59552 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____59552.FStar_Syntax_Syntax.n  in
                            match uu____59551 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____59570 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____59600 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____59644  ->
                                                     match uu____59644 with
                                                     | (e2,uu____59652) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____59600, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____59668 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____59668)
                                  | uu____59677 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____59570 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____59709 ->
                                let uu____59710 = resugar_term' env body2  in
                                ([], uu____59710)
                             in
                          (match uu____59542 with
                           | (pats,body3) ->
                               let uu____59727 = uncurry xs3 pats body3  in
                               (match uu____59727 with
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
                 | uu____59779 ->
                     if op = "forall"
                     then
                       let uu____59783 =
                         let uu____59784 =
                           let uu____59797 = resugar_term' env body  in
                           ([], [[]], uu____59797)  in
                         FStar_Parser_AST.QForall uu____59784  in
                       mk1 uu____59783
                     else
                       (let uu____59810 =
                          let uu____59811 =
                            let uu____59824 = resugar_term' env body  in
                            ([], [[]], uu____59824)  in
                          FStar_Parser_AST.QExists uu____59811  in
                        mk1 uu____59810)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____59853)::[] -> resugar b
                  | uu____59870 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____59882) ->
               let uu____59890 = FStar_List.hd args1  in
               (match uu____59890 with
                | (e1,uu____59904) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____59976  ->
                         match uu____59976 with
                         | (e1,qual) ->
                             let uu____59993 = resugar_term' env e1  in
                             let uu____59994 = resugar_imp env qual  in
                             (uu____59993, uu____59994)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____60010 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____60010 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____60058 =
                               let uu____60059 =
                                 let uu____60066 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____60066)  in
                               FStar_Parser_AST.Op uu____60059  in
                             mk1 uu____60058  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____60084  ->
                                  match uu____60084 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____60103 =
                      let uu____60104 =
                        let uu____60111 =
                          let uu____60114 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____60114
                           in
                        (op1, uu____60111)  in
                      FStar_Parser_AST.Op uu____60104  in
                    mk1 uu____60103
                | uu____60127 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____60196 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____60196 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____60242 =
                   let uu____60255 =
                     let uu____60260 = resugar_pat' env pat1 branch_bv  in
                     let uu____60261 = resugar_term' env e  in
                     (uu____60260, uu____60261)  in
                   (FStar_Pervasives_Native.None, uu____60255)  in
                 [uu____60242]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____60313,t1)::(pat2,uu____60316,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____60412 =
            let uu____60413 =
              let uu____60420 = resugar_term' env e  in
              let uu____60421 = resugar_term' env t1  in
              let uu____60422 = resugar_term' env t2  in
              (uu____60420, uu____60421, uu____60422)  in
            FStar_Parser_AST.If uu____60413  in
          mk1 uu____60412
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____60488 =
            match uu____60488 with
            | (pat,wopt,b) ->
                let uu____60530 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____60530 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____60582 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____60582
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____60586 =
            let uu____60587 =
              let uu____60602 = resugar_term' env e  in
              let uu____60603 = FStar_List.map resugar_branch branches  in
              (uu____60602, uu____60603)  in
            FStar_Parser_AST.Match uu____60587  in
          mk1 uu____60586
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____60649) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____60718 =
            let uu____60719 =
              let uu____60728 = resugar_term' env e  in
              (uu____60728, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____60719  in
          mk1 uu____60718
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____60757 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____60757 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____60811 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____60811
                    in
                 let uu____60818 =
                   let uu____60823 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____60823
                    in
                 match uu____60818 with
                 | (univs1,td) ->
                     let uu____60843 =
                       let uu____60850 =
                         let uu____60851 = FStar_Syntax_Subst.compress td  in
                         uu____60851.FStar_Syntax_Syntax.n  in
                       match uu____60850 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____60860,(t1,uu____60862)::(d,uu____60864)::[])
                           -> (t1, d)
                       | uu____60921 -> failwith "wrong let binding format"
                        in
                     (match uu____60843 with
                      | (typ,def) ->
                          let uu____60952 =
                            let uu____60968 =
                              let uu____60969 =
                                FStar_Syntax_Subst.compress def  in
                              uu____60969.FStar_Syntax_Syntax.n  in
                            match uu____60968 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____60989)
                                ->
                                let uu____61014 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____61014 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____61045 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____61045
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____61068 -> ([], def, false)  in
                          (match uu____60952 with
                           | (binders,term,is_pat_app) ->
                               let uu____61123 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____61134 =
                                       let uu____61135 =
                                         let uu____61136 =
                                           let uu____61143 =
                                             bv_as_unique_ident bv  in
                                           (uu____61143,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____61136
                                          in
                                       mk_pat uu____61135  in
                                     (uu____61134, term)
                                  in
                               (match uu____61123 with
                                | (pat,term1) ->
                                    let uu____61165 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____61208  ->
                                                  match uu____61208 with
                                                  | (bv,q) ->
                                                      let uu____61223 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____61223
                                                        (fun q1  ->
                                                           let uu____61235 =
                                                             let uu____61236
                                                               =
                                                               let uu____61243
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____61243,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____61236
                                                              in
                                                           mk_pat uu____61235)))
                                           in
                                        let uu____61246 =
                                          let uu____61251 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____61251)
                                           in
                                        let uu____61254 =
                                          universe_to_string univs1  in
                                        (uu____61246, uu____61254)
                                      else
                                        (let uu____61263 =
                                           let uu____61268 =
                                             resugar_term' env term1  in
                                           (pat, uu____61268)  in
                                         let uu____61269 =
                                           universe_to_string univs1  in
                                         (uu____61263, uu____61269))
                                       in
                                    (attrs_opt, uu____61165))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____61375 =
                   match uu____61375 with
                   | (attrs,(pb,univs1)) ->
                       let uu____61435 =
                         let uu____61437 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____61437  in
                       if uu____61435
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____61518) ->
          let s =
            let uu____61537 =
              let uu____61539 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____61539 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____61537  in
          let uu____61544 = mk1 FStar_Parser_AST.Wild  in label s uu____61544
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____61552 =
            let uu____61553 =
              let uu____61558 = resugar_term' env tm  in (uu____61558, qi1)
               in
            FStar_Parser_AST.Quote uu____61553  in
          mk1 uu____61552
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_61570 =
            match uu___434_61570 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____61578,(uu____61579,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____61640 =
                        let uu____61641 =
                          let uu____61650 = resugar_seq t11  in
                          (uu____61650, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____61641  in
                      mk1 uu____61640
                  | uu____61653 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____61697  ->
                         match uu____61697 with
                         | (x,uu____61705) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____61710 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____61728,t1) ->
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
               let uu____61768 = FStar_Options.print_universes ()  in
               if uu____61768
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
               let uu____61832 = FStar_Options.print_universes ()  in
               if uu____61832
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
            let uu____61876 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____61876, FStar_Parser_AST.Nothing)  in
          let uu____61877 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____61877
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____61900 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____61900
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____61985 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____61985, (FStar_Pervasives_Native.snd post))  in
                    let uu____61996 =
                      let uu____62005 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____62005 then [] else [pre]  in
                    let uu____62040 =
                      let uu____62049 =
                        let uu____62058 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____62058 then [] else [pats]  in
                      FStar_List.append [post1] uu____62049  in
                    FStar_List.append uu____61996 uu____62040
                | uu____62117 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____62151  ->
                   match uu____62151 with
                   | (e,uu____62163) ->
                       let uu____62168 = resugar_term' env e  in
                       (uu____62168, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_62193 =
              match uu___435_62193 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____62226 = resugar_term' env e  in
                         (uu____62226, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____62231 -> aux l tl1)
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
        let uu____62278 = b  in
        match uu____62278 with
        | (x,aq) ->
            let uu____62287 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____62287
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____62301 =
                       let uu____62302 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____62302  in
                     FStar_Parser_AST.mk_binder uu____62301 r
                       FStar_Parser_AST.Type_level imp
                 | uu____62303 ->
                     let uu____62304 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____62304
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____62309 =
                          let uu____62310 =
                            let uu____62315 = bv_as_unique_ident x  in
                            (uu____62315, e)  in
                          FStar_Parser_AST.Annotated uu____62310  in
                        FStar_Parser_AST.mk_binder uu____62309 r
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
              let uu____62335 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____62335  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____62339 =
                if used
                then
                  let uu____62341 =
                    let uu____62348 = bv_as_unique_ident v1  in
                    (uu____62348, aqual)  in
                  FStar_Parser_AST.PatVar uu____62341
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____62339  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____62355;
                  FStar_Syntax_Syntax.vars = uu____62356;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____62366 = FStar_Options.print_bound_var_types ()  in
                if uu____62366
                then
                  let uu____62369 =
                    let uu____62370 =
                      let uu____62381 =
                        let uu____62388 = resugar_term' env typ  in
                        (uu____62388, FStar_Pervasives_Native.None)  in
                      (pat, uu____62381)  in
                    FStar_Parser_AST.PatAscribed uu____62370  in
                  mk1 uu____62369
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
          let uu____62409 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____62409
            (fun aqual  ->
               let uu____62421 =
                 let uu____62426 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _62437  -> FStar_Pervasives_Native.Some _62437)
                   uu____62426
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____62421)

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
          (let uu____62499 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____62499) &&
            (let uu____62502 =
               FStar_List.existsML
                 (fun uu____62515  ->
                    match uu____62515 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____62537)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____62542 -> false
                          | uu____62544 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____62502)
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
            let uu____62612 = may_drop_implicits args  in
            if uu____62612 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____62637  ->
                 match uu____62637 with
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
              ((let uu____62692 =
                  let uu____62694 =
                    let uu____62696 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____62696  in
                  Prims.op_Negation uu____62694  in
                if uu____62692
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
              let uu____62740 = filter_pattern_imp args  in
              (match uu____62740 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____62790 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____62790 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____62809 =
                       let uu____62815 =
                         let uu____62817 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____62817
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____62815)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____62809);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____62870  ->
                        match uu____62870 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____62887 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____62887)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____62895;
                 FStar_Syntax_Syntax.fv_delta = uu____62896;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____62925 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____62925 FStar_List.rev  in
              let args1 =
                let uu____62941 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____62961  ->
                          match uu____62961 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____62941 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____63039 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____63039
                | (hd1::tl1,hd2::tl2) ->
                    let uu____63062 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____63062
                 in
              let args2 =
                let uu____63080 = map21 fields1 args1  in
                FStar_All.pipe_right uu____63080 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____63124 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____63124 with
               | FStar_Pervasives_Native.Some (op,uu____63136) ->
                   let uu____63153 =
                     let uu____63154 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____63154  in
                   mk1 uu____63153
               | FStar_Pervasives_Native.None  ->
                   let uu____63164 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____63164 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____63169 ->
              let uu____63170 =
                let uu____63171 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____63171  in
              mk1 uu____63170
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
          let uu____63211 =
            let uu____63214 =
              let uu____63215 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____63215  in
            FStar_Pervasives_Native.Some uu____63214  in
          FStar_Pervasives_Native.Some uu____63211

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
          let uu____63227 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____63227

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_63235  ->
    match uu___436_63235 with
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
    | FStar_Syntax_Syntax.Reflectable uu____63242 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____63243 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____63244 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____63249 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____63258 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____63267 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_63273  ->
    match uu___437_63273 with
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
            (tylid,uvs,bs,t,uu____63316,datacons) ->
            let uu____63326 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____63354,uu____63355,uu____63356,inductive_lid,uu____63358,uu____63359)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____63366 -> failwith "unexpected"))
               in
            (match uu____63326 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____63387 = FStar_Options.print_implicits ()  in
                   if uu____63387 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____63404 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_63411  ->
                             match uu___438_63411 with
                             | FStar_Syntax_Syntax.RecordType uu____63413 ->
                                 true
                             | uu____63423 -> false))
                      in
                   if uu____63404
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____63477,univs1,term,uu____63480,num,uu____63482)
                           ->
                           let uu____63489 =
                             let uu____63490 =
                               FStar_Syntax_Subst.compress term  in
                             uu____63490.FStar_Syntax_Syntax.n  in
                           (match uu____63489 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____63504)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____63573  ->
                                          match uu____63573 with
                                          | (b,qual) ->
                                              let uu____63594 =
                                                bv_as_unique_ident b  in
                                              let uu____63595 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____63594, uu____63595,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____63606 -> failwith "unexpected")
                       | uu____63618 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____63749,num,uu____63751) ->
                            let c =
                              let uu____63772 =
                                let uu____63775 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____63775  in
                              ((l.FStar_Ident.ident), uu____63772,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____63795 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____63875 ->
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
        let uu____63901 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____63901;
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
        let uu____63931 = ts  in
        match uu____63931 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____63944 =
              let uu____63945 =
                let uu____63962 =
                  let uu____63971 =
                    let uu____63978 =
                      let uu____63979 =
                        let uu____63992 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____63992)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____63979  in
                    (uu____63978, FStar_Pervasives_Native.None)  in
                  [uu____63971]  in
                (false, false, uu____63962)  in
              FStar_Parser_AST.Tycon uu____63945  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____63944
  
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
              let uu____64081 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____64081 with
              | (bs,action_defn) ->
                  let uu____64088 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____64088 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____64098 = FStar_Options.print_implicits ()
                            in
                         if uu____64098
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____64108 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____64108 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____64125 =
                             let uu____64136 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____64136,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____64125  in
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
            let uu____64220 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____64220 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____64230 = FStar_Options.print_implicits ()  in
                  if uu____64230 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____64240 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____64240 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____64325) ->
          let uu____64334 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____64357 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____64375 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____64383 -> false
                    | uu____64400 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____64334 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____64438 se1 =
                 match uu____64438 with
                 | (datacon_ses1,tycons) ->
                     let uu____64464 = resugar_typ env datacon_ses1 se1  in
                     (match uu____64464 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____64479 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____64479 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____64514 =
                           let uu____64515 =
                             let uu____64516 =
                               let uu____64533 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____64533)  in
                             FStar_Parser_AST.Tycon uu____64516  in
                           decl'_to_decl se uu____64515  in
                         FStar_Pervasives_Native.Some uu____64514
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____64568,uu____64569,uu____64570,uu____64571,uu____64572)
                              ->
                              let uu____64579 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____64579
                          | uu____64582 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____64586 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____64593) ->
          let uu____64598 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_64606  ->
                    match uu___439_64606 with
                    | FStar_Syntax_Syntax.Projector (uu____64608,uu____64609)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____64611 -> true
                    | uu____64613 -> false))
             in
          if uu____64598
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
             | FStar_Parser_AST.Let (isrec,lets,uu____64648) ->
                 let uu____64677 =
                   let uu____64678 =
                     let uu____64679 =
                       let uu____64690 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____64690)  in
                     FStar_Parser_AST.TopLevelLet uu____64679  in
                   decl'_to_decl se uu____64678  in
                 FStar_Pervasives_Native.Some uu____64677
             | uu____64727 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____64732,fml) ->
          let uu____64734 =
            let uu____64735 =
              let uu____64736 =
                let uu____64741 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____64741)  in
              FStar_Parser_AST.Assume uu____64736  in
            decl'_to_decl se uu____64735  in
          FStar_Pervasives_Native.Some uu____64734
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____64743 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64743
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____64746 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64746
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____64756,t) ->
                let uu____64766 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64766
            | uu____64767 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____64775,t) ->
                let uu____64785 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64785
            | uu____64786 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____64810 -> failwith "Should not happen hopefully"  in
          let uu____64820 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____64820
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____64830 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____64830 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____64842 = FStar_Options.print_implicits ()  in
                 if uu____64842 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____64858 =
                 let uu____64859 =
                   let uu____64860 =
                     let uu____64877 =
                       let uu____64886 =
                         let uu____64893 =
                           let uu____64894 =
                             let uu____64907 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____64907)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____64894  in
                         (uu____64893, FStar_Pervasives_Native.None)  in
                       [uu____64886]  in
                     (false, false, uu____64877)  in
                   FStar_Parser_AST.Tycon uu____64860  in
                 decl'_to_decl se uu____64859  in
               FStar_Pervasives_Native.Some uu____64858)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____64939 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____64939
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____64943 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_64951  ->
                    match uu___440_64951 with
                    | FStar_Syntax_Syntax.Projector (uu____64953,uu____64954)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____64956 -> true
                    | uu____64958 -> false))
             in
          if uu____64943
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____64966 =
                 (let uu____64970 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____64970) || (FStar_List.isEmpty uvs)
                  in
               if uu____64966
               then resugar_term' env t
               else
                 (let uu____64975 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____64975 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____64984 = resugar_term' env t1  in
                      label universes uu____64984)
                in
             let uu____64985 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____64985)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____64992 =
            let uu____64993 =
              let uu____64994 =
                let uu____65001 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____65006 = resugar_term' env t  in
                (uu____65001, uu____65006)  in
              FStar_Parser_AST.Splice uu____64994  in
            decl'_to_decl se uu____64993  in
          FStar_Pervasives_Native.Some uu____64992
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____65009 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____65026 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____65042 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____65066 = noenv resugar_term'  in uu____65066 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____65084 = noenv resugar_sigelt'  in uu____65084 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____65102 = noenv resugar_comp'  in uu____65102 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____65125 = noenv resugar_pat'  in uu____65125 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____65159 = noenv resugar_binder'  in uu____65159 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____65184 = noenv resugar_tscheme'  in uu____65184 ts 
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
          let uu____65219 = noenv resugar_eff_decl'  in
          uu____65219 for_free r q ed
  