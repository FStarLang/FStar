open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____55924 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____55924
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____55932 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____55932
  
let map_opt :
  'Auu____55942 'Auu____55943 .
    unit ->
      ('Auu____55942 -> 'Auu____55943 FStar_Pervasives_Native.option) ->
        'Auu____55942 Prims.list -> 'Auu____55943 Prims.list
  = fun uu____55959  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____55968 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____55968
      then
        let uu____55972 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____55972
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____55982 .
    ('Auu____55982 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____55982 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_56037  ->
            match uu___429_56037 with
            | (uu____56045,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56052,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56053)) -> false
            | (uu____56058,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56059)) -> false
            | uu____56065 -> true))
  
let filter_pattern_imp :
  'Auu____56078 .
    ('Auu____56078 * Prims.bool) Prims.list ->
      ('Auu____56078 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____56113  ->
         match uu____56113 with
         | (uu____56120,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____56170 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____56183 = FStar_Options.print_universes ()  in
    if uu____56183
    then
      let uu____56187 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____56187 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____56251 ->
          let uu____56252 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____56252 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____56263 =
                      let uu____56264 =
                        let uu____56265 =
                          let uu____56277 = FStar_Util.string_of_int n1  in
                          (uu____56277, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____56265  in
                      FStar_Parser_AST.Const uu____56264  in
                    mk1 uu____56263 r
                | uu____56290 ->
                    let e1 =
                      let uu____56292 =
                        let uu____56293 =
                          let uu____56294 =
                            let uu____56306 = FStar_Util.string_of_int n1  in
                            (uu____56306, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____56294  in
                        FStar_Parser_AST.Const uu____56293  in
                      mk1 uu____56292 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____56320 =
                      let uu____56321 =
                        let uu____56328 = FStar_Ident.id_of_text "+"  in
                        (uu____56328, [e1; e2])  in
                      FStar_Parser_AST.Op uu____56321  in
                    mk1 uu____56320 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____56336 ->
               let t =
                 let uu____56340 =
                   let uu____56341 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____56341  in
                 mk1 uu____56340 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____56350 =
                        let uu____56351 =
                          let uu____56358 = resugar_universe x r  in
                          (acc, uu____56358, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____56351  in
                      mk1 uu____56350 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____56360 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____56372 =
              let uu____56378 =
                let uu____56380 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____56380  in
              (uu____56378, r)  in
            FStar_Ident.mk_ident uu____56372  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_56418 =
      match uu___430_56418 with
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
      | uu____56746 -> FStar_Pervasives_Native.None  in
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
    | uu____56886 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____56904 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____56904 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____56922 ->
               let op =
                 let uu____56928 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____56982) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____56928
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
      let uu____57309 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____57309 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____57379 ->
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
                (let uu____57491 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____57491
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____57527 =
      let uu____57528 = FStar_Syntax_Subst.compress t  in
      uu____57528.FStar_Syntax_Syntax.n  in
    match uu____57527 with
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
        let uu____57559 = string_to_op s  in
        (match uu____57559 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____57599 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____57616 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____57633 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____57644 -> true
    | uu____57646 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____57667 ->
        let uu____57669 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____57669
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____57683 = may_shorten lid  in
      if uu____57683 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____57828 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____57828  in
      let uu____57831 =
        let uu____57832 = FStar_Syntax_Subst.compress t  in
        uu____57832.FStar_Syntax_Syntax.n  in
      match uu____57831 with
      | FStar_Syntax_Syntax.Tm_delayed uu____57835 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____57860 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____57860
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____57863 =
              let uu____57866 = bv_as_unique_ident x  in [uu____57866]  in
            FStar_Ident.lid_of_ids uu____57863  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____57869 =
              let uu____57872 = bv_as_unique_ident x  in [uu____57872]  in
            FStar_Ident.lid_of_ids uu____57869  in
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
            let uu____57901 =
              let uu____57902 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____57902  in
            mk1 uu____57901
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
               | uu____57926 -> failwith "wrong projector format")
            else
              (let uu____57933 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____57937 =
                      let uu____57939 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____57939  in
                    let uu____57942 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____57937 <> uu____57942)
                  in
               if uu____57933
               then
                 let uu____57947 =
                   let uu____57948 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____57948  in
                 mk1 uu____57947
               else
                 (let uu____57951 =
                    let uu____57952 =
                      let uu____57963 = maybe_shorten_fv env fv  in
                      (uu____57963, [])  in
                    FStar_Parser_AST.Construct uu____57952  in
                  mk1 uu____57951))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____57981 = FStar_Options.print_universes ()  in
          if uu____57981
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
                   let uu____58012 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____58012  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____58035 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____58043 = FStar_Syntax_Syntax.is_teff t  in
          if uu____58043
          then
            let uu____58046 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____58046
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____58051 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____58072 -> ("Type", true)  in
          (match uu____58051 with
           | (nm,needs_app) ->
               let typ =
                 let uu____58084 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____58084  in
               let uu____58085 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____58085
               then
                 let uu____58088 =
                   let uu____58089 =
                     let uu____58096 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____58096, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____58089  in
                 mk1 uu____58088
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____58101) ->
          let uu____58126 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____58126 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58142 = FStar_Options.print_implicits ()  in
                 if uu____58142 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____58180  ->
                         match uu____58180 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____58220 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____58220 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58230 = FStar_Options.print_implicits ()  in
                 if uu____58230 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____58241 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____58241 FStar_List.rev  in
               let rec aux body3 uu___431_58266 =
                 match uu___431_58266 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____58282 =
            let uu____58287 =
              let uu____58288 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____58288]  in
            FStar_Syntax_Subst.open_term uu____58287 phi  in
          (match uu____58282 with
           | (x1,phi1) ->
               let b =
                 let uu____58310 =
                   let uu____58313 = FStar_List.hd x1  in
                   resugar_binder' env uu____58313 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____58310  in
               let uu____58320 =
                 let uu____58321 =
                   let uu____58326 = resugar_term' env phi1  in
                   (b, uu____58326)  in
                 FStar_Parser_AST.Refine uu____58321  in
               mk1 uu____58320)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____58328;
             FStar_Syntax_Syntax.vars = uu____58329;_},(e,uu____58331)::[])
          when
          (let uu____58372 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____58372) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_58421 =
            match uu___432_58421 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____58491 -> failwith "last of an empty list"  in
          let rec last_two uu___433_58530 =
            match uu___433_58530 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____58562::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____58640::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____58711  ->
                   match uu____58711 with
                   | (e2,qual) ->
                       let uu____58728 = resugar_term' env e2  in
                       let uu____58729 = resugar_imp env qual  in
                       (uu____58728, uu____58729)) args1
               in
            let uu____58730 = resugar_term' env e1  in
            match uu____58730 with
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
                     fun uu____58767  ->
                       match uu____58767 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____58783 = FStar_Options.print_implicits ()  in
            if uu____58783 then args else filter_imp args  in
          let uu____58798 = resugar_term_as_op e  in
          (match uu____58798 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____58811) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____58836  ->
                        match uu____58836 with
                        | (x,uu____58848) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____58857 =
                                   let uu____58858 =
                                     let uu____58859 =
                                       let uu____58866 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____58866, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____58859  in
                                   mk1 uu____58858  in
                                 FStar_Pervasives_Native.Some uu____58857))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____58870) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____58896)::[] -> b
                 | uu____58913 -> failwith "wrong arguments to dtuple"  in
               let uu____58923 =
                 let uu____58924 = FStar_Syntax_Subst.compress body  in
                 uu____58924.FStar_Syntax_Syntax.n  in
               (match uu____58923 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____58929) ->
                    let uu____58954 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____58954 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____58964 = FStar_Options.print_implicits ()
                              in
                           if uu____58964 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____58981 =
                           let uu____58982 =
                             let uu____58993 =
                               FStar_List.map
                                 (fun _59004  -> FStar_Util.Inl _59004) xs3
                                in
                             (uu____58993, body3)  in
                           FStar_Parser_AST.Sum uu____58982  in
                         mk1 uu____58981)
                | uu____59011 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____59034  ->
                              match uu____59034 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____59052) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____59061) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____59070 = FStar_List.hd args1  in
               (match uu____59070 with
                | (t1,uu____59084) ->
                    let uu____59089 =
                      let uu____59090 = FStar_Syntax_Subst.compress t1  in
                      uu____59090.FStar_Syntax_Syntax.n  in
                    (match uu____59089 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____59097 =
                           let uu____59098 =
                             let uu____59103 = resugar_term' env t1  in
                             (uu____59103, f)  in
                           FStar_Parser_AST.Project uu____59098  in
                         mk1 uu____59097
                     | uu____59104 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____59105) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____59129 =
                 match new_args with
                 | (a1,uu____59139)::(a2,uu____59141)::[] -> (a1, a2)
                 | uu____59168 -> failwith "wrong arguments to try_with"  in
               (match uu____59129 with
                | (body,handler) ->
                    let decomp term =
                      let uu____59190 =
                        let uu____59191 = FStar_Syntax_Subst.compress term
                           in
                        uu____59191.FStar_Syntax_Syntax.n  in
                      match uu____59190 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____59196) ->
                          let uu____59221 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____59221 with | (x1,e2) -> e2)
                      | uu____59228 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____59231 = decomp body  in
                      resugar_term' env uu____59231  in
                    let handler1 =
                      let uu____59233 = decomp handler  in
                      resugar_term' env uu____59233  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____59241,uu____59242,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____59274,uu____59275,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____59312 =
                            let uu____59313 =
                              let uu____59322 = resugar_body t11  in
                              (uu____59322, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____59313  in
                          mk1 uu____59312
                      | uu____59325 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____59383 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____59413) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59422) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59443) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____59541 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____59554 =
                   let uu____59555 = FStar_Syntax_Subst.compress body  in
                   uu____59555.FStar_Syntax_Syntax.n  in
                 match uu____59554 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____59560) ->
                     let uu____59585 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____59585 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____59595 =
                              FStar_Options.print_implicits ()  in
                            if uu____59595 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____59611 =
                            let uu____59620 =
                              let uu____59621 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____59621.FStar_Syntax_Syntax.n  in
                            match uu____59620 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____59639 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____59669 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____59713  ->
                                                     match uu____59713 with
                                                     | (e2,uu____59721) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____59669, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____59737 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____59737)
                                  | uu____59746 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____59639 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____59778 ->
                                let uu____59779 = resugar_term' env body2  in
                                ([], uu____59779)
                             in
                          (match uu____59611 with
                           | (pats,body3) ->
                               let uu____59796 = uncurry xs3 pats body3  in
                               (match uu____59796 with
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
                 | uu____59848 ->
                     if op = "forall"
                     then
                       let uu____59852 =
                         let uu____59853 =
                           let uu____59866 = resugar_term' env body  in
                           ([], [[]], uu____59866)  in
                         FStar_Parser_AST.QForall uu____59853  in
                       mk1 uu____59852
                     else
                       (let uu____59879 =
                          let uu____59880 =
                            let uu____59893 = resugar_term' env body  in
                            ([], [[]], uu____59893)  in
                          FStar_Parser_AST.QExists uu____59880  in
                        mk1 uu____59879)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____59922)::[] -> resugar b
                  | uu____59939 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____59951) ->
               let uu____59959 = FStar_List.hd args1  in
               (match uu____59959 with
                | (e1,uu____59973) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____60045  ->
                         match uu____60045 with
                         | (e1,qual) ->
                             let uu____60062 = resugar_term' env e1  in
                             let uu____60063 = resugar_imp env qual  in
                             (uu____60062, uu____60063)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____60079 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____60079 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____60127 =
                               let uu____60128 =
                                 let uu____60135 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____60135)  in
                               FStar_Parser_AST.Op uu____60128  in
                             mk1 uu____60127  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____60153  ->
                                  match uu____60153 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____60172 =
                      let uu____60173 =
                        let uu____60180 =
                          let uu____60183 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____60183
                           in
                        (op1, uu____60180)  in
                      FStar_Parser_AST.Op uu____60173  in
                    mk1 uu____60172
                | uu____60196 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____60265 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____60265 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____60311 =
                   let uu____60324 =
                     let uu____60329 = resugar_pat' env pat1 branch_bv  in
                     let uu____60330 = resugar_term' env e  in
                     (uu____60329, uu____60330)  in
                   (FStar_Pervasives_Native.None, uu____60324)  in
                 [uu____60311]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____60382,t1)::(pat2,uu____60385,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____60481 =
            let uu____60482 =
              let uu____60489 = resugar_term' env e  in
              let uu____60490 = resugar_term' env t1  in
              let uu____60491 = resugar_term' env t2  in
              (uu____60489, uu____60490, uu____60491)  in
            FStar_Parser_AST.If uu____60482  in
          mk1 uu____60481
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____60557 =
            match uu____60557 with
            | (pat,wopt,b) ->
                let uu____60599 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____60599 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____60651 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____60651
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____60655 =
            let uu____60656 =
              let uu____60671 = resugar_term' env e  in
              let uu____60672 = FStar_List.map resugar_branch branches  in
              (uu____60671, uu____60672)  in
            FStar_Parser_AST.Match uu____60656  in
          mk1 uu____60655
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____60718) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____60787 =
            let uu____60788 =
              let uu____60797 = resugar_term' env e  in
              (uu____60797, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____60788  in
          mk1 uu____60787
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____60826 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____60826 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____60880 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____60880
                    in
                 let uu____60887 =
                   let uu____60892 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____60892
                    in
                 match uu____60887 with
                 | (univs1,td) ->
                     let uu____60912 =
                       let uu____60919 =
                         let uu____60920 = FStar_Syntax_Subst.compress td  in
                         uu____60920.FStar_Syntax_Syntax.n  in
                       match uu____60919 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____60929,(t1,uu____60931)::(d,uu____60933)::[])
                           -> (t1, d)
                       | uu____60990 -> failwith "wrong let binding format"
                        in
                     (match uu____60912 with
                      | (typ,def) ->
                          let uu____61021 =
                            let uu____61037 =
                              let uu____61038 =
                                FStar_Syntax_Subst.compress def  in
                              uu____61038.FStar_Syntax_Syntax.n  in
                            match uu____61037 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____61058)
                                ->
                                let uu____61083 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____61083 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____61114 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____61114
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____61137 -> ([], def, false)  in
                          (match uu____61021 with
                           | (binders,term,is_pat_app) ->
                               let uu____61192 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____61203 =
                                       let uu____61204 =
                                         let uu____61205 =
                                           let uu____61212 =
                                             bv_as_unique_ident bv  in
                                           (uu____61212,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____61205
                                          in
                                       mk_pat uu____61204  in
                                     (uu____61203, term)
                                  in
                               (match uu____61192 with
                                | (pat,term1) ->
                                    let uu____61234 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____61277  ->
                                                  match uu____61277 with
                                                  | (bv,q) ->
                                                      let uu____61292 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____61292
                                                        (fun q1  ->
                                                           let uu____61304 =
                                                             let uu____61305
                                                               =
                                                               let uu____61312
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____61312,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____61305
                                                              in
                                                           mk_pat uu____61304)))
                                           in
                                        let uu____61315 =
                                          let uu____61320 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____61320)
                                           in
                                        let uu____61323 =
                                          universe_to_string univs1  in
                                        (uu____61315, uu____61323)
                                      else
                                        (let uu____61332 =
                                           let uu____61337 =
                                             resugar_term' env term1  in
                                           (pat, uu____61337)  in
                                         let uu____61338 =
                                           universe_to_string univs1  in
                                         (uu____61332, uu____61338))
                                       in
                                    (attrs_opt, uu____61234))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____61444 =
                   match uu____61444 with
                   | (attrs,(pb,univs1)) ->
                       let uu____61504 =
                         let uu____61506 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____61506  in
                       if uu____61504
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____61587) ->
          let s =
            let uu____61606 =
              let uu____61608 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____61608 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____61606  in
          let uu____61613 = mk1 FStar_Parser_AST.Wild  in label s uu____61613
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____61621 =
            let uu____61622 =
              let uu____61627 = resugar_term' env tm  in (uu____61627, qi1)
               in
            FStar_Parser_AST.Quote uu____61622  in
          mk1 uu____61621
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_61639 =
            match uu___434_61639 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____61647,(uu____61648,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____61709 =
                        let uu____61710 =
                          let uu____61719 = resugar_seq t11  in
                          (uu____61719, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____61710  in
                      mk1 uu____61709
                  | uu____61722 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____61766  ->
                         match uu____61766 with
                         | (x,uu____61774) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____61779 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____61797,t1) ->
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
               let uu____61837 = FStar_Options.print_universes ()  in
               if uu____61837
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
               let uu____61901 = FStar_Options.print_universes ()  in
               if uu____61901
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
            let uu____61945 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____61945, FStar_Parser_AST.Nothing)  in
          let uu____61946 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____61946
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____61969 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____61969
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____62054 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____62054, (FStar_Pervasives_Native.snd post))  in
                    let uu____62065 =
                      let uu____62074 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____62074 then [] else [pre]  in
                    let uu____62109 =
                      let uu____62118 =
                        let uu____62127 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____62127 then [] else [pats]  in
                      FStar_List.append [post1] uu____62118  in
                    FStar_List.append uu____62065 uu____62109
                | uu____62186 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____62220  ->
                   match uu____62220 with
                   | (e,uu____62232) ->
                       let uu____62237 = resugar_term' env e  in
                       (uu____62237, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_62262 =
              match uu___435_62262 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____62295 = resugar_term' env e  in
                         (uu____62295, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____62300 -> aux l tl1)
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
        let uu____62347 = b  in
        match uu____62347 with
        | (x,aq) ->
            let uu____62356 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____62356
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____62370 =
                       let uu____62371 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____62371  in
                     FStar_Parser_AST.mk_binder uu____62370 r
                       FStar_Parser_AST.Type_level imp
                 | uu____62372 ->
                     let uu____62373 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____62373
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____62378 =
                          let uu____62379 =
                            let uu____62384 = bv_as_unique_ident x  in
                            (uu____62384, e)  in
                          FStar_Parser_AST.Annotated uu____62379  in
                        FStar_Parser_AST.mk_binder uu____62378 r
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
              let uu____62404 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____62404  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____62408 =
                if used
                then
                  let uu____62410 =
                    let uu____62417 = bv_as_unique_ident v1  in
                    (uu____62417, aqual)  in
                  FStar_Parser_AST.PatVar uu____62410
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____62408  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____62424;
                  FStar_Syntax_Syntax.vars = uu____62425;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____62435 = FStar_Options.print_bound_var_types ()  in
                if uu____62435
                then
                  let uu____62438 =
                    let uu____62439 =
                      let uu____62450 =
                        let uu____62457 = resugar_term' env typ  in
                        (uu____62457, FStar_Pervasives_Native.None)  in
                      (pat, uu____62450)  in
                    FStar_Parser_AST.PatAscribed uu____62439  in
                  mk1 uu____62438
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
          let uu____62478 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____62478
            (fun aqual  ->
               let uu____62490 =
                 let uu____62495 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _62506  -> FStar_Pervasives_Native.Some _62506)
                   uu____62495
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____62490)

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
          (let uu____62568 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____62568) &&
            (let uu____62571 =
               FStar_List.existsML
                 (fun uu____62584  ->
                    match uu____62584 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____62606)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____62611 -> false
                          | uu____62613 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____62571)
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
            let uu____62681 = may_drop_implicits args  in
            if uu____62681 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____62706  ->
                 match uu____62706 with
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
              ((let uu____62761 =
                  let uu____62763 =
                    let uu____62765 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____62765  in
                  Prims.op_Negation uu____62763  in
                if uu____62761
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
              let uu____62809 = filter_pattern_imp args  in
              (match uu____62809 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____62859 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____62859 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____62878 =
                       let uu____62884 =
                         let uu____62886 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____62886
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____62884)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____62878);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____62939  ->
                        match uu____62939 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____62956 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____62956)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____62964;
                 FStar_Syntax_Syntax.fv_delta = uu____62965;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____62994 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____62994 FStar_List.rev  in
              let args1 =
                let uu____63010 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____63030  ->
                          match uu____63030 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____63010 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____63108 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____63108
                | (hd1::tl1,hd2::tl2) ->
                    let uu____63131 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____63131
                 in
              let args2 =
                let uu____63149 = map21 fields1 args1  in
                FStar_All.pipe_right uu____63149 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____63193 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____63193 with
               | FStar_Pervasives_Native.Some (op,uu____63205) ->
                   let uu____63222 =
                     let uu____63223 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____63223  in
                   mk1 uu____63222
               | FStar_Pervasives_Native.None  ->
                   let uu____63233 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____63233 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____63238 ->
              let uu____63239 =
                let uu____63240 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____63240  in
              mk1 uu____63239
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
          let uu____63280 =
            let uu____63283 =
              let uu____63284 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____63284  in
            FStar_Pervasives_Native.Some uu____63283  in
          FStar_Pervasives_Native.Some uu____63280

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
          let uu____63296 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____63296

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_63304  ->
    match uu___436_63304 with
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
    | FStar_Syntax_Syntax.Reflectable uu____63311 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____63312 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____63313 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____63318 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____63327 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____63336 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_63342  ->
    match uu___437_63342 with
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
            (tylid,uvs,bs,t,uu____63385,datacons) ->
            let uu____63395 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____63423,uu____63424,uu____63425,inductive_lid,uu____63427,uu____63428)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____63435 -> failwith "unexpected"))
               in
            (match uu____63395 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____63456 = FStar_Options.print_implicits ()  in
                   if uu____63456 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____63473 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_63480  ->
                             match uu___438_63480 with
                             | FStar_Syntax_Syntax.RecordType uu____63482 ->
                                 true
                             | uu____63492 -> false))
                      in
                   if uu____63473
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____63546,univs1,term,uu____63549,num,uu____63551)
                           ->
                           let uu____63558 =
                             let uu____63559 =
                               FStar_Syntax_Subst.compress term  in
                             uu____63559.FStar_Syntax_Syntax.n  in
                           (match uu____63558 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____63573)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____63642  ->
                                          match uu____63642 with
                                          | (b,qual) ->
                                              let uu____63663 =
                                                bv_as_unique_ident b  in
                                              let uu____63664 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____63663, uu____63664,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____63675 -> failwith "unexpected")
                       | uu____63687 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____63818,num,uu____63820) ->
                            let c =
                              let uu____63841 =
                                let uu____63844 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____63844  in
                              ((l.FStar_Ident.ident), uu____63841,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____63864 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____63944 ->
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
        let uu____63970 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____63970;
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
        let uu____64000 = ts  in
        match uu____64000 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____64013 =
              let uu____64014 =
                let uu____64031 =
                  let uu____64040 =
                    let uu____64047 =
                      let uu____64048 =
                        let uu____64061 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____64061)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____64048  in
                    (uu____64047, FStar_Pervasives_Native.None)  in
                  [uu____64040]  in
                (false, false, uu____64031)  in
              FStar_Parser_AST.Tycon uu____64014  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____64013
  
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
              let uu____64150 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____64150 with
              | (bs,action_defn) ->
                  let uu____64157 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____64157 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____64167 = FStar_Options.print_implicits ()
                            in
                         if uu____64167
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____64177 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____64177 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____64194 =
                             let uu____64205 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____64205,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____64194  in
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
            let uu____64289 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____64289 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____64299 = FStar_Options.print_implicits ()  in
                  if uu____64299 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____64309 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____64309 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____64394) ->
          let uu____64403 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____64426 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____64444 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____64452 -> false
                    | uu____64469 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____64403 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____64507 se1 =
                 match uu____64507 with
                 | (datacon_ses1,tycons) ->
                     let uu____64533 = resugar_typ env datacon_ses1 se1  in
                     (match uu____64533 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____64548 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____64548 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____64583 =
                           let uu____64584 =
                             let uu____64585 =
                               let uu____64602 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____64602)  in
                             FStar_Parser_AST.Tycon uu____64585  in
                           decl'_to_decl se uu____64584  in
                         FStar_Pervasives_Native.Some uu____64583
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____64637,uu____64638,uu____64639,uu____64640,uu____64641)
                              ->
                              let uu____64648 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____64648
                          | uu____64651 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____64655 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____64662) ->
          let uu____64667 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_64675  ->
                    match uu___439_64675 with
                    | FStar_Syntax_Syntax.Projector (uu____64677,uu____64678)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____64680 -> true
                    | uu____64682 -> false))
             in
          if uu____64667
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
             | FStar_Parser_AST.Let (isrec,lets,uu____64717) ->
                 let uu____64746 =
                   let uu____64747 =
                     let uu____64748 =
                       let uu____64759 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____64759)  in
                     FStar_Parser_AST.TopLevelLet uu____64748  in
                   decl'_to_decl se uu____64747  in
                 FStar_Pervasives_Native.Some uu____64746
             | uu____64796 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____64801,fml) ->
          let uu____64803 =
            let uu____64804 =
              let uu____64805 =
                let uu____64810 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____64810)  in
              FStar_Parser_AST.Assume uu____64805  in
            decl'_to_decl se uu____64804  in
          FStar_Pervasives_Native.Some uu____64803
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____64812 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64812
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____64815 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64815
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____64825,t) ->
                let uu____64835 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64835
            | uu____64836 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____64844,t) ->
                let uu____64854 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64854
            | uu____64855 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____64879 -> failwith "Should not happen hopefully"  in
          let uu____64889 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____64889
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____64899 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____64899 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____64911 = FStar_Options.print_implicits ()  in
                 if uu____64911 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____64927 =
                 let uu____64928 =
                   let uu____64929 =
                     let uu____64946 =
                       let uu____64955 =
                         let uu____64962 =
                           let uu____64963 =
                             let uu____64976 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____64976)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____64963  in
                         (uu____64962, FStar_Pervasives_Native.None)  in
                       [uu____64955]  in
                     (false, false, uu____64946)  in
                   FStar_Parser_AST.Tycon uu____64929  in
                 decl'_to_decl se uu____64928  in
               FStar_Pervasives_Native.Some uu____64927)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____65008 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____65008
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____65012 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_65020  ->
                    match uu___440_65020 with
                    | FStar_Syntax_Syntax.Projector (uu____65022,uu____65023)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____65025 -> true
                    | uu____65027 -> false))
             in
          if uu____65012
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____65035 =
                 (let uu____65039 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____65039) || (FStar_List.isEmpty uvs)
                  in
               if uu____65035
               then resugar_term' env t
               else
                 (let uu____65044 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____65044 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____65053 = resugar_term' env t1  in
                      label universes uu____65053)
                in
             let uu____65054 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____65054)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____65061 =
            let uu____65062 =
              let uu____65063 =
                let uu____65070 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____65075 = resugar_term' env t  in
                (uu____65070, uu____65075)  in
              FStar_Parser_AST.Splice uu____65063  in
            decl'_to_decl se uu____65062  in
          FStar_Pervasives_Native.Some uu____65061
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____65078 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____65095 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____65111 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____65135 = noenv resugar_term'  in uu____65135 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____65153 = noenv resugar_sigelt'  in uu____65153 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____65171 = noenv resugar_comp'  in uu____65171 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____65194 = noenv resugar_pat'  in uu____65194 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____65228 = noenv resugar_binder'  in uu____65228 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____65253 = noenv resugar_tscheme'  in uu____65253 ts 
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
          let uu____65288 = noenv resugar_eff_decl'  in
          uu____65288 for_free r q ed
  