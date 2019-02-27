open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____55919 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____55919
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____55927 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____55927
  
let map_opt :
  'Auu____55937 'Auu____55938 .
    unit ->
      ('Auu____55937 -> 'Auu____55938 FStar_Pervasives_Native.option) ->
        'Auu____55937 Prims.list -> 'Auu____55938 Prims.list
  = fun uu____55954  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____55963 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____55963
      then
        let uu____55967 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____55967
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____55977 .
    ('Auu____55977 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____55977 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_56032  ->
            match uu___429_56032 with
            | (uu____56040,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56047,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56048)) -> false
            | (uu____56053,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56054)) -> false
            | uu____56060 -> true))
  
let filter_pattern_imp :
  'Auu____56073 .
    ('Auu____56073 * Prims.bool) Prims.list ->
      ('Auu____56073 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____56108  ->
         match uu____56108 with
         | (uu____56115,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____56165 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____56178 = FStar_Options.print_universes ()  in
    if uu____56178
    then
      let uu____56182 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____56182 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____56246 ->
          let uu____56247 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____56247 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____56258 =
                      let uu____56259 =
                        let uu____56260 =
                          let uu____56272 = FStar_Util.string_of_int n1  in
                          (uu____56272, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____56260  in
                      FStar_Parser_AST.Const uu____56259  in
                    mk1 uu____56258 r
                | uu____56285 ->
                    let e1 =
                      let uu____56287 =
                        let uu____56288 =
                          let uu____56289 =
                            let uu____56301 = FStar_Util.string_of_int n1  in
                            (uu____56301, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____56289  in
                        FStar_Parser_AST.Const uu____56288  in
                      mk1 uu____56287 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____56315 =
                      let uu____56316 =
                        let uu____56323 = FStar_Ident.id_of_text "+"  in
                        (uu____56323, [e1; e2])  in
                      FStar_Parser_AST.Op uu____56316  in
                    mk1 uu____56315 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____56331 ->
               let t =
                 let uu____56335 =
                   let uu____56336 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____56336  in
                 mk1 uu____56335 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____56345 =
                        let uu____56346 =
                          let uu____56353 = resugar_universe x r  in
                          (acc, uu____56353, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____56346  in
                      mk1 uu____56345 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____56355 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____56367 =
              let uu____56373 =
                let uu____56375 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____56375  in
              (uu____56373, r)  in
            FStar_Ident.mk_ident uu____56367  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_56413 =
      match uu___430_56413 with
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
      | uu____56741 -> FStar_Pervasives_Native.None  in
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
    | uu____56881 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____56899 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____56899 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____56917 ->
               let op =
                 let uu____56923 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____56977) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____56923
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
      let uu____57304 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____57304 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____57374 ->
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
                (let uu____57486 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____57486
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____57522 =
      let uu____57523 = FStar_Syntax_Subst.compress t  in
      uu____57523.FStar_Syntax_Syntax.n  in
    match uu____57522 with
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
        let uu____57554 = string_to_op s  in
        (match uu____57554 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____57594 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____57611 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____57628 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____57639 -> true
    | uu____57641 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____57662 ->
        let uu____57664 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____57664
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____57678 = may_shorten lid  in
      if uu____57678 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____57823 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____57823  in
      let uu____57826 =
        let uu____57827 = FStar_Syntax_Subst.compress t  in
        uu____57827.FStar_Syntax_Syntax.n  in
      match uu____57826 with
      | FStar_Syntax_Syntax.Tm_delayed uu____57830 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____57855 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____57855
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____57858 =
              let uu____57861 = bv_as_unique_ident x  in [uu____57861]  in
            FStar_Ident.lid_of_ids uu____57858  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____57864 =
              let uu____57867 = bv_as_unique_ident x  in [uu____57867]  in
            FStar_Ident.lid_of_ids uu____57864  in
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
            let uu____57896 =
              let uu____57897 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____57897  in
            mk1 uu____57896
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
               | uu____57921 -> failwith "wrong projector format")
            else
              (let uu____57928 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____57932 =
                      let uu____57934 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____57934  in
                    let uu____57937 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____57932 <> uu____57937)
                  in
               if uu____57928
               then
                 let uu____57942 =
                   let uu____57943 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____57943  in
                 mk1 uu____57942
               else
                 (let uu____57946 =
                    let uu____57947 =
                      let uu____57958 = maybe_shorten_fv env fv  in
                      (uu____57958, [])  in
                    FStar_Parser_AST.Construct uu____57947  in
                  mk1 uu____57946))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____57976 = FStar_Options.print_universes ()  in
          if uu____57976
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
                   let uu____58007 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____58007  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____58030 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____58038 = FStar_Syntax_Syntax.is_teff t  in
          if uu____58038
          then
            let uu____58041 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____58041
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____58046 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____58067 -> ("Type", true)  in
          (match uu____58046 with
           | (nm,needs_app) ->
               let typ =
                 let uu____58079 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____58079  in
               let uu____58080 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____58080
               then
                 let uu____58083 =
                   let uu____58084 =
                     let uu____58091 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____58091, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____58084  in
                 mk1 uu____58083
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____58096) ->
          let uu____58121 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____58121 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58137 = FStar_Options.print_implicits ()  in
                 if uu____58137 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____58175  ->
                         match uu____58175 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____58215 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____58215 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58225 = FStar_Options.print_implicits ()  in
                 if uu____58225 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____58236 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____58236 FStar_List.rev  in
               let rec aux body3 uu___431_58261 =
                 match uu___431_58261 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____58277 =
            let uu____58282 =
              let uu____58283 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____58283]  in
            FStar_Syntax_Subst.open_term uu____58282 phi  in
          (match uu____58277 with
           | (x1,phi1) ->
               let b =
                 let uu____58305 =
                   let uu____58308 = FStar_List.hd x1  in
                   resugar_binder' env uu____58308 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____58305  in
               let uu____58315 =
                 let uu____58316 =
                   let uu____58321 = resugar_term' env phi1  in
                   (b, uu____58321)  in
                 FStar_Parser_AST.Refine uu____58316  in
               mk1 uu____58315)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____58323;
             FStar_Syntax_Syntax.vars = uu____58324;_},(e,uu____58326)::[])
          when
          (let uu____58367 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____58367) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_58416 =
            match uu___432_58416 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____58486 -> failwith "last of an empty list"  in
          let rec last_two uu___433_58525 =
            match uu___433_58525 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____58557::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____58635::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____58706  ->
                   match uu____58706 with
                   | (e2,qual) ->
                       let uu____58723 = resugar_term' env e2  in
                       let uu____58724 = resugar_imp env qual  in
                       (uu____58723, uu____58724)) args1
               in
            let uu____58725 = resugar_term' env e1  in
            match uu____58725 with
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
                     fun uu____58762  ->
                       match uu____58762 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____58778 = FStar_Options.print_implicits ()  in
            if uu____58778 then args else filter_imp args  in
          let uu____58793 = resugar_term_as_op e  in
          (match uu____58793 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____58806) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____58831  ->
                        match uu____58831 with
                        | (x,uu____58843) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____58852 =
                                   let uu____58853 =
                                     let uu____58854 =
                                       let uu____58861 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____58861, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____58854  in
                                   mk1 uu____58853  in
                                 FStar_Pervasives_Native.Some uu____58852))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____58865) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____58891)::[] -> b
                 | uu____58908 -> failwith "wrong arguments to dtuple"  in
               let uu____58918 =
                 let uu____58919 = FStar_Syntax_Subst.compress body  in
                 uu____58919.FStar_Syntax_Syntax.n  in
               (match uu____58918 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____58924) ->
                    let uu____58949 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____58949 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____58959 = FStar_Options.print_implicits ()
                              in
                           if uu____58959 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____58976 =
                           let uu____58977 =
                             let uu____58988 =
                               FStar_List.map
                                 (fun _58999  -> FStar_Util.Inl _58999) xs3
                                in
                             (uu____58988, body3)  in
                           FStar_Parser_AST.Sum uu____58977  in
                         mk1 uu____58976)
                | uu____59006 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____59029  ->
                              match uu____59029 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____59047) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____59056) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____59065 = FStar_List.hd args1  in
               (match uu____59065 with
                | (t1,uu____59079) ->
                    let uu____59084 =
                      let uu____59085 = FStar_Syntax_Subst.compress t1  in
                      uu____59085.FStar_Syntax_Syntax.n  in
                    (match uu____59084 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____59092 =
                           let uu____59093 =
                             let uu____59098 = resugar_term' env t1  in
                             (uu____59098, f)  in
                           FStar_Parser_AST.Project uu____59093  in
                         mk1 uu____59092
                     | uu____59099 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____59100) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____59124 =
                 match new_args with
                 | (a1,uu____59134)::(a2,uu____59136)::[] -> (a1, a2)
                 | uu____59163 -> failwith "wrong arguments to try_with"  in
               (match uu____59124 with
                | (body,handler) ->
                    let decomp term =
                      let uu____59185 =
                        let uu____59186 = FStar_Syntax_Subst.compress term
                           in
                        uu____59186.FStar_Syntax_Syntax.n  in
                      match uu____59185 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____59191) ->
                          let uu____59216 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____59216 with | (x1,e2) -> e2)
                      | uu____59223 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____59226 = decomp body  in
                      resugar_term' env uu____59226  in
                    let handler1 =
                      let uu____59228 = decomp handler  in
                      resugar_term' env uu____59228  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____59236,uu____59237,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____59269,uu____59270,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____59307 =
                            let uu____59308 =
                              let uu____59317 = resugar_body t11  in
                              (uu____59317, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____59308  in
                          mk1 uu____59307
                      | uu____59320 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____59378 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____59408) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59417) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59438) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____59536 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____59549 =
                   let uu____59550 = FStar_Syntax_Subst.compress body  in
                   uu____59550.FStar_Syntax_Syntax.n  in
                 match uu____59549 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____59555) ->
                     let uu____59580 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____59580 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____59590 =
                              FStar_Options.print_implicits ()  in
                            if uu____59590 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____59606 =
                            let uu____59615 =
                              let uu____59616 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____59616.FStar_Syntax_Syntax.n  in
                            match uu____59615 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____59634 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____59664 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____59708  ->
                                                     match uu____59708 with
                                                     | (e2,uu____59716) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____59664, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____59732 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____59732)
                                  | uu____59741 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____59634 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____59773 ->
                                let uu____59774 = resugar_term' env body2  in
                                ([], uu____59774)
                             in
                          (match uu____59606 with
                           | (pats,body3) ->
                               let uu____59791 = uncurry xs3 pats body3  in
                               (match uu____59791 with
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
                 | uu____59843 ->
                     if op = "forall"
                     then
                       let uu____59847 =
                         let uu____59848 =
                           let uu____59861 = resugar_term' env body  in
                           ([], [[]], uu____59861)  in
                         FStar_Parser_AST.QForall uu____59848  in
                       mk1 uu____59847
                     else
                       (let uu____59874 =
                          let uu____59875 =
                            let uu____59888 = resugar_term' env body  in
                            ([], [[]], uu____59888)  in
                          FStar_Parser_AST.QExists uu____59875  in
                        mk1 uu____59874)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____59917)::[] -> resugar b
                  | uu____59934 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____59946) ->
               let uu____59954 = FStar_List.hd args1  in
               (match uu____59954 with
                | (e1,uu____59968) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____60040  ->
                         match uu____60040 with
                         | (e1,qual) ->
                             let uu____60057 = resugar_term' env e1  in
                             let uu____60058 = resugar_imp env qual  in
                             (uu____60057, uu____60058)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____60074 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____60074 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____60122 =
                               let uu____60123 =
                                 let uu____60130 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____60130)  in
                               FStar_Parser_AST.Op uu____60123  in
                             mk1 uu____60122  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____60148  ->
                                  match uu____60148 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____60167 =
                      let uu____60168 =
                        let uu____60175 =
                          let uu____60178 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____60178
                           in
                        (op1, uu____60175)  in
                      FStar_Parser_AST.Op uu____60168  in
                    mk1 uu____60167
                | uu____60191 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____60260 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____60260 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____60306 =
                   let uu____60319 =
                     let uu____60324 = resugar_pat' env pat1 branch_bv  in
                     let uu____60325 = resugar_term' env e  in
                     (uu____60324, uu____60325)  in
                   (FStar_Pervasives_Native.None, uu____60319)  in
                 [uu____60306]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____60377,t1)::(pat2,uu____60380,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____60476 =
            let uu____60477 =
              let uu____60484 = resugar_term' env e  in
              let uu____60485 = resugar_term' env t1  in
              let uu____60486 = resugar_term' env t2  in
              (uu____60484, uu____60485, uu____60486)  in
            FStar_Parser_AST.If uu____60477  in
          mk1 uu____60476
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____60552 =
            match uu____60552 with
            | (pat,wopt,b) ->
                let uu____60594 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____60594 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____60646 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____60646
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____60650 =
            let uu____60651 =
              let uu____60666 = resugar_term' env e  in
              let uu____60667 = FStar_List.map resugar_branch branches  in
              (uu____60666, uu____60667)  in
            FStar_Parser_AST.Match uu____60651  in
          mk1 uu____60650
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____60713) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____60782 =
            let uu____60783 =
              let uu____60792 = resugar_term' env e  in
              (uu____60792, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____60783  in
          mk1 uu____60782
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____60821 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____60821 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____60875 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____60875
                    in
                 let uu____60882 =
                   let uu____60887 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____60887
                    in
                 match uu____60882 with
                 | (univs1,td) ->
                     let uu____60907 =
                       let uu____60914 =
                         let uu____60915 = FStar_Syntax_Subst.compress td  in
                         uu____60915.FStar_Syntax_Syntax.n  in
                       match uu____60914 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____60924,(t1,uu____60926)::(d,uu____60928)::[])
                           -> (t1, d)
                       | uu____60985 -> failwith "wrong let binding format"
                        in
                     (match uu____60907 with
                      | (typ,def) ->
                          let uu____61016 =
                            let uu____61032 =
                              let uu____61033 =
                                FStar_Syntax_Subst.compress def  in
                              uu____61033.FStar_Syntax_Syntax.n  in
                            match uu____61032 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____61053)
                                ->
                                let uu____61078 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____61078 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____61109 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____61109
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____61132 -> ([], def, false)  in
                          (match uu____61016 with
                           | (binders,term,is_pat_app) ->
                               let uu____61187 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____61198 =
                                       let uu____61199 =
                                         let uu____61200 =
                                           let uu____61207 =
                                             bv_as_unique_ident bv  in
                                           (uu____61207,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____61200
                                          in
                                       mk_pat uu____61199  in
                                     (uu____61198, term)
                                  in
                               (match uu____61187 with
                                | (pat,term1) ->
                                    let uu____61229 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____61272  ->
                                                  match uu____61272 with
                                                  | (bv,q) ->
                                                      let uu____61287 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____61287
                                                        (fun q1  ->
                                                           let uu____61299 =
                                                             let uu____61300
                                                               =
                                                               let uu____61307
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____61307,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____61300
                                                              in
                                                           mk_pat uu____61299)))
                                           in
                                        let uu____61310 =
                                          let uu____61315 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____61315)
                                           in
                                        let uu____61318 =
                                          universe_to_string univs1  in
                                        (uu____61310, uu____61318)
                                      else
                                        (let uu____61327 =
                                           let uu____61332 =
                                             resugar_term' env term1  in
                                           (pat, uu____61332)  in
                                         let uu____61333 =
                                           universe_to_string univs1  in
                                         (uu____61327, uu____61333))
                                       in
                                    (attrs_opt, uu____61229))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____61439 =
                   match uu____61439 with
                   | (attrs,(pb,univs1)) ->
                       let uu____61499 =
                         let uu____61501 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____61501  in
                       if uu____61499
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____61582) ->
          let s =
            let uu____61601 =
              let uu____61603 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____61603 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____61601  in
          let uu____61608 = mk1 FStar_Parser_AST.Wild  in label s uu____61608
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____61616 =
            let uu____61617 =
              let uu____61622 = resugar_term' env tm  in (uu____61622, qi1)
               in
            FStar_Parser_AST.Quote uu____61617  in
          mk1 uu____61616
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_61634 =
            match uu___434_61634 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____61642,(uu____61643,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____61704 =
                        let uu____61705 =
                          let uu____61714 = resugar_seq t11  in
                          (uu____61714, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____61705  in
                      mk1 uu____61704
                  | uu____61717 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____61761  ->
                         match uu____61761 with
                         | (x,uu____61769) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____61774 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____61792,t1) ->
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
               let uu____61832 = FStar_Options.print_universes ()  in
               if uu____61832
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
               let uu____61896 = FStar_Options.print_universes ()  in
               if uu____61896
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
            let uu____61940 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____61940, FStar_Parser_AST.Nothing)  in
          let uu____61941 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____61941
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____61964 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____61964
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____62049 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____62049, (FStar_Pervasives_Native.snd post))  in
                    let uu____62060 =
                      let uu____62069 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____62069 then [] else [pre]  in
                    let uu____62104 =
                      let uu____62113 =
                        let uu____62122 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____62122 then [] else [pats]  in
                      FStar_List.append [post1] uu____62113  in
                    FStar_List.append uu____62060 uu____62104
                | uu____62181 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____62215  ->
                   match uu____62215 with
                   | (e,uu____62227) ->
                       let uu____62232 = resugar_term' env e  in
                       (uu____62232, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_62257 =
              match uu___435_62257 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____62290 = resugar_term' env e  in
                         (uu____62290, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____62295 -> aux l tl1)
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
        let uu____62342 = b  in
        match uu____62342 with
        | (x,aq) ->
            let uu____62351 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____62351
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____62365 =
                       let uu____62366 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____62366  in
                     FStar_Parser_AST.mk_binder uu____62365 r
                       FStar_Parser_AST.Type_level imp
                 | uu____62367 ->
                     let uu____62368 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____62368
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____62373 =
                          let uu____62374 =
                            let uu____62379 = bv_as_unique_ident x  in
                            (uu____62379, e)  in
                          FStar_Parser_AST.Annotated uu____62374  in
                        FStar_Parser_AST.mk_binder uu____62373 r
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
              let uu____62399 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____62399  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____62403 =
                if used
                then
                  let uu____62405 =
                    let uu____62412 = bv_as_unique_ident v1  in
                    (uu____62412, aqual)  in
                  FStar_Parser_AST.PatVar uu____62405
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____62403  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____62419;
                  FStar_Syntax_Syntax.vars = uu____62420;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____62430 = FStar_Options.print_bound_var_types ()  in
                if uu____62430
                then
                  let uu____62433 =
                    let uu____62434 =
                      let uu____62445 =
                        let uu____62452 = resugar_term' env typ  in
                        (uu____62452, FStar_Pervasives_Native.None)  in
                      (pat, uu____62445)  in
                    FStar_Parser_AST.PatAscribed uu____62434  in
                  mk1 uu____62433
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
          let uu____62473 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____62473
            (fun aqual  ->
               let uu____62485 =
                 let uu____62490 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _62501  -> FStar_Pervasives_Native.Some _62501)
                   uu____62490
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____62485)

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
          (let uu____62563 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____62563) &&
            (let uu____62566 =
               FStar_List.existsML
                 (fun uu____62579  ->
                    match uu____62579 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____62601)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____62606 -> false
                          | uu____62608 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____62566)
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
            let uu____62676 = may_drop_implicits args  in
            if uu____62676 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____62701  ->
                 match uu____62701 with
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
              ((let uu____62756 =
                  let uu____62758 =
                    let uu____62760 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____62760  in
                  Prims.op_Negation uu____62758  in
                if uu____62756
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
              let uu____62804 = filter_pattern_imp args  in
              (match uu____62804 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____62854 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____62854 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____62873 =
                       let uu____62879 =
                         let uu____62881 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____62881
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____62879)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____62873);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____62934  ->
                        match uu____62934 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____62951 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____62951)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____62959;
                 FStar_Syntax_Syntax.fv_delta = uu____62960;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____62989 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____62989 FStar_List.rev  in
              let args1 =
                let uu____63005 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____63025  ->
                          match uu____63025 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____63005 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____63103 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____63103
                | (hd1::tl1,hd2::tl2) ->
                    let uu____63126 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____63126
                 in
              let args2 =
                let uu____63144 = map21 fields1 args1  in
                FStar_All.pipe_right uu____63144 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____63188 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____63188 with
               | FStar_Pervasives_Native.Some (op,uu____63200) ->
                   let uu____63217 =
                     let uu____63218 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____63218  in
                   mk1 uu____63217
               | FStar_Pervasives_Native.None  ->
                   let uu____63228 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____63228 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____63233 ->
              let uu____63234 =
                let uu____63235 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____63235  in
              mk1 uu____63234
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
          let uu____63275 =
            let uu____63278 =
              let uu____63279 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____63279  in
            FStar_Pervasives_Native.Some uu____63278  in
          FStar_Pervasives_Native.Some uu____63275

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
          let uu____63291 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____63291

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_63299  ->
    match uu___436_63299 with
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
    | FStar_Syntax_Syntax.Reflectable uu____63306 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____63307 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____63308 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____63313 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____63322 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____63331 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_63337  ->
    match uu___437_63337 with
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
            (tylid,uvs,bs,t,uu____63380,datacons) ->
            let uu____63390 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____63418,uu____63419,uu____63420,inductive_lid,uu____63422,uu____63423)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____63430 -> failwith "unexpected"))
               in
            (match uu____63390 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____63451 = FStar_Options.print_implicits ()  in
                   if uu____63451 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____63468 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_63475  ->
                             match uu___438_63475 with
                             | FStar_Syntax_Syntax.RecordType uu____63477 ->
                                 true
                             | uu____63487 -> false))
                      in
                   if uu____63468
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____63541,univs1,term,uu____63544,num,uu____63546)
                           ->
                           let uu____63553 =
                             let uu____63554 =
                               FStar_Syntax_Subst.compress term  in
                             uu____63554.FStar_Syntax_Syntax.n  in
                           (match uu____63553 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____63568)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____63637  ->
                                          match uu____63637 with
                                          | (b,qual) ->
                                              let uu____63658 =
                                                bv_as_unique_ident b  in
                                              let uu____63659 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____63658, uu____63659,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____63670 -> failwith "unexpected")
                       | uu____63682 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____63813,num,uu____63815) ->
                            let c =
                              let uu____63836 =
                                let uu____63839 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____63839  in
                              ((l.FStar_Ident.ident), uu____63836,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____63859 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____63939 ->
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
        let uu____63965 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____63965;
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
        let uu____63995 = ts  in
        match uu____63995 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____64008 =
              let uu____64009 =
                let uu____64026 =
                  let uu____64035 =
                    let uu____64042 =
                      let uu____64043 =
                        let uu____64056 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____64056)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____64043  in
                    (uu____64042, FStar_Pervasives_Native.None)  in
                  [uu____64035]  in
                (false, false, uu____64026)  in
              FStar_Parser_AST.Tycon uu____64009  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____64008
  
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
              let uu____64145 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____64145 with
              | (bs,action_defn) ->
                  let uu____64152 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____64152 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____64162 = FStar_Options.print_implicits ()
                            in
                         if uu____64162
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____64172 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____64172 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____64189 =
                             let uu____64200 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____64200,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____64189  in
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
            let uu____64284 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____64284 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____64294 = FStar_Options.print_implicits ()  in
                  if uu____64294 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____64304 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____64304 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____64389) ->
          let uu____64398 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____64421 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____64439 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____64447 -> false
                    | uu____64464 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____64398 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____64502 se1 =
                 match uu____64502 with
                 | (datacon_ses1,tycons) ->
                     let uu____64528 = resugar_typ env datacon_ses1 se1  in
                     (match uu____64528 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____64543 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____64543 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____64578 =
                           let uu____64579 =
                             let uu____64580 =
                               let uu____64597 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____64597)  in
                             FStar_Parser_AST.Tycon uu____64580  in
                           decl'_to_decl se uu____64579  in
                         FStar_Pervasives_Native.Some uu____64578
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____64632,uu____64633,uu____64634,uu____64635,uu____64636)
                              ->
                              let uu____64643 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____64643
                          | uu____64646 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____64650 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____64657) ->
          let uu____64662 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_64670  ->
                    match uu___439_64670 with
                    | FStar_Syntax_Syntax.Projector (uu____64672,uu____64673)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____64675 -> true
                    | uu____64677 -> false))
             in
          if uu____64662
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
             | FStar_Parser_AST.Let (isrec,lets,uu____64712) ->
                 let uu____64741 =
                   let uu____64742 =
                     let uu____64743 =
                       let uu____64754 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____64754)  in
                     FStar_Parser_AST.TopLevelLet uu____64743  in
                   decl'_to_decl se uu____64742  in
                 FStar_Pervasives_Native.Some uu____64741
             | uu____64791 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____64796,fml) ->
          let uu____64798 =
            let uu____64799 =
              let uu____64800 =
                let uu____64805 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____64805)  in
              FStar_Parser_AST.Assume uu____64800  in
            decl'_to_decl se uu____64799  in
          FStar_Pervasives_Native.Some uu____64798
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____64807 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64807
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____64810 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64810
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____64820,t) ->
                let uu____64830 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64830
            | uu____64831 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____64839,t) ->
                let uu____64849 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64849
            | uu____64850 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____64874 -> failwith "Should not happen hopefully"  in
          let uu____64884 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____64884
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____64894 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____64894 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____64906 = FStar_Options.print_implicits ()  in
                 if uu____64906 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____64922 =
                 let uu____64923 =
                   let uu____64924 =
                     let uu____64941 =
                       let uu____64950 =
                         let uu____64957 =
                           let uu____64958 =
                             let uu____64971 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____64971)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____64958  in
                         (uu____64957, FStar_Pervasives_Native.None)  in
                       [uu____64950]  in
                     (false, false, uu____64941)  in
                   FStar_Parser_AST.Tycon uu____64924  in
                 decl'_to_decl se uu____64923  in
               FStar_Pervasives_Native.Some uu____64922)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____65003 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____65003
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____65007 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_65015  ->
                    match uu___440_65015 with
                    | FStar_Syntax_Syntax.Projector (uu____65017,uu____65018)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____65020 -> true
                    | uu____65022 -> false))
             in
          if uu____65007
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____65030 =
                 (let uu____65034 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____65034) || (FStar_List.isEmpty uvs)
                  in
               if uu____65030
               then resugar_term' env t
               else
                 (let uu____65039 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____65039 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____65048 = resugar_term' env t1  in
                      label universes uu____65048)
                in
             let uu____65049 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____65049)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____65056 =
            let uu____65057 =
              let uu____65058 =
                let uu____65065 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____65070 = resugar_term' env t  in
                (uu____65065, uu____65070)  in
              FStar_Parser_AST.Splice uu____65058  in
            decl'_to_decl se uu____65057  in
          FStar_Pervasives_Native.Some uu____65056
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____65073 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____65090 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____65106 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____65130 = noenv resugar_term'  in uu____65130 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____65148 = noenv resugar_sigelt'  in uu____65148 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____65166 = noenv resugar_comp'  in uu____65166 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____65189 = noenv resugar_pat'  in uu____65189 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____65223 = noenv resugar_binder'  in uu____65223 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____65248 = noenv resugar_tscheme'  in uu____65248 ts 
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
          let uu____65283 = noenv resugar_eff_decl'  in
          uu____65283 for_free r q ed
  