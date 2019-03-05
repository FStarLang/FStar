open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____55928 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____55928
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____55936 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____55936
  
let map_opt :
  'Auu____55946 'Auu____55947 .
    unit ->
      ('Auu____55946 -> 'Auu____55947 FStar_Pervasives_Native.option) ->
        'Auu____55946 Prims.list -> 'Auu____55947 Prims.list
  = fun uu____55963  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____55972 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____55972
      then
        let uu____55976 =
          FStar_Util.string_of_int x.FStar_Syntax_Syntax.index  in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____55976
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____55986 .
    ('Auu____55986 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____55986 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___429_56041  ->
            match uu___429_56041 with
            | (uu____56049,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56056,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56057)) -> false
            | (uu____56062,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56063)) -> false
            | uu____56069 -> true))
  
let filter_pattern_imp :
  'Auu____56082 .
    ('Auu____56082 * Prims.bool) Prims.list ->
      ('Auu____56082 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____56117  ->
         match uu____56117 with
         | (uu____56124,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____56174 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____56187 = FStar_Options.print_universes ()  in
    if uu____56187
    then
      let uu____56191 =
        FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1  in
      FStar_All.pipe_right uu____56191 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____56255 ->
          let uu____56256 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____56256 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____56267 =
                      let uu____56268 =
                        let uu____56269 =
                          let uu____56281 = FStar_Util.string_of_int n1  in
                          (uu____56281, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____56269  in
                      FStar_Parser_AST.Const uu____56268  in
                    mk1 uu____56267 r
                | uu____56294 ->
                    let e1 =
                      let uu____56296 =
                        let uu____56297 =
                          let uu____56298 =
                            let uu____56310 = FStar_Util.string_of_int n1  in
                            (uu____56310, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____56298  in
                        FStar_Parser_AST.Const uu____56297  in
                      mk1 uu____56296 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____56324 =
                      let uu____56325 =
                        let uu____56332 = FStar_Ident.id_of_text "+"  in
                        (uu____56332, [e1; e2])  in
                      FStar_Parser_AST.Op uu____56325  in
                    mk1 uu____56324 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____56340 ->
               let t =
                 let uu____56344 =
                   let uu____56345 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____56345  in
                 mk1 uu____56344 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____56354 =
                        let uu____56355 =
                          let uu____56362 = resugar_universe x r  in
                          (acc, uu____56362, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____56355  in
                      mk1 uu____56354 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____56364 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____56376 =
              let uu____56382 =
                let uu____56384 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____56384  in
              (uu____56382, r)  in
            FStar_Ident.mk_ident uu____56376  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___430_56422 =
      match uu___430_56422 with
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
      | uu____56750 -> FStar_Pervasives_Native.None  in
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
    | uu____56890 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____56908 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____56908 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____56926 ->
               let op =
                 let uu____56932 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____56986) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____56932
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
      let uu____57313 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____57313 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____57383 ->
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
                (let uu____57495 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____57495
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____57531 =
      let uu____57532 = FStar_Syntax_Subst.compress t  in
      uu____57532.FStar_Syntax_Syntax.n  in
    match uu____57531 with
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
        let uu____57563 = string_to_op s  in
        (match uu____57563 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____57603 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____57620 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____57637 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____57648 -> true
    | uu____57650 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____57671 ->
        let uu____57673 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____57673
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____57687 = may_shorten lid  in
      if uu____57687 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____57832 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____57832  in
      let uu____57835 =
        let uu____57836 = FStar_Syntax_Subst.compress t  in
        uu____57836.FStar_Syntax_Syntax.n  in
      match uu____57835 with
      | FStar_Syntax_Syntax.Tm_delayed uu____57839 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____57864 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____57864
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____57867 =
              let uu____57870 = bv_as_unique_ident x  in [uu____57870]  in
            FStar_Ident.lid_of_ids uu____57867  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____57873 =
              let uu____57876 = bv_as_unique_ident x  in [uu____57876]  in
            FStar_Ident.lid_of_ids uu____57873  in
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
            let uu____57905 =
              let uu____57906 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____57906  in
            mk1 uu____57905
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
               | uu____57930 -> failwith "wrong projector format")
            else
              (let uu____57937 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____57941 =
                      let uu____57943 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____57943  in
                    let uu____57946 =
                      FStar_String.get s (Prims.parse_int "0")  in
                    uu____57941 <> uu____57946)
                  in
               if uu____57937
               then
                 let uu____57951 =
                   let uu____57952 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____57952  in
                 mk1 uu____57951
               else
                 (let uu____57955 =
                    let uu____57956 =
                      let uu____57967 = maybe_shorten_fv env fv  in
                      (uu____57967, [])  in
                    FStar_Parser_AST.Construct uu____57956  in
                  mk1 uu____57955))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____57985 = FStar_Options.print_universes ()  in
          if uu____57985
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
                   let uu____58016 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____58016  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____58039 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____58047 = FStar_Syntax_Syntax.is_teff t  in
          if uu____58047
          then
            let uu____58050 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____58050
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____58055 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____58076 -> ("Type", true)  in
          (match uu____58055 with
           | (nm,needs_app) ->
               let typ =
                 let uu____58088 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____58088  in
               let uu____58089 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____58089
               then
                 let uu____58092 =
                   let uu____58093 =
                     let uu____58100 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____58100, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____58093  in
                 mk1 uu____58092
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____58105) ->
          let uu____58130 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____58130 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58146 = FStar_Options.print_implicits ()  in
                 if uu____58146 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____58184  ->
                         match uu____58184 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____58224 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____58224 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____58234 = FStar_Options.print_implicits ()  in
                 if uu____58234 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____58245 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____58245 FStar_List.rev  in
               let rec aux body3 uu___431_58270 =
                 match uu___431_58270 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____58286 =
            let uu____58291 =
              let uu____58292 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____58292]  in
            FStar_Syntax_Subst.open_term uu____58291 phi  in
          (match uu____58286 with
           | (x1,phi1) ->
               let b =
                 let uu____58314 =
                   let uu____58317 = FStar_List.hd x1  in
                   resugar_binder' env uu____58317 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____58314  in
               let uu____58324 =
                 let uu____58325 =
                   let uu____58330 = resugar_term' env phi1  in
                   (b, uu____58330)  in
                 FStar_Parser_AST.Refine uu____58325  in
               mk1 uu____58324)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____58332;
             FStar_Syntax_Syntax.vars = uu____58333;_},(e,uu____58335)::[])
          when
          (let uu____58376 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____58376) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___432_58425 =
            match uu___432_58425 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____58495 -> failwith "last of an empty list"  in
          let rec last_two uu___433_58534 =
            match uu___433_58534 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____58566::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____58644::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____58715  ->
                   match uu____58715 with
                   | (e2,qual) ->
                       let uu____58732 = resugar_term' env e2  in
                       let uu____58733 = resugar_imp env qual  in
                       (uu____58732, uu____58733)) args1
               in
            let uu____58734 = resugar_term' env e1  in
            match uu____58734 with
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
                     fun uu____58771  ->
                       match uu____58771 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____58787 = FStar_Options.print_implicits ()  in
            if uu____58787 then args else filter_imp args  in
          let uu____58802 = resugar_term_as_op e  in
          (match uu____58802 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____58815) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____58840  ->
                        match uu____58840 with
                        | (x,uu____58852) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____58861 =
                                   let uu____58862 =
                                     let uu____58863 =
                                       let uu____58870 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____58870, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____58863  in
                                   mk1 uu____58862  in
                                 FStar_Pervasives_Native.Some uu____58861))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____58874) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____58900)::[] -> b
                 | uu____58917 -> failwith "wrong arguments to dtuple"  in
               let uu____58927 =
                 let uu____58928 = FStar_Syntax_Subst.compress body  in
                 uu____58928.FStar_Syntax_Syntax.n  in
               (match uu____58927 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____58933) ->
                    let uu____58958 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____58958 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____58968 = FStar_Options.print_implicits ()
                              in
                           if uu____58968 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____58985 =
                           let uu____58986 =
                             let uu____58997 =
                               FStar_List.map
                                 (fun _59008  -> FStar_Util.Inl _59008) xs3
                                in
                             (uu____58997, body3)  in
                           FStar_Parser_AST.Sum uu____58986  in
                         mk1 uu____58985)
                | uu____59015 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____59038  ->
                              match uu____59038 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____59056) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____59065) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____59074 = FStar_List.hd args1  in
               (match uu____59074 with
                | (t1,uu____59088) ->
                    let uu____59093 =
                      let uu____59094 = FStar_Syntax_Subst.compress t1  in
                      uu____59094.FStar_Syntax_Syntax.n  in
                    (match uu____59093 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____59101 =
                           let uu____59102 =
                             let uu____59107 = resugar_term' env t1  in
                             (uu____59107, f)  in
                           FStar_Parser_AST.Project uu____59102  in
                         mk1 uu____59101
                     | uu____59108 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____59109) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____59133 =
                 match new_args with
                 | (a1,uu____59143)::(a2,uu____59145)::[] -> (a1, a2)
                 | uu____59172 -> failwith "wrong arguments to try_with"  in
               (match uu____59133 with
                | (body,handler) ->
                    let decomp term =
                      let uu____59194 =
                        let uu____59195 = FStar_Syntax_Subst.compress term
                           in
                        uu____59195.FStar_Syntax_Syntax.n  in
                      match uu____59194 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____59200) ->
                          let uu____59225 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____59225 with | (x1,e2) -> e2)
                      | uu____59232 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____59235 = decomp body  in
                      resugar_term' env uu____59235  in
                    let handler1 =
                      let uu____59237 = decomp handler  in
                      resugar_term' env uu____59237  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____59245,uu____59246,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____59278,uu____59279,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____59316 =
                            let uu____59317 =
                              let uu____59326 = resugar_body t11  in
                              (uu____59326, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____59317  in
                          mk1 uu____59316
                      | uu____59329 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____59387 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____59417) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59426) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____59447) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,p,body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____59545 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____59558 =
                   let uu____59559 = FStar_Syntax_Subst.compress body  in
                   uu____59559.FStar_Syntax_Syntax.n  in
                 match uu____59558 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____59564) ->
                     let uu____59589 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____59589 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____59599 =
                              FStar_Options.print_implicits ()  in
                            if uu____59599 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____59615 =
                            let uu____59624 =
                              let uu____59625 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____59625.FStar_Syntax_Syntax.n  in
                            match uu____59624 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____59643 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern pats ->
                                      let uu____59673 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____59717  ->
                                                     match uu____59717 with
                                                     | (e2,uu____59725) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____59673, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____59741 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____59741)
                                  | uu____59750 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____59643 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____59782 ->
                                let uu____59783 = resugar_term' env body2  in
                                ([], uu____59783)
                             in
                          (match uu____59615 with
                           | (pats,body3) ->
                               let uu____59800 = uncurry xs3 pats body3  in
                               (match uu____59800 with
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
                 | uu____59852 ->
                     if op = "forall"
                     then
                       let uu____59856 =
                         let uu____59857 =
                           let uu____59870 = resugar_term' env body  in
                           ([], [[]], uu____59870)  in
                         FStar_Parser_AST.QForall uu____59857  in
                       mk1 uu____59856
                     else
                       (let uu____59883 =
                          let uu____59884 =
                            let uu____59897 = resugar_term' env body  in
                            ([], [[]], uu____59897)  in
                          FStar_Parser_AST.QExists uu____59884  in
                        mk1 uu____59883)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____59926)::[] -> resugar b
                  | uu____59943 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____59955) ->
               let uu____59963 = FStar_List.hd args1  in
               (match uu____59963 with
                | (e1,uu____59977) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____60049  ->
                         match uu____60049 with
                         | (e1,qual) ->
                             let uu____60066 = resugar_term' env e1  in
                             let uu____60067 = resugar_imp env qual  in
                             (uu____60066, uu____60067)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____60083 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____60083 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____60131 =
                               let uu____60132 =
                                 let uu____60139 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____60139)  in
                               FStar_Parser_AST.Op uu____60132  in
                             mk1 uu____60131  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____60157  ->
                                  match uu____60157 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____60176 =
                      let uu____60177 =
                        let uu____60184 =
                          let uu____60187 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____60187
                           in
                        (op1, uu____60184)  in
                      FStar_Parser_AST.Op uu____60177  in
                    mk1 uu____60176
                | uu____60200 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____60269 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)
             in
          (match uu____60269 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____60315 =
                   let uu____60328 =
                     let uu____60333 = resugar_pat' env pat1 branch_bv  in
                     let uu____60334 = resugar_term' env e  in
                     (uu____60333, uu____60334)  in
                   (FStar_Pervasives_Native.None, uu____60328)  in
                 [uu____60315]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____60386,t1)::(pat2,uu____60389,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____60485 =
            let uu____60486 =
              let uu____60493 = resugar_term' env e  in
              let uu____60494 = resugar_term' env t1  in
              let uu____60495 = resugar_term' env t2  in
              (uu____60493, uu____60494, uu____60495)  in
            FStar_Parser_AST.If uu____60486  in
          mk1 uu____60485
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____60561 =
            match uu____60561 with
            | (pat,wopt,b) ->
                let uu____60603 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____60603 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____60655 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____60655
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____60659 =
            let uu____60660 =
              let uu____60675 = resugar_term' env e  in
              let uu____60676 = FStar_List.map resugar_branch branches  in
              (uu____60675, uu____60676)  in
            FStar_Parser_AST.Match uu____60660  in
          mk1 uu____60659
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____60722) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____60791 =
            let uu____60792 =
              let uu____60801 = resugar_term' env e  in
              (uu____60801, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____60792  in
          mk1 uu____60791
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____60830 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____60830 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____60884 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____60884
                    in
                 let uu____60891 =
                   let uu____60896 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____60896
                    in
                 match uu____60891 with
                 | (univs1,td) ->
                     let uu____60916 =
                       let uu____60923 =
                         let uu____60924 = FStar_Syntax_Subst.compress td  in
                         uu____60924.FStar_Syntax_Syntax.n  in
                       match uu____60923 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____60933,(t1,uu____60935)::(d,uu____60937)::[])
                           -> (t1, d)
                       | uu____60994 -> failwith "wrong let binding format"
                        in
                     (match uu____60916 with
                      | (typ,def) ->
                          let uu____61025 =
                            let uu____61041 =
                              let uu____61042 =
                                FStar_Syntax_Subst.compress def  in
                              uu____61042.FStar_Syntax_Syntax.n  in
                            match uu____61041 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____61062)
                                ->
                                let uu____61087 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____61087 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____61118 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____61118
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____61141 -> ([], def, false)  in
                          (match uu____61025 with
                           | (binders,term,is_pat_app) ->
                               let uu____61196 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____61207 =
                                       let uu____61208 =
                                         let uu____61209 =
                                           let uu____61216 =
                                             bv_as_unique_ident bv  in
                                           (uu____61216,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____61209
                                          in
                                       mk_pat uu____61208  in
                                     (uu____61207, term)
                                  in
                               (match uu____61196 with
                                | (pat,term1) ->
                                    let uu____61238 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____61281  ->
                                                  match uu____61281 with
                                                  | (bv,q) ->
                                                      let uu____61296 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____61296
                                                        (fun q1  ->
                                                           let uu____61308 =
                                                             let uu____61309
                                                               =
                                                               let uu____61316
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____61316,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____61309
                                                              in
                                                           mk_pat uu____61308)))
                                           in
                                        let uu____61319 =
                                          let uu____61324 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____61324)
                                           in
                                        let uu____61327 =
                                          universe_to_string univs1  in
                                        (uu____61319, uu____61327)
                                      else
                                        (let uu____61336 =
                                           let uu____61341 =
                                             resugar_term' env term1  in
                                           (pat, uu____61341)  in
                                         let uu____61342 =
                                           universe_to_string univs1  in
                                         (uu____61336, uu____61342))
                                       in
                                    (attrs_opt, uu____61238))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____61448 =
                   match uu____61448 with
                   | (attrs,(pb,univs1)) ->
                       let uu____61508 =
                         let uu____61510 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____61510  in
                       if uu____61508
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____61591) ->
          let s =
            let uu____61610 =
              let uu____61612 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____61612 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____61610  in
          let uu____61617 = mk1 FStar_Parser_AST.Wild  in label s uu____61617
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____61625 =
            let uu____61626 =
              let uu____61631 = resugar_term' env tm  in (uu____61631, qi1)
               in
            FStar_Parser_AST.Quote uu____61626  in
          mk1 uu____61625
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___434_61643 =
            match uu___434_61643 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____61651,(uu____61652,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____61713 =
                        let uu____61714 =
                          let uu____61723 = resugar_seq t11  in
                          (uu____61723, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____61714  in
                      mk1 uu____61713
                  | uu____61726 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern pats ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____61770  ->
                         match uu____61770 with
                         | (x,uu____61778) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____61783 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____61801,t1) ->
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
               let uu____61841 = FStar_Options.print_universes ()  in
               if uu____61841
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
               let uu____61905 = FStar_Options.print_universes ()  in
               if uu____61905
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
            let uu____61949 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____61949, FStar_Parser_AST.Nothing)  in
          let uu____61950 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____61950
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____61973 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____61973
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____62058 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____62058, (FStar_Pervasives_Native.snd post))  in
                    let uu____62069 =
                      let uu____62078 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____62078 then [] else [pre]  in
                    let uu____62113 =
                      let uu____62122 =
                        let uu____62131 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____62131 then [] else [pats]  in
                      FStar_List.append [post1] uu____62122  in
                    FStar_List.append uu____62069 uu____62113
                | uu____62190 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____62224  ->
                   match uu____62224 with
                   | (e,uu____62236) ->
                       let uu____62241 = resugar_term' env e  in
                       (uu____62241, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___435_62266 =
              match uu___435_62266 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____62299 = resugar_term' env e  in
                         (uu____62299, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____62304 -> aux l tl1)
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
        let uu____62351 = b  in
        match uu____62351 with
        | (x,aq) ->
            let uu____62360 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____62360
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____62374 =
                       let uu____62375 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____62375  in
                     FStar_Parser_AST.mk_binder uu____62374 r
                       FStar_Parser_AST.Type_level imp
                 | uu____62376 ->
                     let uu____62377 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____62377
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____62382 =
                          let uu____62383 =
                            let uu____62388 = bv_as_unique_ident x  in
                            (uu____62388, e)  in
                          FStar_Parser_AST.Annotated uu____62383  in
                        FStar_Parser_AST.mk_binder uu____62382 r
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
              let uu____62408 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____62408  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____62412 =
                if used
                then
                  let uu____62414 =
                    let uu____62421 = bv_as_unique_ident v1  in
                    (uu____62421, aqual)  in
                  FStar_Parser_AST.PatVar uu____62414
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____62412  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____62428;
                  FStar_Syntax_Syntax.vars = uu____62429;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____62439 = FStar_Options.print_bound_var_types ()  in
                if uu____62439
                then
                  let uu____62442 =
                    let uu____62443 =
                      let uu____62454 =
                        let uu____62461 = resugar_term' env typ  in
                        (uu____62461, FStar_Pervasives_Native.None)  in
                      (pat, uu____62454)  in
                    FStar_Parser_AST.PatAscribed uu____62443  in
                  mk1 uu____62442
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
          let uu____62482 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____62482
            (fun aqual  ->
               let uu____62494 =
                 let uu____62499 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _62510  -> FStar_Pervasives_Native.Some _62510)
                   uu____62499
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____62494)

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
          (let uu____62572 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____62572) &&
            (let uu____62575 =
               FStar_List.existsML
                 (fun uu____62588  ->
                    match uu____62588 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____62610)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____62615 -> false
                          | uu____62617 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____62575)
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
            let uu____62685 = may_drop_implicits args  in
            if uu____62685 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____62710  ->
                 match uu____62710 with
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
              ((let uu____62765 =
                  let uu____62767 =
                    let uu____62769 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____62769  in
                  Prims.op_Negation uu____62767  in
                if uu____62765
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
              let uu____62813 = filter_pattern_imp args  in
              (match uu____62813 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____62863 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____62863 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____62882 =
                       let uu____62888 =
                         let uu____62890 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____62890
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____62888)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____62882);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____62943  ->
                        match uu____62943 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____62960 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____62960)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____62968;
                 FStar_Syntax_Syntax.fv_delta = uu____62969;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____62998 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____62998 FStar_List.rev  in
              let args1 =
                let uu____63014 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____63034  ->
                          match uu____63034 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____63014 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____63112 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____63112
                | (hd1::tl1,hd2::tl2) ->
                    let uu____63135 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____63135
                 in
              let args2 =
                let uu____63153 = map21 fields1 args1  in
                FStar_All.pipe_right uu____63153 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____63197 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____63197 with
               | FStar_Pervasives_Native.Some (op,uu____63209) ->
                   let uu____63226 =
                     let uu____63227 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____63227  in
                   mk1 uu____63226
               | FStar_Pervasives_Native.None  ->
                   let uu____63237 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____63237 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____63242 ->
              let uu____63243 =
                let uu____63244 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____63244  in
              mk1 uu____63243
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
          let uu____63284 =
            let uu____63287 =
              let uu____63288 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____63288  in
            FStar_Pervasives_Native.Some uu____63287  in
          FStar_Pervasives_Native.Some uu____63284

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
          let uu____63300 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____63300

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___436_63308  ->
    match uu___436_63308 with
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
    | FStar_Syntax_Syntax.Reflectable uu____63315 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____63316 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____63317 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____63322 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____63331 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____63340 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___437_63346  ->
    match uu___437_63346 with
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
            (tylid,uvs,bs,t,uu____63389,datacons) ->
            let uu____63399 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____63427,uu____63428,uu____63429,inductive_lid,uu____63431,uu____63432)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____63439 -> failwith "unexpected"))
               in
            (match uu____63399 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____63460 = FStar_Options.print_implicits ()  in
                   if uu____63460 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____63477 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___438_63484  ->
                             match uu___438_63484 with
                             | FStar_Syntax_Syntax.RecordType uu____63486 ->
                                 true
                             | uu____63496 -> false))
                      in
                   if uu____63477
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____63550,univs1,term,uu____63553,num,uu____63555)
                           ->
                           let uu____63562 =
                             let uu____63563 =
                               FStar_Syntax_Subst.compress term  in
                             uu____63563.FStar_Syntax_Syntax.n  in
                           (match uu____63562 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____63577)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____63646  ->
                                          match uu____63646 with
                                          | (b,qual) ->
                                              let uu____63667 =
                                                bv_as_unique_ident b  in
                                              let uu____63668 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____63667, uu____63668,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____63679 -> failwith "unexpected")
                       | uu____63691 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____63822,num,uu____63824) ->
                            let c =
                              let uu____63845 =
                                let uu____63848 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____63848  in
                              ((l.FStar_Ident.ident), uu____63845,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____63868 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____63948 ->
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
        let uu____63974 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____63974;
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
        let uu____64004 = ts  in
        match uu____64004 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____64017 =
              let uu____64018 =
                let uu____64035 =
                  let uu____64044 =
                    let uu____64051 =
                      let uu____64052 =
                        let uu____64065 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____64065)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____64052  in
                    (uu____64051, FStar_Pervasives_Native.None)  in
                  [uu____64044]  in
                (false, false, uu____64035)  in
              FStar_Parser_AST.Tycon uu____64018  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____64017
  
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
              let uu____64154 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____64154 with
              | (bs,action_defn) ->
                  let uu____64161 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____64161 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____64171 = FStar_Options.print_implicits ()
                            in
                         if uu____64171
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____64181 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____64181 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____64198 =
                             let uu____64209 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____64209,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____64198  in
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
            let uu____64293 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____64293 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____64303 = FStar_Options.print_implicits ()  in
                  if uu____64303 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____64313 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____64313 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____64398) ->
          let uu____64407 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____64430 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____64448 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____64456 -> false
                    | uu____64473 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____64407 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____64511 se1 =
                 match uu____64511 with
                 | (datacon_ses1,tycons) ->
                     let uu____64537 = resugar_typ env datacon_ses1 se1  in
                     (match uu____64537 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____64552 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____64552 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____64587 =
                           let uu____64588 =
                             let uu____64589 =
                               let uu____64606 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____64606)  in
                             FStar_Parser_AST.Tycon uu____64589  in
                           decl'_to_decl se uu____64588  in
                         FStar_Pervasives_Native.Some uu____64587
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____64641,uu____64642,uu____64643,uu____64644,uu____64645)
                              ->
                              let uu____64652 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____64652
                          | uu____64655 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____64659 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____64666) ->
          let uu____64671 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___439_64679  ->
                    match uu___439_64679 with
                    | FStar_Syntax_Syntax.Projector (uu____64681,uu____64682)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____64684 -> true
                    | uu____64686 -> false))
             in
          if uu____64671
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
             | FStar_Parser_AST.Let (isrec,lets,uu____64721) ->
                 let uu____64750 =
                   let uu____64751 =
                     let uu____64752 =
                       let uu____64763 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____64763)  in
                     FStar_Parser_AST.TopLevelLet uu____64752  in
                   decl'_to_decl se uu____64751  in
                 FStar_Pervasives_Native.Some uu____64750
             | uu____64800 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____64805,fml) ->
          let uu____64807 =
            let uu____64808 =
              let uu____64809 =
                let uu____64814 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____64814)  in
              FStar_Parser_AST.Assume uu____64809  in
            decl'_to_decl se uu____64808  in
          FStar_Pervasives_Native.Some uu____64807
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____64816 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64816
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____64819 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____64819
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____64829,t) ->
                let uu____64839 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64839
            | uu____64840 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____64848,t) ->
                let uu____64858 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____64858
            | uu____64859 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____64883 -> failwith "Should not happen hopefully"  in
          let uu____64893 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____64893
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____64903 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____64903 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____64915 = FStar_Options.print_implicits ()  in
                 if uu____64915 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____64931 =
                 let uu____64932 =
                   let uu____64933 =
                     let uu____64950 =
                       let uu____64959 =
                         let uu____64966 =
                           let uu____64967 =
                             let uu____64980 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____64980)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____64967  in
                         (uu____64966, FStar_Pervasives_Native.None)  in
                       [uu____64959]  in
                     (false, false, uu____64950)  in
                   FStar_Parser_AST.Tycon uu____64933  in
                 decl'_to_decl se uu____64932  in
               FStar_Pervasives_Native.Some uu____64931)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____65012 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____65012
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____65016 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___440_65024  ->
                    match uu___440_65024 with
                    | FStar_Syntax_Syntax.Projector (uu____65026,uu____65027)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____65029 -> true
                    | uu____65031 -> false))
             in
          if uu____65016
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____65039 =
                 (let uu____65043 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____65043) || (FStar_List.isEmpty uvs)
                  in
               if uu____65039
               then resugar_term' env t
               else
                 (let uu____65048 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____65048 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____65057 = resugar_term' env t1  in
                      label universes uu____65057)
                in
             let uu____65058 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____65058)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____65065 =
            let uu____65066 =
              let uu____65067 =
                let uu____65074 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____65079 = resugar_term' env t  in
                (uu____65074, uu____65079)  in
              FStar_Parser_AST.Splice uu____65067  in
            decl'_to_decl se uu____65066  in
          FStar_Pervasives_Native.Some uu____65065
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____65082 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____65099 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____65115 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____65139 = noenv resugar_term'  in uu____65139 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____65157 = noenv resugar_sigelt'  in uu____65157 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____65175 = noenv resugar_comp'  in uu____65175 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____65198 = noenv resugar_pat'  in uu____65198 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____65232 = noenv resugar_binder'  in uu____65232 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____65257 = noenv resugar_tscheme'  in uu____65257 ts 
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
          let uu____65292 = noenv resugar_eff_decl'  in
          uu____65292 for_free r q ed
  