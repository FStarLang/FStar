open Prims
let (doc_to_string : FStar_Pprint.document -> Prims.string) =
  fun doc1  ->
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") doc1
  
let (parser_term_to_string : FStar_Parser_AST.term -> Prims.string) =
  fun t  ->
    let uu____21 = FStar_Parser_ToDocument.term_to_document t  in
    doc_to_string uu____21
  
let (parser_pat_to_string : FStar_Parser_AST.pattern -> Prims.string) =
  fun t  ->
    let uu____33 = FStar_Parser_ToDocument.pat_to_document t  in
    doc_to_string uu____33
  
let map_opt :
  'Auu____43 'Auu____44 .
    unit ->
      ('Auu____43 -> 'Auu____44 FStar_Pervasives_Native.option) ->
        'Auu____43 Prims.list -> 'Auu____44 Prims.list
  = fun uu____60  -> FStar_List.filter_map 
let (bv_as_unique_ident : FStar_Syntax_Syntax.bv -> FStar_Ident.ident) =
  fun x  ->
    let unique_name =
      let uu____83 =
        (FStar_Util.starts_with FStar_Ident.reserved_prefix
           (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          || (FStar_Options.print_real_names ())
         in
      if uu____83
      then
        let uu____87 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
          uu____87
      else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
    FStar_Ident.mk_ident
      (unique_name, ((x.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
  
let filter_imp :
  'Auu____97 .
    ('Auu____97 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____97 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___0_152  ->
            match uu___0_152 with
            | (uu____160,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____171,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____172)) -> false
            | (uu____177,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____178)) -> false
            | uu____188 -> true))
  
let filter_pattern_imp :
  'Auu____201 .
    ('Auu____201 * Prims.bool) Prims.list ->
      ('Auu____201 * Prims.bool) Prims.list
  =
  fun xs  ->
    FStar_List.filter
      (fun uu____236  ->
         match uu____236 with
         | (uu____243,is_implicit1) -> Prims.op_Negation is_implicit1) xs
  
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
      | uu____314 -> (n1, u)
  
let (universe_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun univs1  ->
    let uu____331 = FStar_Options.print_universes ()  in
    if uu____331
    then
      let uu____335 = FStar_List.map (fun x  -> x.FStar_Ident.idText) univs1
         in
      FStar_All.pipe_right uu____335 (FStar_String.concat ", ")
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
      | FStar_Syntax_Syntax.U_succ uu____424 ->
          let uu____425 = universe_to_int (Prims.parse_int "0") u  in
          (match uu____425 with
           | (n1,u1) ->
               (match u1 with
                | FStar_Syntax_Syntax.U_zero  ->
                    let uu____442 =
                      let uu____443 =
                        let uu____444 =
                          let uu____456 = FStar_Util.string_of_int n1  in
                          (uu____456, FStar_Pervasives_Native.None)  in
                        FStar_Const.Const_int uu____444  in
                      FStar_Parser_AST.Const uu____443  in
                    mk1 uu____442 r
                | uu____469 ->
                    let e1 =
                      let uu____477 =
                        let uu____478 =
                          let uu____479 =
                            let uu____491 = FStar_Util.string_of_int n1  in
                            (uu____491, FStar_Pervasives_Native.None)  in
                          FStar_Const.Const_int uu____479  in
                        FStar_Parser_AST.Const uu____478  in
                      mk1 uu____477 r  in
                    let e2 = resugar_universe u1 r  in
                    let uu____511 =
                      let uu____512 =
                        let uu____524 = FStar_Ident.id_of_text "+"  in
                        (uu____524, [e1; e2])  in
                      FStar_Parser_AST.Op uu____512  in
                    mk1 uu____511 r))
      | FStar_Syntax_Syntax.U_max l ->
          (match l with
           | [] -> failwith "Impossible: U_max without arguments"
           | uu____556 ->
               let t =
                 let uu____566 =
                   let uu____567 = FStar_Ident.lid_of_path ["max"] r  in
                   FStar_Parser_AST.Var uu____567  in
                 mk1 uu____566 r  in
               FStar_List.fold_left
                 (fun acc  ->
                    fun x  ->
                      let uu____590 =
                        let uu____591 =
                          let uu____604 = resugar_universe x r  in
                          (acc, uu____604, FStar_Parser_AST.Nothing)  in
                        FStar_Parser_AST.App uu____591  in
                      mk1 uu____590 r) t l)
      | FStar_Syntax_Syntax.U_name u1 -> mk1 (FStar_Parser_AST.Uvar u1) r
      | FStar_Syntax_Syntax.U_unif uu____620 -> mk1 FStar_Parser_AST.Wild r
      | FStar_Syntax_Syntax.U_bvar x ->
          let id1 =
            let uu____638 =
              let uu____644 =
                let uu____646 = FStar_Util.string_of_int x  in
                FStar_Util.strcat "uu__univ_bvar_" uu____646  in
              (uu____644, r)  in
            FStar_Ident.mk_ident uu____638  in
          mk1 (FStar_Parser_AST.Uvar id1) r
      | FStar_Syntax_Syntax.U_unknown  -> mk1 FStar_Parser_AST.Wild r

let (string_to_op :
  Prims.string ->
    (Prims.string * Prims.int FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun s  ->
    let name_of_op uu___1_684 =
      match uu___1_684 with
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
      | uu____1012 -> FStar_Pervasives_Native.None  in
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
    | uu____1152 ->
        if FStar_Util.starts_with s "op_"
        then
          let s1 =
            let uu____1170 =
              FStar_Util.substring_from s (FStar_String.length "op_")  in
            FStar_Util.split uu____1170 "_"  in
          (match s1 with
           | op::[] -> name_of_op op
           | uu____1188 ->
               let op =
                 let uu____1194 = FStar_List.map name_of_op s1  in
                 FStar_List.fold_left
                   (fun acc  ->
                      fun x  ->
                        match x with
                        | FStar_Pervasives_Native.Some (op,uu____1248) ->
                            Prims.op_Hat acc op
                        | FStar_Pervasives_Native.None  ->
                            failwith "wrong composed operator format") ""
                   uu____1194
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
      let uu____1853 =
        FStar_All.pipe_right infix_prim_ops
          (FStar_Util.find_opt
             (fun d  ->
                FStar_Syntax_Syntax.fv_eq_lid fv
                  (FStar_Pervasives_Native.fst d)))
         in
      match uu____1853 with
      | FStar_Pervasives_Native.Some op ->
          FStar_Pervasives_Native.Some
            ((FStar_Pervasives_Native.snd op), FStar_Pervasives_Native.None)
      | uu____1959 ->
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
                (let uu____2077 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.sread_lid
                    in
                 if uu____2077
                 then
                   FStar_Pervasives_Native.Some
                     ((((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str),
                       FStar_Pervasives_Native.None)
                 else FStar_Pervasives_Native.None)
       in
    let uu____2117 =
      let uu____2118 = FStar_Syntax_Subst.compress t  in
      uu____2118.FStar_Syntax_Syntax.n  in
    match uu____2117 with
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
        let uu____2162 = string_to_op s  in
        (match uu____2162 with
         | FStar_Pervasives_Native.Some t1 -> FStar_Pervasives_Native.Some t1
         | uu____2202 -> fallback fv)
    | FStar_Syntax_Syntax.Tm_uinst (e,us) -> resugar_term_as_op e
    | uu____2227 -> FStar_Pervasives_Native.None
  
let (is_true_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true )) ->
        true
    | uu____2244 -> false
  
let (is_wild_pat : FStar_Syntax_Syntax.pat -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____2255 -> true
    | uu____2262 -> false
  
let (is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    (FStar_Parser_Const.is_tuple_data_lid' lid) ||
      (FStar_Parser_Const.is_dtuple_data_lid' lid)
  
let (may_shorten : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    match lid.FStar_Ident.str with
    | "Prims.Nil" -> false
    | "Prims.Cons" -> false
    | uu____2299 ->
        let uu____2301 = is_tuple_constructor_lid lid  in
        Prims.op_Negation uu____2301
  
let (maybe_shorten_fv :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lident) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____2337 = may_shorten lid  in
      if uu____2337 then FStar_Syntax_DsEnv.shorten_lid env lid else lid
  
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
        let uu____2552 = FStar_Ident.lid_of_path [a] r  in
        FStar_Parser_AST.Name uu____2552  in
      let uu____2563 =
        let uu____2564 = FStar_Syntax_Subst.compress t  in
        uu____2564.FStar_Syntax_Syntax.n  in
      match uu____2563 with
      | FStar_Syntax_Syntax.Tm_delayed uu____2578 ->
          failwith "Tm_delayed is impossible after compress"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____2618 = FStar_Syntax_Util.unfold_lazy i  in
          resugar_term' env uu____2618
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let l =
            let uu____2642 =
              let uu____2647 = bv_as_unique_ident x  in [uu____2647]  in
            FStar_Ident.lid_of_ids uu____2642  in
          mk1 (FStar_Parser_AST.Var l)
      | FStar_Syntax_Syntax.Tm_name x ->
          let l =
            let uu____2671 =
              let uu____2676 = bv_as_unique_ident x  in [uu____2676]  in
            FStar_Ident.lid_of_ids uu____2671  in
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
            let uu____2725 =
              let uu____2726 =
                FStar_Ident.lid_of_path [rest] t.FStar_Syntax_Syntax.pos  in
              FStar_Parser_AST.Discrim uu____2726  in
            mk1 uu____2725
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
               | uu____2782 -> failwith "wrong projector format")
            else
              (let uu____2792 =
                 ((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) ||
                    (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid))
                   ||
                   (let uu____2796 =
                      let uu____2798 =
                        FStar_String.get s (Prims.parse_int "0")  in
                      FStar_Char.uppercase uu____2798  in
                    let uu____2801 = FStar_String.get s (Prims.parse_int "0")
                       in
                    uu____2796 <> uu____2801)
                  in
               if uu____2792
               then
                 let uu____2809 =
                   let uu____2810 = maybe_shorten_fv env fv  in
                   FStar_Parser_AST.Var uu____2810  in
                 mk1 uu____2809
               else
                 (let uu____2821 =
                    let uu____2822 =
                      let uu____2840 = maybe_shorten_fv env fv  in
                      (uu____2840, [])  in
                    FStar_Parser_AST.Construct uu____2822  in
                  mk1 uu____2821))
      | FStar_Syntax_Syntax.Tm_uinst (e,universes) ->
          let e1 = resugar_term' env e  in
          let uu____2890 = FStar_Options.print_universes ()  in
          if uu____2890
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
                   let uu____2950 =
                     FStar_List.map (fun u  -> (u, FStar_Parser_AST.UnivApp))
                       univs1
                      in
                   FStar_List.append args uu____2950  in
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Construct (hd1, args1)) r l
             | uu____2998 ->
                 FStar_List.fold_left
                   (fun acc  ->
                      fun u  ->
                        mk1
                          (FStar_Parser_AST.App
                             (acc, u, FStar_Parser_AST.UnivApp))) e1 univs1)
          else e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____3027 = FStar_Syntax_Syntax.is_teff t  in
          if uu____3027
          then
            let uu____3033 = name "Effect" t.FStar_Syntax_Syntax.pos  in
            mk1 uu____3033
          else mk1 (FStar_Parser_AST.Const c)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____3038 =
            match u with
            | FStar_Syntax_Syntax.U_zero  -> ("Type0", false)
            | FStar_Syntax_Syntax.U_unknown  -> ("Type", false)
            | uu____3059 -> ("Type", true)  in
          (match uu____3038 with
           | (nm,needs_app) ->
               let typ =
                 let uu____3080 = name nm t.FStar_Syntax_Syntax.pos  in
                 mk1 uu____3080  in
               let uu____3081 =
                 needs_app && (FStar_Options.print_universes ())  in
               if uu____3081
               then
                 let uu____3087 =
                   let uu____3088 =
                     let uu____3101 =
                       resugar_universe u t.FStar_Syntax_Syntax.pos  in
                     (typ, uu____3101, FStar_Parser_AST.UnivApp)  in
                   FStar_Parser_AST.App uu____3088  in
                 mk1 uu____3087
               else typ)
      | FStar_Syntax_Syntax.Tm_abs (xs,body,uu____3118) ->
          let uu____3175 = FStar_Syntax_Subst.open_term xs body  in
          (match uu____3175 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____3211 = FStar_Options.print_implicits ()  in
                 if uu____3211 then xs1 else filter_imp xs1  in
               let body_bv = FStar_Syntax_Free.names body1  in
               let patterns =
                 FStar_All.pipe_right xs2
                   (FStar_List.choose
                      (fun uu____3280  ->
                         match uu____3280 with
                         | (x,qual) -> resugar_bv_as_pat env x qual body_bv))
                  in
               let body2 = resugar_term' env body1  in
               mk1 (FStar_Parser_AST.Abs (patterns, body2)))
      | FStar_Syntax_Syntax.Tm_arrow (xs,body) ->
          let uu____3366 = FStar_Syntax_Subst.open_comp xs body  in
          (match uu____3366 with
           | (xs1,body1) ->
               let xs2 =
                 let uu____3391 = FStar_Options.print_implicits ()  in
                 if uu____3391 then xs1 else filter_imp xs1  in
               let body2 = resugar_comp' env body1  in
               let xs3 =
                 let uu____3417 =
                   FStar_All.pipe_right xs2
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 FStar_All.pipe_right uu____3417 FStar_List.rev  in
               let rec aux body3 uu___2_3476 =
                 match uu___2_3476 with
                 | [] -> body3
                 | hd1::tl1 ->
                     let body4 =
                       mk1 (FStar_Parser_AST.Product ([hd1], body3))  in
                     aux body4 tl1
                  in
               aux body2 xs3)
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____3557 =
            let uu____3566 =
              let uu____3567 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____3567]  in
            FStar_Syntax_Subst.open_term uu____3566 phi  in
          (match uu____3557 with
           | (x1,phi1) ->
               let b =
                 let uu____3623 =
                   let uu____3630 = FStar_List.hd x1  in
                   resugar_binder' env uu____3630 t.FStar_Syntax_Syntax.pos
                    in
                 FStar_Util.must uu____3623  in
               let uu____3646 =
                 let uu____3647 =
                   let uu____3659 = resugar_term' env phi1  in
                   (b, uu____3659)  in
                 FStar_Parser_AST.Refine uu____3647  in
               mk1 uu____3646)
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3674;
             FStar_Syntax_Syntax.vars = uu____3675;_},(e,uu____3677)::[])
          when
          (let uu____3749 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____3749) &&
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)
          -> resugar_term' env e
      | FStar_Syntax_Syntax.Tm_app (e,args) ->
          let rec last1 uu___3_3822 =
            match uu___3_3822 with
            | hd1::[] -> [hd1]
            | hd1::tl1 -> last1 tl1
            | uu____3932 -> failwith "last of an empty list"  in
          let rec last_two uu___4_3987 =
            match uu___4_3987 with
            | [] ->
                failwith
                  "last two elements of a list with less than two elements "
            | uu____4035::[] ->
                failwith
                  "last two elements of a list with less than two elements "
            | a1::a2::[] -> [a1; a2]
            | uu____4161::t1 -> last_two t1  in
          let resugar_as_app e1 args1 =
            let args2 =
              FStar_List.map
                (fun uu____4273  ->
                   match uu____4273 with
                   | (e2,qual) ->
                       let uu____4305 = resugar_term' env e2  in
                       let uu____4312 = resugar_imp env qual  in
                       (uu____4305, uu____4312)) args1
               in
            let uu____4316 = resugar_term' env e1  in
            match uu____4316 with
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
                     fun uu____4395  ->
                       match uu____4395 with
                       | (x,qual) ->
                           mk1 (FStar_Parser_AST.App (acc, x, qual))) e2
                  args2
             in
          let args1 =
            let uu____4436 = FStar_Options.print_implicits ()  in
            if uu____4436 then args else filter_imp args  in
          let uu____4459 = resugar_term_as_op e  in
          (match uu____4459 with
           | FStar_Pervasives_Native.None  -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("tuple",uu____4475) ->
               let out =
                 FStar_List.fold_left
                   (fun out  ->
                      fun uu____4510  ->
                        match uu____4510 with
                        | (x,uu____4532) ->
                            let x1 = resugar_term' env x  in
                            (match out with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some x1
                             | FStar_Pervasives_Native.Some prefix1 ->
                                 let uu____4570 =
                                   let uu____4577 =
                                     let uu____4578 =
                                       let uu____4590 =
                                         FStar_Ident.id_of_text "*"  in
                                       (uu____4590, [prefix1; x1])  in
                                     FStar_Parser_AST.Op uu____4578  in
                                   mk1 uu____4577  in
                                 FStar_Pervasives_Native.Some uu____4570))
                   FStar_Pervasives_Native.None args1
                  in
               FStar_Option.get out
           | FStar_Pervasives_Native.Some ("dtuple",uu____4621) when
               (FStar_List.length args1) > (Prims.parse_int "0") ->
               let args2 = last1 args1  in
               let body =
                 match args2 with
                 | (b,uu____4667)::[] -> b
                 | uu____4700 -> failwith "wrong arguments to dtuple"  in
               let uu____4718 =
                 let uu____4719 = FStar_Syntax_Subst.compress body  in
                 uu____4719.FStar_Syntax_Syntax.n  in
               (match uu____4718 with
                | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____4735) ->
                    let uu____4792 = FStar_Syntax_Subst.open_term xs body1
                       in
                    (match uu____4792 with
                     | (xs1,body2) ->
                         let xs2 =
                           let uu____4817 = FStar_Options.print_implicits ()
                              in
                           if uu____4817 then xs1 else filter_imp xs1  in
                         let xs3 =
                           FStar_All.pipe_right xs2
                             ((map_opt ())
                                (fun b  ->
                                   resugar_binder' env b
                                     t.FStar_Syntax_Syntax.pos))
                            in
                         let body3 = resugar_term' env body2  in
                         let uu____4857 =
                           let uu____4858 =
                             let uu____4879 =
                               FStar_List.map
                                 (fun _4915  -> FStar_Util.Inl _4915) xs3
                                in
                             (uu____4879, body3)  in
                           FStar_Parser_AST.Sum uu____4858  in
                         mk1 uu____4857)
                | uu____4932 ->
                    let args3 =
                      FStar_All.pipe_right args2
                        (FStar_List.map
                           (fun uu____4972  ->
                              match uu____4972 with
                              | (e1,qual) -> resugar_term' env e1))
                       in
                    let e1 = resugar_term' env e  in
                    FStar_List.fold_left
                      (fun acc  ->
                         fun x  ->
                           mk1
                             (FStar_Parser_AST.App
                                (acc, x, FStar_Parser_AST.Nothing))) e1 args3)
           | FStar_Pervasives_Native.Some ("dtuple",uu____5029) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (ref_read,uu____5038) when
               ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str ->
               let uu____5047 = FStar_List.hd args1  in
               (match uu____5047 with
                | (t1,uu____5072) ->
                    let uu____5085 =
                      let uu____5086 = FStar_Syntax_Subst.compress t1  in
                      uu____5086.FStar_Syntax_Syntax.n  in
                    (match uu____5085 with
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Syntax_Util.field_projector_contains_constructor
                           ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                         ->
                         let f =
                           FStar_Ident.lid_of_path
                             [((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str]
                             t1.FStar_Syntax_Syntax.pos
                            in
                         let uu____5123 =
                           let uu____5124 =
                             let uu____5136 = resugar_term' env t1  in
                             (uu____5136, f)  in
                           FStar_Parser_AST.Project uu____5124  in
                         mk1 uu____5123
                     | uu____5150 -> resugar_term' env t1))
           | FStar_Pervasives_Native.Some ("try_with",uu____5151) when
               (FStar_List.length args1) > (Prims.parse_int "1") ->
               let new_args = last_two args1  in
               let uu____5183 =
                 match new_args with
                 | (a1,uu____5209)::(a2,uu____5211)::[] -> (a1, a2)
                 | uu____5274 -> failwith "wrong arguments to try_with"  in
               (match uu____5183 with
                | (body,handler) ->
                    let decomp term =
                      let uu____5339 =
                        let uu____5340 = FStar_Syntax_Subst.compress term  in
                        uu____5340.FStar_Syntax_Syntax.n  in
                      match uu____5339 with
                      | FStar_Syntax_Syntax.Tm_abs (x,e1,uu____5357) ->
                          let uu____5414 = FStar_Syntax_Subst.open_term x e1
                             in
                          (match uu____5414 with | (x1,e2) -> e2)
                      | uu____5437 ->
                          failwith "wrong argument format to try_with"
                       in
                    let body1 =
                      let uu____5450 = decomp body  in
                      resugar_term' env uu____5450  in
                    let handler1 =
                      let uu____5466 = decomp handler  in
                      resugar_term' env uu____5466  in
                    let rec resugar_body t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match
                          (e1,(uu____5494,uu____5495,b)::[]) -> b
                      | FStar_Parser_AST.Let (uu____5573,uu____5574,b) -> b
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          let uu____5651 =
                            let uu____5652 =
                              let uu____5670 = resugar_body t11  in
                              (uu____5670, t2, t3)  in
                            FStar_Parser_AST.Ascribed uu____5652  in
                          mk1 uu____5651
                      | uu____5688 ->
                          failwith "unexpected body format to try_with"
                       in
                    let e1 = resugar_body body1  in
                    let rec resugar_branches t1 =
                      match t1.FStar_Parser_AST.tm with
                      | FStar_Parser_AST.Match (e2,branches) -> branches
                      | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                          resugar_branches t11
                      | uu____5817 -> []  in
                    let branches = resugar_branches handler1  in
                    mk1 (FStar_Parser_AST.TryWith (e1, branches)))
           | FStar_Pervasives_Native.Some ("try_with",uu____5874) ->
               resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____5883) when
               ((((((op = "=") || (op = "==")) || (op = "===")) || (op = "@"))
                   || (op = ":="))
                  || (op = "|>"))
                 && (FStar_Options.print_implicits ())
               -> resugar_as_app e args1
           | FStar_Pervasives_Native.Some (op,uu____5904) when
               (op = "forall") || (op = "exists") ->
               let rec uncurry xs pat t1 =
                 match t1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.QExists (x,(uu____6009,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | FStar_Parser_AST.QForall (x,(uu____6077,p),body) ->
                     uncurry (FStar_List.append x xs)
                       (FStar_List.append p pat) body
                 | uu____6144 -> (xs, pat, t1)  in
               let resugar body =
                 let uu____6178 =
                   let uu____6179 = FStar_Syntax_Subst.compress body  in
                   uu____6179.FStar_Syntax_Syntax.n  in
                 match uu____6178 with
                 | FStar_Syntax_Syntax.Tm_abs (xs,body1,uu____6195) ->
                     let uu____6252 = FStar_Syntax_Subst.open_term xs body1
                        in
                     (match uu____6252 with
                      | (xs1,body2) ->
                          let xs2 =
                            let uu____6277 = FStar_Options.print_implicits ()
                               in
                            if uu____6277 then xs1 else filter_imp xs1  in
                          let xs3 =
                            FStar_All.pipe_right xs2
                              ((map_opt ())
                                 (fun b  ->
                                    resugar_binder' env b
                                      t.FStar_Syntax_Syntax.pos))
                             in
                          let uu____6310 =
                            let uu____6325 =
                              let uu____6326 =
                                FStar_Syntax_Subst.compress body2  in
                              uu____6326.FStar_Syntax_Syntax.n  in
                            match uu____6325 with
                            | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
                                let body3 = resugar_term' env e1  in
                                let uu____6372 =
                                  match m with
                                  | FStar_Syntax_Syntax.Meta_pattern
                                      (uu____6401,pats) ->
                                      let uu____6451 =
                                        FStar_List.map
                                          (fun es  ->
                                             FStar_All.pipe_right es
                                               (FStar_List.map
                                                  (fun uu____6523  ->
                                                     match uu____6523 with
                                                     | (e2,uu____6538) ->
                                                         resugar_term' env e2)))
                                          pats
                                         in
                                      (uu____6451, body3)
                                  | FStar_Syntax_Syntax.Meta_labeled 
                                      (s,r,p) ->
                                      let uu____6568 =
                                        mk1
                                          (FStar_Parser_AST.Labeled
                                             (body3, s, p))
                                         in
                                      ([], uu____6568)
                                  | uu____6595 ->
                                      failwith
                                        "wrong pattern format for QForall/QExists"
                                   in
                                (match uu____6372 with
                                 | (pats,body4) -> (pats, body4))
                            | uu____6657 ->
                                let uu____6658 = resugar_term' env body2  in
                                ([], uu____6658)
                             in
                          (match uu____6310 with
                           | (pats,body3) ->
                               let uu____6705 = uncurry xs3 pats body3  in
                               (match uu____6705 with
                                | (xs4,pats1,body4) ->
                                    let xs5 =
                                      FStar_All.pipe_right xs4 FStar_List.rev
                                       in
                                    if op = "forall"
                                    then
                                      let uu____6795 =
                                        let uu____6796 =
                                          let uu____6827 =
                                            let uu____6843 =
                                              FStar_Parser_AST.idents_of_binders
                                                xs5 t.FStar_Syntax_Syntax.pos
                                               in
                                            (uu____6843, pats1)  in
                                          (xs5, uu____6827, body4)  in
                                        FStar_Parser_AST.QForall uu____6796
                                         in
                                      mk1 uu____6795
                                    else
                                      (let uu____6885 =
                                         let uu____6886 =
                                           let uu____6917 =
                                             let uu____6933 =
                                               FStar_Parser_AST.idents_of_binders
                                                 xs5
                                                 t.FStar_Syntax_Syntax.pos
                                                in
                                             (uu____6933, pats1)  in
                                           (xs5, uu____6917, body4)  in
                                         FStar_Parser_AST.QExists uu____6886
                                          in
                                       mk1 uu____6885))))
                 | uu____6973 ->
                     if op = "forall"
                     then
                       let uu____6980 =
                         let uu____6981 =
                           let uu____7012 = resugar_term' env body  in
                           ([], ([], []), uu____7012)  in
                         FStar_Parser_AST.QForall uu____6981  in
                       mk1 uu____6980
                     else
                       (let uu____7067 =
                          let uu____7068 =
                            let uu____7099 = resugar_term' env body  in
                            ([], ([], []), uu____7099)  in
                          FStar_Parser_AST.QExists uu____7068  in
                        mk1 uu____7067)
                  in
               if (FStar_List.length args1) > (Prims.parse_int "0")
               then
                 let args2 = last1 args1  in
                 (match args2 with
                  | (b,uu____7184)::[] -> resugar b
                  | uu____7217 -> failwith "wrong args format to QForall")
               else resugar_as_app e args1
           | FStar_Pervasives_Native.Some ("alloc",uu____7236) ->
               let uu____7244 = FStar_List.hd args1  in
               (match uu____7244 with
                | (e1,uu____7269) -> resugar_term' env e1)
           | FStar_Pervasives_Native.Some (op,expected_arity) ->
               let op1 = FStar_Ident.id_of_text op  in
               let resugar args2 =
                 FStar_All.pipe_right args2
                   (FStar_List.map
                      (fun uu____7378  ->
                         match uu____7378 with
                         | (e1,qual) ->
                             let uu____7410 = resugar_term' env e1  in
                             let uu____7417 = resugar_imp env qual  in
                             (uu____7410, uu____7417)))
                  in
               (match expected_arity with
                | FStar_Pervasives_Native.None  ->
                    let resugared_args = resugar args1  in
                    let expect_n =
                      FStar_Parser_ToDocument.handleable_args_length op1  in
                    if (FStar_List.length resugared_args) >= expect_n
                    then
                      let uu____7448 =
                        FStar_Util.first_N expect_n resugared_args  in
                      (match uu____7448 with
                       | (op_args,rest) ->
                           let head1 =
                             let uu____7526 =
                               let uu____7527 =
                                 let uu____7539 =
                                   FStar_List.map FStar_Pervasives_Native.fst
                                     op_args
                                    in
                                 (op1, uu____7539)  in
                               FStar_Parser_AST.Op uu____7527  in
                             mk1 uu____7526  in
                           FStar_List.fold_left
                             (fun head2  ->
                                fun uu____7580  ->
                                  match uu____7580 with
                                  | (arg,qual) ->
                                      mk1
                                        (FStar_Parser_AST.App
                                           (head2, arg, qual))) head1 rest)
                    else resugar_as_app e args1
                | FStar_Pervasives_Native.Some n1 when
                    (FStar_List.length args1) = n1 ->
                    let uu____7624 =
                      let uu____7625 =
                        let uu____7637 =
                          let uu____7643 = resugar args1  in
                          FStar_List.map FStar_Pervasives_Native.fst
                            uu____7643
                           in
                        (op1, uu____7637)  in
                      FStar_Parser_AST.Op uu____7625  in
                    mk1 uu____7624
                | uu____7673 -> resugar_as_app e args1))
      | FStar_Syntax_Syntax.Tm_match (e,(pat,wopt,t1)::[]) ->
          let uu____7805 = FStar_Syntax_Subst.open_branch (pat, wopt, t1)  in
          (match uu____7805 with
           | (pat1,wopt1,t2) ->
               let branch_bv = FStar_Syntax_Free.names t2  in
               let bnds =
                 let uu____7900 =
                   let uu____7921 =
                     let uu____7931 = resugar_pat' env pat1 branch_bv  in
                     let uu____7936 = resugar_term' env e  in
                     (uu____7931, uu____7936)  in
                   (FStar_Pervasives_Native.None, uu____7921)  in
                 [uu____7900]  in
               let body = resugar_term' env t2  in
               mk1
                 (FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier, bnds, body)))
      | FStar_Syntax_Syntax.Tm_match
          (e,(pat1,uu____8043,t1)::(pat2,uu____8046,t2)::[]) when
          (is_true_pat pat1) && (is_wild_pat pat2) ->
          let uu____8238 =
            let uu____8239 =
              let uu____8255 = resugar_term' env e  in
              let uu____8262 = resugar_term' env t1  in
              let uu____8269 = resugar_term' env t2  in
              (uu____8255, uu____8262, uu____8269)  in
            FStar_Parser_AST.If uu____8239  in
          mk1 uu____8238
      | FStar_Syntax_Syntax.Tm_match (e,branches) ->
          let resugar_branch uu____8399 =
            match uu____8399 with
            | (pat,wopt,b) ->
                let uu____8479 =
                  FStar_Syntax_Subst.open_branch (pat, wopt, b)  in
                (match uu____8479 with
                 | (pat1,wopt1,b1) ->
                     let branch_bv = FStar_Syntax_Free.names b1  in
                     let pat2 = resugar_pat' env pat1 branch_bv  in
                     let wopt2 =
                       match wopt1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some e1 ->
                           let uu____8602 = resugar_term' env e1  in
                           FStar_Pervasives_Native.Some uu____8602
                        in
                     let b2 = resugar_term' env b1  in (pat2, wopt2, b2))
             in
          let uu____8629 =
            let uu____8630 =
              let uu____8656 = resugar_term' env e  in
              let uu____8663 = FStar_List.map resugar_branch branches  in
              (uu____8656, uu____8663)  in
            FStar_Parser_AST.Match uu____8630  in
          mk1 uu____8629
      | FStar_Syntax_Syntax.Tm_ascribed (e,(asc,tac_opt),uu____8747) ->
          let term =
            match asc with
            | FStar_Util.Inl n1 -> resugar_term' env n1
            | FStar_Util.Inr n1 -> resugar_comp' env n1  in
          let tac_opt1 = FStar_Option.map (resugar_term' env) tac_opt  in
          let uu____8911 =
            let uu____8912 =
              let uu____8930 = resugar_term' env e  in
              (uu____8930, term, tac_opt1)  in
            FStar_Parser_AST.Ascribed uu____8912  in
          mk1 uu____8911
      | FStar_Syntax_Syntax.Tm_let ((is_rec,source_lbs),body) ->
          let mk_pat a =
            FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos  in
          let uu____9009 = FStar_Syntax_Subst.open_let_rec source_lbs body
             in
          (match uu____9009 with
           | (source_lbs1,body1) ->
               let resugar_one_binding bnd =
                 let attrs_opt =
                   match bnd.FStar_Syntax_Syntax.lbattrs with
                   | [] -> FStar_Pervasives_Native.None
                   | tms ->
                       let uu____9138 =
                         FStar_List.map (resugar_term' env) tms  in
                       FStar_Pervasives_Native.Some uu____9138
                    in
                 let uu____9158 =
                   let uu____9167 =
                     FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp
                       bnd.FStar_Syntax_Syntax.lbdef
                      in
                   FStar_Syntax_Subst.open_univ_vars
                     bnd.FStar_Syntax_Syntax.lbunivs uu____9167
                    in
                 match uu____9158 with
                 | (univs1,td) ->
                     let uu____9211 =
                       let uu____9226 =
                         let uu____9227 = FStar_Syntax_Subst.compress td  in
                         uu____9227.FStar_Syntax_Syntax.n  in
                       match uu____9226 with
                       | FStar_Syntax_Syntax.Tm_app
                           (uu____9252,(t1,uu____9254)::(d,uu____9256)::[])
                           -> (t1, d)
                       | uu____9361 -> failwith "wrong let binding format"
                        in
                     (match uu____9211 with
                      | (typ,def) ->
                          let uu____9424 =
                            let uu____9449 =
                              let uu____9450 =
                                FStar_Syntax_Subst.compress def  in
                              uu____9450.FStar_Syntax_Syntax.n  in
                            match uu____9449 with
                            | FStar_Syntax_Syntax.Tm_abs (b,t1,uu____9487) ->
                                let uu____9544 =
                                  FStar_Syntax_Subst.open_term b t1  in
                                (match uu____9544 with
                                 | (b1,t2) ->
                                     let b2 =
                                       let uu____9601 =
                                         FStar_Options.print_implicits ()  in
                                       if uu____9601
                                       then b1
                                       else filter_imp b1  in
                                     (b2, t2, true))
                            | uu____9643 -> ([], def, false)  in
                          (match uu____9424 with
                           | (binders,term,is_pat_app) ->
                               let uu____9738 =
                                 match bnd.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr fv ->
                                     ((mk_pat
                                         (FStar_Parser_AST.PatName
                                            ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))),
                                       term)
                                 | FStar_Util.Inl bv ->
                                     let uu____9795 =
                                       let uu____9800 =
                                         let uu____9801 =
                                           let uu____9810 =
                                             bv_as_unique_ident bv  in
                                           (uu____9810,
                                             FStar_Pervasives_Native.None)
                                            in
                                         FStar_Parser_AST.PatVar uu____9801
                                          in
                                       mk_pat uu____9800  in
                                     (uu____9795, term)
                                  in
                               (match uu____9738 with
                                | (pat,term1) ->
                                    let uu____9864 =
                                      if is_pat_app
                                      then
                                        let args =
                                          FStar_All.pipe_right binders
                                            ((map_opt ())
                                               (fun uu____9933  ->
                                                  match uu____9933 with
                                                  | (bv,q) ->
                                                      let uu____9965 =
                                                        resugar_arg_qual env
                                                          q
                                                         in
                                                      FStar_Util.map_opt
                                                        uu____9965
                                                        (fun q1  ->
                                                           let uu____9979 =
                                                             let uu____9980 =
                                                               let uu____9989
                                                                 =
                                                                 bv_as_unique_ident
                                                                   bv
                                                                  in
                                                               (uu____9989,
                                                                 q1)
                                                                in
                                                             FStar_Parser_AST.PatVar
                                                               uu____9980
                                                              in
                                                           mk_pat uu____9979)))
                                           in
                                        let uu____9998 =
                                          let uu____10008 =
                                            resugar_term' env term1  in
                                          ((mk_pat
                                              (FStar_Parser_AST.PatApp
                                                 (pat, args))), uu____10008)
                                           in
                                        let uu____10026 =
                                          universe_to_string univs1  in
                                        (uu____9998, uu____10026)
                                      else
                                        (let uu____10040 =
                                           let uu____10050 =
                                             resugar_term' env term1  in
                                           (pat, uu____10050)  in
                                         let uu____10062 =
                                           universe_to_string univs1  in
                                         (uu____10040, uu____10062))
                                       in
                                    (attrs_opt, uu____9864))))
                  in
               let r = FStar_List.map resugar_one_binding source_lbs1  in
               let bnds =
                 let f uu____10228 =
                   match uu____10228 with
                   | (attrs,(pb,univs1)) ->
                       let uu____10325 =
                         let uu____10327 = FStar_Options.print_universes ()
                            in
                         Prims.op_Negation uu____10327  in
                       if uu____10325
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
      | FStar_Syntax_Syntax.Tm_uvar (u,uu____10480) ->
          let s =
            let uu____10515 =
              let uu____10517 =
                FStar_Syntax_Unionfind.uvar_id
                  u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_All.pipe_right uu____10517 FStar_Util.string_of_int  in
            Prims.op_Hat "?u" uu____10515  in
          let uu____10522 = mk1 FStar_Parser_AST.Wild  in label s uu____10522
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          let qi1 =
            match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  -> FStar_Parser_AST.Static
            | FStar_Syntax_Syntax.Quote_dynamic  -> FStar_Parser_AST.Dynamic
             in
          let uu____10548 =
            let uu____10549 =
              let uu____10557 = resugar_term' env tm  in (uu____10557, qi1)
               in
            FStar_Parser_AST.Quote uu____10549  in
          mk1 uu____10548
      | FStar_Syntax_Syntax.Tm_meta (e,m) ->
          let resugar_meta_desugared uu___5_10589 =
            match uu___5_10589 with
            | FStar_Syntax_Syntax.Sequence  ->
                let term = resugar_term' env e  in
                let rec resugar_seq t1 =
                  match t1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Let
                      (uu____10618,(uu____10619,(p,t11))::[],t2) ->
                      mk1 (FStar_Parser_AST.Seq (t11, t2))
                  | FStar_Parser_AST.Ascribed (t11,t2,t3) ->
                      let uu____10755 =
                        let uu____10756 =
                          let uu____10774 = resugar_seq t11  in
                          (uu____10774, t2, t3)  in
                        FStar_Parser_AST.Ascribed uu____10756  in
                      mk1 uu____10755
                  | uu____10792 -> t1  in
                resugar_seq term
            | FStar_Syntax_Syntax.Primop  -> resugar_term' env e
            | FStar_Syntax_Syntax.Masked_effect  -> resugar_term' env e
            | FStar_Syntax_Syntax.Meta_smt_pat  -> resugar_term' env e  in
          (match m with
           | FStar_Syntax_Syntax.Meta_pattern (uu____10796,pats) ->
               let pats1 =
                 FStar_All.pipe_right (FStar_List.flatten pats)
                   (FStar_List.map
                      (fun uu____10897  ->
                         match uu____10897 with
                         | (x,uu____10912) -> resugar_term' env x))
                  in
               mk1 (FStar_Parser_AST.Attributes pats1)
           | FStar_Syntax_Syntax.Meta_labeled uu____10925 ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_desugared i -> resugar_meta_desugared i
           | FStar_Syntax_Syntax.Meta_named t1 ->
               mk1 (FStar_Parser_AST.Name t1)
           | FStar_Syntax_Syntax.Meta_monadic (name1,t1) ->
               resugar_term' env e
           | FStar_Syntax_Syntax.Meta_monadic_lift (name1,uu____10963,t1) ->
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
               let uu____11076 = FStar_Options.print_universes ()  in
               if uu____11076
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
               let uu____11220 = FStar_Options.print_universes ()  in
               if uu____11220
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
            let uu____11319 =
              resugar_term' env c1.FStar_Syntax_Syntax.result_typ  in
            (uu____11319, FStar_Parser_AST.Nothing)  in
          let uu____11329 =
            (FStar_Options.print_effect_args ()) ||
              (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                 FStar_Parser_Const.effect_Lemma_lid)
             in
          if uu____11329
          then
            let universe =
              FStar_List.map (fun u  -> resugar_universe u)
                c1.FStar_Syntax_Syntax.comp_univs
               in
            let args =
              let uu____11365 =
                FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Lemma_lid
                 in
              if uu____11365
              then
                match c1.FStar_Syntax_Syntax.effect_args with
                | pre::post::pats::[] ->
                    let post1 =
                      let uu____11490 =
                        FStar_Syntax_Util.unthunk_lemma_post
                          (FStar_Pervasives_Native.fst post)
                         in
                      (uu____11490, (FStar_Pervasives_Native.snd post))  in
                    let uu____11521 =
                      let uu____11534 =
                        FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid
                          (FStar_Pervasives_Native.fst pre)
                         in
                      if uu____11534 then [] else [pre]  in
                    let uu____11589 =
                      let uu____11602 =
                        let uu____11615 =
                          FStar_Syntax_Util.is_fvar
                            FStar_Parser_Const.nil_lid
                            (FStar_Pervasives_Native.fst pats)
                           in
                        if uu____11615 then [] else [pats]  in
                      FStar_List.append [post1] uu____11602  in
                    FStar_List.append uu____11521 uu____11589
                | uu____11710 -> c1.FStar_Syntax_Syntax.effect_args
              else c1.FStar_Syntax_Syntax.effect_args  in
            let args1 =
              FStar_List.map
                (fun uu____11758  ->
                   match uu____11758 with
                   | (e,uu____11777) ->
                       let uu____11790 = resugar_term' env e  in
                       (uu____11790, FStar_Parser_AST.Nothing)) args
               in
            let rec aux l uu___6_11830 =
              match uu___6_11830 with
              | [] -> l
              | hd1::tl1 ->
                  (match hd1 with
                   | FStar_Syntax_Syntax.DECREASES e ->
                       let e1 =
                         let uu____11879 = resugar_term' env e  in
                         (uu____11879, FStar_Parser_AST.Nothing)  in
                       aux (e1 :: l) tl1
                   | uu____11896 -> aux l tl1)
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
        let uu____11979 = b  in
        match uu____11979 with
        | (x,aq) ->
            let uu____12002 = resugar_arg_qual env aq  in
            FStar_Util.map_opt uu____12002
              (fun imp  ->
                 let e = resugar_term' env x.FStar_Syntax_Syntax.sort  in
                 match e.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Wild  ->
                     let uu____12030 =
                       let uu____12031 = bv_as_unique_ident x  in
                       FStar_Parser_AST.Variable uu____12031  in
                     FStar_Parser_AST.mk_binder uu____12030 r
                       FStar_Parser_AST.Type_level imp
                 | uu____12036 ->
                     let uu____12037 = FStar_Syntax_Syntax.is_null_bv x  in
                     if uu____12037
                     then
                       FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName e)
                         r FStar_Parser_AST.Type_level imp
                     else
                       (let uu____12046 =
                          let uu____12047 =
                            let uu____12057 = bv_as_unique_ident x  in
                            (uu____12057, e)  in
                          FStar_Parser_AST.Annotated uu____12047  in
                        FStar_Parser_AST.mk_binder uu____12046 r
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
              let uu____12102 = FStar_Syntax_Syntax.range_of_bv v1  in
              FStar_Parser_AST.mk_pattern a uu____12102  in
            let used = FStar_Util.set_mem v1 body_bv  in
            let pat =
              let uu____12115 =
                if used
                then
                  let uu____12117 =
                    let uu____12126 = bv_as_unique_ident v1  in
                    (uu____12126, aqual)  in
                  FStar_Parser_AST.PatVar uu____12117
                else FStar_Parser_AST.PatWild aqual  in
              mk1 uu____12115  in
            match typ_opt with
            | FStar_Pervasives_Native.None  -> pat
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____12145;
                  FStar_Syntax_Syntax.vars = uu____12146;_}
                -> pat
            | FStar_Pervasives_Native.Some typ ->
                let uu____12172 = FStar_Options.print_bound_var_types ()  in
                if uu____12172
                then
                  let uu____12177 =
                    let uu____12178 =
                      let uu____12197 =
                        let uu____12210 = resugar_term' env typ  in
                        (uu____12210, FStar_Pervasives_Native.None)  in
                      (pat, uu____12197)  in
                    FStar_Parser_AST.PatAscribed uu____12178  in
                  mk1 uu____12177
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
          let uu____12266 = resugar_arg_qual env qual  in
          FStar_Util.map_opt uu____12266
            (fun aqual  ->
               let uu____12280 =
                 let uu____12289 =
                   FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
                 FStar_All.pipe_left
                   (fun _12320  -> FStar_Pervasives_Native.Some _12320)
                   uu____12289
                  in
               resugar_bv_as_pat' env x aqual body_bv uu____12280)

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
          (let uu____12398 = FStar_Options.print_implicits ()  in
           Prims.op_Negation uu____12398) &&
            (let uu____12401 =
               FStar_List.existsML
                 (fun uu____12417  ->
                    match uu____12417 with
                    | (pattern,is_implicit1) ->
                        let might_be_used =
                          match pattern.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_var bv ->
                              FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_dot_term (bv,uu____12455)
                              -> FStar_Util.set_mem bv branch_bv
                          | FStar_Syntax_Syntax.Pat_wild uu____12483 -> false
                          | uu____12490 -> true  in
                        is_implicit1 && might_be_used) args
                in
             Prims.op_Negation uu____12401)
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
            let uu____12595 = may_drop_implicits args  in
            if uu____12595 then filter_pattern_imp args else args  in
          let args2 =
            FStar_List.map
              (fun uu____12627  ->
                 match uu____12627 with
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
              ((let uu____12718 =
                  let uu____12720 =
                    let uu____12722 = filter_pattern_imp args  in
                    FStar_List.isEmpty uu____12722  in
                  Prims.op_Negation uu____12720  in
                if uu____12718
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
              let uu____12793 = filter_pattern_imp args  in
              (match uu____12793 with
               | (hd1,false )::(tl1,false )::[] ->
                   let hd' = aux hd1 (FStar_Pervasives_Native.Some false)  in
                   let uu____12876 =
                     aux tl1 (FStar_Pervasives_Native.Some false)  in
                   (match uu____12876 with
                    | { FStar_Parser_AST.pat = FStar_Parser_AST.PatList tl';
                        FStar_Parser_AST.prange = p2;_} ->
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatList (hd' :: tl')) p2
                    | tl' -> resugar_plain_pat_cons' fv [hd'; tl'])
               | args' ->
                   ((let uu____12916 =
                       let uu____12922 =
                         let uu____12924 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length args')
                            in
                         FStar_Util.format1
                           "Prims.Cons applied to %s explicit arguments"
                           uu____12924
                          in
                       (FStar_Errors.Warning_ConsAppliedExplicitArgs,
                         uu____12922)
                        in
                     FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p
                       uu____12916);
                    resugar_plain_pat_cons fv args))
          | FStar_Syntax_Syntax.Pat_cons (fv,args) when
              (is_tuple_constructor_lid
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                && (may_drop_implicits args)
              ->
              let args1 =
                FStar_All.pipe_right args
                  (FStar_List.filter_map
                     (fun uu____13002  ->
                        match uu____13002 with
                        | (p2,is_implicit1) ->
                            if is_implicit1
                            then FStar_Pervasives_Native.None
                            else
                              (let uu____13025 =
                                 aux p2 (FStar_Pervasives_Native.Some false)
                                  in
                               FStar_Pervasives_Native.Some uu____13025)))
                 in
              let is_dependent_tuple =
                FStar_Parser_Const.is_dtuple_data_lid'
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              mk1 (FStar_Parser_AST.PatTuple (args1, is_dependent_tuple))
          | FStar_Syntax_Syntax.Pat_cons
              ({ FStar_Syntax_Syntax.fv_name = uu____13045;
                 FStar_Syntax_Syntax.fv_delta = uu____13046;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor (name,fields));_},args)
              ->
              let fields1 =
                let uu____13100 =
                  FStar_All.pipe_right fields
                    (FStar_List.map (fun f  -> FStar_Ident.lid_of_ids [f]))
                   in
                FStar_All.pipe_right uu____13100 FStar_List.rev  in
              let args1 =
                let uu____13152 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____13178  ->
                          match uu____13178 with
                          | (p2,b) -> aux p2 (FStar_Pervasives_Native.Some b)))
                   in
                FStar_All.pipe_right uu____13152 FStar_List.rev  in
              let rec map21 l1 l2 =
                match (l1, l2) with
                | ([],[]) -> []
                | ([],hd1::tl1) -> []
                | (hd1::tl1,[]) ->
                    let uu____13354 = map21 tl1 []  in
                    (hd1,
                      (mk1
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)))
                      :: uu____13354
                | (hd1::tl1,hd2::tl2) ->
                    let uu____13421 = map21 tl1 tl2  in (hd1, hd2) ::
                      uu____13421
                 in
              let args2 =
                let uu____13463 = map21 fields1 args1  in
                FStar_All.pipe_right uu____13463 FStar_List.rev  in
              mk1 (FStar_Parser_AST.PatRecord args2)
          | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
              resugar_plain_pat_cons fv args
          | FStar_Syntax_Syntax.Pat_var v1 ->
              let uu____13548 =
                string_to_op
                  (v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                 in
              (match uu____13548 with
               | FStar_Pervasives_Native.Some (op,uu____13562) ->
                   let uu____13579 =
                     let uu____13580 =
                       FStar_Ident.mk_ident
                         (op,
                           ((v1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     FStar_Parser_AST.PatOp uu____13580  in
                   mk1 uu____13579
               | FStar_Pervasives_Native.None  ->
                   let uu____13594 = to_arg_qual imp_opt  in
                   resugar_bv_as_pat' env v1 uu____13594 branch_bv
                     FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Pat_wild uu____13603 ->
              let uu____13609 =
                let uu____13610 = to_arg_qual imp_opt  in
                FStar_Parser_AST.PatWild uu____13610  in
              mk1 uu____13609
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
          let uu____13676 =
            let uu____13679 =
              let uu____13680 = resugar_term' env t  in
              FStar_Parser_AST.Meta uu____13680  in
            FStar_Pervasives_Native.Some uu____13679  in
          FStar_Pervasives_Native.Some uu____13676

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
          let uu____13702 = resugar_term' env t  in
          FStar_Parser_AST.HashBrace uu____13702

let (resugar_qualifier :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Parser_AST.qualifier FStar_Pervasives_Native.option)
  =
  fun uu___7_13716  ->
    match uu___7_13716 with
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
    | FStar_Syntax_Syntax.Reflectable uu____13723 ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Reflectable
    | FStar_Syntax_Syntax.Discriminator uu____13728 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Projector uu____13733 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordType uu____13744 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.RecordConstructor uu____13757 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Action uu____13770 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.ExceptionConstructor  ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.HasMaskedEffect  -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Effect  ->
        FStar_Pervasives_Native.Some FStar_Parser_AST.Effect_qual
    | FStar_Syntax_Syntax.OnlyName  -> FStar_Pervasives_Native.None
  
let (resugar_pragma : FStar_Syntax_Syntax.pragma -> FStar_Parser_AST.pragma)
  =
  fun uu___8_13780  ->
    match uu___8_13780 with
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
            (tylid,uvs,bs,t,uu____13843,datacons) ->
            let uu____13885 =
              FStar_All.pipe_right datacon_ses
                (FStar_List.partition
                   (fun se1  ->
                      match se1.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (uu____13948,uu____13949,uu____13950,inductive_lid,uu____13952,uu____13953)
                          -> FStar_Ident.lid_equals inductive_lid tylid
                      | uu____13992 -> failwith "unexpected"))
               in
            (match uu____13885 with
             | (current_datacons,other_datacons) ->
                 let bs1 =
                   let uu____14033 = FStar_Options.print_implicits ()  in
                   if uu____14033 then bs else filter_imp bs  in
                 let bs2 =
                   FStar_All.pipe_right bs1
                     ((map_opt ())
                        (fun b  ->
                           resugar_binder' env b t.FStar_Syntax_Syntax.pos))
                    in
                 let tyc =
                   let uu____14067 =
                     FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                       (FStar_Util.for_some
                          (fun uu___9_14074  ->
                             match uu___9_14074 with
                             | FStar_Syntax_Syntax.RecordType uu____14076 ->
                                 true
                             | uu____14090 -> false))
                      in
                   if uu____14067
                   then
                     let resugar_datacon_as_fields fields se1 =
                       match se1.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_datacon
                           (uu____14174,univs1,term,uu____14177,num,uu____14179)
                           ->
                           let uu____14218 =
                             let uu____14219 =
                               FStar_Syntax_Subst.compress term  in
                             uu____14219.FStar_Syntax_Syntax.n  in
                           (match uu____14218 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs3,uu____14246)
                                ->
                                let mfields =
                                  FStar_All.pipe_right bs3
                                    (FStar_List.map
                                       (fun uu____14358  ->
                                          match uu____14358 with
                                          | (b,qual) ->
                                              let uu____14399 =
                                                bv_as_unique_ident b  in
                                              let uu____14404 =
                                                resugar_term' env
                                                  b.FStar_Syntax_Syntax.sort
                                                 in
                                              (uu____14399, uu____14404,
                                                FStar_Pervasives_Native.None)))
                                   in
                                FStar_List.append mfields fields
                            | uu____14431 -> failwith "unexpected")
                       | uu____14448 -> failwith "unexpected"  in
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
                            (l,univs1,term,uu____14651,num,uu____14653) ->
                            let c =
                              let uu____14711 =
                                let uu____14717 = resugar_term' env term  in
                                FStar_Pervasives_Native.Some uu____14717  in
                              ((l.FStar_Ident.ident), uu____14711,
                                FStar_Pervasives_Native.None, false)
                               in
                            c :: constructors
                        | uu____14756 -> failwith "unexpected"  in
                      let constructors =
                        FStar_List.fold_left resugar_datacon []
                          current_datacons
                         in
                      FStar_Parser_AST.TyconVariant
                        ((tylid.FStar_Ident.ident), bs2,
                          FStar_Pervasives_Native.None, constructors))
                    in
                 (other_datacons, tyc))
        | uu____14878 ->
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
        let uu____14909 = FStar_List.choose resugar_qualifier q  in
        {
          FStar_Parser_AST.d = d';
          FStar_Parser_AST.drange = r;
          FStar_Parser_AST.doc = FStar_Pervasives_Native.None;
          FStar_Parser_AST.quals = uu____14909;
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
        let uu____14962 = ts  in
        match uu____14962 with
        | (univs1,typ) ->
            let name1 =
              FStar_Ident.mk_ident (name, (typ.FStar_Syntax_Syntax.pos))  in
            let uu____14996 =
              let uu____14997 =
                let uu____15014 =
                  let uu____15023 =
                    let uu____15030 =
                      let uu____15031 =
                        let uu____15056 = resugar_term' env typ  in
                        (name1, [], FStar_Pervasives_Native.None,
                          uu____15056)
                         in
                      FStar_Parser_AST.TyconAbbrev uu____15031  in
                    (uu____15030, FStar_Pervasives_Native.None)  in
                  [uu____15023]  in
                (false, false, uu____15014)  in
              FStar_Parser_AST.Tycon uu____14997  in
            mk_decl typ.FStar_Syntax_Syntax.pos [] uu____14996
  
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
              let uu____15245 =
                FStar_Syntax_Subst.open_term action_params
                  d.FStar_Syntax_Syntax.action_defn
                 in
              match uu____15245 with
              | (bs,action_defn) ->
                  let uu____15269 =
                    FStar_Syntax_Subst.open_term action_params
                      d.FStar_Syntax_Syntax.action_typ
                     in
                  (match uu____15269 with
                   | (bs1,action_typ) ->
                       let action_params1 =
                         let uu____15296 = FStar_Options.print_implicits ()
                            in
                         if uu____15296
                         then action_params
                         else filter_imp action_params  in
                       let action_params2 =
                         let uu____15315 =
                           FStar_All.pipe_right action_params1
                             ((map_opt ())
                                (fun b  -> resugar_binder' env b r))
                            in
                         FStar_All.pipe_right uu____15315 FStar_List.rev  in
                       let action_defn1 = resugar_term' env action_defn  in
                       let action_typ1 = resugar_term' env action_typ  in
                       if for_free1
                       then
                         let a =
                           let uu____15373 =
                             let uu____15391 =
                               FStar_Ident.lid_of_str "construct"  in
                             (uu____15391,
                               [(action_defn1, FStar_Parser_AST.Nothing);
                               (action_typ1, FStar_Parser_AST.Nothing)])
                              in
                           FStar_Parser_AST.Construct uu____15373  in
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
            let uu____15545 =
              FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
                ed.FStar_Syntax_Syntax.signature
               in
            match uu____15545 with
            | (eff_binders,eff_typ) ->
                let eff_binders1 =
                  let uu____15572 = FStar_Options.print_implicits ()  in
                  if uu____15572 then eff_binders else filter_imp eff_binders
                   in
                let eff_binders2 =
                  let uu____15591 =
                    FStar_All.pipe_right eff_binders1
                      ((map_opt ()) (fun b  -> resugar_binder' env b r))
                     in
                  FStar_All.pipe_right uu____15591 FStar_List.rev  in
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16033) ->
          let uu____16060 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun se1  ->
                    match se1.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_inductive_typ uu____16118 ->
                        true
                    | FStar_Syntax_Syntax.Sig_declare_typ uu____16152 -> true
                    | FStar_Syntax_Syntax.Sig_datacon uu____16168 -> false
                    | uu____16201 ->
                        failwith
                          "Found a sigelt which is neither a type declaration or a data constructor in a sigelt"))
             in
          (match uu____16060 with
           | (decl_typ_ses,datacon_ses) ->
               let retrieve_datacons_and_resugar uu____16274 se1 =
                 match uu____16274 with
                 | (datacon_ses1,tycons) ->
                     let uu____16320 = resugar_typ env datacon_ses1 se1  in
                     (match uu____16320 with
                      | (datacon_ses2,tyc) -> (datacon_ses2, (tyc :: tycons)))
                  in
               let uu____16335 =
                 FStar_List.fold_left retrieve_datacons_and_resugar
                   (datacon_ses, []) decl_typ_ses
                  in
               (match uu____16335 with
                | (leftover_datacons,tycons) ->
                    (match leftover_datacons with
                     | [] ->
                         let uu____16415 =
                           let uu____16426 =
                             let uu____16427 =
                               let uu____16444 =
                                 FStar_List.map
                                   (fun tyc  ->
                                      (tyc, FStar_Pervasives_Native.None))
                                   tycons
                                  in
                               (false, false, uu____16444)  in
                             FStar_Parser_AST.Tycon uu____16427  in
                           decl'_to_decl se uu____16426  in
                         FStar_Pervasives_Native.Some uu____16415
                     | se1::[] ->
                         (match se1.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_datacon
                              (l,uu____16504,uu____16505,uu____16506,uu____16507,uu____16508)
                              ->
                              let uu____16547 =
                                decl'_to_decl se1
                                  (FStar_Parser_AST.Exception
                                     ((l.FStar_Ident.ident),
                                       FStar_Pervasives_Native.None))
                                 in
                              FStar_Pervasives_Native.Some uu____16547
                          | uu____16573 ->
                              failwith
                                "wrong format for resguar to Exception")
                     | uu____16582 -> failwith "Should not happen hopefully")))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____16599) ->
          let uu____16612 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___10_16620  ->
                    match uu___10_16620 with
                    | FStar_Syntax_Syntax.Projector (uu____16622,uu____16623)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____16637 -> true
                    | uu____16643 -> false))
             in
          if uu____16612
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
             | FStar_Parser_AST.Let (isrec,lets,uu____16730) ->
                 let uu____16781 =
                   let uu____16792 =
                     let uu____16793 =
                       let uu____16809 =
                         FStar_List.map FStar_Pervasives_Native.snd lets  in
                       (isrec, uu____16809)  in
                     FStar_Parser_AST.TopLevelLet uu____16793  in
                   decl'_to_decl se uu____16792  in
                 FStar_Pervasives_Native.Some uu____16781
             | uu____16882 -> failwith "Should not happen hopefully")
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____16892,fml) ->
          let uu____16910 =
            let uu____16921 =
              let uu____16922 =
                let uu____16932 = resugar_term' env fml  in
                ((lid.FStar_Ident.ident), uu____16932)  in
              FStar_Parser_AST.Assume uu____16922  in
            decl'_to_decl se uu____16921  in
          FStar_Pervasives_Native.Some uu____16910
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____16970 =
            resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____16970
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          let uu____17008 =
            resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng
              se.FStar_Syntax_Syntax.sigquals ed
             in
          FStar_Pervasives_Native.Some uu____17008
      | FStar_Syntax_Syntax.Sig_sub_effect e ->
          let src = e.FStar_Syntax_Syntax.source  in
          let dst = e.FStar_Syntax_Syntax.target  in
          let lift_wp =
            match e.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some (uu____17063,t) ->
                let uu____17085 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____17085
            | uu____17095 -> FStar_Pervasives_Native.None  in
          let lift =
            match e.FStar_Syntax_Syntax.lift with
            | FStar_Pervasives_Native.Some (uu____17112,t) ->
                let uu____17134 = resugar_term' env t  in
                FStar_Pervasives_Native.Some uu____17134
            | uu____17144 -> FStar_Pervasives_Native.None  in
          let op =
            match (lift_wp, lift) with
            | (FStar_Pervasives_Native.Some t,FStar_Pervasives_Native.None )
                -> FStar_Parser_AST.NonReifiableLift t
            | (FStar_Pervasives_Native.Some wp,FStar_Pervasives_Native.Some
               t) -> FStar_Parser_AST.ReifiableLift (wp, t)
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t)
                -> FStar_Parser_AST.LiftForFree t
            | uu____17231 -> failwith "Should not happen hopefully"  in
          let uu____17247 =
            decl'_to_decl se
              (FStar_Parser_AST.SubEffect
                 {
                   FStar_Parser_AST.msource = src;
                   FStar_Parser_AST.mdest = dst;
                   FStar_Parser_AST.lift_op = op
                 })
             in
          FStar_Pervasives_Native.Some uu____17247
      | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,vs,bs,c,flags) ->
          let uu____17288 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____17288 with
           | (bs1,c1) ->
               let bs2 =
                 let uu____17317 = FStar_Options.print_implicits ()  in
                 if uu____17317 then bs1 else filter_imp bs1  in
               let bs3 =
                 FStar_All.pipe_right bs2
                   ((map_opt ())
                      (fun b  ->
                         resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))
                  in
               let uu____17350 =
                 let uu____17361 =
                   let uu____17362 =
                     let uu____17379 =
                       let uu____17388 =
                         let uu____17395 =
                           let uu____17396 =
                             let uu____17421 = resugar_comp' env c1  in
                             ((lid.FStar_Ident.ident), bs3,
                               FStar_Pervasives_Native.None, uu____17421)
                              in
                           FStar_Parser_AST.TyconAbbrev uu____17396  in
                         (uu____17395, FStar_Pervasives_Native.None)  in
                       [uu____17388]  in
                     (false, false, uu____17379)  in
                   FStar_Parser_AST.Tycon uu____17362  in
                 decl'_to_decl se uu____17361  in
               FStar_Pervasives_Native.Some uu____17350)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          let uu____17479 =
            decl'_to_decl se (FStar_Parser_AST.Pragma (resugar_pragma p))  in
          FStar_Pervasives_Native.Some uu____17479
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
          let uu____17514 =
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some
                 (fun uu___11_17522  ->
                    match uu___11_17522 with
                    | FStar_Syntax_Syntax.Projector (uu____17524,uu____17525)
                        -> true
                    | FStar_Syntax_Syntax.Discriminator uu____17539 -> true
                    | uu____17545 -> false))
             in
          if uu____17514
          then FStar_Pervasives_Native.None
          else
            (let t' =
               let uu____17569 =
                 (let uu____17573 = FStar_Options.print_universes ()  in
                  Prims.op_Negation uu____17573) || (FStar_List.isEmpty uvs)
                  in
               if uu____17569
               then resugar_term' env t
               else
                 (let uu____17583 = FStar_Syntax_Subst.open_univ_vars uvs t
                     in
                  match uu____17583 with
                  | (uvs1,t1) ->
                      let universes = universe_to_string uvs1  in
                      let uu____17607 = resugar_term' env t1  in
                      label universes uu____17607)
                in
             let uu____17614 =
               decl'_to_decl se
                 (FStar_Parser_AST.Val ((lid.FStar_Ident.ident), t'))
                in
             FStar_Pervasives_Native.Some uu____17614)
      | FStar_Syntax_Syntax.Sig_splice (ids,t) ->
          let uu____17657 =
            let uu____17668 =
              let uu____17669 =
                let uu____17681 =
                  FStar_List.map (fun l  -> l.FStar_Ident.ident) ids  in
                let uu____17698 = resugar_term' env t  in
                (uu____17681, uu____17698)  in
              FStar_Parser_AST.Splice uu____17669  in
            decl'_to_decl se uu____17668  in
          FStar_Pervasives_Native.Some uu____17657
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____17717 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_datacon uu____17755 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Sig_main uu____17792 ->
          FStar_Pervasives_Native.None
  
let (empty_env : FStar_Syntax_DsEnv.env) =
  FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps 
let noenv : 'a . (FStar_Syntax_DsEnv.env -> 'a) -> 'a = fun f  -> f empty_env 
let (resugar_term : FStar_Syntax_Syntax.term -> FStar_Parser_AST.term) =
  fun t  -> let uu____17839 = noenv resugar_term'  in uu____17839 t 
let (resugar_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Parser_AST.decl FStar_Pervasives_Native.option)
  = fun se  -> let uu____17891 = noenv resugar_sigelt'  in uu____17891 se 
let (resugar_comp : FStar_Syntax_Syntax.comp -> FStar_Parser_AST.term) =
  fun c  -> let uu____17943 = noenv resugar_comp'  in uu____17943 c 
let (resugar_pat :
  FStar_Syntax_Syntax.pat ->
    FStar_Syntax_Syntax.bv FStar_Util.set -> FStar_Parser_AST.pattern)
  =
  fun p  ->
    fun branch_bv  ->
      let uu____17994 = noenv resugar_pat'  in uu____17994 p branch_bv
  
let (resugar_binder :
  FStar_Syntax_Syntax.binder ->
    FStar_Range.range ->
      FStar_Parser_AST.binder FStar_Pervasives_Native.option)
  =
  fun b  ->
    fun r  -> let uu____18050 = noenv resugar_binder'  in uu____18050 b r
  
let (resugar_tscheme : FStar_Syntax_Syntax.tscheme -> FStar_Parser_AST.decl)
  = fun ts  -> let uu____18088 = noenv resugar_tscheme'  in uu____18088 ts 
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
          let uu____18178 = noenv resugar_eff_decl'  in
          uu____18178 for_free r q ed
  