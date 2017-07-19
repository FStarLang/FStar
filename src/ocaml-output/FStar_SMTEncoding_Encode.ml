open Prims
let add_fuel x tl1 =
  let uu____19 = FStar_Options.unthrottle_inductives () in
  if uu____19 then tl1 else x :: tl1
let withenv c uu____48 = match uu____48 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___101_104  ->
       match uu___101_104 with
       | (FStar_Util.Inl uu____113,uu____114) -> false
       | uu____119 -> true) args
let subst_lcomp_opt s l =
  match l with
  | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
      let uu____167 =
        let uu____172 =
          let uu____173 =
            let uu____178 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____178 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____173 in
        FStar_Util.Inl uu____172 in
      FStar_Pervasives_Native.Some uu____167
  | uu____187 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_204 = a in
        let uu____205 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____205;
          FStar_Syntax_Syntax.index =
            (uu___126_204.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_204.FStar_Syntax_Syntax.sort)
        } in
      let uu____206 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____206
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____219 =
          let uu____220 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____220 in
        let uu____221 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____221 with
        | (uu____226,t) ->
            let uu____228 =
              let uu____229 = FStar_Syntax_Subst.compress t in
              uu____229.FStar_Syntax_Syntax.n in
            (match uu____228 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____256 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____256 with
                  | (binders,uu____262) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____277 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____284 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____284
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____291 =
        let uu____296 = mk_term_projector_name lid a in
        (uu____296,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____291
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____303 =
        let uu____308 = mk_term_projector_name_by_pos lid i in
        (uu____308,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____303
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  mark: Prims.unit -> Prims.unit;
  reset_mark: Prims.unit -> Prims.unit;
  commit_mark: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____525 =
    let uu____526 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____529 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____526, uu____529) in
  let scopes =
    let uu____549 = let uu____560 = new_scope () in [uu____560] in
    FStar_Util.mk_ref uu____549 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____601 =
        let uu____604 = FStar_ST.read scopes in
        FStar_Util.find_map uu____604
          (fun uu____635  ->
             match uu____635 with
             | (names1,uu____647) -> FStar_Util.smap_try_find names1 y1) in
      match uu____601 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____656 ->
          (FStar_Util.incr ctr;
           (let uu____661 =
              let uu____662 =
                let uu____663 = FStar_ST.read ctr in
                Prims.string_of_int uu____663 in
              Prims.strcat "__" uu____662 in
            Prims.strcat y1 uu____661)) in
    let top_scope =
      let uu____669 =
        let uu____678 = FStar_ST.read scopes in FStar_List.hd uu____678 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____669 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____738 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____749 =
      let uu____750 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____750 in
    FStar_Util.format2 "%s_%s" pfx uu____749 in
  let string_const s =
    let uu____755 =
      let uu____758 = FStar_ST.read scopes in
      FStar_Util.find_map uu____758
        (fun uu____789  ->
           match uu____789 with
           | (uu____800,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____755 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____813 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____813 in
        let top_scope =
          let uu____817 =
            let uu____826 = FStar_ST.read scopes in FStar_List.hd uu____826 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____817 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____875 =
    let uu____876 =
      let uu____887 = new_scope () in
      let uu____896 = FStar_ST.read scopes in uu____887 :: uu____896 in
    FStar_ST.write scopes uu____876 in
  let pop1 uu____942 =
    let uu____943 =
      let uu____954 = FStar_ST.read scopes in FStar_List.tl uu____954 in
    FStar_ST.write scopes uu____943 in
  let mark1 uu____1000 = push1 () in
  let reset_mark1 uu____1004 = pop1 () in
  let commit_mark1 uu____1008 =
    let uu____1009 = FStar_ST.read scopes in
    match uu____1009 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.write scopes ((next1, next2) :: tl1))
    | uu____1111 -> failwith "Impossible" in
  {
    push = push1;
    pop = pop1;
    mark = mark1;
    reset_mark = reset_mark1;
    commit_mark = commit_mark1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___127_1125 = x in
    let uu____1126 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1126;
      FStar_Syntax_Syntax.index = (uu___127_1125.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_1125.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1159 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1195 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, FStar_Pervasives_Native.None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache: cache_entry FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___102_1427  ->
            match uu___102_1427 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1431 -> [])) in
  {
    cache_symbol_name = tsym;
    cache_symbol_arg_sorts = cvar_sorts;
    cache_symbol_decls = t_decls;
    cache_symbol_assumption_names = names1
  }
let use_cache_entry: cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____1440 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1447  ->
              match uu___103_1447 with
              | Binding_var (x,uu____1449) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1451,uu____1452,uu____1453) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1440 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____1495 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1495
      then
        let uu____1498 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____1498
      else FStar_Pervasives_Native.None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1511 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1511)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___128_1526 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1526.tcenv);
           warn = (uu___128_1526.warn);
           cache = (uu___128_1526.cache);
           nolabels = (uu___128_1526.nolabels);
           use_zfuel_name = (uu___128_1526.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1526.encode_non_total_function_typ);
           current_module_name = (uu___128_1526.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___129_1543 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1543.depth);
           tcenv = (uu___129_1543.tcenv);
           warn = (uu___129_1543.warn);
           cache = (uu___129_1543.cache);
           nolabels = (uu___129_1543.nolabels);
           use_zfuel_name = (uu___129_1543.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1543.encode_non_total_function_typ);
           current_module_name = (uu___129_1543.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___130_1563 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1563.depth);
             tcenv = (uu___130_1563.tcenv);
             warn = (uu___130_1563.warn);
             cache = (uu___130_1563.cache);
             nolabels = (uu___130_1563.nolabels);
             use_zfuel_name = (uu___130_1563.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1563.encode_non_total_function_typ);
             current_module_name = (uu___130_1563.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1573 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1573.depth);
          tcenv = (uu___131_1573.tcenv);
          warn = (uu___131_1573.warn);
          cache = (uu___131_1573.cache);
          nolabels = (uu___131_1573.nolabels);
          use_zfuel_name = (uu___131_1573.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1573.encode_non_total_function_typ);
          current_module_name = (uu___131_1573.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1594  ->
             match uu___104_1594 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____1607 -> FStar_Pervasives_Native.None) in
      let uu____1612 = aux a in
      match uu____1612 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____1624 = aux a2 in
          (match uu____1624 with
           | FStar_Pervasives_Native.None  ->
               let uu____1635 =
                 let uu____1636 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1637 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1636 uu____1637 in
               failwith uu____1635
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1664 =
        let uu___132_1665 = env in
        let uu____1666 =
          let uu____1669 =
            let uu____1670 =
              let uu____1683 =
                let uu____1686 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                  uu____1686 in
              (x, fname, uu____1683, FStar_Pervasives_Native.None) in
            Binding_fvar uu____1670 in
          uu____1669 :: (env.bindings) in
        {
          bindings = uu____1666;
          depth = (uu___132_1665.depth);
          tcenv = (uu___132_1665.tcenv);
          warn = (uu___132_1665.warn);
          cache = (uu___132_1665.cache);
          nolabels = (uu___132_1665.nolabels);
          use_zfuel_name = (uu___132_1665.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1665.encode_non_total_function_typ);
          current_module_name = (uu___132_1665.current_module_name)
        } in
      (fname, ftok, uu____1664)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1723  ->
           match uu___105_1723 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____1762 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1779 =
        lookup_binding env
          (fun uu___106_1782  ->
             match uu___106_1782 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____1797 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____1779 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____1816 = try_lookup_lid env a in
      match uu____1816 with
      | FStar_Pervasives_Native.None  ->
          let uu____1849 =
            let uu____1850 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1850 in
          failwith uu____1849
      | FStar_Pervasives_Native.Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___133_1898 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___133_1898.depth);
            tcenv = (uu___133_1898.tcenv);
            warn = (uu___133_1898.warn);
            cache = (uu___133_1898.cache);
            nolabels = (uu___133_1898.nolabels);
            use_zfuel_name = (uu___133_1898.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1898.encode_non_total_function_typ);
            current_module_name = (uu___133_1898.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1912 = lookup_lid env x in
        match uu____1912 with
        | (t1,t2,uu____1925) ->
            let t3 =
              let uu____1935 =
                let uu____1942 =
                  let uu____1945 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1945] in
                (f, uu____1942) in
              FStar_SMTEncoding_Util.mkApp uu____1935 in
            let uu___134_1950 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___134_1950.depth);
              tcenv = (uu___134_1950.tcenv);
              warn = (uu___134_1950.warn);
              cache = (uu___134_1950.cache);
              nolabels = (uu___134_1950.nolabels);
              use_zfuel_name = (uu___134_1950.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1950.encode_non_total_function_typ);
              current_module_name = (uu___134_1950.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____1963 = try_lookup_lid env l in
      match uu____1963 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2012 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2020,fuel::[]) ->
                         let uu____2024 =
                           let uu____2025 =
                             let uu____2026 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2026
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2025 "fuel" in
                         if uu____2024
                         then
                           let uu____2029 =
                             let uu____2030 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2030
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_30  ->
                                FStar_Pervasives_Native.Some _0_30)
                             uu____2029
                         else FStar_Pervasives_Native.Some t
                     | uu____2034 -> FStar_Pervasives_Native.Some t)
                | uu____2035 -> FStar_Pervasives_Native.None))
let lookup_free_var env a =
  let uu____2058 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____2058 with
  | FStar_Pervasives_Native.Some t -> t
  | FStar_Pervasives_Native.None  ->
      let uu____2062 =
        let uu____2063 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____2063 in
      failwith uu____2062
let lookup_free_var_name env a =
  let uu____2084 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____2084 with | (x,uu____2096,uu____2097) -> x
let lookup_free_var_sym env a =
  let uu____2132 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____2132 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | FStar_Pervasives_Native.Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____2168;
             FStar_SMTEncoding_Term.rng = uu____2169;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____2184 ->
           (match sym with
            | FStar_Pervasives_Native.None  ->
                ((FStar_SMTEncoding_Term.Var name), [])
            | FStar_Pervasives_Native.Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____2208 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_2219  ->
           match uu___107_2219 with
           | Binding_fvar (uu____2222,nm',tok,uu____2225) when nm = nm' ->
               tok
           | uu____2234 -> FStar_Pervasives_Native.None)
let mkForall_fuel' n1 uu____2256 =
  match uu____2256 with
  | (pats,vars,body) ->
      let fallback uu____2281 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____2286 = FStar_Options.unthrottle_inductives () in
      if uu____2286
      then fallback ()
      else
        (let uu____2288 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____2288 with
         | (fsym,fterm) ->
             let add_fuel1 tms =
               FStar_All.pipe_right tms
                 (FStar_List.map
                    (fun p  ->
                       match p.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Var "HasType",args) ->
                           FStar_SMTEncoding_Util.mkApp
                             ("HasTypeFuel", (fterm :: args))
                       | uu____2317 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____2338 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____2338
                     | uu____2341 ->
                         let uu____2342 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____2342 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____2347 -> body in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____2388 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2403 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2412 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2413 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2430 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2459 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2461 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2461 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2483;
             FStar_Syntax_Syntax.pos = uu____2484;
             FStar_Syntax_Syntax.vars = uu____2485;_},uu____2486)
          ->
          let uu____2515 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2515 FStar_Option.isNone
      | uu____2536 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2543 =
        let uu____2544 = FStar_Syntax_Util.un_uinst t in
        uu____2544.FStar_Syntax_Syntax.n in
      match uu____2543 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2549,uu____2550,FStar_Pervasives_Native.Some (FStar_Util.Inr
           (l,flags)))
          ->
          ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_2605  ->
                  match uu___108_2605 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2606 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2607,uu____2608,FStar_Pervasives_Native.Some (FStar_Util.Inl
           lc))
          -> FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2659 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2659 FStar_Option.isSome
      | uu____2680 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2687 = head_normal env t in
      if uu____2687
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let norm: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let trivial_post: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____2698 =
      let uu____2699 = FStar_Syntax_Syntax.null_binder t in [uu____2699] in
    let uu____2700 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____2698 uu____2700 FStar_Pervasives_Native.None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____2745 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2745
                | s ->
                    let uu____2750 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2750) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_2765  ->
    match uu___109_2765 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2766 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____2802;
                       FStar_SMTEncoding_Term.rng = uu____2803;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2826) ->
              let uu____2835 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2843 -> false) args (FStar_List.rev xs)) in
              if uu____2835
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____2847,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2851 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2853 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2853)) in
              if uu____2851
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____2857 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list;}
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____2979 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2982  ->
    match uu___110_2982 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2984 =
          let uu____2991 =
            let uu____2994 =
              let uu____2995 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2995 in
            [uu____2994] in
          ("FStar.Char.Char", uu____2991) in
        FStar_SMTEncoding_Util.mkApp uu____2984
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____3009 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____3009
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____3011) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____3027) ->
        let uu____3032 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____3032
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____3037 =
          let uu____3038 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____3038 in
        failwith uu____3037
let as_function_typ:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3061 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3076 ->
            let uu____3085 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3085
        | uu____3086 ->
            if norm1
            then let uu____3087 = whnf env t1 in aux false uu____3087
            else
              (let uu____3089 =
                 let uu____3090 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3091 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3090 uu____3091 in
               failwith uu____3089) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____3126 ->
        let uu____3127 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3127)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3167::uu____3168::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Parser_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3172::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
  | uu____3175 -> false
let rec encode_binders:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____3364 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3364
         then
           let uu____3365 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3365
         else ());
        (let uu____3367 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3438  ->
                   fun b  ->
                     match uu____3438 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3517 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____3533 = gen_term_var env1 x in
                           match uu____3533 with
                           | (xxsym,xx,env') ->
                               let uu____3557 =
                                 let uu____3562 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3562 env1 xx in
                               (match uu____3557 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____3517 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____3367 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____3721 = encode_term t env in
          match uu____3721 with
          | (t1,decls) ->
              let uu____3732 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3732, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____3743 = encode_term t env in
          match uu____3743 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____3758 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3758, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____3760 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3760, decls))
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____3768 = encode_args args_e env in
        match uu____3768 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3787 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3796 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3796 in
            let binary arg_tms1 =
              let uu____3809 =
                let uu____3810 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3810 in
              let uu____3811 =
                let uu____3812 =
                  let uu____3813 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3813 in
                FStar_SMTEncoding_Term.unboxInt uu____3812 in
              (uu____3809, uu____3811) in
            let mk_default uu____3819 =
              let uu____3820 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3820 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3875 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3875
              then
                let uu____3876 = let uu____3877 = mk_args ts in op uu____3877 in
                FStar_All.pipe_right uu____3876 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3906 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3906
              then
                let uu____3907 = binary ts in
                match uu____3907 with
                | (t1,t2) ->
                    let uu____3914 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3914
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3918 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3918
                 then
                   let uu____3919 = op (binary ts) in
                   FStar_All.pipe_right uu____3919
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____4050 =
              let uu____4059 =
                FStar_List.tryFind
                  (fun uu____4078  ->
                     match uu____4078 with
                     | (l,uu____4088) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____4059 FStar_Util.must in
            (match uu____4050 with
             | (uu____4127,op) ->
                 let uu____4137 = op arg_tms in (uu____4137, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____4146 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____4146
       then
         let uu____4147 = FStar_Syntax_Print.tag_of_term t in
         let uu____4148 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____4149 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4147 uu____4148
           uu____4149
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4155 ->
           let uu____4194 =
             let uu____4195 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4196 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4197 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4198 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4195
               uu____4196 uu____4197 uu____4198 in
           failwith uu____4194
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4203 =
             let uu____4204 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4205 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4206 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4207 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4204
               uu____4205 uu____4206 uu____4207 in
           failwith uu____4203
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4213 =
             let uu____4214 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4214 in
           failwith uu____4213
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____4221) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4279) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4293 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____4293, [])
       | FStar_Syntax_Syntax.Tm_type uu____4300 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4304) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____4314 = encode_const c in (uu____4314, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____4340 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____4340 with
            | (binders1,res) ->
                let uu____4351 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____4351
                then
                  let uu____4356 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____4356 with
                   | (vars,guards,env',decls,uu____4381) ->
                       let fsym =
                         let uu____4399 = varops.fresh "f" in
                         (uu____4399, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____4402 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_4409 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_4409.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_4409.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_4409.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_4409.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_4409.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_4409.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_4409.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_4409.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_4409.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_4409.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_4409.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_4409.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_4409.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_4409.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_4409.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_4409.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_4409.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_4409.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_4409.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_4409.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_4409.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_4409.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_4409.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____4402 with
                        | (pre_opt,res_t) ->
                            let uu____4420 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____4420 with
                             | (res_pred,decls') ->
                                 let uu____4431 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4444 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____4444, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4448 =
                                         encode_formula pre env' in
                                       (match uu____4448 with
                                        | (guard,decls0) ->
                                            let uu____4461 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____4461, decls0)) in
                                 (match uu____4431 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4473 =
                                          let uu____4484 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____4484) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4473 in
                                      let cvars =
                                        let uu____4502 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____4502
                                          (FStar_List.filter
                                             (fun uu____4513  ->
                                                match uu____4513 with
                                                | (x,uu____4519) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4538 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4538 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4546 =
                                             let uu____4547 =
                                               let uu____4554 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____4554) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4547 in
                                           (uu____4546,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4574 =
                                               let uu____4575 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4575 in
                                             varops.mk_unique uu____4574 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____4586 =
                                               FStar_Options.log_queries () in
                                             if uu____4586
                                             then
                                               let uu____4589 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4589
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____4597 =
                                               let uu____4604 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____4604) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4597 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____4616 =
                                               let uu____4623 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____4623,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4616 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____4644 =
                                               let uu____4651 =
                                                 let uu____4652 =
                                                   let uu____4663 =
                                                     let uu____4664 =
                                                       let uu____4669 =
                                                         let uu____4670 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4670 in
                                                       (f_has_t, uu____4669) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4664 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4663) in
                                                 mkForall_fuel uu____4652 in
                                               (uu____4651,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4644 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____4693 =
                                               let uu____4700 =
                                                 let uu____4701 =
                                                   let uu____4712 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4712) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____4701 in
                                               (uu____4700,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4693 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____4737 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____4737);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____4752 =
                       let uu____4759 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____4759,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4752 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____4771 =
                       let uu____4778 =
                         let uu____4779 =
                           let uu____4790 =
                             let uu____4791 =
                               let uu____4796 =
                                 let uu____4797 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4797 in
                               (f_has_t, uu____4796) in
                             FStar_SMTEncoding_Util.mkImp uu____4791 in
                           ([[f_has_t]], [fsym], uu____4790) in
                         mkForall_fuel uu____4779 in
                       (uu____4778, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4771 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4824 ->
           let uu____4833 =
             let uu____4838 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____4838 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____4845;
                 FStar_Syntax_Syntax.pos = uu____4846;
                 FStar_Syntax_Syntax.vars = uu____4847;_} ->
                 let uu____4860 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____4860 with
                  | (b,f1) ->
                      let uu____4885 =
                        let uu____4886 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____4886 in
                      (uu____4885, f1))
             | uu____4895 -> failwith "impossible" in
           (match uu____4833 with
            | (x,f) ->
                let uu____4906 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4906 with
                 | (base_t,decls) ->
                     let uu____4917 = gen_term_var env x in
                     (match uu____4917 with
                      | (x1,xtm,env') ->
                          let uu____4931 = encode_formula f env' in
                          (match uu____4931 with
                           | (refinement,decls') ->
                               let uu____4942 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4942 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4958 =
                                        let uu____4961 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4968 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4961
                                          uu____4968 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4958 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4998  ->
                                              match uu____4998 with
                                              | (y,uu____5004) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____5037 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____5037 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5045 =
                                           let uu____5046 =
                                             let uu____5053 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____5053) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5046 in
                                         (uu____5045,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____5074 =
                                             let uu____5075 =
                                               let uu____5076 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5076 in
                                             Prims.strcat module_name
                                               uu____5075 in
                                           varops.mk_unique uu____5074 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____5090 =
                                             let uu____5097 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____5097) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5090 in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____5111 =
                                             let uu____5118 =
                                               let uu____5119 =
                                                 let uu____5130 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5130) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____5119 in
                                             (uu____5118,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5111 in
                                         let t_kinding =
                                           let uu____5148 =
                                             let uu____5155 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____5155,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5148 in
                                         let t_interp =
                                           let uu____5173 =
                                             let uu____5180 =
                                               let uu____5181 =
                                                 let uu____5192 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5192) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____5181 in
                                             let uu____5215 =
                                               let uu____5218 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____5218 in
                                             (uu____5180, uu____5215,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5173 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____5225 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____5225);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____5255 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5255 in
           let uu____5262 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____5262 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5274 =
                    let uu____5281 =
                      let uu____5282 =
                        let uu____5283 =
                          let uu____5284 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____5284 in
                        FStar_Util.format1 "uvar_typing_%s" uu____5283 in
                      varops.mk_unique uu____5282 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5281) in
                  FStar_SMTEncoding_Util.mkAssume uu____5274 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5295 ->
           let uu____5314 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____5314 with
            | (head1,args_e) ->
                let uu____5367 =
                  let uu____5382 =
                    let uu____5383 = FStar_Syntax_Subst.compress head1 in
                    uu____5383.FStar_Syntax_Syntax.n in
                  (uu____5382, args_e) in
                (match uu____5367 with
                 | uu____5402 when head_redex env head1 ->
                     let uu____5417 = whnf env t in
                     encode_term uu____5417 env
                 | uu____5418 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____5442;
                       FStar_Syntax_Syntax.pos = uu____5443;
                       FStar_Syntax_Syntax.vars = uu____5444;_},uu____5445),uu____5446::
                    (v1,uu____5448)::(v2,uu____5450)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5525 = encode_term v1 env in
                     (match uu____5525 with
                      | (v11,decls1) ->
                          let uu____5536 = encode_term v2 env in
                          (match uu____5536 with
                           | (v21,decls2) ->
                               let uu____5547 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5547,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5551::(v1,uu____5553)::(v2,uu____5555)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5622 = encode_term v1 env in
                     (match uu____5622 with
                      | (v11,decls1) ->
                          let uu____5633 = encode_term v2 env in
                          (match uu____5633 with
                           | (v21,decls2) ->
                               let uu____5644 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5644,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5647) ->
                     let e0 =
                       let uu____5669 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____5669 in
                     ((let uu____5679 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____5679
                       then
                         let uu____5680 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5680
                       else ());
                      (let e =
                         let uu____5687 =
                           let uu____5688 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____5689 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5688
                             uu____5689 in
                         uu____5687 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5700),(arg,uu____5702)::[]) -> encode_term arg env
                 | uu____5737 ->
                     let uu____5752 = encode_args args_e env in
                     (match uu____5752 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5811 = encode_term head1 env in
                            match uu____5811 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5883 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____5883 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5959  ->
                                                 fun uu____5960  ->
                                                   match (uu____5959,
                                                           uu____5960)
                                                   with
                                                   | ((bv,uu____5986),
                                                      (a,uu____5988)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____6014 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____6014
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____6023 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____6023 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____6038 =
                                                   let uu____6045 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____6054 =
                                                     let uu____6055 =
                                                       let uu____6056 =
                                                         let uu____6057 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____6057 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6056 in
                                                     varops.mk_unique
                                                       uu____6055 in
                                                   (uu____6045,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6054) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6038 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____6086 = lookup_free_var_sym env fv in
                            match uu____6086 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.tk = uu____6125;
                                   FStar_Syntax_Syntax.pos = uu____6126;
                                   FStar_Syntax_Syntax.vars = uu____6127;_},uu____6128)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____6147;
                                   FStar_Syntax_Syntax.pos = uu____6148;
                                   FStar_Syntax_Syntax.vars = uu____6149;_},uu____6150)
                                ->
                                let uu____6159 =
                                  let uu____6160 =
                                    let uu____6165 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____6165
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____6160
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____6159
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6199 =
                                  let uu____6200 =
                                    let uu____6205 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____6205
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____6200
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____6199
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6238,(FStar_Util.Inl t1,uu____6240),uu____6241)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6316,(FStar_Util.Inr c,uu____6318),uu____6319)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6394 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6431 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6431 in
                               let uu____6432 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____6432 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____6448;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6449;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6450;_},uu____6451)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____6469 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____6544 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____6544 with
            | (bs1,body1,opening) ->
                let fallback uu____6567 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____6574 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____6574, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____6590 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____6590
                  | FStar_Util.Inr (eff,uu____6592) ->
                      let uu____6603 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____6603 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____6678 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_6679 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_6679.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_6679.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_6679.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_6679.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_6679.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_6679.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_6679.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_6679.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_6679.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_6679.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_6679.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_6679.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_6679.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_6679.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_6679.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_6679.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_6679.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_6679.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_6679.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_6679.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_6679.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_6679.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_6679.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____6678 FStar_Syntax_Syntax.U_unknown in
                        let uu____6680 =
                          let uu____6681 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____6681 in
                        FStar_Util.Inl uu____6680
                    | FStar_Util.Inr (eff_name,uu____6693) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____6749 =
                        let uu____6750 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____6750 in
                      FStar_All.pipe_right uu____6749
                        (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____6768 =
                        let uu____6769 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____6769
                          FStar_Pervasives_Native.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Parser_Const.effect_Tot_lid
                      then
                        let uu____6784 =
                          let uu____6785 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____6785 in
                        FStar_All.pipe_right uu____6784
                          (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Parser_Const.effect_GTot_lid
                        then
                          (let uu____6791 =
                             let uu____6792 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____6792 in
                           FStar_All.pipe_right uu____6791
                             (fun _0_33  ->
                                FStar_Pervasives_Native.Some _0_33))
                        else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6811 =
                         let uu____6812 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____6812 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____6811);
                      fallback ())
                 | FStar_Pervasives_Native.Some lc ->
                     let lc1 = lc in
                     let uu____6839 =
                       (is_impure lc1) &&
                         (let uu____6840 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____6840) in
                     if uu____6839
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____6847 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____6847 with
                        | (vars,guards,envbody,decls,uu____6872) ->
                            let uu____6885 =
                              let uu____6900 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____6900
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____6885 with
                             | (lc2,body2) ->
                                 let uu____6946 = encode_term body2 envbody in
                                 (match uu____6946 with
                                  | (body3,decls') ->
                                      let uu____6957 =
                                        let uu____6966 = codomain_eff lc2 in
                                        match uu____6966 with
                                        | FStar_Pervasives_Native.None  ->
                                            (FStar_Pervasives_Native.None,
                                              [])
                                        | FStar_Pervasives_Native.Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____6987 =
                                              encode_term tfun env in
                                            (match uu____6987 with
                                             | (t1,decls1) ->
                                                 ((FStar_Pervasives_Native.Some
                                                     t1), decls1)) in
                                      (match uu____6957 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____7019 =
                                               let uu____7030 =
                                                 let uu____7031 =
                                                   let uu____7036 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____7036, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____7031 in
                                               ([], vars, uu____7030) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____7019 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | FStar_Pervasives_Native.None 
                                                 -> cvars
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 let uu____7048 =
                                                   let uu____7051 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____7051 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____7048 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____7070 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____7070 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____7078 =
                                                  let uu____7079 =
                                                    let uu____7086 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____7086) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7079 in
                                                (uu____7078,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7097 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____7097 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____7108 =
                                                         let uu____7109 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____7109 =
                                                           cache_size in
                                                       if uu____7108
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'') in
                                                     (t1, decls1)
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.snd
                                                         cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____7125 =
                                                           let uu____7126 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____7126 in
                                                         varops.mk_unique
                                                           uu____7125 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           FStar_Pervasives_Native.None) in
                                                     let f =
                                                       let uu____7133 =
                                                         let uu____7140 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____7140) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7133 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | FStar_Pervasives_Native.None
                                                            -> []
                                                       | FStar_Pervasives_Native.Some
                                                           t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               FStar_Pervasives_Native.None
                                                               f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____7158 =
                                                             let uu____7159 =
                                                               let uu____7166
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____7166,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7159 in
                                                           [uu____7158] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____7179 =
                                                         let uu____7186 =
                                                           let uu____7187 =
                                                             let uu____7198 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7198) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____7187 in
                                                         (uu____7186,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7179 in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f]))) in
                                                     ((let uu____7215 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____7215);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7218,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7219;
                          FStar_Syntax_Syntax.lbunivs = uu____7220;
                          FStar_Syntax_Syntax.lbtyp = uu____7221;
                          FStar_Syntax_Syntax.lbeff = uu____7222;
                          FStar_Syntax_Syntax.lbdef = uu____7223;_}::uu____7224),uu____7225)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7259;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7261;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7290 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____7312 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____7312, [decl_e])))
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and encode_let:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____7383 = encode_term e1 env in
              match uu____7383 with
              | (ee1,decls1) ->
                  let uu____7394 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____7394 with
                   | (xs,e21) ->
                       let uu____7419 = FStar_List.hd xs in
                       (match uu____7419 with
                        | (x1,uu____7433) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____7435 = encode_body e21 env' in
                            (match uu____7435 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____7467 =
              let uu____7474 =
                let uu____7475 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____7475 in
              gen_term_var env uu____7474 in
            match uu____7467 with
            | (scrsym,scr',env1) ->
                let uu____7483 = encode_term e env1 in
                (match uu____7483 with
                 | (scr,decls) ->
                     let uu____7494 =
                       let encode_branch b uu____7519 =
                         match uu____7519 with
                         | (else_case,decls1) ->
                             let uu____7538 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____7538 with
                              | (p,w,br) ->
                                  let uu____7576 = encode_pat env1 p in
                                  (match uu____7576 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7609  ->
                                                   match uu____7609 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____7616 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7644 =
                                               encode_term w1 env2 in
                                             (match uu____7644 with
                                              | (w2,decls2) ->
                                                  let uu____7657 =
                                                    let uu____7658 =
                                                      let uu____7663 =
                                                        let uu____7664 =
                                                          let uu____7669 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____7669) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7664 in
                                                      (guard, uu____7663) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7658 in
                                                  (uu____7657, decls2)) in
                                       (match uu____7616 with
                                        | (guard1,decls2) ->
                                            let uu____7682 =
                                              encode_br br env2 in
                                            (match uu____7682 with
                                             | (br1,decls3) ->
                                                 let uu____7695 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____7695,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____7494 with
                      | (match_tm,decls1) ->
                          let uu____7714 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____7714, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____7754 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____7754
       then
         let uu____7755 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7755
       else ());
      (let uu____7757 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____7757 with
       | (vars,pat_term) ->
           let uu____7774 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7819  ->
                     fun v1  ->
                       match uu____7819 with
                       | (env1,vars1) ->
                           let uu____7871 = gen_term_var env1 v1 in
                           (match uu____7871 with
                            | (xx,uu____7893,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____7774 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____7976 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____7977 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____7978 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____7988 =
                        let uu____7993 = encode_const c in
                        (scrutinee, uu____7993) in
                      FStar_SMTEncoding_Util.mkEq uu____7988
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____8022 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____8022 with
                        | (uu____8029,uu____8030::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8033 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8068  ->
                                  match uu____8068 with
                                  | (arg,uu____8078) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____8092 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____8092)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8123) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8158 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8185 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8227  ->
                                  match uu____8227 with
                                  | (arg,uu____8243) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____8257 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____8257)) in
                      FStar_All.pipe_right uu____8185 FStar_List.flatten in
                let pat_term1 uu____8285 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____8295 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8324  ->
                fun uu____8325  ->
                  match (uu____8324, uu____8325) with
                  | ((tms,decls),(t,uu____8361)) ->
                      let uu____8382 = encode_term t env in
                      (match uu____8382 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____8295 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8439 = FStar_Syntax_Util.list_elements e in
        match uu____8439 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____8462 =
          let uu____8481 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____8481 FStar_Syntax_Util.head_and_args in
        match uu____8462 with
        | (head1,args) ->
            let uu____8534 =
              let uu____8549 =
                let uu____8550 = FStar_Syntax_Util.un_uinst head1 in
                uu____8550.FStar_Syntax_Syntax.n in
              (uu____8549, args) in
            (match uu____8534 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8570,uu____8571)::(e,uu____8573)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____8624 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____8668 =
            let uu____8687 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____8687 FStar_Syntax_Util.head_and_args in
          match uu____8668 with
          | (head1,args) ->
              let uu____8742 =
                let uu____8757 =
                  let uu____8758 = FStar_Syntax_Util.un_uinst head1 in
                  uu____8758.FStar_Syntax_Syntax.n in
                (uu____8757, args) in
              (match uu____8742 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8781)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8820 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____8848 = smt_pat_or1 t1 in
            (match uu____8848 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8872 = list_elements1 e in
                 FStar_All.pipe_right uu____8872
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____8892 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____8892
                           (FStar_List.map one_pat)))
             | uu____8907 ->
                 let uu____8914 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____8914])
        | uu____8945 ->
            let uu____8948 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____8948] in
      let uu____8979 =
        let uu____9004 =
          let uu____9005 = FStar_Syntax_Subst.compress t in
          uu____9005.FStar_Syntax_Syntax.n in
        match uu____9004 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9056 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____9056 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9111;
                        FStar_Syntax_Syntax.effect_name = uu____9112;
                        FStar_Syntax_Syntax.result_typ = uu____9113;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9115)::(post,uu____9117)::(pats,uu____9119)::[];
                        FStar_Syntax_Syntax.flags = uu____9120;_}
                      ->
                      let uu____9183 = lemma_pats pats in
                      (binders1, pre, post, uu____9183)
                  | uu____9208 -> failwith "impos"))
        | uu____9233 -> failwith "Impos" in
      match uu____8979 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_9299 = env in
            {
              bindings = (uu___137_9299.bindings);
              depth = (uu___137_9299.depth);
              tcenv = (uu___137_9299.tcenv);
              warn = (uu___137_9299.warn);
              cache = (uu___137_9299.cache);
              nolabels = (uu___137_9299.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_9299.encode_non_total_function_typ);
              current_module_name = (uu___137_9299.current_module_name)
            } in
          let uu____9300 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____9300 with
           | (vars,guards,env2,decls,uu____9325) ->
               let uu____9338 =
                 let uu____9351 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____9393 =
                             let uu____9402 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____9402 FStar_List.unzip in
                           match uu____9393 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____9351 FStar_List.unzip in
               (match uu____9338 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_9510 = env2 in
                      {
                        bindings = (uu___138_9510.bindings);
                        depth = (uu___138_9510.depth);
                        tcenv = (uu___138_9510.tcenv);
                        warn = (uu___138_9510.warn);
                        cache = (uu___138_9510.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_9510.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_9510.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_9510.current_module_name)
                      } in
                    let uu____9511 =
                      let uu____9516 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____9516 env3 in
                    (match uu____9511 with
                     | (pre1,decls'') ->
                         let uu____9523 =
                           let uu____9528 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____9528 env3 in
                         (match uu____9523 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____9538 =
                                let uu____9539 =
                                  let uu____9550 =
                                    let uu____9551 =
                                      let uu____9556 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____9556, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____9551 in
                                  (pats, vars, uu____9550) in
                                FStar_SMTEncoding_Util.mkForall uu____9539 in
                              (uu____9538, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____9575 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____9575
        then
          let uu____9576 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____9577 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____9576 uu____9577
        else () in
      let enc f r l =
        let uu____9610 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____9633 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____9633 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____9610 with
        | (decls,args) ->
            let uu____9662 =
              let uu___139_9663 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_9663.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_9663.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____9662, decls) in
      let const_op f r uu____9684 = let uu____9687 = f r in (uu____9687, []) in
      let un_op f l =
        let uu____9706 = FStar_List.hd l in FStar_All.pipe_left f uu____9706 in
      let bin_op f uu___111_9722 =
        match uu___111_9722 with
        | t1::t2::[] -> f (t1, t2)
        | uu____9733 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____9767 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____9783  ->
                 match uu____9783 with
                 | (t,uu____9797) ->
                     let uu____9798 = encode_formula t env in
                     (match uu____9798 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____9767 with
        | (decls,phis) ->
            let uu____9827 =
              let uu___140_9828 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_9828.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_9828.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____9827, decls) in
      let eq_op r uu___112_9847 =
        match uu___112_9847 with
        | uu____9852::e1::e2::[] ->
            let uu____9911 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____9911 r [e1; e2]
        | uu____9944::uu____9945::e1::e2::[] ->
            let uu____10020 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____10020 r [e1; e2]
        | l ->
            let uu____10054 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____10054 r l in
      let mk_imp1 r uu___113_10079 =
        match uu___113_10079 with
        | (lhs,uu____10085)::(rhs,uu____10087)::[] ->
            let uu____10128 = encode_formula rhs env in
            (match uu____10128 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10143) ->
                      (l1, decls1)
                  | uu____10148 ->
                      let uu____10149 = encode_formula lhs env in
                      (match uu____10149 with
                       | (l2,decls2) ->
                           let uu____10160 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____10160, (FStar_List.append decls1 decls2)))))
        | uu____10163 -> failwith "impossible" in
      let mk_ite r uu___114_10184 =
        match uu___114_10184 with
        | (guard,uu____10190)::(_then,uu____10192)::(_else,uu____10194)::[]
            ->
            let uu____10251 = encode_formula guard env in
            (match uu____10251 with
             | (g,decls1) ->
                 let uu____10262 = encode_formula _then env in
                 (match uu____10262 with
                  | (t,decls2) ->
                      let uu____10273 = encode_formula _else env in
                      (match uu____10273 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10287 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____10312 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____10312 in
      let connectives =
        let uu____10330 =
          let uu____10343 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____10343) in
        let uu____10360 =
          let uu____10375 =
            let uu____10388 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____10388) in
          let uu____10405 =
            let uu____10420 =
              let uu____10435 =
                let uu____10448 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____10448) in
              let uu____10465 =
                let uu____10480 =
                  let uu____10495 =
                    let uu____10508 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____10508) in
                  [uu____10495;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____10480 in
              uu____10435 :: uu____10465 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____10420 in
          uu____10375 :: uu____10405 in
        uu____10330 :: uu____10360 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____10747 = encode_formula phi' env in
            (match uu____10747 with
             | (phi2,decls) ->
                 let uu____10758 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____10758, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____10759 ->
            let uu____10768 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____10768 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____10823 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____10823 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____10835;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____10837;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____10866 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____10866 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10923::(x,uu____10925)::(t,uu____10927)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10994 = encode_term x env in
                 (match uu____10994 with
                  | (x1,decls) ->
                      let uu____11005 = encode_term t env in
                      (match uu____11005 with
                       | (t1,decls') ->
                           let uu____11016 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11016, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11021)::(msg,uu____11023)::(phi2,uu____11025)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11092 =
                   let uu____11097 =
                     let uu____11098 = FStar_Syntax_Subst.compress r in
                     uu____11098.FStar_Syntax_Syntax.n in
                   let uu____11103 =
                     let uu____11104 = FStar_Syntax_Subst.compress msg in
                     uu____11104.FStar_Syntax_Syntax.n in
                   (uu____11097, uu____11103) in
                 (match uu____11092 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11115))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) FStar_Pervasives_Native.None
                          r1 in
                      fallback phi3
                  | uu____11129 -> fallback phi2)
             | uu____11134 when head_redex env head2 ->
                 let uu____11149 = whnf env phi1 in
                 encode_formula uu____11149 env
             | uu____11150 ->
                 let uu____11165 = encode_term phi1 env in
                 (match uu____11165 with
                  | (tt,decls) ->
                      let uu____11176 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_11177 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_11177.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_11177.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____11176, decls)))
        | uu____11178 ->
            let uu____11179 = encode_term phi1 env in
            (match uu____11179 with
             | (tt,decls) ->
                 let uu____11190 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_11191 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_11191.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_11191.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____11190, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____11227 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____11227 with
        | (vars,guards,env2,decls,uu____11266) ->
            let uu____11279 =
              let uu____11292 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____11336 =
                          let uu____11345 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____11372  ->
                                    match uu____11372 with
                                    | (t,uu____11382) ->
                                        encode_term t
                                          (let uu___143_11383 = env2 in
                                           {
                                             bindings =
                                               (uu___143_11383.bindings);
                                             depth = (uu___143_11383.depth);
                                             tcenv = (uu___143_11383.tcenv);
                                             warn = (uu___143_11383.warn);
                                             cache = (uu___143_11383.cache);
                                             nolabels =
                                               (uu___143_11383.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_11383.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_11383.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____11345 FStar_List.unzip in
                        match uu____11336 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____11292 FStar_List.unzip in
            (match uu____11279 with
             | (pats,decls') ->
                 let uu____11482 = encode_formula body env2 in
                 (match uu____11482 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____11514;
                             FStar_SMTEncoding_Term.rng = uu____11515;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____11530 -> guards in
                      let uu____11535 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____11535, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____11592  ->
                   match uu____11592 with
                   | (x,uu____11598) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____11606 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____11615 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____11615) uu____11606 tl1 in
             let uu____11618 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____11641  ->
                       match uu____11641 with
                       | (b,uu____11647) ->
                           let uu____11648 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____11648)) in
             (match uu____11618 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____11654) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____11670 =
                    let uu____11671 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____11671 in
                  FStar_Errors.warn pos uu____11670) in
       let uu____11672 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____11672 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____11681 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____11736  ->
                     match uu____11736 with
                     | (l,uu____11750) -> FStar_Ident.lid_equals op l)) in
           (match uu____11681 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____11783,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____11823 = encode_q_body env vars pats body in
             match uu____11823 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____11868 =
                     let uu____11879 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____11879) in
                   FStar_SMTEncoding_Term.mkForall uu____11868
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____11898 = encode_q_body env vars pats body in
             match uu____11898 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____11942 =
                   let uu____11943 =
                     let uu____11954 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____11954) in
                   FStar_SMTEncoding_Term.mkExists uu____11943
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____11942, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____12021 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____12021 with
  | (asym,a) ->
      let uu____12028 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____12028 with
       | (xsym,x) ->
           let uu____12035 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____12035 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____12079 =
                      let uu____12090 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____12090, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____12079 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____12116 =
                      let uu____12123 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____12123) in
                    FStar_SMTEncoding_Util.mkApp uu____12116 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____12136 =
                    let uu____12139 =
                      let uu____12142 =
                        let uu____12145 =
                          let uu____12146 =
                            let uu____12153 =
                              let uu____12154 =
                                let uu____12165 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____12165) in
                              FStar_SMTEncoding_Util.mkForall uu____12154 in
                            (uu____12153, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____12146 in
                        let uu____12182 =
                          let uu____12185 =
                            let uu____12186 =
                              let uu____12193 =
                                let uu____12194 =
                                  let uu____12205 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____12205) in
                                FStar_SMTEncoding_Util.mkForall uu____12194 in
                              (uu____12193,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____12186 in
                          [uu____12185] in
                        uu____12145 :: uu____12182 in
                      xtok_decl :: uu____12142 in
                    xname_decl :: uu____12139 in
                  (xtok1, uu____12136) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____12296 =
                    let uu____12309 =
                      let uu____12318 =
                        let uu____12319 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____12319 in
                      quant axy uu____12318 in
                    (FStar_Parser_Const.op_Eq, uu____12309) in
                  let uu____12328 =
                    let uu____12343 =
                      let uu____12356 =
                        let uu____12365 =
                          let uu____12366 =
                            let uu____12367 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____12367 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____12366 in
                        quant axy uu____12365 in
                      (FStar_Parser_Const.op_notEq, uu____12356) in
                    let uu____12376 =
                      let uu____12391 =
                        let uu____12404 =
                          let uu____12413 =
                            let uu____12414 =
                              let uu____12415 =
                                let uu____12420 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____12421 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____12420, uu____12421) in
                              FStar_SMTEncoding_Util.mkLT uu____12415 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____12414 in
                          quant xy uu____12413 in
                        (FStar_Parser_Const.op_LT, uu____12404) in
                      let uu____12430 =
                        let uu____12445 =
                          let uu____12458 =
                            let uu____12467 =
                              let uu____12468 =
                                let uu____12469 =
                                  let uu____12474 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____12475 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____12474, uu____12475) in
                                FStar_SMTEncoding_Util.mkLTE uu____12469 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____12468 in
                            quant xy uu____12467 in
                          (FStar_Parser_Const.op_LTE, uu____12458) in
                        let uu____12484 =
                          let uu____12499 =
                            let uu____12512 =
                              let uu____12521 =
                                let uu____12522 =
                                  let uu____12523 =
                                    let uu____12528 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____12529 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____12528, uu____12529) in
                                  FStar_SMTEncoding_Util.mkGT uu____12523 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____12522 in
                              quant xy uu____12521 in
                            (FStar_Parser_Const.op_GT, uu____12512) in
                          let uu____12538 =
                            let uu____12553 =
                              let uu____12566 =
                                let uu____12575 =
                                  let uu____12576 =
                                    let uu____12577 =
                                      let uu____12582 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____12583 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____12582, uu____12583) in
                                    FStar_SMTEncoding_Util.mkGTE uu____12577 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____12576 in
                                quant xy uu____12575 in
                              (FStar_Parser_Const.op_GTE, uu____12566) in
                            let uu____12592 =
                              let uu____12607 =
                                let uu____12620 =
                                  let uu____12629 =
                                    let uu____12630 =
                                      let uu____12631 =
                                        let uu____12636 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____12637 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____12636, uu____12637) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____12631 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____12630 in
                                  quant xy uu____12629 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____12620) in
                              let uu____12646 =
                                let uu____12661 =
                                  let uu____12674 =
                                    let uu____12683 =
                                      let uu____12684 =
                                        let uu____12685 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____12685 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____12684 in
                                    quant qx uu____12683 in
                                  (FStar_Parser_Const.op_Minus, uu____12674) in
                                let uu____12694 =
                                  let uu____12709 =
                                    let uu____12722 =
                                      let uu____12731 =
                                        let uu____12732 =
                                          let uu____12733 =
                                            let uu____12738 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____12739 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____12738, uu____12739) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____12733 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____12732 in
                                      quant xy uu____12731 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____12722) in
                                  let uu____12748 =
                                    let uu____12763 =
                                      let uu____12776 =
                                        let uu____12785 =
                                          let uu____12786 =
                                            let uu____12787 =
                                              let uu____12792 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____12793 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____12792, uu____12793) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____12787 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____12786 in
                                        quant xy uu____12785 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____12776) in
                                    let uu____12802 =
                                      let uu____12817 =
                                        let uu____12830 =
                                          let uu____12839 =
                                            let uu____12840 =
                                              let uu____12841 =
                                                let uu____12846 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____12847 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____12846, uu____12847) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____12841 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____12840 in
                                          quant xy uu____12839 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____12830) in
                                      let uu____12856 =
                                        let uu____12871 =
                                          let uu____12884 =
                                            let uu____12893 =
                                              let uu____12894 =
                                                let uu____12895 =
                                                  let uu____12900 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____12901 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____12900, uu____12901) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____12895 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____12894 in
                                            quant xy uu____12893 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____12884) in
                                        let uu____12910 =
                                          let uu____12925 =
                                            let uu____12938 =
                                              let uu____12947 =
                                                let uu____12948 =
                                                  let uu____12949 =
                                                    let uu____12954 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____12955 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____12954,
                                                      uu____12955) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____12949 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____12948 in
                                              quant xy uu____12947 in
                                            (FStar_Parser_Const.op_And,
                                              uu____12938) in
                                          let uu____12964 =
                                            let uu____12979 =
                                              let uu____12992 =
                                                let uu____13001 =
                                                  let uu____13002 =
                                                    let uu____13003 =
                                                      let uu____13008 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____13009 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____13008,
                                                        uu____13009) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____13003 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13002 in
                                                quant xy uu____13001 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____12992) in
                                            let uu____13018 =
                                              let uu____13033 =
                                                let uu____13046 =
                                                  let uu____13055 =
                                                    let uu____13056 =
                                                      let uu____13057 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____13057 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____13056 in
                                                  quant qx uu____13055 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____13046) in
                                              [uu____13033] in
                                            uu____12979 :: uu____13018 in
                                          uu____12925 :: uu____12964 in
                                        uu____12871 :: uu____12910 in
                                      uu____12817 :: uu____12856 in
                                    uu____12763 :: uu____12802 in
                                  uu____12709 :: uu____12748 in
                                uu____12661 :: uu____12694 in
                              uu____12607 :: uu____12646 in
                            uu____12553 :: uu____12592 in
                          uu____12499 :: uu____12538 in
                        uu____12445 :: uu____12484 in
                      uu____12391 :: uu____12430 in
                    uu____12343 :: uu____12376 in
                  uu____12296 :: uu____12328 in
                let mk1 l v1 =
                  let uu____13271 =
                    let uu____13280 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____13335  ->
                              match uu____13335 with
                              | (l',uu____13349) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____13280
                      (FStar_Option.map
                         (fun uu____13406  ->
                            match uu____13406 with | (uu____13425,b) -> b v1)) in
                  FStar_All.pipe_right uu____13271 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____13493  ->
                          match uu____13493 with
                          | (l',uu____13507) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____13545 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____13545 with
        | (xxsym,xx) ->
            let uu____13552 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____13552 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____13562 =
                   let uu____13569 =
                     let uu____13570 =
                       let uu____13581 =
                         let uu____13582 =
                           let uu____13587 =
                             let uu____13588 =
                               let uu____13593 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____13593) in
                             FStar_SMTEncoding_Util.mkEq uu____13588 in
                           (xx_has_type, uu____13587) in
                         FStar_SMTEncoding_Util.mkImp uu____13582 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____13581) in
                     FStar_SMTEncoding_Util.mkForall uu____13570 in
                   let uu____13618 =
                     let uu____13619 =
                       let uu____13620 =
                         let uu____13621 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____13621 in
                       Prims.strcat module_name uu____13620 in
                     varops.mk_unique uu____13619 in
                   (uu____13569, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____13618) in
                 FStar_SMTEncoding_Util.mkAssume uu____13562)
let primitive_type_axioms:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____13657 =
      let uu____13658 =
        let uu____13665 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____13665, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____13658 in
    let uu____13668 =
      let uu____13671 =
        let uu____13672 =
          let uu____13679 =
            let uu____13680 =
              let uu____13691 =
                let uu____13692 =
                  let uu____13697 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____13697) in
                FStar_SMTEncoding_Util.mkImp uu____13692 in
              ([[typing_pred]], [xx], uu____13691) in
            mkForall_fuel uu____13680 in
          (uu____13679, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____13672 in
      [uu____13671] in
    uu____13657 :: uu____13668 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____13739 =
      let uu____13740 =
        let uu____13747 =
          let uu____13748 =
            let uu____13759 =
              let uu____13764 =
                let uu____13767 = FStar_SMTEncoding_Term.boxBool b in
                [uu____13767] in
              [uu____13764] in
            let uu____13772 =
              let uu____13773 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____13773 tt in
            (uu____13759, [bb], uu____13772) in
          FStar_SMTEncoding_Util.mkForall uu____13748 in
        (uu____13747, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____13740 in
    let uu____13794 =
      let uu____13797 =
        let uu____13798 =
          let uu____13805 =
            let uu____13806 =
              let uu____13817 =
                let uu____13818 =
                  let uu____13823 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____13823) in
                FStar_SMTEncoding_Util.mkImp uu____13818 in
              ([[typing_pred]], [xx], uu____13817) in
            mkForall_fuel uu____13806 in
          (uu____13805, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____13798 in
      [uu____13797] in
    uu____13739 :: uu____13794 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____13873 =
        let uu____13874 =
          let uu____13881 =
            let uu____13884 =
              let uu____13887 =
                let uu____13890 = FStar_SMTEncoding_Term.boxInt a in
                let uu____13891 =
                  let uu____13894 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____13894] in
                uu____13890 :: uu____13891 in
              tt :: uu____13887 in
            tt :: uu____13884 in
          ("Prims.Precedes", uu____13881) in
        FStar_SMTEncoding_Util.mkApp uu____13874 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____13873 in
    let precedes_y_x =
      let uu____13898 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____13898 in
    let uu____13901 =
      let uu____13902 =
        let uu____13909 =
          let uu____13910 =
            let uu____13921 =
              let uu____13926 =
                let uu____13929 = FStar_SMTEncoding_Term.boxInt b in
                [uu____13929] in
              [uu____13926] in
            let uu____13934 =
              let uu____13935 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____13935 tt in
            (uu____13921, [bb], uu____13934) in
          FStar_SMTEncoding_Util.mkForall uu____13910 in
        (uu____13909, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____13902 in
    let uu____13956 =
      let uu____13959 =
        let uu____13960 =
          let uu____13967 =
            let uu____13968 =
              let uu____13979 =
                let uu____13980 =
                  let uu____13985 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____13985) in
                FStar_SMTEncoding_Util.mkImp uu____13980 in
              ([[typing_pred]], [xx], uu____13979) in
            mkForall_fuel uu____13968 in
          (uu____13967, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____13960 in
      let uu____14010 =
        let uu____14013 =
          let uu____14014 =
            let uu____14021 =
              let uu____14022 =
                let uu____14033 =
                  let uu____14034 =
                    let uu____14039 =
                      let uu____14040 =
                        let uu____14043 =
                          let uu____14046 =
                            let uu____14049 =
                              let uu____14050 =
                                let uu____14055 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____14056 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____14055, uu____14056) in
                              FStar_SMTEncoding_Util.mkGT uu____14050 in
                            let uu____14057 =
                              let uu____14060 =
                                let uu____14061 =
                                  let uu____14066 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____14067 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____14066, uu____14067) in
                                FStar_SMTEncoding_Util.mkGTE uu____14061 in
                              let uu____14068 =
                                let uu____14071 =
                                  let uu____14072 =
                                    let uu____14077 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____14078 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____14077, uu____14078) in
                                  FStar_SMTEncoding_Util.mkLT uu____14072 in
                                [uu____14071] in
                              uu____14060 :: uu____14068 in
                            uu____14049 :: uu____14057 in
                          typing_pred_y :: uu____14046 in
                        typing_pred :: uu____14043 in
                      FStar_SMTEncoding_Util.mk_and_l uu____14040 in
                    (uu____14039, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____14034 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____14033) in
              mkForall_fuel uu____14022 in
            (uu____14021,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____14014 in
        [uu____14013] in
      uu____13959 :: uu____14010 in
    uu____13901 :: uu____13956 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14124 =
      let uu____14125 =
        let uu____14132 =
          let uu____14133 =
            let uu____14144 =
              let uu____14149 =
                let uu____14152 = FStar_SMTEncoding_Term.boxString b in
                [uu____14152] in
              [uu____14149] in
            let uu____14157 =
              let uu____14158 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____14158 tt in
            (uu____14144, [bb], uu____14157) in
          FStar_SMTEncoding_Util.mkForall uu____14133 in
        (uu____14132, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14125 in
    let uu____14179 =
      let uu____14182 =
        let uu____14183 =
          let uu____14190 =
            let uu____14191 =
              let uu____14202 =
                let uu____14203 =
                  let uu____14208 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____14208) in
                FStar_SMTEncoding_Util.mkImp uu____14203 in
              ([[typing_pred]], [xx], uu____14202) in
            mkForall_fuel uu____14191 in
          (uu____14190, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14183 in
      [uu____14182] in
    uu____14124 :: uu____14179 in
  let mk_ref1 env reft_name uu____14242 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____14259 =
        let uu____14266 =
          let uu____14269 = FStar_SMTEncoding_Util.mkFreeV aa in
          [uu____14269] in
        (reft_name, uu____14266) in
      FStar_SMTEncoding_Util.mkApp uu____14259 in
    let refb =
      let uu____14273 =
        let uu____14280 =
          let uu____14283 = FStar_SMTEncoding_Util.mkFreeV bb in
          [uu____14283] in
        (reft_name, uu____14280) in
      FStar_SMTEncoding_Util.mkApp uu____14273 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____14288 =
      let uu____14289 =
        let uu____14296 =
          let uu____14297 =
            let uu____14308 =
              let uu____14309 =
                let uu____14314 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____14314) in
              FStar_SMTEncoding_Util.mkImp uu____14309 in
            ([[typing_pred]], [xx; aa], uu____14308) in
          mkForall_fuel uu____14297 in
        (uu____14296, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____14289 in
    [uu____14288] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____14371 =
      let uu____14372 =
        let uu____14379 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____14379, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14372 in
    [uu____14371] in
  let mk_and_interp env conj uu____14391 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____14416 =
      let uu____14417 =
        let uu____14424 =
          let uu____14425 =
            let uu____14436 =
              let uu____14437 =
                let uu____14442 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____14442, valid) in
              FStar_SMTEncoding_Util.mkIff uu____14437 in
            ([[l_and_a_b]], [aa; bb], uu____14436) in
          FStar_SMTEncoding_Util.mkForall uu____14425 in
        (uu____14424, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14417 in
    [uu____14416] in
  let mk_or_interp env disj uu____14480 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____14505 =
      let uu____14506 =
        let uu____14513 =
          let uu____14514 =
            let uu____14525 =
              let uu____14526 =
                let uu____14531 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____14531, valid) in
              FStar_SMTEncoding_Util.mkIff uu____14526 in
            ([[l_or_a_b]], [aa; bb], uu____14525) in
          FStar_SMTEncoding_Util.mkForall uu____14514 in
        (uu____14513, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14506 in
    [uu____14505] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____14594 =
      let uu____14595 =
        let uu____14602 =
          let uu____14603 =
            let uu____14614 =
              let uu____14615 =
                let uu____14620 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____14620, valid) in
              FStar_SMTEncoding_Util.mkIff uu____14615 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____14614) in
          FStar_SMTEncoding_Util.mkForall uu____14603 in
        (uu____14602, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14595 in
    [uu____14594] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____14693 =
      let uu____14694 =
        let uu____14701 =
          let uu____14702 =
            let uu____14713 =
              let uu____14714 =
                let uu____14719 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____14719, valid) in
              FStar_SMTEncoding_Util.mkIff uu____14714 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____14713) in
          FStar_SMTEncoding_Util.mkForall uu____14702 in
        (uu____14701, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14694 in
    [uu____14693] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____14790 =
      let uu____14791 =
        let uu____14798 =
          let uu____14799 =
            let uu____14810 =
              let uu____14811 =
                let uu____14816 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____14816, valid) in
              FStar_SMTEncoding_Util.mkIff uu____14811 in
            ([[l_imp_a_b]], [aa; bb], uu____14810) in
          FStar_SMTEncoding_Util.mkForall uu____14799 in
        (uu____14798, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14791 in
    [uu____14790] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____14879 =
      let uu____14880 =
        let uu____14887 =
          let uu____14888 =
            let uu____14899 =
              let uu____14900 =
                let uu____14905 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____14905, valid) in
              FStar_SMTEncoding_Util.mkIff uu____14900 in
            ([[l_iff_a_b]], [aa; bb], uu____14899) in
          FStar_SMTEncoding_Util.mkForall uu____14888 in
        (uu____14887, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14880 in
    [uu____14879] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____14957 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____14957 in
    let uu____14960 =
      let uu____14961 =
        let uu____14968 =
          let uu____14969 =
            let uu____14980 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____14980) in
          FStar_SMTEncoding_Util.mkForall uu____14969 in
        (uu____14968, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____14961 in
    [uu____14960] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____15040 =
        let uu____15047 =
          let uu____15050 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15050] in
        ("Valid", uu____15047) in
      FStar_SMTEncoding_Util.mkApp uu____15040 in
    let uu____15053 =
      let uu____15054 =
        let uu____15061 =
          let uu____15062 =
            let uu____15073 =
              let uu____15074 =
                let uu____15079 =
                  let uu____15080 =
                    let uu____15091 =
                      let uu____15096 =
                        let uu____15099 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15099] in
                      [uu____15096] in
                    let uu____15104 =
                      let uu____15105 =
                        let uu____15110 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____15110, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____15105 in
                    (uu____15091, [xx1], uu____15104) in
                  FStar_SMTEncoding_Util.mkForall uu____15080 in
                (uu____15079, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15074 in
            ([[l_forall_a_b]], [aa; bb], uu____15073) in
          FStar_SMTEncoding_Util.mkForall uu____15062 in
        (uu____15061, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15054 in
    [uu____15053] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____15192 =
        let uu____15199 =
          let uu____15202 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15202] in
        ("Valid", uu____15199) in
      FStar_SMTEncoding_Util.mkApp uu____15192 in
    let uu____15205 =
      let uu____15206 =
        let uu____15213 =
          let uu____15214 =
            let uu____15225 =
              let uu____15226 =
                let uu____15231 =
                  let uu____15232 =
                    let uu____15243 =
                      let uu____15248 =
                        let uu____15251 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15251] in
                      [uu____15248] in
                    let uu____15256 =
                      let uu____15257 =
                        let uu____15262 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____15262, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____15257 in
                    (uu____15243, [xx1], uu____15256) in
                  FStar_SMTEncoding_Util.mkExists uu____15232 in
                (uu____15231, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15226 in
            ([[l_exists_a_b]], [aa; bb], uu____15225) in
          FStar_SMTEncoding_Util.mkForall uu____15214 in
        (uu____15213, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15206 in
    [uu____15205] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____15322 =
      let uu____15323 =
        let uu____15330 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____15331 = varops.mk_unique "typing_range_const" in
        (uu____15330, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____15331) in
      FStar_SMTEncoding_Util.mkAssume uu____15323 in
    [uu____15322] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.ref_lid, mk_ref1);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____15633 =
            FStar_Util.find_opt
              (fun uu____15656  ->
                 match uu____15656 with
                 | (l,uu____15668) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____15633 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____15693,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____15733 = encode_function_type_as_formula t env in
        match uu____15733 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____15774 =
              (let uu____15775 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____15775) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____15774
            then
              let uu____15782 = new_term_constant_and_tok_from_lid env lid in
              match uu____15782 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____15801 =
                      let uu____15802 = FStar_Syntax_Subst.compress t_norm in
                      uu____15802.FStar_Syntax_Syntax.n in
                    match uu____15801 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15810) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____15843  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____15848 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____15862 = prims.is lid in
               if uu____15862
               then
                 let vname = varops.new_fvar lid in
                 let uu____15870 = prims.mk lid vname in
                 match uu____15870 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____15894 =
                    let uu____15905 = curried_arrow_formals_comp t_norm in
                    match uu____15905 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____15923 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____15923
                          then
                            let uu____15924 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_15925 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_15925.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_15925.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_15925.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_15925.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_15925.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_15925.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_15925.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_15925.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_15925.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_15925.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_15925.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_15925.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_15925.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_15925.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_15925.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_15925.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_15925.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_15925.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_15925.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_15925.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_15925.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_15925.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_15925.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____15924
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____15937 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____15937)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____15894 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____15986 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____15986 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____16007 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_16041  ->
                                     match uu___115_16041 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____16045 =
                                           FStar_Util.prefix vars in
                                         (match uu____16045 with
                                          | (uu____16066,(xxsym,uu____16068))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____16086 =
                                                let uu____16087 =
                                                  let uu____16094 =
                                                    let uu____16095 =
                                                      let uu____16106 =
                                                        let uu____16107 =
                                                          let uu____16112 =
                                                            let uu____16113 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____16113 in
                                                          (vapp, uu____16112) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____16107 in
                                                      ([[vapp]], vars,
                                                        uu____16106) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____16095 in
                                                  (uu____16094,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____16087 in
                                              [uu____16086])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____16132 =
                                           FStar_Util.prefix vars in
                                         (match uu____16132 with
                                          | (uu____16153,(xxsym,uu____16155))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                } in
                                              let tp_name =
                                                mk_term_projector_name d f1 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx]) in
                                              let uu____16178 =
                                                let uu____16179 =
                                                  let uu____16186 =
                                                    let uu____16187 =
                                                      let uu____16198 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____16198) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____16187 in
                                                  (uu____16186,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____16179 in
                                              [uu____16178])
                                     | uu____16215 -> [])) in
                           let uu____16216 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____16216 with
                            | (vars,guards,env',decls1,uu____16243) ->
                                let uu____16256 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____16265 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____16265, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____16267 = encode_formula p env' in
                                      (match uu____16267 with
                                       | (g,ds) ->
                                           let uu____16278 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____16278,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____16256 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____16291 =
                                         let uu____16298 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____16298) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____16291 in
                                     let uu____16307 =
                                       let vname_decl =
                                         let uu____16315 =
                                           let uu____16326 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____16335  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____16326,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____16315 in
                                       let uu____16344 =
                                         let env2 =
                                           let uu___145_16350 = env1 in
                                           {
                                             bindings =
                                               (uu___145_16350.bindings);
                                             depth = (uu___145_16350.depth);
                                             tcenv = (uu___145_16350.tcenv);
                                             warn = (uu___145_16350.warn);
                                             cache = (uu___145_16350.cache);
                                             nolabels =
                                               (uu___145_16350.nolabels);
                                             use_zfuel_name =
                                               (uu___145_16350.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_16350.current_module_name)
                                           } in
                                         let uu____16351 =
                                           let uu____16352 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____16352 in
                                         if uu____16351
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____16344 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____16367::uu____16368 ->
                                                 let ff =
                                                   ("ty",
                                                     FStar_SMTEncoding_Term.Term_sort) in
                                                 let f =
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                     ff in
                                                 let vtok_app_l =
                                                   mk_Apply vtok_tm [ff] in
                                                 let vtok_app_r =
                                                   mk_Apply f
                                                     [(vtok,
                                                        FStar_SMTEncoding_Term.Term_sort)] in
                                                 let guarded_tok_typing =
                                                   let uu____16408 =
                                                     let uu____16419 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____16419) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____16408 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____16446 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____16449 =
                                             match formals with
                                             | [] ->
                                                 let uu____16466 =
                                                   let uu____16467 =
                                                     let uu____16470 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_34)
                                                       uu____16470 in
                                                   push_free_var env1 lid
                                                     vname uu____16467 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____16466)
                                             | uu____16475 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____16482 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____16482 in
                                                 let name_tok_corr =
                                                   let uu____16484 =
                                                     let uu____16491 =
                                                       let uu____16492 =
                                                         let uu____16503 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____16503) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____16492 in
                                                     (uu____16491,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____16484 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____16449 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____16307 with
                                      | (decls2,env2) ->
                                          let uu____16546 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____16554 =
                                              encode_term res_t1 env' in
                                            match uu____16554 with
                                            | (encoded_res_t,decls) ->
                                                let uu____16567 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____16567,
                                                  decls) in
                                          (match uu____16546 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____16578 =
                                                   let uu____16585 =
                                                     let uu____16586 =
                                                       let uu____16597 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____16597) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____16586 in
                                                   (uu____16585,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____16578 in
                                               let freshness =
                                                 let uu____16613 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____16613
                                                 then
                                                   let uu____16618 =
                                                     let uu____16619 =
                                                       let uu____16630 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____16641 =
                                                         varops.next_id () in
                                                       (vname, uu____16630,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____16641) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____16619 in
                                                   let uu____16644 =
                                                     let uu____16647 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____16647] in
                                                   uu____16618 :: uu____16644
                                                 else [] in
                                               let g =
                                                 let uu____16652 =
                                                   let uu____16655 =
                                                     let uu____16658 =
                                                       let uu____16661 =
                                                         let uu____16664 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____16664 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____16661 in
                                                     FStar_List.append decls3
                                                       uu____16658 in
                                                   FStar_List.append decls2
                                                     uu____16655 in
                                                 FStar_List.append decls11
                                                   uu____16652 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____16695 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____16695 with
          | FStar_Pervasives_Native.None  ->
              let uu____16736 = encode_free_var env x t t_norm [] in
              (match uu____16736 with
               | (decls,env1) ->
                   let uu____16763 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____16763 with
                    | (n1,x',uu____16794) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____16815) ->
              ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list,env_t)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____16867 = encode_free_var env lid t tt quals in
          match uu____16867 with
          | (decls,env1) ->
              let uu____16886 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____16886
              then
                let uu____16893 =
                  let uu____16896 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____16896 in
                (uu____16893, env1)
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____16941  ->
                fun lb  ->
                  match uu____16941 with
                  | (decls,env1) ->
                      let uu____16961 =
                        let uu____16968 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____16968
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____16961 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____16989 = FStar_Syntax_Util.head_and_args t in
    match uu____16989 with
    | (hd1,args) ->
        let uu____17038 =
          let uu____17039 = FStar_Syntax_Util.un_uinst hd1 in
          uu____17039.FStar_Syntax_Syntax.n in
        (match uu____17038 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____17045,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____17068 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____17090  ->
      fun quals  ->
        match uu____17090 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____17168 = FStar_Util.first_N nbinders formals in
              match uu____17168 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____17242  ->
                         fun uu____17243  ->
                           match (uu____17242, uu____17243) with
                           | ((formal,uu____17261),(binder,uu____17263)) ->
                               let uu____17272 =
                                 let uu____17281 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____17281) in
                               FStar_Syntax_Syntax.NT uu____17272) formals1
                      binders in
                  let extra_formals1 =
                    let uu____17289 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____17316  ->
                              match uu____17316 with
                              | (x,i) ->
                                  let uu____17327 =
                                    let uu___146_17328 = x in
                                    let uu____17329 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_17328.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_17328.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____17329
                                    } in
                                  (uu____17327, i))) in
                    FStar_All.pipe_right uu____17289
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____17351 =
                      let uu____17354 =
                        let uu____17355 = FStar_Syntax_Subst.subst subst1 t in
                        uu____17355.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                        uu____17354 in
                    let uu____17362 =
                      let uu____17363 = FStar_Syntax_Subst.compress body in
                      let uu____17364 =
                        let uu____17365 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____17365 in
                      FStar_Syntax_Syntax.extend_app_n uu____17363
                        uu____17364 in
                    uu____17362 uu____17351 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____17428 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____17428
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_17429 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_17429.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_17429.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_17429.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_17429.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_17429.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_17429.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_17429.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_17429.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_17429.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_17429.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_17429.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_17429.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_17429.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_17429.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_17429.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_17429.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_17429.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_17429.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_17429.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_17429.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_17429.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_17429.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_17429.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____17462 = FStar_Syntax_Util.abs_formals e in
                match uu____17462 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____17556::uu____17557 ->
                         let uu____17572 =
                           let uu____17573 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____17573.FStar_Syntax_Syntax.n in
                         (match uu____17572 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____17624 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____17624 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____17666 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____17666
                                   then
                                     let uu____17696 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____17696 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____17781  ->
                                                   fun uu____17782  ->
                                                     match (uu____17781,
                                                             uu____17782)
                                                     with
                                                     | ((x,uu____17800),
                                                        (b,uu____17802)) ->
                                                         let uu____17811 =
                                                           let uu____17820 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____17820) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____17811)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____17822 =
                                            let uu____17843 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____17843) in
                                          (uu____17822, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____17906 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____17906 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18005) ->
                              let uu____18014 =
                                let uu____18035 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____18035 in
                              (uu____18014, true)
                          | uu____18100 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____18102 ->
                              let uu____18103 =
                                let uu____18104 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____18105 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____18104
                                  uu____18105 in
                              failwith uu____18103)
                     | uu____18130 ->
                         let uu____18131 =
                           let uu____18132 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____18132.FStar_Syntax_Syntax.n in
                         (match uu____18131 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18183 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18183 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____18215 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____18215 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____18308 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____18362 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____18362
               then encode_top_level_vals env bindings quals
               else
                 (let uu____18373 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____18454  ->
                            fun lb  ->
                              match uu____18454 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____18549 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____18549
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____18552 =
                                      let uu____18567 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____18567
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____18552 with
                                    | (tok,decl,env2) ->
                                        let uu____18613 =
                                          let uu____18626 =
                                            let uu____18637 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____18637, tok) in
                                          uu____18626 :: toks in
                                        (uu____18613, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____18373 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____18820 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____18828 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____18828 vars)
                            else
                              (let uu____18830 =
                                 let uu____18837 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____18837) in
                               FStar_SMTEncoding_Util.mkApp uu____18830) in
                      let uu____18846 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_18849  ->
                                 match uu___116_18849 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____18850 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____18854 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____18854))) in
                      if uu____18846
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____18892;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____18894;
                                FStar_Syntax_Syntax.lbeff = uu____18895;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____18966 =
                                 let uu____18973 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____18973 with
                                 | (tcenv',uu____18993,e_t) ->
                                     let uu____18999 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____19010 -> failwith "Impossible" in
                                     (match uu____18999 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_19025 = env1 in
                                            {
                                              bindings =
                                                (uu___150_19025.bindings);
                                              depth = (uu___150_19025.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_19025.warn);
                                              cache = (uu___150_19025.cache);
                                              nolabels =
                                                (uu___150_19025.nolabels);
                                              use_zfuel_name =
                                                (uu___150_19025.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_19025.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_19025.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____18966 with
                                | (env',e1,t_norm1) ->
                                    let uu____19035 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____19035 with
                                     | ((binders,body,uu____19056,uu____19057),curry)
                                         ->
                                         ((let uu____19068 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____19068
                                           then
                                             let uu____19069 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____19070 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____19069 uu____19070
                                           else ());
                                          (let uu____19072 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____19072 with
                                           | (vars,guards,env'1,binder_decls,uu____19099)
                                               ->
                                               let body1 =
                                                 let uu____19113 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____19113
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____19116 =
                                                 let uu____19125 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____19125
                                                 then
                                                   let uu____19136 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____19137 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____19136, uu____19137)
                                                 else
                                                   (let uu____19147 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____19147)) in
                                               (match uu____19116 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____19170 =
                                                        let uu____19177 =
                                                          let uu____19178 =
                                                            let uu____19189 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____19189) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____19178 in
                                                        let uu____19200 =
                                                          let uu____19203 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____19203 in
                                                        (uu____19177,
                                                          uu____19200,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____19170 in
                                                    let uu____19206 =
                                                      let uu____19209 =
                                                        let uu____19212 =
                                                          let uu____19215 =
                                                            let uu____19218 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____19218 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____19215 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____19212 in
                                                      FStar_List.append
                                                        decls1 uu____19209 in
                                                    (uu____19206, env1))))))
                           | uu____19223 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____19258 = varops.fresh "fuel" in
                             (uu____19258, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____19261 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____19338  ->
                                     fun uu____19339  ->
                                       match (uu____19338, uu____19339) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____19491 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____19491 in
                                           let gtok =
                                             let uu____19493 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____19493 in
                                           let env3 =
                                             let uu____19495 =
                                               let uu____19498 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_36) uu____19498 in
                                             push_free_var env2 flid gtok
                                               uu____19495 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____19261 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____19656
                                 t_norm uu____19658 =
                                 match (uu____19656, uu____19658) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____19704;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____19705;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____19737 =
                                       let uu____19744 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____19744 with
                                       | (tcenv',uu____19772,e_t) ->
                                           let uu____19778 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____19789 ->
                                                 failwith "Impossible" in
                                           (match uu____19778 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_19804 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_19804.bindings);
                                                    depth =
                                                      (uu___151_19804.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_19804.warn);
                                                    cache =
                                                      (uu___151_19804.cache);
                                                    nolabels =
                                                      (uu___151_19804.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_19804.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_19804.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_19804.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____19737 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____19819 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____19819
                                            then
                                              let uu____19820 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____19821 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____19822 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____19820 uu____19821
                                                uu____19822
                                            else ());
                                           (let uu____19824 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____19824 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____19861 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____19861
                                                  then
                                                    let uu____19862 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____19863 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____19864 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____19865 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____19862 uu____19863
                                                      uu____19864 uu____19865
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____19869 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____19869 with
                                                  | (vars,guards,env'1,binder_decls,uu____19900)
                                                      ->
                                                      let decl_g =
                                                        let uu____19914 =
                                                          let uu____19925 =
                                                            let uu____19928 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____19928 in
                                                          (g, uu____19925,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____19914 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____19953 =
                                                          let uu____19960 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____19960) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____19953 in
                                                      let gsapp =
                                                        let uu____19970 =
                                                          let uu____19977 =
                                                            let uu____19980 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____19980 ::
                                                              vars_tm in
                                                          (g, uu____19977) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____19970 in
                                                      let gmax =
                                                        let uu____19986 =
                                                          let uu____19993 =
                                                            let uu____19996 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____19996 ::
                                                              vars_tm in
                                                          (g, uu____19993) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____19986 in
                                                      let body1 =
                                                        let uu____20002 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____20002
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____20004 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____20004 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____20022
                                                               =
                                                               let uu____20029
                                                                 =
                                                                 let uu____20030
                                                                   =
                                                                   let uu____20045
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____20045) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____20030 in
                                                               let uu____20066
                                                                 =
                                                                 let uu____20069
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____20069 in
                                                               (uu____20029,
                                                                 uu____20066,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____20022 in
                                                           let eqn_f =
                                                             let uu____20073
                                                               =
                                                               let uu____20080
                                                                 =
                                                                 let uu____20081
                                                                   =
                                                                   let uu____20092
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____20092) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____20081 in
                                                               (uu____20080,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____20073 in
                                                           let eqn_g' =
                                                             let uu____20106
                                                               =
                                                               let uu____20113
                                                                 =
                                                                 let uu____20114
                                                                   =
                                                                   let uu____20125
                                                                    =
                                                                    let uu____20126
                                                                    =
                                                                    let uu____20131
                                                                    =
                                                                    let uu____20132
                                                                    =
                                                                    let uu____20139
                                                                    =
                                                                    let uu____20142
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____20142
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____20139) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____20132 in
                                                                    (gsapp,
                                                                    uu____20131) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____20126 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____20125) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____20114 in
                                                               (uu____20113,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____20106 in
                                                           let uu____20165 =
                                                             let uu____20174
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____20174
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____20203)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1 in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____20228
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____20228
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____20233
                                                                    =
                                                                    let uu____20240
                                                                    =
                                                                    let uu____20241
                                                                    =
                                                                    let uu____20252
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20252) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20241 in
                                                                    (uu____20240,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____20233 in
                                                                 let uu____20273
                                                                   =
                                                                   let uu____20280
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____20280
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____20293
                                                                    =
                                                                    let uu____20296
                                                                    =
                                                                    let uu____20297
                                                                    =
                                                                    let uu____20304
                                                                    =
                                                                    let uu____20305
                                                                    =
                                                                    let uu____20316
                                                                    =
                                                                    let uu____20317
                                                                    =
                                                                    let uu____20322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____20322,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____20317 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____20316) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____20305 in
                                                                    (uu____20304,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____20297 in
                                                                    [uu____20296] in
                                                                    (d3,
                                                                    uu____20293) in
                                                                 (match uu____20273
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____20165
                                                            with
                                                            | (aux_decls,g_typing)
                                                                ->
                                                                ((FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                  (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                  env02)))))))) in
                               let uu____20387 =
                                 let uu____20400 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____20471  ->
                                      fun uu____20472  ->
                                        match (uu____20471, uu____20472) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____20637 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____20637 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____20400 in
                               (match uu____20387 with
                                | (decls2,eqns,env01) ->
                                    let uu____20710 =
                                      let isDeclFun uu___117_20722 =
                                        match uu___117_20722 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____20723 -> true
                                        | uu____20734 -> false in
                                      let uu____20735 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____20735
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____20710 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____20783 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____20783
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____20831 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____20831 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____20835 = encode_sigelt' env se in
      match uu____20835 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____20851 =
                  let uu____20852 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____20852 in
                [uu____20851]
            | uu____20853 ->
                let uu____20854 =
                  let uu____20857 =
                    let uu____20858 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____20858 in
                  uu____20857 :: g in
                let uu____20859 =
                  let uu____20862 =
                    let uu____20863 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____20863 in
                  [uu____20862] in
                FStar_List.append uu____20854 uu____20859 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____20876 =
          let uu____20877 = FStar_Syntax_Subst.compress t in
          uu____20877.FStar_Syntax_Syntax.n in
        match uu____20876 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____20883)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____20888 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20893 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____20898 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____20901 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20904 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____20919 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____20923 =
            let uu____20924 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____20924 Prims.op_Negation in
          if uu____20923
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____20958 ->
                   let uu____20959 =
                     let uu____20964 =
                       let uu____20965 =
                         let uu____20994 =
                           FStar_All.pipe_left
                             (fun _0_37  ->
                                FStar_Pervasives_Native.Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Parser_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____20994) in
                       FStar_Syntax_Syntax.Tm_abs uu____20965 in
                     FStar_Syntax_Syntax.mk uu____20964 in
                   uu____20959 FStar_Pervasives_Native.None
                     tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____21080 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____21080 with
               | (aname,atok,env2) ->
                   let uu____21096 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____21096 with
                    | (formals,uu____21114) ->
                        let uu____21127 =
                          let uu____21132 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____21132 env2 in
                        (match uu____21127 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____21144 =
                                 let uu____21145 =
                                   let uu____21156 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____21171  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____21156,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____21145 in
                               [uu____21144;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____21184 =
                               let aux uu____21236 uu____21237 =
                                 match (uu____21236, uu____21237) with
                                 | ((bv,uu____21289),(env3,acc_sorts,acc)) ->
                                     let uu____21327 = gen_term_var env3 bv in
                                     (match uu____21327 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____21184 with
                              | (uu____21399,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____21422 =
                                      let uu____21429 =
                                        let uu____21430 =
                                          let uu____21441 =
                                            let uu____21442 =
                                              let uu____21447 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____21447) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____21442 in
                                          ([[app]], xs_sorts, uu____21441) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____21430 in
                                      (uu____21429,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____21422 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____21467 =
                                      let uu____21474 =
                                        let uu____21475 =
                                          let uu____21486 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____21486) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____21475 in
                                      (uu____21474,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____21467 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____21505 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____21505 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____21533,uu____21534)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____21535 = new_term_constant_and_tok_from_lid env lid in
          (match uu____21535 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____21552,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____21558 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_21561  ->
                      match uu___118_21561 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____21562 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____21567 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21568 -> false)) in
            Prims.op_Negation uu____21558 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____21577 = encode_top_level_val env fv t quals in
             match uu____21577 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____21596 =
                   let uu____21599 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____21599 in
                 (uu____21596, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____21606 = encode_formula f env in
          (match uu____21606 with
           | (f1,decls) ->
               let g =
                 let uu____21620 =
                   let uu____21621 =
                     let uu____21628 =
                       let uu____21631 =
                         let uu____21632 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____21632 in
                       FStar_Pervasives_Native.Some uu____21631 in
                     let uu____21633 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____21628, uu____21633) in
                   FStar_SMTEncoding_Util.mkAssume uu____21621 in
                 [uu____21620] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____21639,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____21653 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____21663 =
                       let uu____21672 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____21672.FStar_Syntax_Syntax.fv_name in
                     uu____21663.FStar_Syntax_Syntax.v in
                   let uu____21677 =
                     let uu____21678 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____21678 in
                   if uu____21677
                   then
                     let val_decl =
                       let uu___152_21706 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_21706.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_21706.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____21713 = encode_sigelt' env1 val_decl in
                     match uu____21713 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____21653 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____21741,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____21743;
                          FStar_Syntax_Syntax.lbtyp = uu____21744;
                          FStar_Syntax_Syntax.lbeff = uu____21745;
                          FStar_Syntax_Syntax.lbdef = uu____21746;_}::[]),uu____21747,uu____21748)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____21775 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____21775 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____21808 =
                   let uu____21811 =
                     let uu____21812 =
                       let uu____21819 =
                         let uu____21820 =
                           let uu____21831 =
                             let uu____21832 =
                               let uu____21837 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____21837) in
                             FStar_SMTEncoding_Util.mkEq uu____21832 in
                           ([[b2t_x]], [xx], uu____21831) in
                         FStar_SMTEncoding_Util.mkForall uu____21820 in
                       (uu____21819,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____21812 in
                   [uu____21811] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____21808 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____21870,uu____21871,uu____21872)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_21883  ->
                  match uu___119_21883 with
                  | FStar_Syntax_Syntax.Discriminator uu____21884 -> true
                  | uu____21885 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____21888,lids,uu____21890) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____21902 =
                     let uu____21903 = FStar_List.hd l.FStar_Ident.ns in
                     uu____21903.FStar_Ident.idText in
                   uu____21902 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_21906  ->
                     match uu___120_21906 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____21907 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____21911,uu____21912)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_21931  ->
                  match uu___121_21931 with
                  | FStar_Syntax_Syntax.Projector uu____21932 -> true
                  | uu____21937 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____21944 = try_lookup_free_var env l in
          (match uu____21944 with
           | FStar_Pervasives_Native.Some uu____21951 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___153_21955 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_21955.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_21955.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____21964,uu____21965) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____21987) ->
          let uu____21996 = encode_sigelts env ses in
          (match uu____21996 with
           | (g,env1) ->
               let uu____22013 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_22032  ->
                         match uu___122_22032 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22033;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22034;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22035;_}
                             -> false
                         | uu____22038 -> true)) in
               (match uu____22013 with
                | (g',inversions) ->
                    let uu____22053 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_22072  ->
                              match uu___123_22072 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22073 ->
                                  true
                              | uu____22084 -> false)) in
                    (match uu____22053 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____22102,tps,k,uu____22105,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_22121  ->
                    match uu___124_22121 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____22122 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____22131 = c in
              match uu____22131 with
              | (name,args,uu____22136,uu____22137,uu____22138) ->
                  let uu____22143 =
                    let uu____22144 =
                      let uu____22155 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22168  ->
                                match uu____22168 with
                                | (uu____22175,sort,uu____22177) -> sort)) in
                      (name, uu____22155, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____22144 in
                  [uu____22143]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____22204 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____22208 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____22208 FStar_Option.isNone)) in
            if uu____22204
            then []
            else
              (let uu____22240 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____22240 with
               | (xxsym,xx) ->
                   let uu____22249 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____22270  ->
                             fun l  ->
                               match uu____22270 with
                               | (out,decls) ->
                                   let uu____22290 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____22290 with
                                    | (uu____22301,data_t) ->
                                        let uu____22303 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____22303 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____22357 =
                                                 let uu____22358 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____22358.FStar_Syntax_Syntax.n in
                                               match uu____22357 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____22373,indices) ->
                                                   indices
                                               | uu____22403 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____22424  ->
                                                         match uu____22424
                                                         with
                                                         | (x,uu____22430) ->
                                                             let uu____22431
                                                               =
                                                               let uu____22432
                                                                 =
                                                                 let uu____22439
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____22439,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____22432 in
                                                             push_term_var
                                                               env1 x
                                                               uu____22431)
                                                    env) in
                                             let uu____22442 =
                                               encode_args indices env1 in
                                             (match uu____22442 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____22468 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____22481
                                                                 =
                                                                 let uu____22486
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____22486,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____22481)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____22468
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____22489 =
                                                      let uu____22490 =
                                                        let uu____22495 =
                                                          let uu____22496 =
                                                            let uu____22501 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____22501,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____22496 in
                                                        (out, uu____22495) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____22490 in
                                                    (uu____22489,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____22249 with
                    | (data_ax,decls) ->
                        let uu____22514 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____22514 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____22525 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____22525 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____22529 =
                                 let uu____22536 =
                                   let uu____22537 =
                                     let uu____22548 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____22563 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____22548,
                                       uu____22563) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____22537 in
                                 let uu____22578 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____22536,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____22578) in
                               FStar_SMTEncoding_Util.mkAssume uu____22529 in
                             let pattern_guarded_inversion =
                               let uu____22584 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____22584
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____22591 =
                                   let uu____22592 =
                                     let uu____22599 =
                                       let uu____22600 =
                                         let uu____22611 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____22626 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____22611, uu____22626) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____22600 in
                                     let uu____22641 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____22599,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____22641) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____22592 in
                                 [uu____22591]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____22645 =
            let uu____22660 =
              let uu____22661 = FStar_Syntax_Subst.compress k in
              uu____22661.FStar_Syntax_Syntax.n in
            match uu____22660 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____22716 -> (tps, k) in
          (match uu____22645 with
           | (formals,res) ->
               let uu____22743 = FStar_Syntax_Subst.open_term formals res in
               (match uu____22743 with
                | (formals1,res1) ->
                    let uu____22754 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____22754 with
                     | (vars,guards,env',binder_decls,uu____22779) ->
                         let uu____22792 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____22792 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____22811 =
                                  let uu____22818 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____22818) in
                                FStar_SMTEncoding_Util.mkApp uu____22811 in
                              let uu____22827 =
                                let tname_decl =
                                  let uu____22837 =
                                    let uu____22838 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____22867  ->
                                              match uu____22867 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____22880 = varops.next_id () in
                                    (tname, uu____22838,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____22880, false) in
                                  constructor_or_logic_type_decl uu____22837 in
                                let uu____22889 =
                                  match vars with
                                  | [] ->
                                      let uu____22902 =
                                        let uu____22903 =
                                          let uu____22906 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_38) uu____22906 in
                                        push_free_var env1 t tname
                                          uu____22903 in
                                      ([], uu____22902)
                                  | uu____22913 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____22922 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____22922 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____22936 =
                                          let uu____22943 =
                                            let uu____22944 =
                                              let uu____22959 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____22959) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____22944 in
                                          (uu____22943,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____22936 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____22889 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____22827 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____22999 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____22999 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23017 =
                                               let uu____23018 =
                                                 let uu____23025 =
                                                   let uu____23026 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23026 in
                                                 (uu____23025,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23018 in
                                             [uu____23017]
                                           else [] in
                                         let uu____23030 =
                                           let uu____23033 =
                                             let uu____23036 =
                                               let uu____23037 =
                                                 let uu____23044 =
                                                   let uu____23045 =
                                                     let uu____23056 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23056) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23045 in
                                                 (uu____23044,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23037 in
                                             [uu____23036] in
                                           FStar_List.append karr uu____23033 in
                                         FStar_List.append decls1 uu____23030 in
                                   let aux =
                                     let uu____23072 =
                                       let uu____23075 =
                                         inversion_axioms tapp vars in
                                       let uu____23078 =
                                         let uu____23081 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23081] in
                                       FStar_List.append uu____23075
                                         uu____23078 in
                                     FStar_List.append kindingAx uu____23072 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23088,uu____23089,uu____23090,uu____23091,uu____23092)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23100,t,uu____23102,n_tps,uu____23104) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____23112 = new_term_constant_and_tok_from_lid env d in
          (match uu____23112 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____23129 = FStar_Syntax_Util.arrow_formals t in
               (match uu____23129 with
                | (formals,t_res) ->
                    let uu____23170 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____23170 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____23184 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____23184 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____23250 =
                                            mk_term_projector_name d x in
                                          (uu____23250,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____23252 =
                                  let uu____23271 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____23271, true) in
                                FStar_All.pipe_right uu____23252
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____23310 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____23310 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____23322::uu____23323 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____23368 =
                                           let uu____23379 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____23379) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____23368
                                     | uu____23404 -> tok_typing in
                                   let uu____23413 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____23413 with
                                    | (vars',guards',env'',decls_formals,uu____23438)
                                        ->
                                        let uu____23451 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____23451 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____23482 ->
                                                   let uu____23489 =
                                                     let uu____23490 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____23490 in
                                                   [uu____23489] in
                                             let encode_elim uu____23500 =
                                               let uu____23501 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____23501 with
                                               | (head1,args) ->
                                                   let uu____23556 =
                                                     let uu____23557 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____23557.FStar_Syntax_Syntax.n in
                                                   (match uu____23556 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____23569;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____23570;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____23571;_},uu____23572)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____23586 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____23586
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____23629
                                                                    ->
                                                                    let uu____23630
                                                                    =
                                                                    let uu____23631
                                                                    =
                                                                    let uu____23636
                                                                    =
                                                                    let uu____23637
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____23637 in
                                                                    (uu____23636,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____23631 in
                                                                    raise
                                                                    uu____23630 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____23650
                                                                    =
                                                                    let uu____23651
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____23651 in
                                                                    if
                                                                    uu____23650
                                                                    then
                                                                    let uu____23664
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____23664]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____23666
                                                               =
                                                               let uu____23679
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____23718
                                                                     ->
                                                                    fun
                                                                    uu____23719
                                                                     ->
                                                                    match 
                                                                    (uu____23718,
                                                                    uu____23719)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____23814
                                                                    =
                                                                    let uu____23821
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____23821 in
                                                                    (match uu____23814
                                                                    with
                                                                    | 
                                                                    (uu____23834,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____23842
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____23842
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____23844
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____23844
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____23679 in
                                                             (match uu____23666
                                                              with
                                                              | (uu____23859,arg_vars,elim_eqns_or_guards,uu____23862)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____23892
                                                                    =
                                                                    let uu____23899
                                                                    =
                                                                    let uu____23900
                                                                    =
                                                                    let uu____23911
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____23922
                                                                    =
                                                                    let uu____23923
                                                                    =
                                                                    let uu____23928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____23928) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____23923 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____23911,
                                                                    uu____23922) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____23900 in
                                                                    (uu____23899,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____23892 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____23951
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____23951,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____23953
                                                                    =
                                                                    let uu____23960
                                                                    =
                                                                    let uu____23961
                                                                    =
                                                                    let uu____23972
                                                                    =
                                                                    let uu____23977
                                                                    =
                                                                    let uu____23980
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____23980] in
                                                                    [uu____23977] in
                                                                    let uu____23985
                                                                    =
                                                                    let uu____23986
                                                                    =
                                                                    let uu____23991
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____23992
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____23991,
                                                                    uu____23992) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____23986 in
                                                                    (uu____23972,
                                                                    [x],
                                                                    uu____23985) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____23961 in
                                                                    let uu____24011
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____23960,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24011) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____23953
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24018
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____24044
                                                                    =
                                                                    let uu____24045
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24045
                                                                    dapp1 in
                                                                    [uu____24044]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24018
                                                                    FStar_List.flatten in
                                                                    let uu____24052
                                                                    =
                                                                    let uu____24059
                                                                    =
                                                                    let uu____24060
                                                                    =
                                                                    let uu____24071
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24082
                                                                    =
                                                                    let uu____24083
                                                                    =
                                                                    let uu____24088
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24088) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24083 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24071,
                                                                    uu____24082) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24060 in
                                                                    (uu____24059,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24052) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24113 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24113
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____24156
                                                                    ->
                                                                    let uu____24157
                                                                    =
                                                                    let uu____24158
                                                                    =
                                                                    let uu____24163
                                                                    =
                                                                    let uu____24164
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24164 in
                                                                    (uu____24163,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24158 in
                                                                    raise
                                                                    uu____24157 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24177
                                                                    =
                                                                    let uu____24178
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24178 in
                                                                    if
                                                                    uu____24177
                                                                    then
                                                                    let uu____24191
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24191]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24193
                                                               =
                                                               let uu____24206
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24245
                                                                     ->
                                                                    fun
                                                                    uu____24246
                                                                     ->
                                                                    match 
                                                                    (uu____24245,
                                                                    uu____24246)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24341
                                                                    =
                                                                    let uu____24348
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24348 in
                                                                    (match uu____24341
                                                                    with
                                                                    | 
                                                                    (uu____24361,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24369
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24369
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24371
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24371
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 uu____24206 in
                                                             (match uu____24193
                                                              with
                                                              | (uu____24386,arg_vars,elim_eqns_or_guards,uu____24389)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____24419
                                                                    =
                                                                    let uu____24426
                                                                    =
                                                                    let uu____24427
                                                                    =
                                                                    let uu____24438
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24449
                                                                    =
                                                                    let uu____24450
                                                                    =
                                                                    let uu____24455
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24455) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24450 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24438,
                                                                    uu____24449) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24427 in
                                                                    (uu____24426,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24419 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24478
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24478,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24480
                                                                    =
                                                                    let uu____24487
                                                                    =
                                                                    let uu____24488
                                                                    =
                                                                    let uu____24499
                                                                    =
                                                                    let uu____24504
                                                                    =
                                                                    let uu____24507
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24507] in
                                                                    [uu____24504] in
                                                                    let uu____24512
                                                                    =
                                                                    let uu____24513
                                                                    =
                                                                    let uu____24518
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24519
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24518,
                                                                    uu____24519) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24513 in
                                                                    (uu____24499,
                                                                    [x],
                                                                    uu____24512) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24488 in
                                                                    let uu____24538
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24487,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24538) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24480
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24545
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____24571
                                                                    =
                                                                    let uu____24572
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24572
                                                                    dapp1 in
                                                                    [uu____24571]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24545
                                                                    FStar_List.flatten in
                                                                    let uu____24579
                                                                    =
                                                                    let uu____24586
                                                                    =
                                                                    let uu____24587
                                                                    =
                                                                    let uu____24598
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24609
                                                                    =
                                                                    let uu____24610
                                                                    =
                                                                    let uu____24615
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24615) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24610 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24598,
                                                                    uu____24609) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24587 in
                                                                    (uu____24586,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24579) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____24634 ->
                                                        ((let uu____24636 =
                                                            let uu____24637 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____24638 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____24637
                                                              uu____24638 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____24636);
                                                         ([], []))) in
                                             let uu____24643 = encode_elim () in
                                             (match uu____24643 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____24663 =
                                                      let uu____24666 =
                                                        let uu____24669 =
                                                          let uu____24672 =
                                                            let uu____24675 =
                                                              let uu____24676
                                                                =
                                                                let uu____24687
                                                                  =
                                                                  let uu____24690
                                                                    =
                                                                    let uu____24691
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____24691 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____24690 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____24687) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____24676 in
                                                            [uu____24675] in
                                                          let uu____24696 =
                                                            let uu____24699 =
                                                              let uu____24702
                                                                =
                                                                let uu____24705
                                                                  =
                                                                  let uu____24708
                                                                    =
                                                                    let uu____24711
                                                                    =
                                                                    let uu____24714
                                                                    =
                                                                    let uu____24715
                                                                    =
                                                                    let uu____24722
                                                                    =
                                                                    let uu____24723
                                                                    =
                                                                    let uu____24734
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____24734) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24723 in
                                                                    (uu____24722,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24715 in
                                                                    let uu____24747
                                                                    =
                                                                    let uu____24750
                                                                    =
                                                                    let uu____24751
                                                                    =
                                                                    let uu____24758
                                                                    =
                                                                    let uu____24759
                                                                    =
                                                                    let uu____24770
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____24781
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____24770,
                                                                    uu____24781) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24759 in
                                                                    (uu____24758,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24751 in
                                                                    [uu____24750] in
                                                                    uu____24714
                                                                    ::
                                                                    uu____24747 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____24711 in
                                                                  FStar_List.append
                                                                    uu____24708
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____24705 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____24702 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____24699 in
                                                          FStar_List.append
                                                            uu____24672
                                                            uu____24696 in
                                                        FStar_List.append
                                                          decls3 uu____24669 in
                                                      FStar_List.append
                                                        decls2 uu____24666 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____24663 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____24820  ->
              fun se  ->
                match uu____24820 with
                | (g,env1) ->
                    let uu____24840 = encode_sigelt env1 se in
                    (match uu____24840 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____24897 =
        match uu____24897 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____24929 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____24935 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____24935
                   then
                     let uu____24936 = FStar_Syntax_Print.bv_to_string x in
                     let uu____24937 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____24938 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____24936 uu____24937 uu____24938
                   else ());
                  (let uu____24940 = encode_term t1 env1 in
                   match uu____24940 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____24956 =
                         let uu____24963 =
                           let uu____24964 =
                             let uu____24965 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____24965
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____24964 in
                         new_term_constant_from_string env1 x uu____24963 in
                       (match uu____24956 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____24981 = FStar_Options.log_queries () in
                              if uu____24981
                              then
                                let uu____24984 =
                                  let uu____24985 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____24986 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____24987 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____24985 uu____24986 uu____24987 in
                                FStar_Pervasives_Native.Some uu____24984
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25003,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25017 = encode_free_var env1 fv t t_norm [] in
                 (match uu____25017 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25040,se,uu____25042) ->
                 let uu____25047 = encode_sigelt env1 se in
                 (match uu____25047 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25064,se) ->
                 let uu____25070 = encode_sigelt env1 se in
                 (match uu____25070 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____25087 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____25087 with | (uu____25110,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____25187  ->
            match uu____25187 with
            | (l,uu____25199,uu____25200) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____25240  ->
            match uu____25240 with
            | (l,uu____25254,uu____25255) ->
                let uu____25264 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (FStar_Pervasives_Native.fst l) in
                let uu____25265 =
                  let uu____25268 =
                    let uu____25269 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____25269 in
                  [uu____25268] in
                uu____25264 :: uu____25265)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____25284 =
      let uu____25287 =
        let uu____25288 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____25291 =
          let uu____25292 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____25292 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____25288;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____25291
        } in
      [uu____25287] in
    FStar_ST.write last_env uu____25284
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____25301 = FStar_ST.read last_env in
      match uu____25301 with
      | [] -> failwith "No env; call init first!"
      | e::uu____25307 ->
          let uu___154_25310 = e in
          let uu____25311 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_25310.bindings);
            depth = (uu___154_25310.depth);
            tcenv;
            warn = (uu___154_25310.warn);
            cache = (uu___154_25310.cache);
            nolabels = (uu___154_25310.nolabels);
            use_zfuel_name = (uu___154_25310.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_25310.encode_non_total_function_typ);
            current_module_name = uu____25311
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____25315 = FStar_ST.read last_env in
    match uu____25315 with
    | [] -> failwith "Empty env stack"
    | uu____25320::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____25328  ->
    let uu____25329 = FStar_ST.read last_env in
    match uu____25329 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_25342 = hd1 in
          {
            bindings = (uu___155_25342.bindings);
            depth = (uu___155_25342.depth);
            tcenv = (uu___155_25342.tcenv);
            warn = (uu___155_25342.warn);
            cache = refs;
            nolabels = (uu___155_25342.nolabels);
            use_zfuel_name = (uu___155_25342.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_25342.encode_non_total_function_typ);
            current_module_name = (uu___155_25342.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____25347  ->
    let uu____25348 = FStar_ST.read last_env in
    match uu____25348 with
    | [] -> failwith "Popping an empty stack"
    | uu____25353::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____25361  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____25364  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____25367  ->
    let uu____25368 = FStar_ST.read last_env in
    match uu____25368 with
    | hd1::uu____25374::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____25380 -> failwith "Impossible"
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let mark: Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg
let reset_mark: Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
let open_fact_db_tags: env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____25435::uu____25436,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_25442 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_25442.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_25442.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_25442.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____25443 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____25458 =
        let uu____25461 =
          let uu____25462 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____25462 in
        let uu____25463 = open_fact_db_tags env in uu____25461 :: uu____25463 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____25458
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____25485 = encode_sigelt env se in
      match uu____25485 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____25521 = FStar_Options.log_queries () in
        if uu____25521
        then
          let uu____25524 =
            let uu____25525 =
              let uu____25526 =
                let uu____25527 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____25527 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____25526 in
            FStar_SMTEncoding_Term.Caption uu____25525 in
          uu____25524 :: decls
        else decls in
      let env =
        let uu____25538 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____25538 tcenv in
      let uu____25539 = encode_top_level_facts env se in
      match uu____25539 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____25553 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____25553))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____25565 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____25565
       then
         let uu____25566 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____25566
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____25594  ->
                 fun se  ->
                   match uu____25594 with
                   | (g,env2) ->
                       let uu____25614 = encode_top_level_facts env2 se in
                       (match uu____25614 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____25637 =
         encode_signature
           (let uu___157_25644 = env in
            {
              bindings = (uu___157_25644.bindings);
              depth = (uu___157_25644.depth);
              tcenv = (uu___157_25644.tcenv);
              warn = false;
              cache = (uu___157_25644.cache);
              nolabels = (uu___157_25644.nolabels);
              use_zfuel_name = (uu___157_25644.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_25644.encode_non_total_function_typ);
              current_module_name = (uu___157_25644.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____25637 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____25661 = FStar_Options.log_queries () in
             if uu____25661
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_25667 = env1 in
               {
                 bindings = (uu___158_25667.bindings);
                 depth = (uu___158_25667.depth);
                 tcenv = (uu___158_25667.tcenv);
                 warn = true;
                 cache = (uu___158_25667.cache);
                 nolabels = (uu___158_25667.nolabels);
                 use_zfuel_name = (uu___158_25667.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_25667.encode_non_total_function_typ);
                 current_module_name = (uu___158_25667.current_module_name)
               });
            (let uu____25669 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____25669
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____25721 =
           let uu____25722 = FStar_TypeChecker_Env.current_module tcenv in
           uu____25722.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____25721);
        (let env =
           let uu____25724 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____25724 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____25734 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____25769 = aux rest in
                 (match uu____25769 with
                  | (out,rest1) ->
                      let t =
                        let uu____25801 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____25801 with
                        | FStar_Pervasives_Native.Some uu____25808 ->
                            let uu____25809 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____25809
                              x.FStar_Syntax_Syntax.sort
                        | uu____25810 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____25814 =
                        let uu____25817 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_25818 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_25818.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_25818.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____25817 :: out in
                      (uu____25814, rest1))
             | uu____25823 -> ([], bindings1) in
           let uu____25830 = aux bindings in
           match uu____25830 with
           | (closing,bindings1) ->
               let uu____25855 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____25855, bindings1) in
         match uu____25734 with
         | (q1,bindings1) ->
             let uu____25878 =
               let uu____25883 =
                 FStar_List.filter
                   (fun uu___125_25886  ->
                      match uu___125_25886 with
                      | FStar_TypeChecker_Env.Binding_sig uu____25887 ->
                          false
                      | uu____25894 -> true) bindings1 in
               encode_env_bindings env uu____25883 in
             (match uu____25878 with
              | (env_decls,env1) ->
                  ((let uu____25912 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____25912
                    then
                      let uu____25913 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____25913
                    else ());
                   (let uu____25915 = encode_formula q1 env1 in
                    match uu____25915 with
                    | (phi,qdecls) ->
                        let uu____25936 =
                          let uu____25941 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____25941 phi in
                        (match uu____25936 with
                         | (labels,phi1) ->
                             let uu____25958 = encode_labels labels in
                             (match uu____25958 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____25995 =
                                      let uu____26002 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____26003 =
                                        varops.mk_unique "@query" in
                                      (uu____26002,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26003) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____25995 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____26020 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26020 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____26022 = encode_formula q env in
       match uu____26022 with
       | (f,uu____26028) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____26030) -> true
             | uu____26035 -> false)))