open Prims
let add_fuel x tl1 =
  let uu____19 = FStar_Options.unthrottle_inductives () in
  if uu____19 then tl1 else x :: tl1
let withenv c uu____47 = match uu____47 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
<<<<<<< HEAD
    (fun uu___101_77  ->
       match uu___101_77 with
       | (FStar_Util.Inl uu____82,uu____83) -> false
       | uu____86 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____117 =
        let uu____120 =
          let uu____121 =
            let uu____124 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____124 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____121 in
        FStar_Util.Inl uu____120 in
      Some uu____117
  | uu____129 -> l
=======
    (fun uu___102_86  ->
       match uu___102_86 with
       | (FStar_Util.Inl uu____91,uu____92) -> false
       | uu____95 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____129 =
        let uu____132 =
          let uu____133 =
            let uu____136 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____136 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____133 in
        FStar_Util.Inl uu____132 in
      Some uu____129
  | uu____141 -> l
>>>>>>> origin/guido_tactics
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
<<<<<<< HEAD
        let uu___126_143 = a in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___126_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_143.FStar_Syntax_Syntax.sort)
        } in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____145
=======
        let uu___126_158 = a in
        let uu____159 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____159;
          FStar_Syntax_Syntax.index =
            (uu___126_158.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_158.FStar_Syntax_Syntax.sort)
        } in
      let uu____160 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____160
>>>>>>> origin/guido_tactics
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
<<<<<<< HEAD
        let fail uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____159 in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____160 with
        | (uu____163,t) ->
            let uu____165 =
              let uu____166 = FStar_Syntax_Subst.compress t in
              uu____166.FStar_Syntax_Syntax.n in
            (match uu____165 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____181 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____181 with
                  | (binders,uu____185) ->
=======
        let fail uu____176 =
          let uu____177 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____177 in
        let uu____178 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____178 with
        | (uu____181,t) ->
            let uu____183 =
              let uu____184 = FStar_Syntax_Subst.compress t in
              uu____184.FStar_Syntax_Syntax.n in
            (match uu____183 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____199 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____199 with
                  | (binders,uu____203) ->
>>>>>>> origin/guido_tactics
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (fst b)))
<<<<<<< HEAD
             | uu____196 -> fail ())
=======
             | uu____216 -> fail ())
>>>>>>> origin/guido_tactics
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
<<<<<<< HEAD
      let uu____203 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____203
=======
      let uu____225 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____225
>>>>>>> origin/guido_tactics
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
<<<<<<< HEAD
      let uu____210 =
        let uu____213 = mk_term_projector_name lid a in
        (uu____213,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____210
=======
      let uu____234 =
        let uu____237 = mk_term_projector_name lid a in
        (uu____237,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____234
>>>>>>> origin/guido_tactics
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
<<<<<<< HEAD
      let uu____220 =
        let uu____223 = mk_term_projector_name_by_pos lid i in
        (uu____223,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____220
=======
      let uu____246 =
        let uu____249 = mk_term_projector_name_by_pos lid i in
        (uu____249,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____246
>>>>>>> origin/guido_tactics
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
let __proj__Mkvarops_t__item__push: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__push
let __proj__Mkvarops_t__item__pop: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__pop
let __proj__Mkvarops_t__item__mark: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mark
let __proj__Mkvarops_t__item__reset_mark:
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__reset_mark
let __proj__Mkvarops_t__item__commit_mark:
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__commit_mark
let __proj__Mkvarops_t__item__new_var:
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_var
let __proj__Mkvarops_t__item__new_fvar:
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_fvar
let __proj__Mkvarops_t__item__fresh: varops_t -> Prims.string -> Prims.string
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__fresh
let __proj__Mkvarops_t__item__string_const:
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__string_const
let __proj__Mkvarops_t__item__next_id: varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__next_id
let __proj__Mkvarops_t__item__mk_unique:
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mk_unique
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
<<<<<<< HEAD
  let new_scope uu____436 =
    let uu____437 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____439 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____437, uu____439) in
  let scopes =
    let uu____450 = let uu____456 = new_scope () in [uu____456] in
    FStar_Util.mk_ref uu____450 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____481 =
        let uu____483 = FStar_ST.read scopes in
        FStar_Util.find_map uu____483
          (fun uu____503  ->
             match uu____503 with
             | (names1,uu____510) -> FStar_Util.smap_try_find names1 y1) in
      match uu____481 with
      | None  -> y1
      | Some uu____515 ->
          (FStar_Util.incr ctr;
           (let uu____520 =
              let uu____521 =
                let uu____522 = FStar_ST.read ctr in
                Prims.string_of_int uu____522 in
              Prims.strcat "__" uu____521 in
            Prims.strcat y1 uu____520)) in
    let top_scope =
      let uu____527 =
        let uu____532 = FStar_ST.read scopes in FStar_List.hd uu____532 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____527 in
=======
  let new_scope uu____863 =
    let uu____864 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____866 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____864, uu____866) in
  let scopes =
    let uu____877 = let uu____883 = new_scope () in [uu____883] in
    FStar_Util.mk_ref uu____877 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____908 =
        let uu____910 = FStar_ST.read scopes in
        FStar_Util.find_map uu____910
          (fun uu____927  ->
             match uu____927 with
             | (names1,uu____934) -> FStar_Util.smap_try_find names1 y1) in
      match uu____908 with
      | None  -> y1
      | Some uu____939 ->
          (FStar_Util.incr ctr;
           (let uu____944 =
              let uu____945 =
                let uu____946 = FStar_ST.read ctr in
                Prims.string_of_int uu____946 in
              Prims.strcat "__" uu____945 in
            Prims.strcat y1 uu____944)) in
    let top_scope =
      let uu____951 =
        let uu____956 = FStar_ST.read scopes in FStar_List.hd uu____956 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____951 in
>>>>>>> origin/guido_tactics
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
<<<<<<< HEAD
  let next_id1 uu____571 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____582 =
      let uu____583 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____583 in
    FStar_Util.format2 "%s_%s" pfx uu____582 in
  let string_const s =
    let uu____588 =
      let uu____590 = FStar_ST.read scopes in
      FStar_Util.find_map uu____590
        (fun uu____610  ->
           match uu____610 with
           | (uu____616,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____588 with
=======
  let next_id1 uu____995 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____1006 =
      let uu____1007 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1007 in
    FStar_Util.format2 "%s_%s" pfx uu____1006 in
  let string_const s =
    let uu____1012 =
      let uu____1014 = FStar_ST.read scopes in
      FStar_Util.find_map uu____1014
        (fun uu____1031  ->
           match uu____1031 with
           | (uu____1037,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1012 with
>>>>>>> origin/guido_tactics
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
<<<<<<< HEAD
          let uu____625 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____625 in
        let top_scope =
          let uu____628 =
            let uu____633 = FStar_ST.read scopes in FStar_List.hd uu____633 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____628 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____661 =
    let uu____662 =
      let uu____668 = new_scope () in
      let uu____673 = FStar_ST.read scopes in uu____668 :: uu____673 in
    FStar_ST.write scopes uu____662 in
  let pop1 uu____700 =
    let uu____701 =
      let uu____707 = FStar_ST.read scopes in FStar_List.tl uu____707 in
    FStar_ST.write scopes uu____701 in
  let mark1 uu____734 = push1 () in
  let reset_mark1 uu____738 = pop1 () in
  let commit_mark1 uu____742 =
    let uu____743 = FStar_ST.read scopes in
    match uu____743 with
=======
          let uu____1046 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1046 in
        let top_scope =
          let uu____1049 =
            let uu____1054 = FStar_ST.read scopes in FStar_List.hd uu____1054 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____1049 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1082 =
    let uu____1083 =
      let uu____1089 = new_scope () in
      let uu____1094 = FStar_ST.read scopes in uu____1089 :: uu____1094 in
    FStar_ST.write scopes uu____1083 in
  let pop1 uu____1121 =
    let uu____1122 =
      let uu____1128 = FStar_ST.read scopes in FStar_List.tl uu____1128 in
    FStar_ST.write scopes uu____1122 in
  let mark1 uu____1155 = push1 () in
  let reset_mark1 uu____1159 = pop1 () in
  let commit_mark1 uu____1163 =
    let uu____1164 = FStar_ST.read scopes in
    match uu____1164 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    | uu____809 -> failwith "Impossible" in
=======
    | uu____1224 -> failwith "Impossible" in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    let uu___127_818 = x in
    let uu____819 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____819;
      FStar_Syntax_Syntax.index = (uu___127_818.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_818.FStar_Syntax_Syntax.sort)
=======
    let uu___127_1234 = x in
    let uu____1235 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1235;
      FStar_Syntax_Syntax.index = (uu___127_1234.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_1234.FStar_Syntax_Syntax.sort)
>>>>>>> origin/guido_tactics
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Binding_var _0 -> true | uu____842 -> false
=======
    match projectee with | Binding_var _0 -> true | uu____1259 -> false
>>>>>>> origin/guido_tactics
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | Binding_fvar _0 -> true | uu____866 -> false
=======
    match projectee with | Binding_fvar _0 -> true | uu____1285 -> false
>>>>>>> origin/guido_tactics
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term option*
      FStar_SMTEncoding_Term.term option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}
let __proj__Mkcache_entry__item__cache_symbol_name:
  cache_entry -> Prims.string =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
let __proj__Mkcache_entry__item__cache_symbol_arg_sorts:
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
let __proj__Mkcache_entry__item__cache_symbol_decls:
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
let __proj__Mkcache_entry__item__cache_symbol_assumption_names:
  cache_entry -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_assumption_names
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
let __proj__Mkenv_t__item__bindings: env_t -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__bindings
let __proj__Mkenv_t__item__depth: env_t -> Prims.int =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__depth
let __proj__Mkenv_t__item__tcenv: env_t -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__tcenv
let __proj__Mkenv_t__item__warn: env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__warn
let __proj__Mkenv_t__item__cache: env_t -> cache_entry FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__cache
let __proj__Mkenv_t__item__nolabels: env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__nolabels
let __proj__Mkenv_t__item__use_zfuel_name: env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__use_zfuel_name
let __proj__Mkenv_t__item__encode_non_total_function_typ: env_t -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__encode_non_total_function_typ
let __proj__Mkenv_t__item__current_module_name: env_t -> Prims.string =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__current_module_name
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
<<<<<<< HEAD
         (fun uu___102_1056  ->
            match uu___102_1056 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1059 -> [])) in
=======
         (fun uu___103_1609  ->
            match uu___103_1609 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1612 -> [])) in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    let uu____1067 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1074  ->
              match uu___103_1074 with
              | Binding_var (x,uu____1076) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1078,uu____1079,uu____1080) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1067 (FStar_String.concat ", ")
=======
    let uu____1622 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___104_1626  ->
              match uu___104_1626 with
              | Binding_var (x,uu____1628) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1630,uu____1631,uu____1632) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1622 (FStar_String.concat ", ")
>>>>>>> origin/guido_tactics
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
<<<<<<< HEAD
      let uu____1113 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1113
      then
        let uu____1115 = FStar_Syntax_Print.term_to_string t in
        Some uu____1115
=======
      let uu____1670 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1670
      then
        let uu____1672 = FStar_Syntax_Print.term_to_string t in
        Some uu____1672
>>>>>>> origin/guido_tactics
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
<<<<<<< HEAD
      let uu____1126 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1126)
=======
      let uu____1685 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1685)
>>>>>>> origin/guido_tactics
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
<<<<<<< HEAD
        (let uu___128_1139 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1139.tcenv);
           warn = (uu___128_1139.warn);
           cache = (uu___128_1139.cache);
           nolabels = (uu___128_1139.nolabels);
           use_zfuel_name = (uu___128_1139.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1139.encode_non_total_function_typ);
           current_module_name = (uu___128_1139.current_module_name)
=======
        (let uu___128_1699 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1699.tcenv);
           warn = (uu___128_1699.warn);
           cache = (uu___128_1699.cache);
           nolabels = (uu___128_1699.nolabels);
           use_zfuel_name = (uu___128_1699.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1699.encode_non_total_function_typ);
           current_module_name = (uu___128_1699.current_module_name)
>>>>>>> origin/guido_tactics
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
<<<<<<< HEAD
        (let uu___129_1153 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1153.depth);
           tcenv = (uu___129_1153.tcenv);
           warn = (uu___129_1153.warn);
           cache = (uu___129_1153.cache);
           nolabels = (uu___129_1153.nolabels);
           use_zfuel_name = (uu___129_1153.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1153.encode_non_total_function_typ);
           current_module_name = (uu___129_1153.current_module_name)
=======
        (let uu___129_1714 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1714.depth);
           tcenv = (uu___129_1714.tcenv);
           warn = (uu___129_1714.warn);
           cache = (uu___129_1714.cache);
           nolabels = (uu___129_1714.nolabels);
           use_zfuel_name = (uu___129_1714.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1714.encode_non_total_function_typ);
           current_module_name = (uu___129_1714.current_module_name)
>>>>>>> origin/guido_tactics
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
<<<<<<< HEAD
          (let uu___130_1170 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1170.depth);
             tcenv = (uu___130_1170.tcenv);
             warn = (uu___130_1170.warn);
             cache = (uu___130_1170.cache);
             nolabels = (uu___130_1170.nolabels);
             use_zfuel_name = (uu___130_1170.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1170.encode_non_total_function_typ);
             current_module_name = (uu___130_1170.current_module_name)
=======
          (let uu___130_1733 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1733.depth);
             tcenv = (uu___130_1733.tcenv);
             warn = (uu___130_1733.warn);
             cache = (uu___130_1733.cache);
             nolabels = (uu___130_1733.nolabels);
             use_zfuel_name = (uu___130_1733.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1733.encode_non_total_function_typ);
             current_module_name = (uu___130_1733.current_module_name)
>>>>>>> origin/guido_tactics
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
<<<<<<< HEAD
        let uu___131_1180 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1180.depth);
          tcenv = (uu___131_1180.tcenv);
          warn = (uu___131_1180.warn);
          cache = (uu___131_1180.cache);
          nolabels = (uu___131_1180.nolabels);
          use_zfuel_name = (uu___131_1180.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1180.encode_non_total_function_typ);
          current_module_name = (uu___131_1180.current_module_name)
=======
        let uu___131_1746 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1746.depth);
          tcenv = (uu___131_1746.tcenv);
          warn = (uu___131_1746.warn);
          cache = (uu___131_1746.cache);
          nolabels = (uu___131_1746.nolabels);
          use_zfuel_name = (uu___131_1746.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1746.encode_non_total_function_typ);
          current_module_name = (uu___131_1746.current_module_name)
>>>>>>> origin/guido_tactics
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
<<<<<<< HEAD
          (fun uu___104_1199  ->
             match uu___104_1199 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1207 -> None) in
      let uu____1210 = aux a in
      match uu____1210 with
      | None  ->
          let a2 = unmangle a in
          let uu____1217 = aux a2 in
          (match uu____1217 with
           | None  ->
               let uu____1223 =
                 let uu____1224 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1225 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1224 uu____1225 in
               failwith uu____1223
=======
          (fun uu___105_1764  ->
             match uu___105_1764 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1772 -> None) in
      let uu____1775 = aux a in
      match uu____1775 with
      | None  ->
          let a2 = unmangle a in
          let uu____1782 = aux a2 in
          (match uu____1782 with
           | None  ->
               let uu____1788 =
                 let uu____1789 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1790 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1789 uu____1790 in
               failwith uu____1788
>>>>>>> origin/guido_tactics
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
<<<<<<< HEAD
      let uu____1245 =
        let uu___132_1246 = env in
        let uu____1247 =
          let uu____1249 =
            let uu____1250 =
              let uu____1257 =
                let uu____1259 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1259 in
              (x, fname, uu____1257, None) in
            Binding_fvar uu____1250 in
          uu____1249 :: (env.bindings) in
        {
          bindings = uu____1247;
          depth = (uu___132_1246.depth);
          tcenv = (uu___132_1246.tcenv);
          warn = (uu___132_1246.warn);
          cache = (uu___132_1246.cache);
          nolabels = (uu___132_1246.nolabels);
          use_zfuel_name = (uu___132_1246.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1246.encode_non_total_function_typ);
          current_module_name = (uu___132_1246.current_module_name)
        } in
      (fname, ftok, uu____1245)
=======
      let uu____1812 =
        let uu___132_1813 = env in
        let uu____1814 =
          let uu____1816 =
            let uu____1817 =
              let uu____1824 =
                let uu____1826 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1826 in
              (x, fname, uu____1824, None) in
            Binding_fvar uu____1817 in
          uu____1816 :: (env.bindings) in
        {
          bindings = uu____1814;
          depth = (uu___132_1813.depth);
          tcenv = (uu___132_1813.tcenv);
          warn = (uu___132_1813.warn);
          cache = (uu___132_1813.cache);
          nolabels = (uu___132_1813.nolabels);
          use_zfuel_name = (uu___132_1813.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1813.encode_non_total_function_typ);
          current_module_name = (uu___132_1813.current_module_name)
        } in
      (fname, ftok, uu____1812)
>>>>>>> origin/guido_tactics
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
<<<<<<< HEAD
        (fun uu___105_1286  ->
           match uu___105_1286 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1308 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1320 =
        lookup_binding env
          (fun uu___106_1327  ->
             match uu___106_1327 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1337 -> None) in
      FStar_All.pipe_right uu____1320 FStar_Option.isSome
=======
        (fun uu___106_1850  ->
           match uu___106_1850 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1872 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1886 =
        lookup_binding env
          (fun uu___107_1888  ->
             match uu___107_1888 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1898 -> None) in
      FStar_All.pipe_right uu____1886 FStar_Option.isSome
>>>>>>> origin/guido_tactics
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
<<<<<<< HEAD
      let uu____1350 = try_lookup_lid env a in
      match uu____1350 with
      | None  ->
          let uu____1367 =
            let uu____1368 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1368 in
          failwith uu____1367
=======
      let uu____1913 = try_lookup_lid env a in
      match uu____1913 with
      | None  ->
          let uu____1930 =
            let uu____1931 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1931 in
          failwith uu____1930
>>>>>>> origin/guido_tactics
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
<<<<<<< HEAD
          let uu___133_1399 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1399.depth);
            tcenv = (uu___133_1399.tcenv);
            warn = (uu___133_1399.warn);
            cache = (uu___133_1399.cache);
            nolabels = (uu___133_1399.nolabels);
            use_zfuel_name = (uu___133_1399.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1399.encode_non_total_function_typ);
            current_module_name = (uu___133_1399.current_module_name)
=======
          let uu___133_1966 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1966.depth);
            tcenv = (uu___133_1966.tcenv);
            warn = (uu___133_1966.warn);
            cache = (uu___133_1966.cache);
            nolabels = (uu___133_1966.nolabels);
            use_zfuel_name = (uu___133_1966.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1966.encode_non_total_function_typ);
            current_module_name = (uu___133_1966.current_module_name)
>>>>>>> origin/guido_tactics
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
<<<<<<< HEAD
        let uu____1411 = lookup_lid env x in
        match uu____1411 with
        | (t1,t2,uu____1419) ->
            let t3 =
              let uu____1425 =
                let uu____1429 =
                  let uu____1431 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1431] in
                (f, uu____1429) in
              FStar_SMTEncoding_Util.mkApp uu____1425 in
            let uu___134_1434 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_1434.depth);
              tcenv = (uu___134_1434.tcenv);
              warn = (uu___134_1434.warn);
              cache = (uu___134_1434.cache);
              nolabels = (uu___134_1434.nolabels);
              use_zfuel_name = (uu___134_1434.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1434.encode_non_total_function_typ);
              current_module_name = (uu___134_1434.current_module_name)
=======
        let uu____1981 = lookup_lid env x in
        match uu____1981 with
        | (t1,t2,uu____1989) ->
            let t3 =
              let uu____1995 =
                let uu____1999 =
                  let uu____2001 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2001] in
                (f, uu____1999) in
              FStar_SMTEncoding_Util.mkApp uu____1995 in
            let uu___134_2004 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_2004.depth);
              tcenv = (uu___134_2004.tcenv);
              warn = (uu___134_2004.warn);
              cache = (uu___134_2004.cache);
              nolabels = (uu___134_2004.nolabels);
              use_zfuel_name = (uu___134_2004.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_2004.encode_non_total_function_typ);
              current_module_name = (uu___134_2004.current_module_name)
>>>>>>> origin/guido_tactics
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
<<<<<<< HEAD
      let uu____1444 = try_lookup_lid env l in
      match uu____1444 with
=======
      let uu____2016 = try_lookup_lid env l in
      match uu____2016 with
>>>>>>> origin/guido_tactics
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
<<<<<<< HEAD
           | uu____1471 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1476,fuel::[]) ->
                         let uu____1479 =
                           let uu____1480 =
                             let uu____1481 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1481
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1480 "fuel" in
                         if uu____1479
                         then
                           let uu____1483 =
                             let uu____1484 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1484
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1483
                         else Some t
                     | uu____1487 -> Some t)
                | uu____1488 -> None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____1498 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____1498 with
      | Some t -> t
      | None  ->
          let uu____1501 =
            let uu____1502 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____1502 in
          failwith uu____1501
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____1511 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____1511 with | (x,uu____1518,uu____1519) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op* FStar_SMTEncoding_Term.term Prims.list)
  =
  fun env  ->
    fun a  ->
      let uu____1535 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____1535 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____1556;
                 FStar_SMTEncoding_Term.rng = uu____1557;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____1565 ->
               (match sym with
                | None  -> ((FStar_SMTEncoding_Term.Var name), [])
                | Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____1579 -> ((FStar_SMTEncoding_Term.Var name), []))))
=======
           | uu____2043 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2048,fuel::[]) ->
                         let uu____2051 =
                           let uu____2052 =
                             let uu____2053 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2053
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____2052 "fuel" in
                         if uu____2051
                         then
                           let uu____2055 =
                             let uu____2056 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2056
                               fuel in
                           FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                             uu____2055
                         else Some t
                     | uu____2059 -> Some t)
                | uu____2060 -> None))
let lookup_free_var env a =
  let uu____2081 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____2081 with
  | Some t -> t
  | None  ->
      let uu____2084 =
        let uu____2085 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____2085 in
      failwith uu____2084
let lookup_free_var_name env a =
  let uu____2105 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____2105 with | (x,uu____2112,uu____2113) -> x
let lookup_free_var_sym env a =
  let uu____2140 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____2140 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____2161;
             FStar_SMTEncoding_Term.rng = uu____2162;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____2170 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____2184 -> ((FStar_SMTEncoding_Term.Var name), []))))
>>>>>>> origin/guido_tactics
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
<<<<<<< HEAD
        (fun uu___107_1593  ->
           match uu___107_1593 with
           | Binding_fvar (uu____1595,nm',tok,uu____1598) when nm = nm' ->
               tok
           | uu____1603 -> None)
let mkForall_fuel' n1 uu____1620 =
  match uu____1620 with
  | (pats,vars,body) ->
      let fallback uu____1636 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1639 = FStar_Options.unthrottle_inductives () in
      if uu____1639
      then fallback ()
      else
        (let uu____1641 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1641 with
=======
        (fun uu___108_2195  ->
           match uu___108_2195 with
           | Binding_fvar (uu____2197,nm',tok,uu____2200) when nm = nm' ->
               tok
           | uu____2205 -> None)
let mkForall_fuel' n1 uu____2225 =
  match uu____2225 with
  | (pats,vars,body) ->
      let fallback uu____2241 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____2244 = FStar_Options.unthrottle_inductives () in
      if uu____2244
      then fallback ()
      else
        (let uu____2246 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____2246 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                       | uu____1662 -> p)) in
=======
                       | uu____2265 -> p)) in
>>>>>>> origin/guido_tactics
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
<<<<<<< HEAD
                         let uu____1676 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1676
                     | uu____1678 ->
                         let uu____1679 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1679 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1682 -> body in
=======
                         let uu____2279 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____2279
                     | uu____2281 ->
                         let uu____2282 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____2282 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____2285 -> body in
>>>>>>> origin/guido_tactics
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Tm_arrow uu____1708 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1716 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1721 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1722 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1733 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1748 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1750 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1750 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1760;
             FStar_Syntax_Syntax.pos = uu____1761;
             FStar_Syntax_Syntax.vars = uu____1762;_},uu____1763)
          ->
          let uu____1778 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1778 FStar_Option.isNone
      | uu____1787 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1794 =
        let uu____1795 = FStar_Syntax_Util.un_uinst t in
        uu____1795.FStar_Syntax_Syntax.n in
      match uu____1794 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1798,uu____1799,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1829  ->
                  match uu___108_1829 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1830 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1831,uu____1832,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1859 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1859 FStar_Option.isSome
      | uu____1868 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1875 = head_normal env t in
      if uu____1875
=======
      | FStar_Syntax_Syntax.Tm_arrow uu____2314 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2322 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2327 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2328 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2337 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2347 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2349 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2349 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2363;
             FStar_Syntax_Syntax.pos = uu____2364;
             FStar_Syntax_Syntax.vars = uu____2365;_},uu____2366)
          ->
          let uu____2381 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2381 FStar_Option.isNone
      | uu____2394 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2403 =
        let uu____2404 = FStar_Syntax_Util.un_uinst t in
        uu____2404.FStar_Syntax_Syntax.n in
      match uu____2403 with
      | FStar_Syntax_Syntax.Tm_abs (uu____2407,uu____2408,Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Syntax_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_2421  ->
                  match uu___109_2421 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2422 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2424 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2424 FStar_Option.isSome
      | uu____2437 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2446 = head_normal env t in
      if uu____2446
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    let uu____1886 =
      let uu____1887 = FStar_Syntax_Syntax.null_binder t in [uu____1887] in
    let uu____1888 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1886 uu____1888 None
=======
    let uu____2460 =
      let uu____2461 = FStar_Syntax_Syntax.null_binder t in [uu____2461] in
    let uu____2462 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____2460 uu____2462 None
>>>>>>> origin/guido_tactics
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
<<<<<<< HEAD
                    let uu____1918 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1918
                | s ->
                    let uu____1922 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1922) e)
=======
                    let uu____2486 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2486
                | s ->
                    let uu____2489 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2489) e)
>>>>>>> origin/guido_tactics
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
<<<<<<< HEAD
  fun uu___109_1934  ->
    match uu___109_1934 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1935 -> false
=======
  fun uu___110_2504  ->
    match uu___110_2504 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2505 -> false
>>>>>>> origin/guido_tactics
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term option
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
<<<<<<< HEAD
                       FStar_SMTEncoding_Term.freevars = uu____1963;
                       FStar_SMTEncoding_Term.rng = uu____1964;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1978) ->
              let uu____1983 =
=======
                       FStar_SMTEncoding_Term.freevars = uu____2536;
                       FStar_SMTEncoding_Term.rng = uu____2537;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2551) ->
              let uu____2556 =
>>>>>>> origin/guido_tactics
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
<<<<<<< HEAD
                          | uu____1996 -> false) args (FStar_List.rev xs)) in
              if uu____1983 then tok_of_name env f else None
          | (uu____1999,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2002 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2006 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2006)) in
              if uu____2002 then Some t else None
          | uu____2009 -> None in
=======
                          | uu____2570 -> false) args (FStar_List.rev xs)) in
              if uu____2556 then tok_of_name env f else None
          | (uu____2573,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2576 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2578 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2578)) in
              if uu____2576 then Some t else None
          | uu____2581 -> None in
>>>>>>> origin/guido_tactics
        check_partial_applications body (FStar_List.rev vars)
type label = (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t);
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list;}
let __proj__Mkpattern__item__pat_vars:
  pattern -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
let __proj__Mkpattern__item__pat_term:
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
let __proj__Mkpattern__item__guard:
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
let __proj__Mkpattern__item__projections:
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
<<<<<<< HEAD
    | uu____2100 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2103  ->
    match uu___110_2103 with
=======
    | uu____2748 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2752  ->
    match uu___111_2752 with
>>>>>>> origin/guido_tactics
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
<<<<<<< HEAD
        let uu____2105 =
          let uu____2109 =
            let uu____2111 =
              let uu____2112 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2112 in
            [uu____2111] in
          ("FStar.Char.Char", uu____2109) in
        FStar_SMTEncoding_Util.mkApp uu____2105
    | FStar_Const.Const_int (i,None ) ->
        let uu____2120 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2120
    | FStar_Const.Const_int (i,Some uu____2122) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2131) ->
        let uu____2134 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2134
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2138 =
          let uu____2139 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2139 in
        failwith uu____2138
=======
        let uu____2754 =
          let uu____2758 =
            let uu____2760 =
              let uu____2761 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2761 in
            [uu____2760] in
          ("FStar.Char.Char", uu____2758) in
        FStar_SMTEncoding_Util.mkApp uu____2754
    | FStar_Const.Const_int (i,None ) ->
        let uu____2769 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2769
    | FStar_Const.Const_int (i,Some uu____2771) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2780) ->
        let uu____2783 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2783
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2787 =
          let uu____2788 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2788 in
        failwith uu____2787
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        | FStar_Syntax_Syntax.Tm_arrow uu____2158 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2166 ->
            let uu____2171 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2171
        | uu____2172 ->
            if norm1
            then let uu____2173 = whnf env t1 in aux false uu____2173
            else
              (let uu____2175 =
                 let uu____2176 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2177 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2176 uu____2177 in
               failwith uu____2175) in
=======
        | FStar_Syntax_Syntax.Tm_arrow uu____2809 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2817 ->
            let uu____2822 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2822
        | uu____2823 ->
            if norm1
            then let uu____2824 = whnf env t1 in aux false uu____2824
            else
              (let uu____2826 =
                 let uu____2827 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2828 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2827 uu____2828 in
               failwith uu____2826) in
>>>>>>> origin/guido_tactics
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
<<<<<<< HEAD
    | uu____2198 ->
        let uu____2199 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2199)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2227::uu____2228::[]) ->
=======
    | uu____2850 ->
        let uu____2851 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2851)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2883::uu____2884::[]) ->
>>>>>>> origin/guido_tactics
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
<<<<<<< HEAD
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2231::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2233 -> false
=======
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2887::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2889 -> false
>>>>>>> origin/guido_tactics
let rec encode_binders:
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
<<<<<<< HEAD
        (let uu____2371 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2371
         then
           let uu____2372 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2372
         else ());
        (let uu____2374 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2423  ->
                   fun b  ->
                     match uu____2423 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2466 =
                           let x = unmangle (fst b) in
                           let uu____2475 = gen_term_var env1 x in
                           match uu____2475 with
                           | (xxsym,xx,env') ->
                               let uu____2489 =
                                 let uu____2492 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2492 env1 xx in
                               (match uu____2489 with
=======
        (let uu____3027 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3027
         then
           let uu____3028 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3028
         else ());
        (let uu____3030 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3066  ->
                   fun b  ->
                     match uu____3066 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3109 =
                           let x = unmangle (fst b) in
                           let uu____3118 = gen_term_var env1 x in
                           match uu____3118 with
                           | (xxsym,xx,env') ->
                               let uu____3132 =
                                 let uu____3135 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3135 env1 xx in
                               (match uu____3132 with
>>>>>>> origin/guido_tactics
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
<<<<<<< HEAD
                         (match uu____2466 with
=======
                         (match uu____3109 with
>>>>>>> origin/guido_tactics
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
<<<<<<< HEAD
         match uu____2374 with
=======
         match uu____3030 with
>>>>>>> origin/guido_tactics
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
<<<<<<< HEAD
          let uu____2580 = encode_term t env in
          match uu____2580 with
          | (t1,decls) ->
              let uu____2587 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2587, decls)
=======
          let uu____3223 = encode_term t env in
          match uu____3223 with
          | (t1,decls) ->
              let uu____3230 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3230, decls)
>>>>>>> origin/guido_tactics
and encode_term_pred':
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
<<<<<<< HEAD
          let uu____2595 = encode_term t env in
          match uu____2595 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2604 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2604, decls)
               | Some f ->
                   let uu____2606 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2606, decls))
=======
          let uu____3238 = encode_term t env in
          match uu____3238 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____3247 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3247, decls)
               | Some f ->
                   let uu____3249 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3249, decls))
>>>>>>> origin/guido_tactics
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
<<<<<<< HEAD
        let uu____2612 = encode_args args_e env in
        match uu____2612 with
=======
        let uu____3255 = encode_args args_e env in
        match uu____3255 with
>>>>>>> origin/guido_tactics
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
<<<<<<< HEAD
              | uu____2624 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2631 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2631 in
            let binary arg_tms1 =
              let uu____2640 =
                let uu____2641 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2641 in
              let uu____2642 =
                let uu____2643 =
                  let uu____2644 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2644 in
                FStar_SMTEncoding_Term.unboxInt uu____2643 in
              (uu____2640, uu____2642) in
            let mk_default uu____2649 =
              let uu____2650 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2650 with
=======
              | uu____3267 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3274 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3274 in
            let binary arg_tms1 =
              let uu____3283 =
                let uu____3284 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3284 in
              let uu____3285 =
                let uu____3286 =
                  let uu____3287 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3287 in
                FStar_SMTEncoding_Term.unboxInt uu____3286 in
              (uu____3283, uu____3285) in
            let mk_default uu____3292 =
              let uu____3293 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3293 with
>>>>>>> origin/guido_tactics
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
<<<<<<< HEAD
              let uu____2691 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2691
              then
                let uu____2692 = let uu____2693 = mk_args ts in op uu____2693 in
                FStar_All.pipe_right uu____2692 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2716 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2716
              then
                let uu____2717 = binary ts in
                match uu____2717 with
                | (t1,t2) ->
                    let uu____2722 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2722
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2725 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2725
                 then
                   let uu____2726 = op (binary ts) in
                   FStar_All.pipe_right uu____2726
=======
              let uu____3338 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3338
              then
                let uu____3339 = let uu____3340 = mk_args ts in op uu____3340 in
                FStar_All.pipe_right uu____3339 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3363 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3363
              then
                let uu____3364 = binary ts in
                match uu____3364 with
                | (t1,t2) ->
                    let uu____3369 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3369
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3372 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3372
                 then
                   let uu____3373 = op (binary ts) in
                   FStar_All.pipe_right uu____3373
>>>>>>> origin/guido_tactics
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Syntax_Const.op_Addition, add1);
              (FStar_Syntax_Const.op_Subtraction, sub1);
              (FStar_Syntax_Const.op_Multiply, mul1);
              (FStar_Syntax_Const.op_Division, div1);
              (FStar_Syntax_Const.op_Modulus, modulus);
              (FStar_Syntax_Const.op_Minus, minus)] in
<<<<<<< HEAD
            let uu____2816 =
              let uu____2822 =
                FStar_List.tryFind
                  (fun uu____2837  ->
                     match uu____2837 with
                     | (l,uu____2844) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2822 FStar_Util.must in
            (match uu____2816 with
             | (uu____2869,op) ->
                 let uu____2877 = op arg_tms in (uu____2877, decls))
=======
            let uu____3463 =
              let uu____3469 =
                FStar_List.tryFind
                  (fun uu____3481  ->
                     match uu____3481 with
                     | (l,uu____3488) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3469 FStar_Util.must in
            (match uu____3463 with
             | (uu____3513,op) ->
                 let uu____3521 = op arg_tms in (uu____3521, decls))
>>>>>>> origin/guido_tactics
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
<<<<<<< HEAD
      (let uu____2884 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2884
       then
         let uu____2885 = FStar_Syntax_Print.tag_of_term t in
         let uu____2886 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2887 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2885 uu____2886
           uu____2887
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2891 ->
           let uu____2912 =
             let uu____2913 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2914 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2915 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2916 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2913
               uu____2914 uu____2915 uu____2916 in
           failwith uu____2912
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2919 =
             let uu____2920 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2921 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2922 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2923 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2920
               uu____2921 uu____2922 uu____2923 in
           failwith uu____2919
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2927 =
             let uu____2928 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2928 in
           failwith uu____2927
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2933) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2963) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2972 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2972, [])
       | FStar_Syntax_Syntax.Tm_type uu____2974 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2977) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2983 = encode_const c in (uu____2983, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2998 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2998 with
            | (binders1,res) ->
                let uu____3005 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3005
                then
                  let uu____3008 = encode_binders None binders1 env in
                  (match uu____3008 with
                   | (vars,guards,env',decls,uu____3023) ->
                       let fsym =
                         let uu____3033 = varops.fresh "f" in
                         (uu____3033, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3036 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3042 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3042.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3042.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3042.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3042.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3042.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3042.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3042.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3042.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3042.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3042.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3042.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3042.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3042.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3042.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3042.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3042.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3042.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3042.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3042.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3042.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3042.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3042.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3042.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____3036 with
                        | (pre_opt,res_t) ->
                            let uu____3049 =
                              encode_term_pred None res_t env' app in
                            (match uu____3049 with
                             | (res_pred,decls') ->
                                 let uu____3056 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3063 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3063, [])
                                   | Some pre ->
                                       let uu____3066 =
                                         encode_formula pre env' in
                                       (match uu____3066 with
                                        | (guard,decls0) ->
                                            let uu____3074 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3074, decls0)) in
                                 (match uu____3056 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3082 =
                                          let uu____3088 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3088) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3082 in
                                      let cvars =
                                        let uu____3098 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3098
                                          (FStar_List.filter
                                             (fun uu____3107  ->
                                                match uu____3107 with
                                                | (x,uu____3111) ->
=======
      (let uu____3528 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3528
       then
         let uu____3529 = FStar_Syntax_Print.tag_of_term t in
         let uu____3530 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3531 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3529 uu____3530
           uu____3531
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3535 ->
           let uu____3550 =
             let uu____3551 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3552 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3553 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3554 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3551
               uu____3552 uu____3553 uu____3554 in
           failwith uu____3550
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3557 =
             let uu____3558 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3559 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3560 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3561 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3558
               uu____3559 uu____3560 uu____3561 in
           failwith uu____3557
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3565 =
             let uu____3566 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3566 in
           failwith uu____3565
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3571) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3601) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3610 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3610, [])
       | FStar_Syntax_Syntax.Tm_type uu____3616 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3619) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3625 = encode_const c in (uu____3625, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3640 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3640 with
            | (binders1,res) ->
                let uu____3647 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3647
                then
                  let uu____3650 = encode_binders None binders1 env in
                  (match uu____3650 with
                   | (vars,guards,env',decls,uu____3665) ->
                       let fsym =
                         let uu____3675 = varops.fresh "f" in
                         (uu____3675, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3678 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3682 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3682.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3682.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3682.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3682.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3682.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3682.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3682.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3682.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3682.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3682.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3682.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3682.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3682.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3682.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3682.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3682.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3682.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3682.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3682.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3682.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3682.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3682.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3682.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_3682.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_3682.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_3682.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____3678 with
                        | (pre_opt,res_t) ->
                            let uu____3689 =
                              encode_term_pred None res_t env' app in
                            (match uu____3689 with
                             | (res_pred,decls') ->
                                 let uu____3696 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3703 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3703, [])
                                   | Some pre ->
                                       let uu____3706 =
                                         encode_formula pre env' in
                                       (match uu____3706 with
                                        | (guard,decls0) ->
                                            let uu____3714 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3714, decls0)) in
                                 (match uu____3696 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3722 =
                                          let uu____3728 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3728) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3722 in
                                      let cvars =
                                        let uu____3738 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3738
                                          (FStar_List.filter
                                             (fun uu____3744  ->
                                                match uu____3744 with
                                                | (x,uu____3748) ->
>>>>>>> origin/guido_tactics
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
<<<<<<< HEAD
                                      let uu____3122 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3122 with
                                       | Some cache_entry ->
                                           let uu____3127 =
                                             let uu____3128 =
                                               let uu____3132 =
=======
                                      let uu____3759 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3759 with
                                       | Some cache_entry ->
                                           let uu____3764 =
                                             let uu____3765 =
                                               let uu____3769 =
>>>>>>> origin/guido_tactics
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
<<<<<<< HEAD
                                                 uu____3132) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3128 in
                                           (uu____3127,
=======
                                                 uu____3769) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3765 in
                                           (uu____3764,
>>>>>>> origin/guido_tactics
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
<<<<<<< HEAD
                                             let uu____3143 =
                                               let uu____3144 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3144 in
                                             varops.mk_unique uu____3143 in
=======
                                             let uu____3780 =
                                               let uu____3781 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3781 in
                                             varops.mk_unique uu____3780 in
>>>>>>> origin/guido_tactics
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
<<<<<<< HEAD
                                             let uu____3151 =
                                               FStar_Options.log_queries () in
                                             if uu____3151
                                             then
                                               let uu____3153 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3153
=======
                                             let uu____3788 =
                                               FStar_Options.log_queries () in
                                             if uu____3788
                                             then
                                               let uu____3790 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3790
>>>>>>> origin/guido_tactics
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
<<<<<<< HEAD
                                             let uu____3159 =
                                               let uu____3163 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3163) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3159 in
=======
                                             let uu____3796 =
                                               let uu____3800 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3800) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3796 in
>>>>>>> origin/guido_tactics
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
<<<<<<< HEAD
                                             let uu____3171 =
                                               let uu____3175 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3175, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3171 in
=======
                                             let uu____3808 =
                                               let uu____3812 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3812, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3808 in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                             let uu____3188 =
                                               let uu____3192 =
                                                 let uu____3193 =
                                                   let uu____3199 =
                                                     let uu____3200 =
                                                       let uu____3203 =
                                                         let uu____3204 =
=======
                                             let uu____3825 =
                                               let uu____3829 =
                                                 let uu____3830 =
                                                   let uu____3836 =
                                                     let uu____3837 =
                                                       let uu____3840 =
                                                         let uu____3841 =
>>>>>>> origin/guido_tactics
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
<<<<<<< HEAD
                                                           uu____3204 in
                                                       (f_has_t, uu____3203) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3200 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3199) in
                                                 mkForall_fuel uu____3193 in
                                               (uu____3192,
=======
                                                           uu____3841 in
                                                       (f_has_t, uu____3840) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3837 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3836) in
                                                 mkForall_fuel uu____3830 in
                                               (uu____3829,
>>>>>>> origin/guido_tactics
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                               uu____3188 in
=======
                                               uu____3825 in
>>>>>>> origin/guido_tactics
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
<<<<<<< HEAD
                                             let uu____3217 =
                                               let uu____3221 =
                                                 let uu____3222 =
                                                   let uu____3228 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3228) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3222 in
                                               (uu____3221, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3217 in
=======
                                             let uu____3854 =
                                               let uu____3858 =
                                                 let uu____3859 =
                                                   let uu____3865 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3865) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3859 in
                                               (uu____3858, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3854 in
>>>>>>> origin/guido_tactics
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
<<<<<<< HEAD
                                           ((let uu____3242 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3242);
=======
                                           ((let uu____3879 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3879);
>>>>>>> origin/guido_tactics
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
<<<<<<< HEAD
                     let uu____3253 =
                       let uu____3257 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3257, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3253 in
=======
                     let uu____3890 =
                       let uu____3894 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3894, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3890 in
>>>>>>> origin/guido_tactics
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
<<<<<<< HEAD
                     let uu____3266 =
                       let uu____3270 =
                         let uu____3271 =
                           let uu____3277 =
                             let uu____3278 =
                               let uu____3281 =
                                 let uu____3282 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3282 in
                               (f_has_t, uu____3281) in
                             FStar_SMTEncoding_Util.mkImp uu____3278 in
                           ([[f_has_t]], [fsym], uu____3277) in
                         mkForall_fuel uu____3271 in
                       (uu____3270, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3266 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3296 ->
           let uu____3301 =
             let uu____3304 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3304 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3309;
                 FStar_Syntax_Syntax.pos = uu____3310;
                 FStar_Syntax_Syntax.vars = uu____3311;_} ->
                 let uu____3318 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3318 with
                  | (b,f1) ->
                      let uu____3332 =
                        let uu____3333 = FStar_List.hd b in fst uu____3333 in
                      (uu____3332, f1))
             | uu____3338 -> failwith "impossible" in
           (match uu____3301 with
            | (x,f) ->
                let uu____3345 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3345 with
                 | (base_t,decls) ->
                     let uu____3352 = gen_term_var env x in
                     (match uu____3352 with
                      | (x1,xtm,env') ->
                          let uu____3361 = encode_formula f env' in
                          (match uu____3361 with
                           | (refinement,decls') ->
                               let uu____3368 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3368 with
=======
                     let uu____3903 =
                       let uu____3907 =
                         let uu____3908 =
                           let uu____3914 =
                             let uu____3915 =
                               let uu____3918 =
                                 let uu____3919 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3919 in
                               (f_has_t, uu____3918) in
                             FStar_SMTEncoding_Util.mkImp uu____3915 in
                           ([[f_has_t]], [fsym], uu____3914) in
                         mkForall_fuel uu____3908 in
                       (uu____3907, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3903 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3933 ->
           let uu____3938 =
             let uu____3941 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3941 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3946;
                 FStar_Syntax_Syntax.pos = uu____3947;
                 FStar_Syntax_Syntax.vars = uu____3948;_} ->
                 let uu____3955 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3955 with
                  | (b,f1) ->
                      let uu____3969 =
                        let uu____3970 = FStar_List.hd b in fst uu____3970 in
                      (uu____3969, f1))
             | uu____3975 -> failwith "impossible" in
           (match uu____3938 with
            | (x,f) ->
                let uu____3982 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3982 with
                 | (base_t,decls) ->
                     let uu____3989 = gen_term_var env x in
                     (match uu____3989 with
                      | (x1,xtm,env') ->
                          let uu____3998 = encode_formula f env' in
                          (match uu____3998 with
                           | (refinement,decls') ->
                               let uu____4005 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4005 with
>>>>>>> origin/guido_tactics
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
<<<<<<< HEAD
                                      let uu____3379 =
                                        let uu____3381 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3385 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3381
                                          uu____3385 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3379 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3404  ->
                                              match uu____3404 with
                                              | (y,uu____3408) ->
=======
                                      let uu____4016 =
                                        let uu____4018 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4022 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4018
                                          uu____4022 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4016 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4038  ->
                                              match uu____4038 with
                                              | (y,uu____4042) ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                    let uu____3427 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3427 with
                                     | Some cache_entry ->
                                         let uu____3432 =
                                           let uu____3433 =
                                             let uu____3437 =
=======
                                    let uu____4061 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4061 with
                                     | Some cache_entry ->
                                         let uu____4066 =
                                           let uu____4067 =
                                             let uu____4071 =
>>>>>>> origin/guido_tactics
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
<<<<<<< HEAD
                                               uu____3437) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3433 in
                                         (uu____3432,
=======
                                               uu____4071) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4067 in
                                         (uu____4066,
>>>>>>> origin/guido_tactics
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
<<<<<<< HEAD
                                           let uu____3449 =
                                             let uu____3450 =
                                               let uu____3451 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3451 in
                                             Prims.strcat module_name
                                               uu____3450 in
                                           varops.mk_unique uu____3449 in
=======
                                           let uu____4083 =
                                             let uu____4084 =
                                               let uu____4085 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4085 in
                                             Prims.strcat module_name
                                               uu____4084 in
                                           varops.mk_unique uu____4083 in
>>>>>>> origin/guido_tactics
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
<<<<<<< HEAD
                                           let uu____3460 =
                                             let uu____3464 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3464) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3460 in
=======
                                           let uu____4094 =
                                             let uu____4098 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4098) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4094 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
>>>>>>> origin/guido_tactics
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1 in
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
<<<<<<< HEAD
                                           let uu____3474 =
                                             let uu____3478 =
                                               let uu____3479 =
                                                 let uu____3485 =
=======
                                           let uu____4109 =
                                             let uu____4113 =
                                               let uu____4114 =
                                                 let uu____4120 =
>>>>>>> origin/guido_tactics
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
<<<<<<< HEAD
                                                   uu____3485) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3479 in
                                             (uu____3478,
=======
                                                   uu____4120) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4114 in
                                             (uu____4113,
>>>>>>> origin/guido_tactics
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                             uu____3474 in
                                         let t_kinding =
                                           let uu____3495 =
                                             let uu____3499 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3499,
=======
                                             uu____4109 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4135 =
                                             let uu____4139 =
                                               let uu____4140 =
                                                 let uu____4146 =
                                                   let uu____4147 =
                                                     let uu____4150 =
                                                       let uu____4151 =
                                                         let uu____4157 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4157) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4151 in
                                                     (uu____4150, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4147 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4146) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4140 in
                                             (uu____4139,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4135 in
                                         let t_kinding =
                                           let uu____4177 =
                                             let uu____4181 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4181,
>>>>>>> origin/guido_tactics
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                             uu____3495 in
                                         let t_interp =
                                           let uu____3509 =
                                             let uu____3513 =
                                               let uu____3514 =
                                                 let uu____3520 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3520) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3514 in
                                             let uu____3532 =
                                               let uu____3534 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3534 in
                                             (uu____3513, uu____3532,
=======
                                             uu____4177 in
                                         let t_interp =
                                           let uu____4191 =
                                             let uu____4195 =
                                               let uu____4196 =
                                                 let uu____4202 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4202) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4196 in
                                             let uu____4214 =
                                               let uu____4216 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____4216 in
                                             (uu____4195, uu____4214,
>>>>>>> origin/guido_tactics
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                             uu____3509 in
=======
                                             uu____4191 in
>>>>>>> origin/guido_tactics
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
<<<<<<< HEAD
                                         ((let uu____3539 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3539);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3560 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3560 in
           let uu____3561 = encode_term_pred None k env ttm in
           (match uu____3561 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3569 =
                    let uu____3573 =
                      let uu____3574 =
                        let uu____3575 =
                          let uu____3576 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3576 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3575 in
                      varops.mk_unique uu____3574 in
                    (t_has_k, (Some "Uvar typing"), uu____3573) in
                  FStar_SMTEncoding_Util.mkAssume uu____3569 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3579 ->
           let uu____3589 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3589 with
            | (head1,args_e) ->
                let uu____3617 =
                  let uu____3625 =
                    let uu____3626 = FStar_Syntax_Subst.compress head1 in
                    uu____3626.FStar_Syntax_Syntax.n in
                  (uu____3625, args_e) in
                (match uu____3617 with
                 | uu____3636 when head_redex env head1 ->
                     let uu____3644 = whnf env t in
                     encode_term uu____3644 env
                 | uu____3645 when is_arithmetic_primitive head1 args_e ->
=======
                                         ((let uu____4221 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4221);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4238 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4238 in
           let uu____4239 = encode_term_pred None k env ttm in
           (match uu____4239 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4247 =
                    let uu____4251 =
                      let uu____4252 =
                        let uu____4253 =
                          let uu____4254 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4254 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4253 in
                      varops.mk_unique uu____4252 in
                    (t_has_k, (Some "Uvar typing"), uu____4251) in
                  FStar_SMTEncoding_Util.mkAssume uu____4247 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4257 ->
           let uu____4267 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4267 with
            | (head1,args_e) ->
                let uu____4295 =
                  let uu____4303 =
                    let uu____4304 = FStar_Syntax_Subst.compress head1 in
                    uu____4304.FStar_Syntax_Syntax.n in
                  (uu____4303, args_e) in
                (match uu____4295 with
                 | uu____4314 when head_redex env head1 ->
                     let uu____4322 = whnf env t in
                     encode_term uu____4322 env
                 | uu____4323 when is_arithmetic_primitive head1 args_e ->
>>>>>>> origin/guido_tactics
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
<<<<<<< HEAD
                       FStar_Syntax_Syntax.tk = uu____3658;
                       FStar_Syntax_Syntax.pos = uu____3659;
                       FStar_Syntax_Syntax.vars = uu____3660;_},uu____3661),uu____3662::
                    (v1,uu____3664)::(v2,uu____3666)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3704 = encode_term v1 env in
                     (match uu____3704 with
                      | (v11,decls1) ->
                          let uu____3711 = encode_term v2 env in
                          (match uu____3711 with
                           | (v21,decls2) ->
                               let uu____3718 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3718,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3721::(v1,uu____3723)::(v2,uu____3725)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3759 = encode_term v1 env in
                     (match uu____3759 with
                      | (v11,decls1) ->
                          let uu____3766 = encode_term v2 env in
                          (match uu____3766 with
                           | (v21,decls2) ->
                               let uu____3773 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3773,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3775) ->
                     let e0 =
                       let uu____3787 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3787 in
                     ((let uu____3793 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3793
                       then
                         let uu____3794 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3794
                       else ());
                      (let e =
                         let uu____3799 =
                           let uu____3800 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3801 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3800
                             uu____3801 in
                         uu____3799 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3810),(arg,uu____3812)::[]) -> encode_term arg env
                 | uu____3830 ->
                     let uu____3838 = encode_args args_e env in
                     (match uu____3838 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3871 = encode_term head1 env in
                            match uu____3871 with
=======
                       FStar_Syntax_Syntax.tk = uu____4336;
                       FStar_Syntax_Syntax.pos = uu____4337;
                       FStar_Syntax_Syntax.vars = uu____4338;_},uu____4339),uu____4340::
                    (v1,uu____4342)::(v2,uu____4344)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4382 = encode_term v1 env in
                     (match uu____4382 with
                      | (v11,decls1) ->
                          let uu____4389 = encode_term v2 env in
                          (match uu____4389 with
                           | (v21,decls2) ->
                               let uu____4396 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4396,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4399::(v1,uu____4401)::(v2,uu____4403)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4437 = encode_term v1 env in
                     (match uu____4437 with
                      | (v11,decls1) ->
                          let uu____4444 = encode_term v2 env in
                          (match uu____4444 with
                           | (v21,decls2) ->
                               let uu____4451 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4451,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4453) ->
                     let e0 =
                       let uu____4465 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____4465 in
                     ((let uu____4471 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____4471
                       then
                         let uu____4472 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4472
                       else ());
                      (let e =
                         let uu____4477 =
                           let uu____4478 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____4479 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4478
                             uu____4479 in
                         uu____4477 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4488),(arg,uu____4490)::[]) -> encode_term arg env
                 | uu____4508 ->
                     let uu____4516 = encode_args args_e env in
                     (match uu____4516 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4549 = encode_term head1 env in
                            match uu____4549 with
>>>>>>> origin/guido_tactics
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
<<<<<<< HEAD
                                     let uu____3910 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3910 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3958  ->
                                                 fun uu____3959  ->
                                                   match (uu____3958,
                                                           uu____3959)
                                                   with
                                                   | ((bv,uu____3973),
                                                      (a,uu____3975)) ->
=======
                                     let uu____4588 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4588 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4632  ->
                                                 fun uu____4633  ->
                                                   match (uu____4632,
                                                           uu____4633)
                                                   with
                                                   | ((bv,uu____4647),
                                                      (a,uu____4649)) ->
>>>>>>> origin/guido_tactics
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
<<<<<<< HEAD
                                            let uu____3989 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3989
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3994 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3994 with
=======
                                            let uu____4663 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4663
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4668 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____4668 with
>>>>>>> origin/guido_tactics
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
<<<<<<< HEAD
                                                 let uu____4004 =
                                                   let uu____4008 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4013 =
                                                     let uu____4014 =
                                                       let uu____4015 =
                                                         let uu____4016 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4016 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4015 in
                                                     varops.mk_unique
                                                       uu____4014 in
                                                   (uu____4008,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4013) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4004 in
=======
                                                 let uu____4678 =
                                                   let uu____4682 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4687 =
                                                     let uu____4688 =
                                                       let uu____4689 =
                                                         let uu____4690 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4690 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4689 in
                                                     varops.mk_unique
                                                       uu____4688 in
                                                   (uu____4682,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4687) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4678 in
>>>>>>> origin/guido_tactics
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
<<<<<<< HEAD
                            let uu____4027 = lookup_free_var_sym env fv in
                            match uu____4027 with
=======
                            let uu____4707 = lookup_free_var_sym env fv in
                            match uu____4707 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                   FStar_Syntax_Syntax.tk = uu____4048;
                                   FStar_Syntax_Syntax.pos = uu____4049;
                                   FStar_Syntax_Syntax.vars = uu____4050;_},uu____4051)
=======
                                   FStar_Syntax_Syntax.tk = uu____4730;
                                   FStar_Syntax_Syntax.pos = uu____4731;
                                   FStar_Syntax_Syntax.vars = uu____4732;_},uu____4733)
>>>>>>> origin/guido_tactics
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
<<<<<<< HEAD
                                   FStar_Syntax_Syntax.tk = uu____4062;
                                   FStar_Syntax_Syntax.pos = uu____4063;
                                   FStar_Syntax_Syntax.vars = uu____4064;_},uu____4065)
                                ->
                                let uu____4070 =
                                  let uu____4071 =
                                    let uu____4074 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4074
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4071
                                    FStar_Pervasives.snd in
                                Some uu____4070
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4090 =
                                  let uu____4091 =
                                    let uu____4094 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4094
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4091
                                    FStar_Pervasives.snd in
                                Some uu____4090
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4109,(FStar_Util.Inl t1,uu____4111),uu____4112)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4150,(FStar_Util.Inr c,uu____4152),uu____4153)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4191 -> None in
=======
                                   FStar_Syntax_Syntax.tk = uu____4744;
                                   FStar_Syntax_Syntax.pos = uu____4745;
                                   FStar_Syntax_Syntax.vars = uu____4746;_},uu____4747)
                                ->
                                let uu____4752 =
                                  let uu____4753 =
                                    let uu____4756 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4756
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4753
                                    FStar_Pervasives.snd in
                                Some uu____4752
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4776 =
                                  let uu____4777 =
                                    let uu____4780 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4780
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4777
                                    FStar_Pervasives.snd in
                                Some uu____4776
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4799,(FStar_Util.Inl t1,uu____4801),uu____4802)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4840,(FStar_Util.Inr c,uu____4842),uu____4843)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4881 -> None in
>>>>>>> origin/guido_tactics
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
<<<<<<< HEAD
                                 let uu____4211 =
=======
                                 let uu____4901 =
>>>>>>> origin/guido_tactics
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
<<<<<<< HEAD
                                   FStar_Syntax_Util.unrefine uu____4211 in
                               let uu____4212 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4212 with
=======
                                   FStar_Syntax_Util.unrefine uu____4901 in
                               let uu____4902 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4902 with
>>>>>>> origin/guido_tactics
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
<<<<<<< HEAD
                                              uu____4222;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4223;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4224;_},uu____4225)
=======
                                              uu____4912;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4913;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4914;_},uu____4915)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                     | uu____4243 ->
=======
                                     | uu____4947 ->
>>>>>>> origin/guido_tactics
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
<<<<<<< HEAD
           let uu____4288 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4288 with
            | (bs1,body1,opening) ->
                let fallback uu____4303 =
=======
           let uu____4987 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4987 with
            | (bs1,body1,opening) ->
                let fallback uu____5002 =
>>>>>>> origin/guido_tactics
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
<<<<<<< HEAD
                  let uu____4308 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4308, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4319 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4319
                  | FStar_Util.Inr (eff,uu____4321) ->
                      let uu____4327 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4327 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4372 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4375 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4375.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4375.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4375.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4375.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4375.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4375.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4375.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4375.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4375.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4375.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4375.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4375.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4375.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4375.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4375.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4375.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4375.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4375.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4375.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4375.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4375.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4375.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4375.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4372 FStar_Syntax_Syntax.U_unknown in
                        let uu____4376 =
                          let uu____4377 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4377 in
                        FStar_Util.Inl uu____4376
                    | FStar_Util.Inr (eff_name,uu____4384) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4415 =
                        let uu____4416 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4416 in
                      FStar_All.pipe_right uu____4415
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4428 =
                        let uu____4429 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4429 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4437 =
                          let uu____4438 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4438 in
                        FStar_All.pipe_right uu____4437
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4442 =
                             let uu____4443 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4443 in
                           FStar_All.pipe_right uu____4442
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4454 =
                         let uu____4455 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4455 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4454);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4470 =
                       (is_impure lc1) &&
                         (let uu____4472 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4472) in
                     if uu____4470
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4477 = encode_binders None bs1 env in
                        match uu____4477 with
                        | (vars,guards,envbody,decls,uu____4492) ->
                            let uu____4499 =
                              let uu____4507 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4507
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4499 with
                             | (lc2,body2) ->
                                 let uu____4532 = encode_term body2 envbody in
                                 (match uu____4532 with
                                  | (body3,decls') ->
                                      let uu____4539 =
                                        let uu____4544 = codomain_eff lc2 in
                                        match uu____4544 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4556 =
                                              encode_term tfun env in
                                            (match uu____4556 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4539 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4575 =
                                               let uu____4581 =
                                                 let uu____4582 =
                                                   let uu____4585 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4585, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4582 in
                                               ([], vars, uu____4581) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4575 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4593 =
                                                   let uu____4595 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4595 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4593 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4606 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4606 with
                                            | Some cache_entry ->
                                                let uu____4611 =
                                                  let uu____4612 =
                                                    let uu____4616 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4616) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4612 in
                                                (uu____4611,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4622 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4622 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4629 =
                                                         let uu____4630 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4630 =
                                                           cache_size in
                                                       if uu____4629
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'') in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives.snd
                                                         cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4641 =
                                                           let uu____4642 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4642 in
                                                         varops.mk_unique
                                                           uu____4641 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let f =
                                                       let uu____4647 =
                                                         let uu____4651 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4651) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4647 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4663 =
                                                             let uu____4664 =
                                                               let uu____4668
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4668,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4664 in
                                                           [uu____4663] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4676 =
                                                         let uu____4680 =
                                                           let uu____4681 =
                                                             let uu____4687 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4687) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4681 in
                                                         (uu____4680,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4676 in
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
                                                     ((let uu____4697 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4697);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4699,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4700;
                          FStar_Syntax_Syntax.lbunivs = uu____4701;
                          FStar_Syntax_Syntax.lbtyp = uu____4702;
                          FStar_Syntax_Syntax.lbeff = uu____4703;
                          FStar_Syntax_Syntax.lbdef = uu____4704;_}::uu____4705),uu____4706)
=======
                  let uu____5007 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____5007, [decl]) in
                let is_impure rc =
                  let uu____5013 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____5013 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | None  ->
                        let uu____5022 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5022 FStar_Pervasives.fst
                    | Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Syntax_Const.effect_Tot_lid
                  then
                    let uu____5035 = FStar_Syntax_Syntax.mk_Total res_typ in
                    Some uu____5035
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Syntax_Const.effect_GTot_lid
                    then
                      (let uu____5038 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       Some uu____5038)
                    else None in
                (match lopt with
                 | None  ->
                     ((let uu____5043 =
                         let uu____5044 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5044 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5043);
                      fallback ())
                 | Some rc ->
                     let uu____5046 =
                       (is_impure rc) &&
                         (let uu____5047 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____5047) in
                     if uu____5046
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5052 = encode_binders None bs1 env in
                        match uu____5052 with
                        | (vars,guards,envbody,decls,uu____5067) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____5075 = encode_term body2 envbody in
                            (match uu____5075 with
                             | (body3,decls') ->
                                 let uu____5082 =
                                   let uu____5087 = codomain_eff rc in
                                   match uu____5087 with
                                   | None  -> (None, [])
                                   | Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____5099 = encode_term tfun env in
                                       (match uu____5099 with
                                        | (t1,decls1) -> ((Some t1), decls1)) in
                                 (match uu____5082 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5118 =
                                          let uu____5124 =
                                            let uu____5125 =
                                              let uu____5128 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____5128, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5125 in
                                          ([], vars, uu____5124) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5118 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | None  -> cvars
                                        | Some t1 ->
                                            let uu____5136 =
                                              let uu____5138 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____5138
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5136 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____5149 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____5149 with
                                       | Some cache_entry ->
                                           let uu____5154 =
                                             let uu____5155 =
                                               let uu____5159 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5159) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5155 in
                                           (uu____5154,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let uu____5165 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____5165 with
                                            | Some t1 ->
                                                let decls1 =
                                                  let uu____5172 =
                                                    let uu____5173 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____5173 = cache_size in
                                                  if uu____5172
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'') in
                                                (t1, decls1)
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives.snd
                                                    cvars1 in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name in
                                                  let fsym =
                                                    let uu____5184 =
                                                      let uu____5185 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5185 in
                                                    varops.mk_unique
                                                      uu____5184 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____5190 =
                                                    let uu____5194 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____5194) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5190 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | None  -> []
                                                  | Some t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          None f t1 in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym in
                                                      let uu____5206 =
                                                        let uu____5207 =
                                                          let uu____5211 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____5211,
                                                            (Some a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5207 in
                                                      [uu____5206] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____5219 =
                                                    let uu____5223 =
                                                      let uu____5224 =
                                                        let uu____5230 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5230) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5224 in
                                                    (uu____5223,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5219 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____5240 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5240);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5242,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5243;
                          FStar_Syntax_Syntax.lbunivs = uu____5244;
                          FStar_Syntax_Syntax.lbtyp = uu____5245;
                          FStar_Syntax_Syntax.lbeff = uu____5246;
                          FStar_Syntax_Syntax.lbdef = uu____5247;_}::uu____5248),uu____5249)
>>>>>>> origin/guido_tactics
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
<<<<<<< HEAD
                FStar_Syntax_Syntax.lbunivs = uu____4724;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4726;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4742 ->
=======
                FStar_Syntax_Syntax.lbunivs = uu____5267;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5269;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5285 ->
>>>>>>> origin/guido_tactics
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
<<<<<<< HEAD
             let uu____4755 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4755, [decl_e])))
=======
             let uu____5298 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5298, [decl_e])))
>>>>>>> origin/guido_tactics
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
                 (FStar_SMTEncoding_Term.term*
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
<<<<<<< HEAD
              let uu____4795 = encode_term e1 env in
              match uu____4795 with
              | (ee1,decls1) ->
                  let uu____4802 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4802 with
                   | (xs,e21) ->
                       let uu____4816 = FStar_List.hd xs in
                       (match uu____4816 with
                        | (x1,uu____4824) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4826 = encode_body e21 env' in
                            (match uu____4826 with
=======
              let uu____5340 = encode_term e1 env in
              match uu____5340 with
              | (ee1,decls1) ->
                  let uu____5347 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____5347 with
                   | (xs,e21) ->
                       let uu____5361 = FStar_List.hd xs in
                       (match uu____5361 with
                        | (x1,uu____5369) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5371 = encode_body e21 env' in
                            (match uu____5371 with
>>>>>>> origin/guido_tactics
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
<<<<<<< HEAD
            let uu____4848 =
              let uu____4852 =
                let uu____4853 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4853 in
              gen_term_var env uu____4852 in
            match uu____4848 with
            | (scrsym,scr',env1) ->
                let uu____4863 = encode_term e env1 in
                (match uu____4863 with
                 | (scr,decls) ->
                     let uu____4870 =
                       let encode_branch b uu____4886 =
                         match uu____4886 with
                         | (else_case,decls1) ->
                             let uu____4897 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4897 with
                              | (p,w,br) ->
                                  let uu____4916 = encode_pat env1 p in
                                  (match uu____4916 with
=======
            let uu____5393 =
              let uu____5397 =
                let uu____5398 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5398 in
              gen_term_var env uu____5397 in
            match uu____5393 with
            | (scrsym,scr',env1) ->
                let uu____5408 = encode_term e env1 in
                (match uu____5408 with
                 | (scr,decls) ->
                     let uu____5415 =
                       let encode_branch b uu____5431 =
                         match uu____5431 with
                         | (else_case,decls1) ->
                             let uu____5442 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5442 with
                              | (p,w,br) ->
                                  let uu____5463 = encode_pat env1 p in
                                  (match uu____5463 with
>>>>>>> origin/guido_tactics
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
<<<<<<< HEAD
                                                 fun uu____4940  ->
                                                   match uu____4940 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4945 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4960 =
                                               encode_term w1 env2 in
                                             (match uu____4960 with
                                              | (w2,decls2) ->
                                                  let uu____4968 =
                                                    let uu____4969 =
                                                      let uu____4972 =
                                                        let uu____4973 =
                                                          let uu____4976 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4976) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4973 in
                                                      (guard, uu____4972) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4969 in
                                                  (uu____4968, decls2)) in
                                       (match uu____4945 with
                                        | (guard1,decls2) ->
                                            let uu____4984 =
                                              encode_br br env2 in
                                            (match uu____4984 with
                                             | (br1,decls3) ->
                                                 let uu____4992 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4992,
=======
                                                 fun uu____5483  ->
                                                   match uu____5483 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____5488 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____5503 =
                                               encode_term w1 env2 in
                                             (match uu____5503 with
                                              | (w2,decls2) ->
                                                  let uu____5511 =
                                                    let uu____5512 =
                                                      let uu____5515 =
                                                        let uu____5516 =
                                                          let uu____5519 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5519) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5516 in
                                                      (guard, uu____5515) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5512 in
                                                  (uu____5511, decls2)) in
                                       (match uu____5488 with
                                        | (guard1,decls2) ->
                                            let uu____5527 =
                                              encode_br br env2 in
                                            (match uu____5527 with
                                             | (br1,decls3) ->
                                                 let uu____5535 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5535,
>>>>>>> origin/guido_tactics
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
<<<<<<< HEAD
                     (match uu____4870 with
                      | (match_tm,decls1) ->
                          let uu____5003 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5003, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5025 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5025
       then
         let uu____5026 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5026
       else ());
      (let uu____5028 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5028 with
       | (vars,pat_term) ->
           let uu____5038 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5069  ->
                     fun v1  ->
                       match uu____5069 with
                       | (env1,vars1) ->
                           let uu____5097 = gen_term_var env1 v1 in
                           (match uu____5097 with
                            | (xx,uu____5109,env2) ->
=======
                     (match uu____5415 with
                      | (match_tm,decls1) ->
                          let uu____5546 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5546, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5568 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5568
       then
         let uu____5569 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5569
       else ());
      (let uu____5571 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5571 with
       | (vars,pat_term) ->
           let uu____5581 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5604  ->
                     fun v1  ->
                       match uu____5604 with
                       | (env1,vars1) ->
                           let uu____5632 = gen_term_var env1 v1 in
                           (match uu____5632 with
                            | (xx,uu____5644,env2) ->
>>>>>>> origin/guido_tactics
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
<<<<<<< HEAD
           (match uu____5038 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5154 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5155 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5156 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5162 =
                        let uu____5165 = encode_const c in
                        (scrutinee, uu____5165) in
                      FStar_SMTEncoding_Util.mkEq uu____5162
=======
           (match uu____5581 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5691 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5692 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5693 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5699 =
                        let uu____5702 = encode_const c in
                        (scrutinee, uu____5702) in
                      FStar_SMTEncoding_Util.mkEq uu____5699
>>>>>>> origin/guido_tactics
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
<<<<<<< HEAD
                        let uu____5178 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5178 with
                        | (uu____5182,uu____5183::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5185 ->
=======
                        let uu____5721 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5721 with
                        | (uu____5725,uu____5726::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5728 ->
>>>>>>> origin/guido_tactics
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
<<<<<<< HEAD
                                fun uu____5206  ->
                                  match uu____5206 with
                                  | (arg,uu____5211) ->
=======
                                fun uu____5749  ->
                                  match uu____5749 with
                                  | (arg,uu____5755) ->
>>>>>>> origin/guido_tactics
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
<<<<<<< HEAD
                                      let uu____5215 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5215)) in
=======
                                      let uu____5765 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5765)) in
>>>>>>> origin/guido_tactics
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
<<<<<<< HEAD
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5233) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5252 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5265 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5291  ->
                                  match uu____5291 with
                                  | (arg,uu____5299) ->
=======
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5785) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5804 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5819 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5841  ->
                                  match uu____5841 with
                                  | (arg,uu____5850) ->
>>>>>>> origin/guido_tactics
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
<<<<<<< HEAD
                                      let uu____5303 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5303)) in
                      FStar_All.pipe_right uu____5265 FStar_List.flatten in
                let pat_term1 uu____5319 = encode_term pat_term env1 in
=======
                                      let uu____5860 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5860)) in
                      FStar_All.pipe_right uu____5819 FStar_List.flatten in
                let pat_term1 uu____5876 = encode_term pat_term env1 in
>>>>>>> origin/guido_tactics
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
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
<<<<<<< HEAD
      let uu____5326 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5350  ->
                fun uu____5351  ->
                  match (uu____5350, uu____5351) with
                  | ((tms,decls),(t,uu____5371)) ->
                      let uu____5382 = encode_term t env in
                      (match uu____5382 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5326 with | (l1,decls) -> ((FStar_List.rev l1), decls)
=======
      let uu____5883 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5898  ->
                fun uu____5899  ->
                  match (uu____5898, uu____5899) with
                  | ((tms,decls),(t,uu____5919)) ->
                      let uu____5930 = encode_term t env in
                      (match uu____5930 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5883 with | (l1,decls) -> ((FStar_List.rev l1), decls)
>>>>>>> origin/guido_tactics
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
<<<<<<< HEAD
        let uu____5416 = FStar_Syntax_Util.list_elements e in
        match uu____5416 with
=======
        let uu____5964 = FStar_Syntax_Util.list_elements e in
        match uu____5964 with
>>>>>>> origin/guido_tactics
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
<<<<<<< HEAD
        let uu____5431 =
          let uu____5441 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5441 FStar_Syntax_Util.head_and_args in
        match uu____5431 with
        | (head1,args) ->
            let uu____5469 =
              let uu____5477 =
                let uu____5478 = FStar_Syntax_Util.un_uinst head1 in
                uu____5478.FStar_Syntax_Syntax.n in
              (uu____5477, args) in
            (match uu____5469 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5489,uu____5490)::(e,uu____5492)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____5518 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5545 =
            let uu____5555 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5555 FStar_Syntax_Util.head_and_args in
          match uu____5545 with
          | (head1,args) ->
              let uu____5584 =
                let uu____5592 =
                  let uu____5593 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5593.FStar_Syntax_Syntax.n in
                (uu____5592, args) in
              (match uu____5584 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5606)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5626 -> None) in
        match elts with
        | t1::[] ->
            let uu____5641 = smt_pat_or1 t1 in
            (match uu____5641 with
             | Some e ->
                 let uu____5654 = list_elements1 e in
                 FStar_All.pipe_right uu____5654
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5667 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5667
                           (FStar_List.map one_pat)))
             | uu____5675 ->
                 let uu____5679 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5679])
        | uu____5695 ->
            let uu____5697 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5697] in
      let uu____5713 =
        let uu____5726 =
          let uu____5727 = FStar_Syntax_Subst.compress t in
          uu____5727.FStar_Syntax_Syntax.n in
        match uu____5726 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5754 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5754 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5783;
                        FStar_Syntax_Syntax.effect_name = uu____5784;
                        FStar_Syntax_Syntax.result_typ = uu____5785;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5787)::(post,uu____5789)::(pats,uu____5791)::[];
                        FStar_Syntax_Syntax.flags = uu____5792;_}
                      ->
                      let uu____5824 = lemma_pats pats in
                      (binders1, pre, post, uu____5824)
                  | uu____5837 -> failwith "impos"))
        | uu____5850 -> failwith "Impos" in
      match uu____5713 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5886 = env in
            {
              bindings = (uu___137_5886.bindings);
              depth = (uu___137_5886.depth);
              tcenv = (uu___137_5886.tcenv);
              warn = (uu___137_5886.warn);
              cache = (uu___137_5886.cache);
              nolabels = (uu___137_5886.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5886.encode_non_total_function_typ);
              current_module_name = (uu___137_5886.current_module_name)
            } in
          let uu____5887 = encode_binders None binders env1 in
          (match uu____5887 with
           | (vars,guards,env2,decls,uu____5902) ->
               let uu____5909 =
                 let uu____5916 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5942 =
                             let uu____5947 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5947 FStar_List.unzip in
                           match uu____5942 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5916 FStar_List.unzip in
               (match uu____5909 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_6006 = env2 in
                      {
                        bindings = (uu___138_6006.bindings);
                        depth = (uu___138_6006.depth);
                        tcenv = (uu___138_6006.tcenv);
                        warn = (uu___138_6006.warn);
                        cache = (uu___138_6006.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_6006.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_6006.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_6006.current_module_name)
                      } in
                    let uu____6007 =
                      let uu____6010 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6010 env3 in
                    (match uu____6007 with
                     | (pre1,decls'') ->
                         let uu____6015 =
                           let uu____6018 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6018 env3 in
                         (match uu____6015 with
=======
        let uu____5979 =
          let uu____5989 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5989 FStar_Syntax_Util.head_and_args in
        match uu____5979 with
        | (head1,args) ->
            let uu____6017 =
              let uu____6025 =
                let uu____6026 = FStar_Syntax_Util.un_uinst head1 in
                uu____6026.FStar_Syntax_Syntax.n in
              (uu____6025, args) in
            (match uu____6017 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6037,uu____6038)::(e,uu____6040)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____6066 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6093 =
            let uu____6103 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6103 FStar_Syntax_Util.head_and_args in
          match uu____6093 with
          | (head1,args) ->
              let uu____6132 =
                let uu____6140 =
                  let uu____6141 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6141.FStar_Syntax_Syntax.n in
                (uu____6140, args) in
              (match uu____6132 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6154)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____6174 -> None) in
        match elts with
        | t1::[] ->
            let uu____6189 = smt_pat_or1 t1 in
            (match uu____6189 with
             | Some e ->
                 let uu____6202 = list_elements1 e in
                 FStar_All.pipe_right uu____6202
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6213 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6213
                           (FStar_List.map one_pat)))
             | uu____6221 ->
                 let uu____6225 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6225])
        | uu____6241 ->
            let uu____6243 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6243] in
      let uu____6259 =
        let uu____6272 =
          let uu____6273 = FStar_Syntax_Subst.compress t in
          uu____6273.FStar_Syntax_Syntax.n in
        match uu____6272 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6300 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6300 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6329;
                        FStar_Syntax_Syntax.effect_name = uu____6330;
                        FStar_Syntax_Syntax.result_typ = uu____6331;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6333)::(post,uu____6335)::(pats,uu____6337)::[];
                        FStar_Syntax_Syntax.flags = uu____6338;_}
                      ->
                      let uu____6370 = lemma_pats pats in
                      (binders1, pre, post, uu____6370)
                  | uu____6383 -> failwith "impos"))
        | uu____6396 -> failwith "Impos" in
      match uu____6259 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6432 = env in
            {
              bindings = (uu___136_6432.bindings);
              depth = (uu___136_6432.depth);
              tcenv = (uu___136_6432.tcenv);
              warn = (uu___136_6432.warn);
              cache = (uu___136_6432.cache);
              nolabels = (uu___136_6432.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6432.encode_non_total_function_typ);
              current_module_name = (uu___136_6432.current_module_name)
            } in
          let uu____6433 = encode_binders None binders env1 in
          (match uu____6433 with
           | (vars,guards,env2,decls,uu____6448) ->
               let uu____6455 =
                 let uu____6462 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6484 =
                             let uu____6489 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6489 FStar_List.unzip in
                           match uu____6484 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6462 FStar_List.unzip in
               (match uu____6455 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6547 = env2 in
                      {
                        bindings = (uu___137_6547.bindings);
                        depth = (uu___137_6547.depth);
                        tcenv = (uu___137_6547.tcenv);
                        warn = (uu___137_6547.warn);
                        cache = (uu___137_6547.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6547.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6547.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6547.current_module_name)
                      } in
                    let uu____6548 =
                      let uu____6551 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6551 env3 in
                    (match uu____6548 with
                     | (pre1,decls'') ->
                         let uu____6556 =
                           let uu____6559 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6559 env3 in
                         (match uu____6556 with
>>>>>>> origin/guido_tactics
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
<<<<<<< HEAD
                              let uu____6025 =
                                let uu____6026 =
                                  let uu____6032 =
                                    let uu____6033 =
                                      let uu____6036 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6036, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6033 in
                                  (pats, vars, uu____6032) in
                                FStar_SMTEncoding_Util.mkForall uu____6026 in
                              (uu____6025, decls1)))))
=======
                              let uu____6566 =
                                let uu____6567 =
                                  let uu____6573 =
                                    let uu____6574 =
                                      let uu____6577 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6577, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6574 in
                                  (pats, vars, uu____6573) in
                                FStar_SMTEncoding_Util.mkForall uu____6567 in
                              (uu____6566, decls1)))))
>>>>>>> origin/guido_tactics
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
<<<<<<< HEAD
        let uu____6049 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6049
        then
          let uu____6050 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6051 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6050 uu____6051
        else () in
      let enc f r l =
        let uu____6078 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6096 = encode_term (fst x) env in
                 match uu____6096 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6078 with
        | (decls,args) ->
            let uu____6113 =
              let uu___139_6114 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6114.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6114.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6113, decls) in
      let const_op f r uu____6133 = let uu____6136 = f r in (uu____6136, []) in
      let un_op f l =
        let uu____6152 = FStar_List.hd l in FStar_All.pipe_left f uu____6152 in
      let bin_op f uu___111_6165 =
        match uu___111_6165 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6173 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6200 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6216  ->
                 match uu____6216 with
                 | (t,uu____6224) ->
                     let uu____6225 = encode_formula t env in
                     (match uu____6225 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6200 with
        | (decls,phis) ->
            let uu____6242 =
              let uu___140_6243 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6243.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6243.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6242, decls) in
      let eq_op r uu___112_6259 =
        match uu___112_6259 with
        | uu____6262::e1::e2::[] ->
            let uu____6293 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6293 r [e1; e2]
        | uu____6312::uu____6313::e1::e2::[] ->
            let uu____6352 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6352 r [e1; e2]
        | l ->
            let uu____6372 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6372 r l in
      let mk_imp1 r uu___113_6391 =
        match uu___113_6391 with
        | (lhs,uu____6395)::(rhs,uu____6397)::[] ->
            let uu____6418 = encode_formula rhs env in
            (match uu____6418 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6427) ->
                      (l1, decls1)
                  | uu____6430 ->
                      let uu____6431 = encode_formula lhs env in
                      (match uu____6431 with
                       | (l2,decls2) ->
                           let uu____6438 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6438, (FStar_List.append decls1 decls2)))))
        | uu____6440 -> failwith "impossible" in
      let mk_ite r uu___114_6455 =
        match uu___114_6455 with
        | (guard,uu____6459)::(_then,uu____6461)::(_else,uu____6463)::[] ->
            let uu____6492 = encode_formula guard env in
            (match uu____6492 with
             | (g,decls1) ->
                 let uu____6499 = encode_formula _then env in
                 (match uu____6499 with
                  | (t,decls2) ->
                      let uu____6506 = encode_formula _else env in
                      (match uu____6506 with
=======
        let uu____6590 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6590
        then
          let uu____6591 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6592 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6591 uu____6592
        else () in
      let enc f r l =
        let uu____6619 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6632 = encode_term (fst x) env in
                 match uu____6632 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6619 with
        | (decls,args) ->
            let uu____6649 =
              let uu___138_6650 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6650.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6650.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6649, decls) in
      let const_op f r uu____6675 = let uu____6684 = f r in (uu____6684, []) in
      let un_op f l =
        let uu____6700 = FStar_List.hd l in FStar_All.pipe_left f uu____6700 in
      let bin_op f uu___112_6713 =
        match uu___112_6713 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6721 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6748 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6757  ->
                 match uu____6757 with
                 | (t,uu____6765) ->
                     let uu____6766 = encode_formula t env in
                     (match uu____6766 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6748 with
        | (decls,phis) ->
            let uu____6783 =
              let uu___139_6784 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6784.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6784.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6783, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6823  ->
               match uu____6823 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6837) -> false
                    | uu____6838 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6851 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6851
        else
          (let uu____6866 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6866 r rf) in
      let mk_imp1 r uu___113_6885 =
        match uu___113_6885 with
        | (lhs,uu____6889)::(rhs,uu____6891)::[] ->
            let uu____6912 = encode_formula rhs env in
            (match uu____6912 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6921) ->
                      (l1, decls1)
                  | uu____6924 ->
                      let uu____6925 = encode_formula lhs env in
                      (match uu____6925 with
                       | (l2,decls2) ->
                           let uu____6932 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6932, (FStar_List.append decls1 decls2)))))
        | uu____6934 -> failwith "impossible" in
      let mk_ite r uu___114_6949 =
        match uu___114_6949 with
        | (guard,uu____6953)::(_then,uu____6955)::(_else,uu____6957)::[] ->
            let uu____6986 = encode_formula guard env in
            (match uu____6986 with
             | (g,decls1) ->
                 let uu____6993 = encode_formula _then env in
                 (match uu____6993 with
                  | (t,decls2) ->
                      let uu____7000 = encode_formula _else env in
                      (match uu____7000 with
>>>>>>> origin/guido_tactics
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
<<<<<<< HEAD
        | uu____6515 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6534 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6534 in
      let connectives =
        let uu____6546 =
          let uu____6555 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6555) in
        let uu____6568 =
          let uu____6578 =
            let uu____6587 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6587) in
          let uu____6600 =
            let uu____6610 =
              let uu____6620 =
                let uu____6629 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6629) in
              let uu____6642 =
                let uu____6652 =
                  let uu____6662 =
                    let uu____6671 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6671) in
                  [uu____6662;
=======
        | uu____7009 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7028 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7028 in
      let connectives =
        let uu____7040 =
          let uu____7049 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____7049) in
        let uu____7062 =
          let uu____7072 =
            let uu____7081 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____7081) in
          let uu____7094 =
            let uu____7104 =
              let uu____7114 =
                let uu____7123 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____7123) in
              let uu____7136 =
                let uu____7146 =
                  let uu____7156 =
                    let uu____7165 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____7165) in
                  [uu____7156;
>>>>>>> origin/guido_tactics
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
<<<<<<< HEAD
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6652 in
              uu____6620 :: uu____6642 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6610 in
          uu____6578 :: uu____6600 in
        uu____6546 :: uu____6568 in
=======
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____7146 in
              uu____7114 :: uu____7136 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____7104 in
          uu____7072 :: uu____7094 in
        uu____7040 :: uu____7062 in
>>>>>>> origin/guido_tactics
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
<<<<<<< HEAD
            let uu____6833 = encode_formula phi' env in
            (match uu____6833 with
             | (phi2,decls) ->
                 let uu____6840 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6840, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6841 ->
            let uu____6846 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6846 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6873 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6873 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6881;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6883;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6899 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6899 with | (t,decls) -> (t, decls))
=======
            let uu____7381 = encode_formula phi' env in
            (match uu____7381 with
             | (phi2,decls) ->
                 let uu____7388 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7388, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7389 ->
            let uu____7394 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7394 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7423 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7423 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7431;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7433;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7449 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7449 with | (t,decls) -> (t, decls))
>>>>>>> origin/guido_tactics
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
                fv,uu____6931::(x,uu____6933)::(t,uu____6935)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6969 = encode_term x env in
                 (match uu____6969 with
                  | (x1,decls) ->
                      let uu____6976 = encode_term t env in
                      (match uu____6976 with
                       | (t1,decls') ->
                           let uu____6983 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6983, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6987)::(msg,uu____6989)::(phi2,uu____6991)::[])
=======
                fv,uu____7481::(x,uu____7483)::(t,uu____7485)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7519 = encode_term x env in
                 (match uu____7519 with
                  | (x1,decls) ->
                      let uu____7526 = encode_term t env in
                      (match uu____7526 with
                       | (t1,decls') ->
                           let uu____7533 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7533, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7537)::(msg,uu____7539)::(phi2,uu____7541)::[])
>>>>>>> origin/guido_tactics
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
<<<<<<< HEAD
                 let uu____7025 =
                   let uu____7028 =
                     let uu____7029 = FStar_Syntax_Subst.compress r in
                     uu____7029.FStar_Syntax_Syntax.n in
                   let uu____7032 =
                     let uu____7033 = FStar_Syntax_Subst.compress msg in
                     uu____7033.FStar_Syntax_Syntax.n in
                   (uu____7028, uu____7032) in
                 (match uu____7025 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7040))) ->
=======
                 let uu____7575 =
                   let uu____7578 =
                     let uu____7579 = FStar_Syntax_Subst.compress r in
                     uu____7579.FStar_Syntax_Syntax.n in
                   let uu____7582 =
                     let uu____7583 = FStar_Syntax_Subst.compress msg in
                     uu____7583.FStar_Syntax_Syntax.n in
                   (uu____7578, uu____7582) in
                 (match uu____7575 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7590))) ->
>>>>>>> origin/guido_tactics
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) None r1 in
                      fallback phi3
<<<<<<< HEAD
                  | uu____7052 -> fallback phi2)
             | uu____7055 when head_redex env head2 ->
                 let uu____7063 = whnf env phi1 in
                 encode_formula uu____7063 env
             | uu____7064 ->
                 let uu____7072 = encode_term phi1 env in
                 (match uu____7072 with
                  | (tt,decls) ->
                      let uu____7079 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7082 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7082.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7082.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7079, decls)))
        | uu____7085 ->
            let uu____7086 = encode_term phi1 env in
            (match uu____7086 with
             | (tt,decls) ->
                 let uu____7093 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7096 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7096.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7096.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7093, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7123 = encode_binders None bs env1 in
        match uu____7123 with
        | (vars,guards,env2,decls,uu____7145) ->
            let uu____7152 =
              let uu____7159 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7186 =
                          let uu____7191 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7208  ->
                                    match uu____7208 with
                                    | (t,uu____7214) ->
                                        encode_term t
                                          (let uu___143_7216 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7216.bindings);
                                             depth = (uu___143_7216.depth);
                                             tcenv = (uu___143_7216.tcenv);
                                             warn = (uu___143_7216.warn);
                                             cache = (uu___143_7216.cache);
                                             nolabels =
                                               (uu___143_7216.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7216.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7216.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7191 FStar_List.unzip in
                        match uu____7186 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7159 FStar_List.unzip in
            (match uu____7152 with
             | (pats,decls') ->
                 let uu____7268 = encode_formula body env2 in
                 (match uu____7268 with
=======
                  | uu____7606 -> fallback phi2)
             | uu____7609 when head_redex env head2 ->
                 let uu____7617 = whnf env phi1 in
                 encode_formula uu____7617 env
             | uu____7618 ->
                 let uu____7626 = encode_term phi1 env in
                 (match uu____7626 with
                  | (tt,decls) ->
                      let uu____7633 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7634 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7634.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7634.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7633, decls)))
        | uu____7637 ->
            let uu____7638 = encode_term phi1 env in
            (match uu____7638 with
             | (tt,decls) ->
                 let uu____7645 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7646 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7646.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7646.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7645, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7673 = encode_binders None bs env1 in
        match uu____7673 with
        | (vars,guards,env2,decls,uu____7695) ->
            let uu____7702 =
              let uu____7709 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7732 =
                          let uu____7737 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7751  ->
                                    match uu____7751 with
                                    | (t,uu____7757) ->
                                        encode_term t
                                          (let uu___142_7758 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7758.bindings);
                                             depth = (uu___142_7758.depth);
                                             tcenv = (uu___142_7758.tcenv);
                                             warn = (uu___142_7758.warn);
                                             cache = (uu___142_7758.cache);
                                             nolabels =
                                               (uu___142_7758.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7758.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7758.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7737 FStar_List.unzip in
                        match uu____7732 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7709 FStar_List.unzip in
            (match uu____7702 with
             | (pats,decls') ->
                 let uu____7810 = encode_formula body env2 in
                 (match uu____7810 with
>>>>>>> origin/guido_tactics
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
<<<<<<< HEAD
                             FStar_SMTEncoding_Term.freevars = uu____7287;
                             FStar_SMTEncoding_Term.rng = uu____7288;_}::[])::[]
=======
                             FStar_SMTEncoding_Term.freevars = uu____7829;
                             FStar_SMTEncoding_Term.rng = uu____7830;_}::[])::[]
>>>>>>> origin/guido_tactics
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
<<<<<<< HEAD
                        | uu____7296 -> guards in
                      let uu____7299 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7299, body1,
=======
                        | uu____7838 -> guards in
                      let uu____7841 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7841, body1,
>>>>>>> origin/guido_tactics
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
<<<<<<< HEAD
                (fun uu____7336  ->
                   match uu____7336 with
                   | (x,uu____7340) ->
=======
                (fun uu____7875  ->
                   match uu____7875 with
                   | (x,uu____7879) ->
>>>>>>> origin/guido_tactics
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
<<<<<<< HEAD
               let uu____7346 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7355 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7355) uu____7346 tl1 in
             let uu____7357 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7373  ->
                       match uu____7373 with
                       | (b,uu____7377) ->
                           let uu____7378 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7378)) in
             (match uu____7357 with
              | None  -> ()
              | Some (x,uu____7382) ->
=======
               let uu____7885 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7891 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7891) uu____7885 tl1 in
             let uu____7893 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7905  ->
                       match uu____7905 with
                       | (b,uu____7909) ->
                           let uu____7910 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7910)) in
             (match uu____7893 with
              | None  -> ()
              | Some (x,uu____7914) ->
>>>>>>> origin/guido_tactics
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
<<<<<<< HEAD
                  let uu____7394 =
                    let uu____7395 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7395 in
                  FStar_Errors.warn pos uu____7394) in
       let uu____7396 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7396 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7402 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7441  ->
                     match uu____7441 with
                     | (l,uu____7451) -> FStar_Ident.lid_equals op l)) in
           (match uu____7402 with
            | None  -> fallback phi1
            | Some (uu____7474,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7503 = encode_q_body env vars pats body in
             match uu____7503 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7529 =
                     let uu____7535 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7535) in
                   FStar_SMTEncoding_Term.mkForall uu____7529
=======
                  let uu____7924 =
                    let uu____7925 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7925 in
                  FStar_Errors.warn pos uu____7924) in
       let uu____7926 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7926 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7932 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7968  ->
                     match uu____7968 with
                     | (l,uu____7978) -> FStar_Ident.lid_equals op l)) in
           (match uu____7932 with
            | None  -> fallback phi1
            | Some (uu____8001,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8030 = encode_q_body env vars pats body in
             match uu____8030 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8056 =
                     let uu____8062 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8062) in
                   FStar_SMTEncoding_Term.mkForall uu____8056
>>>>>>> origin/guido_tactics
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
<<<<<<< HEAD
            (let uu____7547 = encode_q_body env vars pats body in
             match uu____7547 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7572 =
                   let uu____7573 =
                     let uu____7579 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7579) in
                   FStar_SMTEncoding_Term.mkExists uu____7573
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7572, decls))))
=======
            (let uu____8074 = encode_q_body env vars pats body in
             match uu____8074 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8099 =
                   let uu____8100 =
                     let uu____8106 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8106) in
                   FStar_SMTEncoding_Term.mkExists uu____8100
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8099, decls))))
>>>>>>> origin/guido_tactics
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let __proj__Mkprims_t__item__mk:
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
let __proj__Mkprims_t__item__is: prims_t -> FStar_Ident.lident -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
let prims: prims_t =
<<<<<<< HEAD
  let uu____7633 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7633 with
  | (asym,a) ->
      let uu____7638 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7638 with
       | (xsym,x) ->
           let uu____7643 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7643 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7673 =
                      let uu____7679 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7679, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7673 in
=======
  let uu____8185 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8185 with
  | (asym,a) ->
      let uu____8190 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8190 with
       | (xsym,x) ->
           let uu____8195 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8195 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8225 =
                      let uu____8231 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____8231, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8225 in
>>>>>>> origin/guido_tactics
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
<<<<<<< HEAD
                    let uu____7694 =
                      let uu____7698 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7698) in
                    FStar_SMTEncoding_Util.mkApp uu____7694 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7706 =
                    let uu____7708 =
                      let uu____7710 =
                        let uu____7712 =
                          let uu____7713 =
                            let uu____7717 =
                              let uu____7718 =
                                let uu____7724 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7724) in
                              FStar_SMTEncoding_Util.mkForall uu____7718 in
                            (uu____7717, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7713 in
                        let uu____7733 =
                          let uu____7735 =
                            let uu____7736 =
                              let uu____7740 =
                                let uu____7741 =
                                  let uu____7747 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7747) in
                                FStar_SMTEncoding_Util.mkForall uu____7741 in
                              (uu____7740,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7736 in
                          [uu____7735] in
                        uu____7712 :: uu____7733 in
                      xtok_decl :: uu____7710 in
                    xname_decl :: uu____7708 in
                  (xtok1, uu____7706) in
=======
                    let uu____8246 =
                      let uu____8250 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8250) in
                    FStar_SMTEncoding_Util.mkApp uu____8246 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8258 =
                    let uu____8260 =
                      let uu____8262 =
                        let uu____8264 =
                          let uu____8265 =
                            let uu____8269 =
                              let uu____8270 =
                                let uu____8276 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8276) in
                              FStar_SMTEncoding_Util.mkForall uu____8270 in
                            (uu____8269, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8265 in
                        let uu____8285 =
                          let uu____8287 =
                            let uu____8288 =
                              let uu____8292 =
                                let uu____8293 =
                                  let uu____8299 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____8299) in
                                FStar_SMTEncoding_Util.mkForall uu____8293 in
                              (uu____8292,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____8288 in
                          [uu____8287] in
                        uu____8264 :: uu____8285 in
                      xtok_decl :: uu____8262 in
                    xname_decl :: uu____8260 in
                  (xtok1, uu____8258) in
>>>>>>> origin/guido_tactics
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
<<<<<<< HEAD
                  let uu____7796 =
                    let uu____7804 =
                      let uu____7810 =
                        let uu____7811 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7811 in
                      quant axy uu____7810 in
                    (FStar_Syntax_Const.op_Eq, uu____7804) in
                  let uu____7817 =
                    let uu____7826 =
                      let uu____7834 =
                        let uu____7840 =
                          let uu____7841 =
                            let uu____7842 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7842 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7841 in
                        quant axy uu____7840 in
                      (FStar_Syntax_Const.op_notEq, uu____7834) in
                    let uu____7848 =
                      let uu____7857 =
                        let uu____7865 =
                          let uu____7871 =
                            let uu____7872 =
                              let uu____7873 =
                                let uu____7876 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7877 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7876, uu____7877) in
                              FStar_SMTEncoding_Util.mkLT uu____7873 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7872 in
                          quant xy uu____7871 in
                        (FStar_Syntax_Const.op_LT, uu____7865) in
                      let uu____7883 =
                        let uu____7892 =
                          let uu____7900 =
                            let uu____7906 =
                              let uu____7907 =
                                let uu____7908 =
                                  let uu____7911 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7912 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7911, uu____7912) in
                                FStar_SMTEncoding_Util.mkLTE uu____7908 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7907 in
                            quant xy uu____7906 in
                          (FStar_Syntax_Const.op_LTE, uu____7900) in
                        let uu____7918 =
                          let uu____7927 =
                            let uu____7935 =
                              let uu____7941 =
                                let uu____7942 =
                                  let uu____7943 =
                                    let uu____7946 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7947 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7946, uu____7947) in
                                  FStar_SMTEncoding_Util.mkGT uu____7943 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7942 in
                              quant xy uu____7941 in
                            (FStar_Syntax_Const.op_GT, uu____7935) in
                          let uu____7953 =
                            let uu____7962 =
                              let uu____7970 =
                                let uu____7976 =
                                  let uu____7977 =
                                    let uu____7978 =
                                      let uu____7981 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7982 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7981, uu____7982) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7978 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7977 in
                                quant xy uu____7976 in
                              (FStar_Syntax_Const.op_GTE, uu____7970) in
                            let uu____7988 =
                              let uu____7997 =
                                let uu____8005 =
                                  let uu____8011 =
                                    let uu____8012 =
                                      let uu____8013 =
                                        let uu____8016 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8017 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8016, uu____8017) in
                                      FStar_SMTEncoding_Util.mkSub uu____8013 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8012 in
                                  quant xy uu____8011 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8005) in
                              let uu____8023 =
                                let uu____8032 =
                                  let uu____8040 =
                                    let uu____8046 =
                                      let uu____8047 =
                                        let uu____8048 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8048 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8047 in
                                    quant qx uu____8046 in
                                  (FStar_Syntax_Const.op_Minus, uu____8040) in
                                let uu____8054 =
                                  let uu____8063 =
                                    let uu____8071 =
                                      let uu____8077 =
                                        let uu____8078 =
                                          let uu____8079 =
                                            let uu____8082 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8083 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8082, uu____8083) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8079 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8078 in
                                      quant xy uu____8077 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8071) in
                                  let uu____8089 =
                                    let uu____8098 =
                                      let uu____8106 =
                                        let uu____8112 =
                                          let uu____8113 =
                                            let uu____8114 =
                                              let uu____8117 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8118 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8117, uu____8118) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8114 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8113 in
                                        quant xy uu____8112 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8106) in
                                    let uu____8124 =
                                      let uu____8133 =
                                        let uu____8141 =
                                          let uu____8147 =
                                            let uu____8148 =
                                              let uu____8149 =
                                                let uu____8152 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8153 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8152, uu____8153) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8149 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8148 in
                                          quant xy uu____8147 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8141) in
                                      let uu____8159 =
                                        let uu____8168 =
                                          let uu____8176 =
                                            let uu____8182 =
                                              let uu____8183 =
                                                let uu____8184 =
                                                  let uu____8187 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8188 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8187, uu____8188) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8184 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8183 in
                                            quant xy uu____8182 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8176) in
                                        let uu____8194 =
                                          let uu____8203 =
                                            let uu____8211 =
                                              let uu____8217 =
                                                let uu____8218 =
                                                  let uu____8219 =
                                                    let uu____8222 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8223 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8222, uu____8223) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8219 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8218 in
                                              quant xy uu____8217 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8211) in
                                          let uu____8229 =
                                            let uu____8238 =
                                              let uu____8246 =
                                                let uu____8252 =
                                                  let uu____8253 =
                                                    let uu____8254 =
                                                      let uu____8257 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8258 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8257,
                                                        uu____8258) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8254 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8253 in
                                                quant xy uu____8252 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8246) in
                                            let uu____8264 =
                                              let uu____8273 =
                                                let uu____8281 =
                                                  let uu____8287 =
                                                    let uu____8288 =
                                                      let uu____8289 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8289 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8288 in
                                                  quant qx uu____8287 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8281) in
                                              [uu____8273] in
                                            uu____8238 :: uu____8264 in
                                          uu____8203 :: uu____8229 in
                                        uu____8168 :: uu____8194 in
                                      uu____8133 :: uu____8159 in
                                    uu____8098 :: uu____8124 in
                                  uu____8063 :: uu____8089 in
                                uu____8032 :: uu____8054 in
                              uu____7997 :: uu____8023 in
                            uu____7962 :: uu____7988 in
                          uu____7927 :: uu____7953 in
                        uu____7892 :: uu____7918 in
                      uu____7857 :: uu____7883 in
                    uu____7826 :: uu____7848 in
                  uu____7796 :: uu____7817 in
                let mk1 l v1 =
                  let uu____8417 =
                    let uu____8422 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8457  ->
                              match uu____8457 with
                              | (l',uu____8466) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8422
                      (FStar_Option.map
                         (fun uu____8502  ->
                            match uu____8502 with | (uu____8513,b) -> b v1)) in
                  FStar_All.pipe_right uu____8417 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8557  ->
                          match uu____8557 with
                          | (l',uu____8566) -> FStar_Ident.lid_equals l l')) in
=======
                  let uu____8348 =
                    let uu____8356 =
                      let uu____8362 =
                        let uu____8363 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8363 in
                      quant axy uu____8362 in
                    (FStar_Syntax_Const.op_Eq, uu____8356) in
                  let uu____8369 =
                    let uu____8378 =
                      let uu____8386 =
                        let uu____8392 =
                          let uu____8393 =
                            let uu____8394 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8394 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8393 in
                        quant axy uu____8392 in
                      (FStar_Syntax_Const.op_notEq, uu____8386) in
                    let uu____8400 =
                      let uu____8409 =
                        let uu____8417 =
                          let uu____8423 =
                            let uu____8424 =
                              let uu____8425 =
                                let uu____8428 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8429 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8428, uu____8429) in
                              FStar_SMTEncoding_Util.mkLT uu____8425 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8424 in
                          quant xy uu____8423 in
                        (FStar_Syntax_Const.op_LT, uu____8417) in
                      let uu____8435 =
                        let uu____8444 =
                          let uu____8452 =
                            let uu____8458 =
                              let uu____8459 =
                                let uu____8460 =
                                  let uu____8463 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8464 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8463, uu____8464) in
                                FStar_SMTEncoding_Util.mkLTE uu____8460 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8459 in
                            quant xy uu____8458 in
                          (FStar_Syntax_Const.op_LTE, uu____8452) in
                        let uu____8470 =
                          let uu____8479 =
                            let uu____8487 =
                              let uu____8493 =
                                let uu____8494 =
                                  let uu____8495 =
                                    let uu____8498 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8499 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8498, uu____8499) in
                                  FStar_SMTEncoding_Util.mkGT uu____8495 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8494 in
                              quant xy uu____8493 in
                            (FStar_Syntax_Const.op_GT, uu____8487) in
                          let uu____8505 =
                            let uu____8514 =
                              let uu____8522 =
                                let uu____8528 =
                                  let uu____8529 =
                                    let uu____8530 =
                                      let uu____8533 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8534 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8533, uu____8534) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8530 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8529 in
                                quant xy uu____8528 in
                              (FStar_Syntax_Const.op_GTE, uu____8522) in
                            let uu____8540 =
                              let uu____8549 =
                                let uu____8557 =
                                  let uu____8563 =
                                    let uu____8564 =
                                      let uu____8565 =
                                        let uu____8568 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8569 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8568, uu____8569) in
                                      FStar_SMTEncoding_Util.mkSub uu____8565 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8564 in
                                  quant xy uu____8563 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8557) in
                              let uu____8575 =
                                let uu____8584 =
                                  let uu____8592 =
                                    let uu____8598 =
                                      let uu____8599 =
                                        let uu____8600 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8600 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8599 in
                                    quant qx uu____8598 in
                                  (FStar_Syntax_Const.op_Minus, uu____8592) in
                                let uu____8606 =
                                  let uu____8615 =
                                    let uu____8623 =
                                      let uu____8629 =
                                        let uu____8630 =
                                          let uu____8631 =
                                            let uu____8634 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8635 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8634, uu____8635) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8631 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8630 in
                                      quant xy uu____8629 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8623) in
                                  let uu____8641 =
                                    let uu____8650 =
                                      let uu____8658 =
                                        let uu____8664 =
                                          let uu____8665 =
                                            let uu____8666 =
                                              let uu____8669 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8670 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8669, uu____8670) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8666 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8665 in
                                        quant xy uu____8664 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8658) in
                                    let uu____8676 =
                                      let uu____8685 =
                                        let uu____8693 =
                                          let uu____8699 =
                                            let uu____8700 =
                                              let uu____8701 =
                                                let uu____8704 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8705 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8704, uu____8705) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8701 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8700 in
                                          quant xy uu____8699 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8693) in
                                      let uu____8711 =
                                        let uu____8720 =
                                          let uu____8728 =
                                            let uu____8734 =
                                              let uu____8735 =
                                                let uu____8736 =
                                                  let uu____8739 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8740 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8739, uu____8740) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8736 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8735 in
                                            quant xy uu____8734 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8728) in
                                        let uu____8746 =
                                          let uu____8755 =
                                            let uu____8763 =
                                              let uu____8769 =
                                                let uu____8770 =
                                                  let uu____8771 =
                                                    let uu____8774 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8775 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8774, uu____8775) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8771 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8770 in
                                              quant xy uu____8769 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8763) in
                                          let uu____8781 =
                                            let uu____8790 =
                                              let uu____8798 =
                                                let uu____8804 =
                                                  let uu____8805 =
                                                    let uu____8806 =
                                                      let uu____8809 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8810 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8809,
                                                        uu____8810) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8806 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8805 in
                                                quant xy uu____8804 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8798) in
                                            let uu____8816 =
                                              let uu____8825 =
                                                let uu____8833 =
                                                  let uu____8839 =
                                                    let uu____8840 =
                                                      let uu____8841 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8841 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8840 in
                                                  quant qx uu____8839 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8833) in
                                              [uu____8825] in
                                            uu____8790 :: uu____8816 in
                                          uu____8755 :: uu____8781 in
                                        uu____8720 :: uu____8746 in
                                      uu____8685 :: uu____8711 in
                                    uu____8650 :: uu____8676 in
                                  uu____8615 :: uu____8641 in
                                uu____8584 :: uu____8606 in
                              uu____8549 :: uu____8575 in
                            uu____8514 :: uu____8540 in
                          uu____8479 :: uu____8505 in
                        uu____8444 :: uu____8470 in
                      uu____8409 :: uu____8435 in
                    uu____8378 :: uu____8400 in
                  uu____8348 :: uu____8369 in
                let mk1 l v1 =
                  let uu____8969 =
                    let uu____8974 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9006  ->
                              match uu____9006 with
                              | (l',uu____9015) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8974
                      (FStar_Option.map
                         (fun uu____9048  ->
                            match uu____9048 with | (uu____9059,b) -> b v1)) in
                  FStar_All.pipe_right uu____8969 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9100  ->
                          match uu____9100 with
                          | (l',uu____9109) -> FStar_Ident.lid_equals l l')) in
>>>>>>> origin/guido_tactics
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
<<<<<<< HEAD
        let uu____8592 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8592 with
        | (xxsym,xx) ->
            let uu____8597 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8597 with
=======
        let uu____9138 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9138 with
        | (xxsym,xx) ->
            let uu____9143 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9143 with
>>>>>>> origin/guido_tactics
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
<<<<<<< HEAD
                 let uu____8605 =
                   let uu____8609 =
                     let uu____8610 =
                       let uu____8616 =
                         let uu____8617 =
                           let uu____8620 =
                             let uu____8621 =
                               let uu____8624 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8624) in
                             FStar_SMTEncoding_Util.mkEq uu____8621 in
                           (xx_has_type, uu____8620) in
                         FStar_SMTEncoding_Util.mkImp uu____8617 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8616) in
                     FStar_SMTEncoding_Util.mkForall uu____8610 in
                   let uu____8637 =
                     let uu____8638 =
                       let uu____8639 =
                         let uu____8640 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8640 in
                       Prims.strcat module_name uu____8639 in
                     varops.mk_unique uu____8638 in
                   (uu____8609, (Some "pretyping"), uu____8637) in
                 FStar_SMTEncoding_Util.mkAssume uu____8605)
=======
                 let uu____9151 =
                   let uu____9155 =
                     let uu____9156 =
                       let uu____9162 =
                         let uu____9163 =
                           let uu____9166 =
                             let uu____9167 =
                               let uu____9170 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9170) in
                             FStar_SMTEncoding_Util.mkEq uu____9167 in
                           (xx_has_type, uu____9166) in
                         FStar_SMTEncoding_Util.mkImp uu____9163 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9162) in
                     FStar_SMTEncoding_Util.mkForall uu____9156 in
                   let uu____9183 =
                     let uu____9184 =
                       let uu____9185 =
                         let uu____9186 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9186 in
                       Prims.strcat module_name uu____9185 in
                     varops.mk_unique uu____9184 in
                   (uu____9155, (Some "pretyping"), uu____9183) in
                 FStar_SMTEncoding_Util.mkAssume uu____9151)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    let uu____8670 =
      let uu____8671 =
        let uu____8675 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8675, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8671 in
    let uu____8677 =
      let uu____8679 =
        let uu____8680 =
          let uu____8684 =
            let uu____8685 =
              let uu____8691 =
                let uu____8692 =
                  let uu____8695 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8695) in
                FStar_SMTEncoding_Util.mkImp uu____8692 in
              ([[typing_pred]], [xx], uu____8691) in
            mkForall_fuel uu____8685 in
          (uu____8684, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8680 in
      [uu____8679] in
    uu____8670 :: uu____8677 in
=======
    let uu____9220 =
      let uu____9221 =
        let uu____9225 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9225, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9221 in
    let uu____9227 =
      let uu____9229 =
        let uu____9230 =
          let uu____9234 =
            let uu____9235 =
              let uu____9241 =
                let uu____9242 =
                  let uu____9245 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9245) in
                FStar_SMTEncoding_Util.mkImp uu____9242 in
              ([[typing_pred]], [xx], uu____9241) in
            mkForall_fuel uu____9235 in
          (uu____9234, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9230 in
      [uu____9229] in
    uu____9220 :: uu____9227 in
>>>>>>> origin/guido_tactics
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
<<<<<<< HEAD
    let uu____8723 =
      let uu____8724 =
        let uu____8728 =
          let uu____8729 =
            let uu____8735 =
              let uu____8738 =
                let uu____8740 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8740] in
              [uu____8738] in
            let uu____8743 =
              let uu____8744 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8744 tt in
            (uu____8735, [bb], uu____8743) in
          FStar_SMTEncoding_Util.mkForall uu____8729 in
        (uu____8728, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8724 in
    let uu____8755 =
      let uu____8757 =
        let uu____8758 =
          let uu____8762 =
            let uu____8763 =
              let uu____8769 =
                let uu____8770 =
                  let uu____8773 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8773) in
                FStar_SMTEncoding_Util.mkImp uu____8770 in
              ([[typing_pred]], [xx], uu____8769) in
            mkForall_fuel uu____8763 in
          (uu____8762, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8758 in
      [uu____8757] in
    uu____8723 :: uu____8755 in
=======
    let uu____9273 =
      let uu____9274 =
        let uu____9278 =
          let uu____9279 =
            let uu____9285 =
              let uu____9288 =
                let uu____9290 = FStar_SMTEncoding_Term.boxBool b in
                [uu____9290] in
              [uu____9288] in
            let uu____9293 =
              let uu____9294 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____9294 tt in
            (uu____9285, [bb], uu____9293) in
          FStar_SMTEncoding_Util.mkForall uu____9279 in
        (uu____9278, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9274 in
    let uu____9305 =
      let uu____9307 =
        let uu____9308 =
          let uu____9312 =
            let uu____9313 =
              let uu____9319 =
                let uu____9320 =
                  let uu____9323 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____9323) in
                FStar_SMTEncoding_Util.mkImp uu____9320 in
              ([[typing_pred]], [xx], uu____9319) in
            mkForall_fuel uu____9313 in
          (uu____9312, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9308 in
      [uu____9307] in
    uu____9273 :: uu____9305 in
>>>>>>> origin/guido_tactics
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
<<<<<<< HEAD
      let uu____8807 =
        let uu____8808 =
          let uu____8812 =
            let uu____8814 =
              let uu____8816 =
                let uu____8818 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8819 =
                  let uu____8821 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8821] in
                uu____8818 :: uu____8819 in
              tt :: uu____8816 in
            tt :: uu____8814 in
          ("Prims.Precedes", uu____8812) in
        FStar_SMTEncoding_Util.mkApp uu____8808 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8807 in
    let precedes_y_x =
      let uu____8824 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8824 in
    let uu____8826 =
      let uu____8827 =
        let uu____8831 =
          let uu____8832 =
            let uu____8838 =
              let uu____8841 =
                let uu____8843 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8843] in
              [uu____8841] in
            let uu____8846 =
              let uu____8847 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8847 tt in
            (uu____8838, [bb], uu____8846) in
          FStar_SMTEncoding_Util.mkForall uu____8832 in
        (uu____8831, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8827 in
    let uu____8858 =
      let uu____8860 =
        let uu____8861 =
          let uu____8865 =
            let uu____8866 =
              let uu____8872 =
                let uu____8873 =
                  let uu____8876 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8876) in
                FStar_SMTEncoding_Util.mkImp uu____8873 in
              ([[typing_pred]], [xx], uu____8872) in
            mkForall_fuel uu____8866 in
          (uu____8865, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8861 in
      let uu____8889 =
        let uu____8891 =
          let uu____8892 =
            let uu____8896 =
              let uu____8897 =
                let uu____8903 =
                  let uu____8904 =
                    let uu____8907 =
                      let uu____8908 =
                        let uu____8910 =
                          let uu____8912 =
                            let uu____8914 =
                              let uu____8915 =
                                let uu____8918 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8919 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8918, uu____8919) in
                              FStar_SMTEncoding_Util.mkGT uu____8915 in
                            let uu____8920 =
                              let uu____8922 =
                                let uu____8923 =
                                  let uu____8926 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8927 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8926, uu____8927) in
                                FStar_SMTEncoding_Util.mkGTE uu____8923 in
                              let uu____8928 =
                                let uu____8930 =
                                  let uu____8931 =
                                    let uu____8934 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8935 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8934, uu____8935) in
                                  FStar_SMTEncoding_Util.mkLT uu____8931 in
                                [uu____8930] in
                              uu____8922 :: uu____8928 in
                            uu____8914 :: uu____8920 in
                          typing_pred_y :: uu____8912 in
                        typing_pred :: uu____8910 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8908 in
                    (uu____8907, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8904 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8903) in
              mkForall_fuel uu____8897 in
            (uu____8896, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8892 in
        [uu____8891] in
      uu____8860 :: uu____8889 in
    uu____8826 :: uu____8858 in
=======
      let uu____9357 =
        let uu____9358 =
          let uu____9362 =
            let uu____9364 =
              let uu____9366 =
                let uu____9368 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9369 =
                  let uu____9371 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9371] in
                uu____9368 :: uu____9369 in
              tt :: uu____9366 in
            tt :: uu____9364 in
          ("Prims.Precedes", uu____9362) in
        FStar_SMTEncoding_Util.mkApp uu____9358 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9357 in
    let precedes_y_x =
      let uu____9374 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9374 in
    let uu____9376 =
      let uu____9377 =
        let uu____9381 =
          let uu____9382 =
            let uu____9388 =
              let uu____9391 =
                let uu____9393 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9393] in
              [uu____9391] in
            let uu____9396 =
              let uu____9397 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9397 tt in
            (uu____9388, [bb], uu____9396) in
          FStar_SMTEncoding_Util.mkForall uu____9382 in
        (uu____9381, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9377 in
    let uu____9408 =
      let uu____9410 =
        let uu____9411 =
          let uu____9415 =
            let uu____9416 =
              let uu____9422 =
                let uu____9423 =
                  let uu____9426 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9426) in
                FStar_SMTEncoding_Util.mkImp uu____9423 in
              ([[typing_pred]], [xx], uu____9422) in
            mkForall_fuel uu____9416 in
          (uu____9415, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9411 in
      let uu____9439 =
        let uu____9441 =
          let uu____9442 =
            let uu____9446 =
              let uu____9447 =
                let uu____9453 =
                  let uu____9454 =
                    let uu____9457 =
                      let uu____9458 =
                        let uu____9460 =
                          let uu____9462 =
                            let uu____9464 =
                              let uu____9465 =
                                let uu____9468 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9469 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9468, uu____9469) in
                              FStar_SMTEncoding_Util.mkGT uu____9465 in
                            let uu____9470 =
                              let uu____9472 =
                                let uu____9473 =
                                  let uu____9476 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9477 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9476, uu____9477) in
                                FStar_SMTEncoding_Util.mkGTE uu____9473 in
                              let uu____9478 =
                                let uu____9480 =
                                  let uu____9481 =
                                    let uu____9484 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9485 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9484, uu____9485) in
                                  FStar_SMTEncoding_Util.mkLT uu____9481 in
                                [uu____9480] in
                              uu____9472 :: uu____9478 in
                            uu____9464 :: uu____9470 in
                          typing_pred_y :: uu____9462 in
                        typing_pred :: uu____9460 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9458 in
                    (uu____9457, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9454 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9453) in
              mkForall_fuel uu____9447 in
            (uu____9446, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9442 in
        [uu____9441] in
      uu____9410 :: uu____9439 in
    uu____9376 :: uu____9408 in
>>>>>>> origin/guido_tactics
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
<<<<<<< HEAD
    let uu____8965 =
      let uu____8966 =
        let uu____8970 =
          let uu____8971 =
            let uu____8977 =
              let uu____8980 =
                let uu____8982 = FStar_SMTEncoding_Term.boxString b in
                [uu____8982] in
              [uu____8980] in
            let uu____8985 =
              let uu____8986 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8986 tt in
            (uu____8977, [bb], uu____8985) in
          FStar_SMTEncoding_Util.mkForall uu____8971 in
        (uu____8970, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8966 in
    let uu____8997 =
      let uu____8999 =
        let uu____9000 =
          let uu____9004 =
            let uu____9005 =
              let uu____9011 =
                let uu____9012 =
                  let uu____9015 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9015) in
                FStar_SMTEncoding_Util.mkImp uu____9012 in
              ([[typing_pred]], [xx], uu____9011) in
            mkForall_fuel uu____9005 in
          (uu____9004, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9000 in
      [uu____8999] in
    uu____8965 :: uu____8997 in
  let mk_ref1 env reft_name uu____9037 =
=======
    let uu____9515 =
      let uu____9516 =
        let uu____9520 =
          let uu____9521 =
            let uu____9527 =
              let uu____9530 =
                let uu____9532 = FStar_SMTEncoding_Term.boxString b in
                [uu____9532] in
              [uu____9530] in
            let uu____9535 =
              let uu____9536 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9536 tt in
            (uu____9527, [bb], uu____9535) in
          FStar_SMTEncoding_Util.mkForall uu____9521 in
        (uu____9520, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9516 in
    let uu____9547 =
      let uu____9549 =
        let uu____9550 =
          let uu____9554 =
            let uu____9555 =
              let uu____9561 =
                let uu____9562 =
                  let uu____9565 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9565) in
                FStar_SMTEncoding_Util.mkImp uu____9562 in
              ([[typing_pred]], [xx], uu____9561) in
            mkForall_fuel uu____9555 in
          (uu____9554, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9550 in
      [uu____9549] in
    uu____9515 :: uu____9547 in
  let mk_ref1 env reft_name uu____9587 =
>>>>>>> origin/guido_tactics
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
<<<<<<< HEAD
      let uu____9048 =
        let uu____9052 =
          let uu____9054 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9054] in
        (reft_name, uu____9052) in
      FStar_SMTEncoding_Util.mkApp uu____9048 in
    let refb =
      let uu____9057 =
        let uu____9061 =
          let uu____9063 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9063] in
        (reft_name, uu____9061) in
      FStar_SMTEncoding_Util.mkApp uu____9057 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9067 =
      let uu____9068 =
        let uu____9072 =
          let uu____9073 =
            let uu____9079 =
              let uu____9080 =
                let uu____9083 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9083) in
              FStar_SMTEncoding_Util.mkImp uu____9080 in
            ([[typing_pred]], [xx; aa], uu____9079) in
          mkForall_fuel uu____9073 in
        (uu____9072, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9068 in
    [uu____9067] in
=======
      let uu____9598 =
        let uu____9602 =
          let uu____9604 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9604] in
        (reft_name, uu____9602) in
      FStar_SMTEncoding_Util.mkApp uu____9598 in
    let refb =
      let uu____9607 =
        let uu____9611 =
          let uu____9613 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9613] in
        (reft_name, uu____9611) in
      FStar_SMTEncoding_Util.mkApp uu____9607 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9617 =
      let uu____9618 =
        let uu____9622 =
          let uu____9623 =
            let uu____9629 =
              let uu____9630 =
                let uu____9633 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9633) in
              FStar_SMTEncoding_Util.mkImp uu____9630 in
            ([[typing_pred]], [xx; aa], uu____9629) in
          mkForall_fuel uu____9623 in
        (uu____9622, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9618 in
    [uu____9617] in
>>>>>>> origin/guido_tactics
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
<<<<<<< HEAD
    let uu____9123 =
      let uu____9124 =
        let uu____9128 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9128, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9124 in
    [uu____9123] in
  let mk_and_interp env conj uu____9139 =
=======
    let uu____9673 =
      let uu____9674 =
        let uu____9678 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9678, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9674 in
    [uu____9673] in
  let mk_and_interp env conj uu____9689 =
>>>>>>> origin/guido_tactics
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
<<<<<<< HEAD
    let uu____9156 =
      let uu____9157 =
        let uu____9161 =
          let uu____9162 =
            let uu____9168 =
              let uu____9169 =
                let uu____9172 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9172, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9169 in
            ([[l_and_a_b]], [aa; bb], uu____9168) in
          FStar_SMTEncoding_Util.mkForall uu____9162 in
        (uu____9161, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9157 in
    [uu____9156] in
  let mk_or_interp env disj uu____9196 =
=======
    let uu____9706 =
      let uu____9707 =
        let uu____9711 =
          let uu____9712 =
            let uu____9718 =
              let uu____9719 =
                let uu____9722 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9722, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9719 in
            ([[l_and_a_b]], [aa; bb], uu____9718) in
          FStar_SMTEncoding_Util.mkForall uu____9712 in
        (uu____9711, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9707 in
    [uu____9706] in
  let mk_or_interp env disj uu____9746 =
>>>>>>> origin/guido_tactics
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
<<<<<<< HEAD
    let uu____9213 =
      let uu____9214 =
        let uu____9218 =
          let uu____9219 =
            let uu____9225 =
              let uu____9226 =
                let uu____9229 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9229, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9226 in
            ([[l_or_a_b]], [aa; bb], uu____9225) in
          FStar_SMTEncoding_Util.mkForall uu____9219 in
        (uu____9218, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9214 in
    [uu____9213] in
=======
    let uu____9763 =
      let uu____9764 =
        let uu____9768 =
          let uu____9769 =
            let uu____9775 =
              let uu____9776 =
                let uu____9779 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9779, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9776 in
            ([[l_or_a_b]], [aa; bb], uu____9775) in
          FStar_SMTEncoding_Util.mkForall uu____9769 in
        (uu____9768, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9764 in
    [uu____9763] in
>>>>>>> origin/guido_tactics
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
<<<<<<< HEAD
    let uu____9270 =
      let uu____9271 =
        let uu____9275 =
          let uu____9276 =
            let uu____9282 =
              let uu____9283 =
                let uu____9286 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9286, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9283 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9282) in
          FStar_SMTEncoding_Util.mkForall uu____9276 in
        (uu____9275, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9271 in
    [uu____9270] in
=======
    let uu____9820 =
      let uu____9821 =
        let uu____9825 =
          let uu____9826 =
            let uu____9832 =
              let uu____9833 =
                let uu____9836 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9836, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9833 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9832) in
          FStar_SMTEncoding_Util.mkForall uu____9826 in
        (uu____9825, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9821 in
    [uu____9820] in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    let uu____9333 =
      let uu____9334 =
        let uu____9338 =
          let uu____9339 =
            let uu____9345 =
              let uu____9346 =
                let uu____9349 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9349, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9346 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9345) in
          FStar_SMTEncoding_Util.mkForall uu____9339 in
        (uu____9338, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9334 in
    [uu____9333] in
=======
    let uu____9883 =
      let uu____9884 =
        let uu____9888 =
          let uu____9889 =
            let uu____9895 =
              let uu____9896 =
                let uu____9899 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9899, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9896 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9895) in
          FStar_SMTEncoding_Util.mkForall uu____9889 in
        (uu____9888, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9884 in
    [uu____9883] in
>>>>>>> origin/guido_tactics
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
<<<<<<< HEAD
    let uu____9394 =
      let uu____9395 =
        let uu____9399 =
          let uu____9400 =
            let uu____9406 =
              let uu____9407 =
                let uu____9410 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9410, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9407 in
            ([[l_imp_a_b]], [aa; bb], uu____9406) in
          FStar_SMTEncoding_Util.mkForall uu____9400 in
        (uu____9399, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9395 in
    [uu____9394] in
=======
    let uu____9944 =
      let uu____9945 =
        let uu____9949 =
          let uu____9950 =
            let uu____9956 =
              let uu____9957 =
                let uu____9960 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9960, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9957 in
            ([[l_imp_a_b]], [aa; bb], uu____9956) in
          FStar_SMTEncoding_Util.mkForall uu____9950 in
        (uu____9949, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9945 in
    [uu____9944] in
>>>>>>> origin/guido_tactics
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
<<<<<<< HEAD
    let uu____9451 =
      let uu____9452 =
        let uu____9456 =
          let uu____9457 =
            let uu____9463 =
              let uu____9464 =
                let uu____9467 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9467, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9464 in
            ([[l_iff_a_b]], [aa; bb], uu____9463) in
          FStar_SMTEncoding_Util.mkForall uu____9457 in
        (uu____9456, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9452 in
    [uu____9451] in
=======
    let uu____10001 =
      let uu____10002 =
        let uu____10006 =
          let uu____10007 =
            let uu____10013 =
              let uu____10014 =
                let uu____10017 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10017, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10014 in
            ([[l_iff_a_b]], [aa; bb], uu____10013) in
          FStar_SMTEncoding_Util.mkForall uu____10007 in
        (uu____10006, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10002 in
    [uu____10001] in
>>>>>>> origin/guido_tactics
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
<<<<<<< HEAD
      let uu____9501 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9501 in
    let uu____9503 =
      let uu____9504 =
        let uu____9508 =
          let uu____9509 =
            let uu____9515 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9515) in
          FStar_SMTEncoding_Util.mkForall uu____9509 in
        (uu____9508, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9504 in
    [uu____9503] in
=======
      let uu____10051 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10051 in
    let uu____10053 =
      let uu____10054 =
        let uu____10058 =
          let uu____10059 =
            let uu____10065 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10065) in
          FStar_SMTEncoding_Util.mkForall uu____10059 in
        (uu____10058, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10054 in
    [uu____10053] in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      let uu____9555 =
        let uu____9559 =
          let uu____9561 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9561] in
        ("Valid", uu____9559) in
      FStar_SMTEncoding_Util.mkApp uu____9555 in
    let uu____9563 =
      let uu____9564 =
        let uu____9568 =
          let uu____9569 =
            let uu____9575 =
              let uu____9576 =
                let uu____9579 =
                  let uu____9580 =
                    let uu____9586 =
                      let uu____9589 =
                        let uu____9591 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9591] in
                      [uu____9589] in
                    let uu____9594 =
                      let uu____9595 =
                        let uu____9598 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9598, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9595 in
                    (uu____9586, [xx1], uu____9594) in
                  FStar_SMTEncoding_Util.mkForall uu____9580 in
                (uu____9579, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9576 in
            ([[l_forall_a_b]], [aa; bb], uu____9575) in
          FStar_SMTEncoding_Util.mkForall uu____9569 in
        (uu____9568, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9564 in
    [uu____9563] in
=======
      let uu____10105 =
        let uu____10109 =
          let uu____10111 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10111] in
        ("Valid", uu____10109) in
      FStar_SMTEncoding_Util.mkApp uu____10105 in
    let uu____10113 =
      let uu____10114 =
        let uu____10118 =
          let uu____10119 =
            let uu____10125 =
              let uu____10126 =
                let uu____10129 =
                  let uu____10130 =
                    let uu____10136 =
                      let uu____10139 =
                        let uu____10141 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10141] in
                      [uu____10139] in
                    let uu____10144 =
                      let uu____10145 =
                        let uu____10148 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10148, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10145 in
                    (uu____10136, [xx1], uu____10144) in
                  FStar_SMTEncoding_Util.mkForall uu____10130 in
                (uu____10129, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10126 in
            ([[l_forall_a_b]], [aa; bb], uu____10125) in
          FStar_SMTEncoding_Util.mkForall uu____10119 in
        (uu____10118, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10114 in
    [uu____10113] in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      let uu____9649 =
        let uu____9653 =
          let uu____9655 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9655] in
        ("Valid", uu____9653) in
      FStar_SMTEncoding_Util.mkApp uu____9649 in
    let uu____9657 =
      let uu____9658 =
        let uu____9662 =
          let uu____9663 =
            let uu____9669 =
              let uu____9670 =
                let uu____9673 =
                  let uu____9674 =
                    let uu____9680 =
                      let uu____9683 =
                        let uu____9685 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9685] in
                      [uu____9683] in
                    let uu____9688 =
                      let uu____9689 =
                        let uu____9692 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9692, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9689 in
                    (uu____9680, [xx1], uu____9688) in
                  FStar_SMTEncoding_Util.mkExists uu____9674 in
                (uu____9673, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9670 in
            ([[l_exists_a_b]], [aa; bb], uu____9669) in
          FStar_SMTEncoding_Util.mkForall uu____9663 in
        (uu____9662, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9658 in
    [uu____9657] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9728 =
      let uu____9729 =
        let uu____9733 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9734 = varops.mk_unique "typing_range_const" in
        (uu____9733, (Some "Range_const typing"), uu____9734) in
      FStar_SMTEncoding_Util.mkAssume uu____9729 in
    [uu____9728] in
=======
      let uu____10199 =
        let uu____10203 =
          let uu____10205 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10205] in
        ("Valid", uu____10203) in
      FStar_SMTEncoding_Util.mkApp uu____10199 in
    let uu____10207 =
      let uu____10208 =
        let uu____10212 =
          let uu____10213 =
            let uu____10219 =
              let uu____10220 =
                let uu____10223 =
                  let uu____10224 =
                    let uu____10230 =
                      let uu____10233 =
                        let uu____10235 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10235] in
                      [uu____10233] in
                    let uu____10238 =
                      let uu____10239 =
                        let uu____10242 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10242, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10239 in
                    (uu____10230, [xx1], uu____10238) in
                  FStar_SMTEncoding_Util.mkExists uu____10224 in
                (uu____10223, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10220 in
            ([[l_exists_a_b]], [aa; bb], uu____10219) in
          FStar_SMTEncoding_Util.mkForall uu____10213 in
        (uu____10212, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10208 in
    [uu____10207] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____10278 =
      let uu____10279 =
        let uu____10283 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____10284 = varops.mk_unique "typing_range_const" in
        (uu____10283, (Some "Range_const typing"), uu____10284) in
      FStar_SMTEncoding_Util.mkAssume uu____10279 in
    [uu____10278] in
>>>>>>> origin/guido_tactics
  let prims1 =
    [(FStar_Syntax_Const.unit_lid, mk_unit);
    (FStar_Syntax_Const.bool_lid, mk_bool);
    (FStar_Syntax_Const.int_lid, mk_int);
    (FStar_Syntax_Const.string_lid, mk_str);
    (FStar_Syntax_Const.ref_lid, mk_ref1);
    (FStar_Syntax_Const.true_lid, mk_true_interp);
    (FStar_Syntax_Const.false_lid, mk_false_interp);
    (FStar_Syntax_Const.and_lid, mk_and_interp);
    (FStar_Syntax_Const.or_lid, mk_or_interp);
    (FStar_Syntax_Const.eq2_lid, mk_eq2_interp);
    (FStar_Syntax_Const.eq3_lid, mk_eq3_interp);
    (FStar_Syntax_Const.imp_lid, mk_imp_interp);
    (FStar_Syntax_Const.iff_lid, mk_iff_interp);
    (FStar_Syntax_Const.not_lid, mk_not_interp);
    (FStar_Syntax_Const.forall_lid, mk_forall_interp);
    (FStar_Syntax_Const.exists_lid, mk_exists_interp);
    (FStar_Syntax_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
<<<<<<< HEAD
          let uu____9996 =
            FStar_Util.find_opt
              (fun uu____10017  ->
                 match uu____10017 with
                 | (l,uu____10027) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9996 with
          | None  -> []
          | Some (uu____10049,f) -> f env s tt
=======
          let uu____10546 =
            FStar_Util.find_opt
              (fun uu____10564  ->
                 match uu____10564 with
                 | (l,uu____10574) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10546 with
          | None  -> []
          | Some (uu____10596,f) -> f env s tt
>>>>>>> origin/guido_tactics
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
<<<<<<< HEAD
        let uu____10082 = encode_function_type_as_formula t env in
        match uu____10082 with
=======
        let uu____10636 = encode_function_type_as_formula t env in
        match uu____10636 with
>>>>>>> origin/guido_tactics
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
<<<<<<< HEAD
            let uu____10110 =
              (let uu____10113 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10113) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10110
            then
              let uu____10117 = new_term_constant_and_tok_from_lid env lid in
              match uu____10117 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10129 =
                      let uu____10130 = FStar_Syntax_Subst.compress t_norm in
                      uu____10130.FStar_Syntax_Syntax.n in
                    match uu____10129 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10135) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10153  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10156 -> [] in
=======
            let uu____10673 =
              (let uu____10674 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10674) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10673
            then
              let uu____10678 = new_term_constant_and_tok_from_lid env lid in
              match uu____10678 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10690 =
                      let uu____10691 = FStar_Syntax_Subst.compress t_norm in
                      uu____10691.FStar_Syntax_Syntax.n in
                    match uu____10690 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10696) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10713  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10716 -> [] in
>>>>>>> origin/guido_tactics
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
<<<<<<< HEAD
              (let uu____10165 = prims.is lid in
               if uu____10165
               then
                 let vname = varops.new_fvar lid in
                 let uu____10170 = prims.mk lid vname in
                 match uu____10170 with
=======
              (let uu____10725 = prims.is lid in
               if uu____10725
               then
                 let vname = varops.new_fvar lid in
                 let uu____10730 = prims.mk lid vname in
                 match uu____10730 with
>>>>>>> origin/guido_tactics
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
<<<<<<< HEAD
                  let uu____10185 =
                    let uu____10191 = curried_arrow_formals_comp t_norm in
                    match uu____10191 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10202 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10202
                          then
                            let uu____10203 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10206 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10206.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10206.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10206.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10206.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10206.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10206.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10206.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10206.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10206.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10206.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10206.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10206.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10206.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10206.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10206.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10206.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10206.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10206.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10206.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10206.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10206.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10206.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10206.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10203
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10213 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10213)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10185 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10240 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10240 with
=======
                  let uu____10745 =
                    let uu____10751 = curried_arrow_formals_comp t_norm in
                    match uu____10751 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10762 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10762
                          then
                            let uu____10763 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10764 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10764.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10764.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10764.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10764.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10764.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10764.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10764.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10764.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10764.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10764.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10764.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10764.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10764.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10764.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10764.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10764.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10764.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10764.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10764.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10764.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10764.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10764.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10764.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10764.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10764.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10764.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10763
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10771 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10771)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10745 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10798 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10798 with
>>>>>>> origin/guido_tactics
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
<<<<<<< HEAD
                             | uu____10253 ->
=======
                             | uu____10811 ->
>>>>>>> origin/guido_tactics
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
<<<<<<< HEAD
                                  (fun uu___115_10285  ->
                                     match uu___115_10285 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10288 =
                                           FStar_Util.prefix vars in
                                         (match uu____10288 with
                                          | (uu____10299,(xxsym,uu____10301))
=======
                                  (fun uu___115_10835  ->
                                     match uu___115_10835 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10838 =
                                           FStar_Util.prefix vars in
                                         (match uu____10838 with
                                          | (uu____10849,(xxsym,uu____10851))
>>>>>>> origin/guido_tactics
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
<<<<<<< HEAD
                                              let uu____10311 =
                                                let uu____10312 =
                                                  let uu____10316 =
                                                    let uu____10317 =
                                                      let uu____10323 =
                                                        let uu____10324 =
                                                          let uu____10327 =
                                                            let uu____10328 =
=======
                                              let uu____10861 =
                                                let uu____10862 =
                                                  let uu____10866 =
                                                    let uu____10867 =
                                                      let uu____10873 =
                                                        let uu____10874 =
                                                          let uu____10877 =
                                                            let uu____10878 =
>>>>>>> origin/guido_tactics
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
<<<<<<< HEAD
                                                              uu____10328 in
                                                          (vapp, uu____10327) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10324 in
                                                      ([[vapp]], vars,
                                                        uu____10323) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10317 in
                                                  (uu____10316,
=======
                                                              uu____10878 in
                                                          (vapp, uu____10877) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10874 in
                                                      ([[vapp]], vars,
                                                        uu____10873) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10867 in
                                                  (uu____10866,
>>>>>>> origin/guido_tactics
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                  uu____10312 in
                                              [uu____10311])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10339 =
                                           FStar_Util.prefix vars in
                                         (match uu____10339 with
                                          | (uu____10350,(xxsym,uu____10352))
=======
                                                  uu____10862 in
                                              [uu____10861])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10889 =
                                           FStar_Util.prefix vars in
                                         (match uu____10889 with
                                          | (uu____10900,(xxsym,uu____10902))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                              let uu____10366 =
                                                let uu____10367 =
                                                  let uu____10371 =
                                                    let uu____10372 =
                                                      let uu____10378 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10378) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10372 in
                                                  (uu____10371,
=======
                                              let uu____10916 =
                                                let uu____10917 =
                                                  let uu____10921 =
                                                    let uu____10922 =
                                                      let uu____10928 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10928) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10922 in
                                                  (uu____10921,
>>>>>>> origin/guido_tactics
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                  uu____10367 in
                                              [uu____10366])
                                     | uu____10387 -> [])) in
                           let uu____10388 = encode_binders None formals env1 in
                           (match uu____10388 with
                            | (vars,guards,env',decls1,uu____10404) ->
                                let uu____10411 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10416 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10416, decls1)
                                  | Some p ->
                                      let uu____10418 = encode_formula p env' in
                                      (match uu____10418 with
                                       | (g,ds) ->
                                           let uu____10425 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10425,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10411 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10434 =
                                         let uu____10438 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10438) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10434 in
                                     let uu____10443 =
                                       let vname_decl =
                                         let uu____10448 =
                                           let uu____10454 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10460  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10454,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10448 in
                                       let uu____10465 =
                                         let env2 =
                                           let uu___145_10469 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10469.bindings);
                                             depth = (uu___145_10469.depth);
                                             tcenv = (uu___145_10469.tcenv);
                                             warn = (uu___145_10469.warn);
                                             cache = (uu___145_10469.cache);
                                             nolabels =
                                               (uu___145_10469.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10469.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10469.current_module_name)
                                           } in
                                         let uu____10470 =
                                           let uu____10471 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10471 in
                                         if uu____10470
=======
                                                  uu____10917 in
                                              [uu____10916])
                                     | uu____10937 -> [])) in
                           let uu____10938 = encode_binders None formals env1 in
                           (match uu____10938 with
                            | (vars,guards,env',decls1,uu____10954) ->
                                let uu____10961 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10966 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10966, decls1)
                                  | Some p ->
                                      let uu____10968 = encode_formula p env' in
                                      (match uu____10968 with
                                       | (g,ds) ->
                                           let uu____10975 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10975,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10961 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10984 =
                                         let uu____10988 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10988) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10984 in
                                     let uu____10993 =
                                       let vname_decl =
                                         let uu____10998 =
                                           let uu____11004 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11009  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11004,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10998 in
                                       let uu____11014 =
                                         let env2 =
                                           let uu___144_11018 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11018.bindings);
                                             depth = (uu___144_11018.depth);
                                             tcenv = (uu___144_11018.tcenv);
                                             warn = (uu___144_11018.warn);
                                             cache = (uu___144_11018.cache);
                                             nolabels =
                                               (uu___144_11018.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11018.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11018.current_module_name)
                                           } in
                                         let uu____11019 =
                                           let uu____11020 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11020 in
                                         if uu____11019
>>>>>>> origin/guido_tactics
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
<<<<<<< HEAD
                                       match uu____10465 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10481::uu____10482 ->
=======
                                       match uu____11014 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11030::uu____11031 ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                                   let uu____10505 =
                                                     let uu____10511 =
=======
                                                   let uu____11054 =
                                                     let uu____11060 =
>>>>>>> origin/guido_tactics
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
<<<<<<< HEAD
                                                       [ff], uu____10511) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10505 in
=======
                                                       [ff], uu____11060) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11054 in
>>>>>>> origin/guido_tactics
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
<<<<<<< HEAD
                                             | uu____10525 ->
=======
                                             | uu____11074 ->
>>>>>>> origin/guido_tactics
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
<<<<<<< HEAD
                                           let uu____10527 =
                                             match formals with
                                             | [] ->
                                                 let uu____10536 =
                                                   let uu____10537 =
                                                     let uu____10539 =
=======
                                           let uu____11076 =
                                             match formals with
                                             | [] ->
                                                 let uu____11085 =
                                                   let uu____11086 =
                                                     let uu____11088 =
>>>>>>> origin/guido_tactics
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
<<<<<<< HEAD
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10539 in
                                                   push_free_var env1 lid
                                                     vname uu____10537 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10536)
                                             | uu____10542 ->
=======
                                                       (fun _0_41  ->
                                                          Some _0_41)
                                                       uu____11088 in
                                                   push_free_var env1 lid
                                                     vname uu____11086 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11085)
                                             | uu____11091 ->
>>>>>>> origin/guido_tactics
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
<<<<<<< HEAD
                                                   let uu____10547 =
=======
                                                   let uu____11096 =
>>>>>>> origin/guido_tactics
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
<<<<<<< HEAD
                                                     uu____10547 in
                                                 let name_tok_corr =
                                                   let uu____10549 =
                                                     let uu____10553 =
                                                       let uu____10554 =
                                                         let uu____10560 =
=======
                                                     uu____11096 in
                                                 let name_tok_corr =
                                                   let uu____11098 =
                                                     let uu____11102 =
                                                       let uu____11103 =
                                                         let uu____11109 =
>>>>>>> origin/guido_tactics
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
<<<<<<< HEAD
                                                           uu____10560) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10554 in
                                                     (uu____10553,
=======
                                                           uu____11109) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11103 in
                                                     (uu____11102,
>>>>>>> origin/guido_tactics
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                     uu____10549 in
=======
                                                     uu____11098 in
>>>>>>> origin/guido_tactics
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
<<<<<<< HEAD
                                           (match uu____10527 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10443 with
                                      | (decls2,env2) ->
                                          let uu____10584 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10589 =
                                              encode_term res_t1 env' in
                                            match uu____10589 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10597 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10597,
                                                  decls) in
                                          (match uu____10584 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10605 =
                                                   let uu____10609 =
                                                     let uu____10610 =
                                                       let uu____10616 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10616) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10610 in
                                                   (uu____10609,
=======
                                           (match uu____11076 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10993 with
                                      | (decls2,env2) ->
                                          let uu____11133 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11138 =
                                              encode_term res_t1 env' in
                                            match uu____11138 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11146 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11146,
                                                  decls) in
                                          (match uu____11133 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11154 =
                                                   let uu____11158 =
                                                     let uu____11159 =
                                                       let uu____11165 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11165) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11159 in
                                                   (uu____11158,
>>>>>>> origin/guido_tactics
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                   uu____10605 in
                                               let freshness =
                                                 let uu____10625 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10625
                                                 then
                                                   let uu____10628 =
                                                     let uu____10629 =
                                                       let uu____10635 =
=======
                                                   uu____11154 in
                                               let freshness =
                                                 let uu____11174 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11174
                                                 then
                                                   let uu____11177 =
                                                     let uu____11178 =
                                                       let uu____11184 =
>>>>>>> origin/guido_tactics
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
<<<<<<< HEAD
                                                       let uu____10641 =
                                                         varops.next_id () in
                                                       (vname, uu____10635,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10641) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10629 in
                                                   let uu____10643 =
                                                     let uu____10645 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10645] in
                                                   uu____10628 :: uu____10643
                                                 else [] in
                                               let g =
                                                 let uu____10649 =
                                                   let uu____10651 =
                                                     let uu____10653 =
                                                       let uu____10655 =
                                                         let uu____10657 =
=======
                                                       let uu____11190 =
                                                         varops.next_id () in
                                                       (vname, uu____11184,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11190) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11178 in
                                                   let uu____11192 =
                                                     let uu____11194 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11194] in
                                                   uu____11177 :: uu____11192
                                                 else [] in
                                               let g =
                                                 let uu____11198 =
                                                   let uu____11200 =
                                                     let uu____11202 =
                                                       let uu____11204 =
                                                         let uu____11206 =
>>>>>>> origin/guido_tactics
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
<<<<<<< HEAD
                                                           uu____10657 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10655 in
                                                     FStar_List.append decls3
                                                       uu____10653 in
                                                   FStar_List.append decls2
                                                     uu____10651 in
                                                 FStar_List.append decls11
                                                   uu____10649 in
=======
                                                           uu____11206 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11204 in
                                                     FStar_List.append decls3
                                                       uu____11202 in
                                                   FStar_List.append decls2
                                                     uu____11200 in
                                                 FStar_List.append decls11
                                                   uu____11198 in
>>>>>>> origin/guido_tactics
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
<<<<<<< HEAD
          let uu____10679 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10679 with
          | None  ->
              let uu____10698 = encode_free_var env x t t_norm [] in
              (match uu____10698 with
               | (decls,env1) ->
                   let uu____10713 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10713 with
                    | (n1,x',uu____10728) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10740) -> ((n1, x1), [], env)
=======
          let uu____11232 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11232 with
          | None  ->
              let uu____11255 = encode_free_var env x t t_norm [] in
              (match uu____11255 with
               | (decls,env1) ->
                   let uu____11270 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____11270 with
                    | (n1,x',uu____11289) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____11301) -> ((n1, x1), [], env)
>>>>>>> origin/guido_tactics
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
<<<<<<< HEAD
          let uu____10773 = encode_free_var env lid t tt quals in
          match uu____10773 with
          | (decls,env1) ->
              let uu____10784 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10784
              then
                let uu____10788 =
                  let uu____10790 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10790 in
                (uu____10788, env1)
=======
          let uu____11338 = encode_free_var env lid t tt quals in
          match uu____11338 with
          | (decls,env1) ->
              let uu____11349 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____11349
              then
                let uu____11353 =
                  let uu____11355 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11355 in
                (uu____11353, env1)
>>>>>>> origin/guido_tactics
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
<<<<<<< HEAD
             (fun uu____10825  ->
                fun lb  ->
                  match uu____10825 with
                  | (decls,env1) ->
                      let uu____10837 =
                        let uu____10841 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10841
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10837 with
=======
             (fun uu____11386  ->
                fun lb  ->
                  match uu____11386 with
                  | (decls,env1) ->
                      let uu____11398 =
                        let uu____11402 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11402
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11398 with
>>>>>>> origin/guido_tactics
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
<<<<<<< HEAD
    let uu____10855 = FStar_Syntax_Util.head_and_args t in
    match uu____10855 with
    | (hd1,args) ->
        let uu____10881 =
          let uu____10882 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10882.FStar_Syntax_Syntax.n in
        (match uu____10881 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10886,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10899 -> false)
=======
    let uu____11417 = FStar_Syntax_Util.head_and_args t in
    match uu____11417 with
    | (hd1,args) ->
        let uu____11443 =
          let uu____11444 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11444.FStar_Syntax_Syntax.n in
        (match uu____11443 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11448,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11461 -> false)
>>>>>>> origin/guido_tactics
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
<<<<<<< HEAD
    fun uu____10914  ->
      fun quals  ->
        match uu____10914 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10963 = FStar_Util.first_N nbinders formals in
              match uu____10963 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11010  ->
                         fun uu____11011  ->
                           match (uu____11010, uu____11011) with
                           | ((formal,uu____11021),(binder,uu____11023)) ->
                               let uu____11028 =
                                 let uu____11033 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11033) in
                               FStar_Syntax_Syntax.NT uu____11028) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11038 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11056  ->
                              match uu____11056 with
                              | (x,i) ->
                                  let uu____11063 =
                                    let uu___146_11064 = x in
                                    let uu____11065 =
=======
    fun uu____11479  ->
      fun quals  ->
        match uu____11479 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11529 = FStar_Util.first_N nbinders formals in
              match uu____11529 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11571  ->
                         fun uu____11572  ->
                           match (uu____11571, uu____11572) with
                           | ((formal,uu____11582),(binder,uu____11584)) ->
                               let uu____11589 =
                                 let uu____11594 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11594) in
                               FStar_Syntax_Syntax.NT uu____11589) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11599 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11613  ->
                              match uu____11613 with
                              | (x,i) ->
                                  let uu____11620 =
                                    let uu___145_11621 = x in
                                    let uu____11622 =
>>>>>>> origin/guido_tactics
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                        (uu___146_11064.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_11064.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11065
                                    } in
                                  (uu____11063, i))) in
                    FStar_All.pipe_right uu____11038
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11077 =
                      let uu____11079 =
                        let uu____11080 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11080.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11079 in
                    let uu____11084 =
                      let uu____11085 = FStar_Syntax_Subst.compress body in
                      let uu____11086 =
                        let uu____11087 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11087 in
                      FStar_Syntax_Syntax.extend_app_n uu____11085
                        uu____11086 in
                    uu____11084 uu____11077 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11129 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11129
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11132 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11132.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11132.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11132.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11132.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11132.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11132.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11132.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11132.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11132.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11132.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11132.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11132.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11132.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11132.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11132.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11132.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11132.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11132.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11132.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11132.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11132.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11132.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11132.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11153 = FStar_Syntax_Util.abs_formals e in
                match uu____11153 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11202::uu____11203 ->
                         let uu____11211 =
                           let uu____11212 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11212.FStar_Syntax_Syntax.n in
                         (match uu____11211 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11239 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11239 with
=======
                                        (uu___145_11621.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11621.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11622
                                    } in
                                  (uu____11620, i))) in
                    FStar_All.pipe_right uu____11599
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11634 =
                      let uu____11636 =
                        let uu____11637 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11637.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_42  -> Some _0_42)
                        uu____11636 in
                    let uu____11641 =
                      let uu____11642 = FStar_Syntax_Subst.compress body in
                      let uu____11643 =
                        let uu____11644 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11644 in
                      FStar_Syntax_Syntax.extend_app_n uu____11642
                        uu____11643 in
                    uu____11641 uu____11634 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11686 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11686
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11687 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11687.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11687.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11687.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11687.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11687.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11687.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11687.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11687.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11687.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11687.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11687.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11687.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11687.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11687.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11687.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11687.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11687.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11687.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11687.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11687.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11687.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11687.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11687.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11687.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11687.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11687.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11708 = FStar_Syntax_Util.abs_formals e in
                match uu____11708 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11742::uu____11743 ->
                         let uu____11751 =
                           let uu____11752 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11752.FStar_Syntax_Syntax.n in
                         (match uu____11751 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11779 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11779 with
>>>>>>> origin/guido_tactics
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
<<<<<<< HEAD
                                   let uu____11265 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11265
                                   then
                                     let uu____11283 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11283 with
=======
                                   let uu____11807 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11807
                                   then
                                     let uu____11830 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11830 with
>>>>>>> origin/guido_tactics
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
<<<<<<< HEAD
                                                (fun uu____11336  ->
                                                   fun uu____11337  ->
                                                     match (uu____11336,
                                                             uu____11337)
                                                     with
                                                     | ((x,uu____11347),
                                                        (b,uu____11349)) ->
                                                         let uu____11354 =
                                                           let uu____11359 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11359) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11354)
=======
                                                (fun uu____11878  ->
                                                   fun uu____11879  ->
                                                     match (uu____11878,
                                                             uu____11879)
                                                     with
                                                     | ((x,uu____11889),
                                                        (b,uu____11891)) ->
                                                         let uu____11896 =
                                                           let uu____11901 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11901) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11896)
>>>>>>> origin/guido_tactics
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
<<<<<<< HEAD
                                          let uu____11361 =
                                            let uu____11372 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11372) in
                                          (uu____11361, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11407 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11407 with
=======
                                          let uu____11903 =
                                            let uu____11914 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11914) in
                                          (uu____11903, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11954 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11954 with
>>>>>>> origin/guido_tactics
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
<<<<<<< HEAD
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11459) ->
                              let uu____11464 =
                                let uu____11475 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11475 in
                              (uu____11464, true)
                          | uu____11508 when Prims.op_Negation norm1 ->
=======
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12006) ->
                              let uu____12011 =
                                let uu____12022 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____12022 in
                              (uu____12011, true)
                          | uu____12055 when Prims.op_Negation norm1 ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                          | uu____11510 ->
                              let uu____11511 =
                                let uu____11512 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11513 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11512
                                  uu____11513 in
                              failwith uu____11511)
                     | uu____11526 ->
                         let uu____11527 =
                           let uu____11528 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11528.FStar_Syntax_Syntax.n in
                         (match uu____11527 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11555 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11555 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11573 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11573 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11621 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11651 =
=======
                          | uu____12057 ->
                              let uu____12058 =
                                let uu____12059 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12060 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12059
                                  uu____12060 in
                              failwith uu____12058)
                     | uu____12073 ->
                         let uu____12074 =
                           let uu____12075 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12075.FStar_Syntax_Syntax.n in
                         (match uu____12074 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12102 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12102 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12120 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12120 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12168 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12196 =
>>>>>>> origin/guido_tactics
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
<<<<<<< HEAD
               if uu____11651
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11659 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11713  ->
                            fun lb  ->
                              match uu____11713 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11764 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11764
=======
               if uu____12196
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12203 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____12244  ->
                            fun lb  ->
                              match uu____12244 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____12295 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____12295
>>>>>>> origin/guido_tactics
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
<<<<<<< HEAD
                                    let uu____11767 =
                                      let uu____11775 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11775
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11767 with
                                    | (tok,decl,env2) ->
                                        let uu____11800 =
                                          let uu____11807 =
                                            let uu____11813 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11813, tok) in
                                          uu____11807 :: toks in
                                        (uu____11800, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11659 with
=======
                                    let uu____12298 =
                                      let uu____12306 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____12306
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____12298 with
                                    | (tok,decl,env2) ->
                                        let uu____12331 =
                                          let uu____12338 =
                                            let uu____12344 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12344, tok) in
                                          uu____12338 :: toks in
                                        (uu____12331, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12203 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                        | uu____11915 ->
=======
                        | uu____12446 ->
>>>>>>> origin/guido_tactics
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
<<<<<<< HEAD
                                   let uu____11920 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11920 vars)
                            else
                              (let uu____11922 =
                                 let uu____11926 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11926) in
                               FStar_SMTEncoding_Util.mkApp uu____11922) in
                      let uu____11931 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11934  ->
                                 match uu___116_11934 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11935 -> false)))
=======
                                   let uu____12451 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12451 vars)
                            else
                              (let uu____12453 =
                                 let uu____12457 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12457) in
                               FStar_SMTEncoding_Util.mkApp uu____12453) in
                      let uu____12462 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_12464  ->
                                 match uu___116_12464 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12465 -> false)))
>>>>>>> origin/guido_tactics
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
<<<<<<< HEAD
                                   let uu____11940 =
=======
                                   let uu____12468 =
>>>>>>> origin/guido_tactics
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
<<<<<<< HEAD
                                     uu____11940))) in
                      if uu____11931
=======
                                     uu____12468))) in
                      if uu____12462
>>>>>>> origin/guido_tactics
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
<<<<<<< HEAD
                           | ({ FStar_Syntax_Syntax.lbname = uu____11960;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11962;
                                FStar_Syntax_Syntax.lbeff = uu____11963;
=======
                           | ({ FStar_Syntax_Syntax.lbname = uu____12488;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12490;
                                FStar_Syntax_Syntax.lbeff = uu____12491;
>>>>>>> origin/guido_tactics
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
<<<<<<< HEAD
                               let uu____12000 =
                                 let uu____12004 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12004 with
                                 | (tcenv',uu____12015,e_t) ->
                                     let uu____12019 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12026 -> failwith "Impossible" in
                                     (match uu____12019 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_12036 = env1 in
                                            {
                                              bindings =
                                                (uu___150_12036.bindings);
                                              depth = (uu___150_12036.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_12036.warn);
                                              cache = (uu___150_12036.cache);
                                              nolabels =
                                                (uu___150_12036.nolabels);
                                              use_zfuel_name =
                                                (uu___150_12036.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_12036.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_12036.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12000 with
                                | (env',e1,t_norm1) ->
                                    let uu____12043 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12043 with
                                     | ((binders,body,uu____12055,uu____12056),curry)
                                         ->
                                         ((let uu____12063 =
=======
                               let uu____12532 =
                                 let uu____12536 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12536 with
                                 | (tcenv',uu____12547,e_t) ->
                                     let uu____12551 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12558 -> failwith "Impossible" in
                                     (match uu____12551 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12567 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12567.bindings);
                                              depth = (uu___149_12567.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12567.warn);
                                              cache = (uu___149_12567.cache);
                                              nolabels =
                                                (uu___149_12567.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12567.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12567.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12567.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12532 with
                                | (env',e1,t_norm1) ->
                                    let uu____12574 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12574 with
                                     | ((binders,body,uu____12586,uu____12587),curry)
                                         ->
                                         ((let uu____12594 =
>>>>>>> origin/guido_tactics
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
<<<<<<< HEAD
                                           if uu____12063
                                           then
                                             let uu____12064 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12065 =
=======
                                           if uu____12594
                                           then
                                             let uu____12595 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12596 =
>>>>>>> origin/guido_tactics
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
<<<<<<< HEAD
                                               uu____12064 uu____12065
                                           else ());
                                          (let uu____12067 =
                                             encode_binders None binders env' in
                                           match uu____12067 with
                                           | (vars,guards,env'1,binder_decls,uu____12083)
                                               ->
                                               let body1 =
                                                 let uu____12091 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12091
=======
                                               uu____12595 uu____12596
                                           else ());
                                          (let uu____12598 =
                                             encode_binders None binders env' in
                                           match uu____12598 with
                                           | (vars,guards,env'1,binder_decls,uu____12614)
                                               ->
                                               let body1 =
                                                 let uu____12622 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12622
>>>>>>> origin/guido_tactics
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
<<<<<<< HEAD
                                               let uu____12094 =
                                                 let uu____12099 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12099
                                                 then
                                                   let uu____12105 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12106 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12105, uu____12106)
                                                 else
                                                   (let uu____12112 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12112)) in
                                               (match uu____12094 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12126 =
                                                        let uu____12130 =
                                                          let uu____12131 =
                                                            let uu____12137 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12137) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12131 in
                                                        let uu____12143 =
                                                          let uu____12145 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12145 in
                                                        (uu____12130,
                                                          uu____12143,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12126 in
                                                    let uu____12147 =
                                                      let uu____12149 =
                                                        let uu____12151 =
                                                          let uu____12153 =
                                                            let uu____12155 =
=======
                                               let uu____12625 =
                                                 let uu____12630 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12630
                                                 then
                                                   let uu____12636 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12637 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12636, uu____12637)
                                                 else
                                                   (let uu____12643 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12643)) in
                                               (match uu____12625 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12657 =
                                                        let uu____12661 =
                                                          let uu____12662 =
                                                            let uu____12668 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12668) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12662 in
                                                        let uu____12674 =
                                                          let uu____12676 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12676 in
                                                        (uu____12661,
                                                          uu____12674,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12657 in
                                                    let uu____12678 =
                                                      let uu____12680 =
                                                        let uu____12682 =
                                                          let uu____12684 =
                                                            let uu____12686 =
>>>>>>> origin/guido_tactics
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
<<<<<<< HEAD
                                                              uu____12155 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12153 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12151 in
                                                      FStar_List.append
                                                        decls1 uu____12149 in
                                                    (uu____12147, env1))))))
                           | uu____12158 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12177 = varops.fresh "fuel" in
                             (uu____12177, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12180 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12230  ->
                                     fun uu____12231  ->
                                       match (uu____12230, uu____12231) with
=======
                                                              uu____12686 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12684 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12682 in
                                                      FStar_List.append
                                                        decls1 uu____12680 in
                                                    (uu____12678, env1))))))
                           | uu____12689 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12708 = varops.fresh "fuel" in
                             (uu____12708, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12711 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12750  ->
                                     fun uu____12751  ->
                                       match (uu____12750, uu____12751) with
>>>>>>> origin/guido_tactics
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
<<<<<<< HEAD
                                             let uu____12309 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12309 in
                                           let gtok =
                                             let uu____12311 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12311 in
                                           let env3 =
                                             let uu____12313 =
                                               let uu____12315 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12315 in
                                             push_free_var env2 flid gtok
                                               uu____12313 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12180 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12401
                                 t_norm uu____12403 =
                                 match (uu____12401, uu____12403) with
=======
                                             let uu____12833 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12833 in
                                           let gtok =
                                             let uu____12835 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12835 in
                                           let env3 =
                                             let uu____12837 =
                                               let uu____12839 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  -> Some _0_43)
                                                 uu____12839 in
                                             push_free_var env2 flid gtok
                                               uu____12837 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12711 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12925
                                 t_norm uu____12927 =
                                 match (uu____12925, uu____12927) with
>>>>>>> origin/guido_tactics
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
<<<<<<< HEAD
                                                             = uu____12430;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12431;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12448 =
                                       let uu____12452 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12452 with
                                       | (tcenv',uu____12467,e_t) ->
                                           let uu____12471 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12478 ->
                                                 failwith "Impossible" in
                                           (match uu____12471 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12488 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12488.bindings);
                                                    depth =
                                                      (uu___151_12488.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12488.warn);
                                                    cache =
                                                      (uu___151_12488.cache);
                                                    nolabels =
                                                      (uu___151_12488.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12488.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12488.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12488.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12448 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12498 =
=======
                                                             = uu____12954;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12955;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12972 =
                                       let uu____12976 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12976 with
                                       | (tcenv',uu____12991,e_t) ->
                                           let uu____12995 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13002 ->
                                                 failwith "Impossible" in
                                           (match uu____12995 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13011 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13011.bindings);
                                                    depth =
                                                      (uu___150_13011.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13011.warn);
                                                    cache =
                                                      (uu___150_13011.cache);
                                                    nolabels =
                                                      (uu___150_13011.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13011.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13011.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13011.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12972 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13021 =
>>>>>>> origin/guido_tactics
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
<<<<<<< HEAD
                                            if uu____12498
                                            then
                                              let uu____12499 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12500 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12501 =
=======
                                            if uu____13021
                                            then
                                              let uu____13022 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13023 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13024 =
>>>>>>> origin/guido_tactics
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
<<<<<<< HEAD
                                                uu____12499 uu____12500
                                                uu____12501
                                            else ());
                                           (let uu____12503 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12503 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12525 =
=======
                                                uu____13022 uu____13023
                                                uu____13024
                                            else ());
                                           (let uu____13026 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13026 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13048 =
>>>>>>> origin/guido_tactics
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
<<<<<<< HEAD
                                                  if uu____12525
                                                  then
                                                    let uu____12526 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12527 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12528 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12529 =
=======
                                                  if uu____13048
                                                  then
                                                    let uu____13049 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13050 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13051 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13052 =
>>>>>>> origin/guido_tactics
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
<<<<<<< HEAD
                                                      uu____12526 uu____12527
                                                      uu____12528 uu____12529
=======
                                                      uu____13049 uu____13050
                                                      uu____13051 uu____13052
>>>>>>> origin/guido_tactics
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
<<<<<<< HEAD
                                                 (let uu____12533 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12533 with
                                                  | (vars,guards,env'1,binder_decls,uu____12551)
                                                      ->
                                                      let decl_g =
                                                        let uu____12559 =
                                                          let uu____12565 =
                                                            let uu____12567 =
=======
                                                 (let uu____13056 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____13056 with
                                                  | (vars,guards,env'1,binder_decls,uu____13074)
                                                      ->
                                                      let decl_g =
                                                        let uu____13082 =
                                                          let uu____13088 =
                                                            let uu____13090 =
>>>>>>> origin/guido_tactics
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
<<<<<<< HEAD
                                                              :: uu____12567 in
                                                          (g, uu____12565,
=======
                                                              :: uu____13090 in
                                                          (g, uu____13088,
>>>>>>> origin/guido_tactics
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
<<<<<<< HEAD
                                                          uu____12559 in
=======
                                                          uu____13082 in
>>>>>>> origin/guido_tactics
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
<<<<<<< HEAD
                                                        let uu____12582 =
                                                          let uu____12586 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12586) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12582 in
                                                      let gsapp =
                                                        let uu____12592 =
                                                          let uu____12596 =
                                                            let uu____12598 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12598 ::
                                                              vars_tm in
                                                          (g, uu____12596) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12592 in
                                                      let gmax =
                                                        let uu____12602 =
                                                          let uu____12606 =
                                                            let uu____12608 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12608 ::
                                                              vars_tm in
                                                          (g, uu____12606) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12602 in
                                                      let body1 =
                                                        let uu____12612 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12612
=======
                                                        let uu____13105 =
                                                          let uu____13109 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13109) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13105 in
                                                      let gsapp =
                                                        let uu____13115 =
                                                          let uu____13119 =
                                                            let uu____13121 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13121 ::
                                                              vars_tm in
                                                          (g, uu____13119) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13115 in
                                                      let gmax =
                                                        let uu____13125 =
                                                          let uu____13129 =
                                                            let uu____13131 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13131 ::
                                                              vars_tm in
                                                          (g, uu____13129) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13125 in
                                                      let body1 =
                                                        let uu____13135 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13135
>>>>>>> origin/guido_tactics
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
<<<<<<< HEAD
                                                      let uu____12614 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12614 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12625
                                                               =
                                                               let uu____12629
                                                                 =
                                                                 let uu____12630
                                                                   =
                                                                   let uu____12638
=======
                                                      let uu____13137 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13137 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13148
                                                               =
                                                               let uu____13152
                                                                 =
                                                                 let uu____13153
                                                                   =
                                                                   let uu____13161
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
<<<<<<< HEAD
                                                                    uu____12638) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12630 in
                                                               let uu____12649
                                                                 =
                                                                 let uu____12651
=======
                                                                    uu____13161) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13153 in
                                                               let uu____13172
                                                                 =
                                                                 let uu____13174
>>>>>>> origin/guido_tactics
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
<<<<<<< HEAD
                                                                   uu____12651 in
                                                               (uu____12629,
                                                                 uu____12649,
=======
                                                                   uu____13174 in
                                                               (uu____13152,
                                                                 uu____13172,
>>>>>>> origin/guido_tactics
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                               uu____12625 in
                                                           let eqn_f =
                                                             let uu____12654
                                                               =
                                                               let uu____12658
                                                                 =
                                                                 let uu____12659
                                                                   =
                                                                   let uu____12665
=======
                                                               uu____13148 in
                                                           let eqn_f =
                                                             let uu____13177
                                                               =
                                                               let uu____13181
                                                                 =
                                                                 let uu____13182
                                                                   =
                                                                   let uu____13188
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
<<<<<<< HEAD
                                                                    uu____12665) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12659 in
                                                               (uu____12658,
=======
                                                                    uu____13188) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13182 in
                                                               (uu____13181,
>>>>>>> origin/guido_tactics
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                               uu____12654 in
                                                           let eqn_g' =
                                                             let uu____12673
                                                               =
                                                               let uu____12677
                                                                 =
                                                                 let uu____12678
                                                                   =
                                                                   let uu____12684
                                                                    =
                                                                    let uu____12685
                                                                    =
                                                                    let uu____12688
                                                                    =
                                                                    let uu____12689
                                                                    =
                                                                    let uu____12693
                                                                    =
                                                                    let uu____12695
=======
                                                               uu____13177 in
                                                           let eqn_g' =
                                                             let uu____13196
                                                               =
                                                               let uu____13200
                                                                 =
                                                                 let uu____13201
                                                                   =
                                                                   let uu____13207
                                                                    =
                                                                    let uu____13208
                                                                    =
                                                                    let uu____13211
                                                                    =
                                                                    let uu____13212
                                                                    =
                                                                    let uu____13216
                                                                    =
                                                                    let uu____13218
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
<<<<<<< HEAD
                                                                    uu____12695
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12693) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12689 in
                                                                    (gsapp,
                                                                    uu____12688) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12685 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12684) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12678 in
                                                               (uu____12677,
=======
                                                                    uu____13218
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13216) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13212 in
                                                                    (gsapp,
                                                                    uu____13211) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13208 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13207) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13201 in
                                                               (uu____13200,
>>>>>>> origin/guido_tactics
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                               uu____12673 in
                                                           let uu____12707 =
                                                             let uu____12712
=======
                                                               uu____13196 in
                                                           let uu____13230 =
                                                             let uu____13235
>>>>>>> origin/guido_tactics
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
<<<<<<< HEAD
                                                             match uu____12712
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12729)
=======
                                                             match uu____13235
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____13252)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                                                    let uu____12744
=======
                                                                    let uu____13267
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
<<<<<<< HEAD
                                                                    uu____12744
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12747
                                                                    =
                                                                    let uu____12751
                                                                    =
                                                                    let uu____12752
                                                                    =
                                                                    let uu____12758
=======
                                                                    uu____13267
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____13270
                                                                    =
                                                                    let uu____13274
                                                                    =
                                                                    let uu____13275
                                                                    =
                                                                    let uu____13281
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
<<<<<<< HEAD
                                                                    uu____12758) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12752 in
                                                                    (uu____12751,
=======
                                                                    uu____13281) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13275 in
                                                                    (uu____13274,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____12747 in
                                                                 let uu____12769
                                                                   =
                                                                   let uu____12773
=======
                                                                    uu____13270 in
                                                                 let uu____13292
                                                                   =
                                                                   let uu____13296
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
<<<<<<< HEAD
                                                                   match uu____12773
=======
                                                                   match uu____13296
>>>>>>> origin/guido_tactics
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____12781
                                                                    =
                                                                    let uu____12783
                                                                    =
                                                                    let uu____12784
                                                                    =
                                                                    let uu____12788
                                                                    =
                                                                    let uu____12789
                                                                    =
                                                                    let uu____12795
                                                                    =
                                                                    let uu____12796
                                                                    =
                                                                    let uu____12799
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12799,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12796 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12795) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12789 in
                                                                    (uu____12788,
=======
                                                                    let uu____13304
                                                                    =
                                                                    let uu____13306
                                                                    =
                                                                    let uu____13307
                                                                    =
                                                                    let uu____13311
                                                                    =
                                                                    let uu____13312
                                                                    =
                                                                    let uu____13318
                                                                    =
                                                                    let uu____13319
                                                                    =
                                                                    let uu____13322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____13322,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13319 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13318) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13312 in
                                                                    (uu____13311,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____12784 in
                                                                    [uu____12783] in
                                                                    (d3,
                                                                    uu____12781) in
                                                                 (match uu____12769
=======
                                                                    uu____13307 in
                                                                    [uu____13306] in
                                                                    (d3,
                                                                    uu____13304) in
                                                                 (match uu____13292
>>>>>>> origin/guido_tactics
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
<<<<<<< HEAD
                                                           (match uu____12707
=======
                                                           (match uu____13230
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                               let uu____12834 =
                                 let uu____12841 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12889  ->
                                      fun uu____12890  ->
                                        match (uu____12889, uu____12890) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12976 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12976 with
=======
                               let uu____13357 =
                                 let uu____13364 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____13400  ->
                                      fun uu____13401  ->
                                        match (uu____13400, uu____13401) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13487 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13487 with
>>>>>>> origin/guido_tactics
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
<<<<<<< HEAD
                                   ([decls1], [], env0) uu____12841 in
                               (match uu____12834 with
                                | (decls2,eqns,env01) ->
                                    let uu____13016 =
                                      let isDeclFun uu___117_13024 =
                                        match uu___117_13024 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13025 -> true
                                        | uu____13031 -> false in
                                      let uu____13032 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13032
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13016 with
=======
                                   ([decls1], [], env0) uu____13364 in
                               (match uu____13357 with
                                | (decls2,eqns,env01) ->
                                    let uu____13527 =
                                      let isDeclFun uu___117_13535 =
                                        match uu___117_13535 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13536 -> true
                                        | uu____13542 -> false in
                                      let uu____13543 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13543
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13527 with
>>>>>>> origin/guido_tactics
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
<<<<<<< HEAD
                   let uu____13062 =
=======
                   let uu____13570 =
>>>>>>> origin/guido_tactics
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
<<<<<<< HEAD
                   FStar_All.pipe_right uu____13062
=======
                   FStar_All.pipe_right uu____13570
>>>>>>> origin/guido_tactics
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let nm =
<<<<<<< HEAD
        let uu____13096 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13096 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13099 = encode_sigelt' env se in
      match uu____13099 with
=======
        let uu____13603 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13603 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13606 = encode_sigelt' env se in
      match uu____13606 with
>>>>>>> origin/guido_tactics
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
<<<<<<< HEAD
                let uu____13109 =
                  let uu____13110 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13110 in
                [uu____13109]
            | uu____13111 ->
                let uu____13112 =
                  let uu____13114 =
                    let uu____13115 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13115 in
                  uu____13114 :: g in
                let uu____13116 =
                  let uu____13118 =
                    let uu____13119 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13119 in
                  [uu____13118] in
                FStar_List.append uu____13112 uu____13116 in
=======
                let uu____13616 =
                  let uu____13617 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13617 in
                [uu____13616]
            | uu____13618 ->
                let uu____13619 =
                  let uu____13621 =
                    let uu____13622 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13622 in
                  uu____13621 :: g in
                let uu____13623 =
                  let uu____13625 =
                    let uu____13626 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13626 in
                  [uu____13625] in
                FStar_List.append uu____13619 uu____13623 in
>>>>>>> origin/guido_tactics
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
<<<<<<< HEAD
        let uu____13129 =
          let uu____13130 = FStar_Syntax_Subst.compress t in
          uu____13130.FStar_Syntax_Syntax.n in
        match uu____13129 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13134)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13137 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13140 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13143 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13145 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13147 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13155 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13158 =
            let uu____13159 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13159 Prims.op_Negation in
          if uu____13158
=======
        let uu____13636 =
          let uu____13637 = FStar_Syntax_Subst.compress t in
          uu____13637.FStar_Syntax_Syntax.n in
        match uu____13636 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13641)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13644 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13647 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13650 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13652 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13654 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13662 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13665 =
            let uu____13666 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13666 Prims.op_Negation in
          if uu____13665
>>>>>>> origin/guido_tactics
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
<<<<<<< HEAD
               | uu____13179 ->
                   let uu____13180 =
                     let uu____13183 =
                       let uu____13184 =
                         let uu____13199 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13199) in
                       FStar_Syntax_Syntax.Tm_abs uu____13184 in
                     FStar_Syntax_Syntax.mk uu____13183 in
                   uu____13180 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13252 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13252 with
               | (aname,atok,env2) ->
                   let uu____13262 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13262 with
                    | (formals,uu____13272) ->
                        let uu____13279 =
                          let uu____13282 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13282 env2 in
                        (match uu____13279 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13290 =
                                 let uu____13291 =
                                   let uu____13297 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13306  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13297,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13291 in
                               [uu____13290;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13313 =
                               let aux uu____13342 uu____13343 =
                                 match (uu____13342, uu____13343) with
                                 | ((bv,uu____13370),(env3,acc_sorts,acc)) ->
                                     let uu____13391 = gen_term_var env3 bv in
                                     (match uu____13391 with
=======
               | uu____13686 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Syntax_Const.effect_Tot_lid None
                                [FStar_Syntax_Syntax.TOTAL])))) None
                     tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13706 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13706 with
               | (aname,atok,env2) ->
                   let uu____13716 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13716 with
                    | (formals,uu____13726) ->
                        let uu____13733 =
                          let uu____13736 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13736 env2 in
                        (match uu____13733 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13744 =
                                 let uu____13745 =
                                   let uu____13751 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13759  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13751,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13745 in
                               [uu____13744;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13766 =
                               let aux uu____13795 uu____13796 =
                                 match (uu____13795, uu____13796) with
                                 | ((bv,uu____13823),(env3,acc_sorts,acc)) ->
                                     let uu____13844 = gen_term_var env3 bv in
                                     (match uu____13844 with
>>>>>>> origin/guido_tactics
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
<<<<<<< HEAD
                             (match uu____13313 with
                              | (uu____13429,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13443 =
                                      let uu____13447 =
                                        let uu____13448 =
                                          let uu____13454 =
                                            let uu____13455 =
                                              let uu____13458 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13458) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13455 in
                                          ([[app]], xs_sorts, uu____13454) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13448 in
                                      (uu____13447, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13443 in
=======
                             (match uu____13766 with
                              | (uu____13882,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13896 =
                                      let uu____13900 =
                                        let uu____13901 =
                                          let uu____13907 =
                                            let uu____13908 =
                                              let uu____13911 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13911) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13908 in
                                          ([[app]], xs_sorts, uu____13907) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13901 in
                                      (uu____13900, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13896 in
>>>>>>> origin/guido_tactics
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
<<<<<<< HEAD
                                    let uu____13470 =
                                      let uu____13474 =
                                        let uu____13475 =
                                          let uu____13481 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13481) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13475 in
                                      (uu____13474,
=======
                                    let uu____13923 =
                                      let uu____13927 =
                                        let uu____13928 =
                                          let uu____13934 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13934) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13928 in
                                      (uu____13927,
>>>>>>> origin/guido_tactics
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                      uu____13470 in
=======
                                      uu____13923 in
>>>>>>> origin/guido_tactics
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
<<<<<<< HEAD
             let uu____13491 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13491 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13507,uu____13508)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13509 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13509 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13520,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13525 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13528  ->
                      match uu___118_13528 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13529 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13532 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13533 -> false)) in
            Prims.op_Negation uu____13525 in
=======
             let uu____13944 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13944 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13960,uu____13961)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13962 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13962 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13973,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13978 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13980  ->
                      match uu___118_13980 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13981 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13984 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13985 -> false)) in
            Prims.op_Negation uu____13978 in
>>>>>>> origin/guido_tactics
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
<<<<<<< HEAD
             let uu____13539 = encode_top_level_val env fv t quals in
             match uu____13539 with
=======
             let uu____13991 = encode_top_level_val env fv t quals in
             match uu____13991 with
>>>>>>> origin/guido_tactics
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
<<<<<<< HEAD
                 let uu____13551 =
                   let uu____13553 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13553 in
                 (uu____13551, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____13559 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____13559 with
           | (uu____13564,f1) ->
               let uu____13566 = encode_formula f1 env in
               (match uu____13566 with
                | (f2,decls) ->
                    let g =
                      let uu____13575 =
                        let uu____13576 =
                          let uu____13580 =
                            let uu____13582 =
                              let uu____13583 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____13583 in
                            Some uu____13582 in
                          let uu____13584 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____13580, uu____13584) in
                        FStar_SMTEncoding_Util.mkAssume uu____13576 in
                      [uu____13575] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13588,attrs) when
=======
                 let uu____14003 =
                   let uu____14005 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14005 in
                 (uu____14003, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____14010 = encode_formula f env in
          (match uu____14010 with
           | (f1,decls) ->
               let g =
                 let uu____14019 =
                   let uu____14020 =
                     let uu____14024 =
                       let uu____14026 =
                         let uu____14027 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____14027 in
                       Some uu____14026 in
                     let uu____14028 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____14024, uu____14028) in
                   FStar_SMTEncoding_Util.mkAssume uu____14020 in
                 [uu____14019] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14032,attrs) when
>>>>>>> origin/guido_tactics
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
<<<<<<< HEAD
          let uu____13596 =
=======
          let uu____14040 =
>>>>>>> origin/guido_tactics
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
<<<<<<< HEAD
                     let uu____13611 =
                       let uu____13613 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13613.FStar_Syntax_Syntax.fv_name in
                     uu____13611.FStar_Syntax_Syntax.v in
                   let uu____13614 =
                     let uu____13615 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13615 in
                   if uu____13614
                   then
                     let val_decl =
                       let uu___152_13630 = se in
=======
                     let uu____14047 =
                       let uu____14052 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14052.FStar_Syntax_Syntax.fv_name in
                     uu____14047.FStar_Syntax_Syntax.v in
                   let uu____14056 =
                     let uu____14057 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14057 in
                   if uu____14056
                   then
                     let val_decl =
                       let uu___151_14072 = se in
>>>>>>> origin/guido_tactics
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                           (uu___152_13630.FStar_Syntax_Syntax.sigrng);
=======
                           (uu___151_14072.FStar_Syntax_Syntax.sigrng);
>>>>>>> origin/guido_tactics
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
<<<<<<< HEAD
                           (uu___152_13630.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13634 = encode_sigelt' env1 val_decl in
                     match uu____13634 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13596 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13651,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13653;
                          FStar_Syntax_Syntax.lbtyp = uu____13654;
                          FStar_Syntax_Syntax.lbeff = uu____13655;
                          FStar_Syntax_Syntax.lbdef = uu____13656;_}::[]),uu____13657,uu____13658)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13672 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13672 with
=======
                           (uu___151_14072.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____14076 = encode_sigelt' env1 val_decl in
                     match uu____14076 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____14040 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14093,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14095;
                          FStar_Syntax_Syntax.lbtyp = uu____14096;
                          FStar_Syntax_Syntax.lbeff = uu____14097;
                          FStar_Syntax_Syntax.lbdef = uu____14098;_}::[]),uu____14099,uu____14100)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____14114 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14114 with
>>>>>>> origin/guido_tactics
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
<<<<<<< HEAD
                 let uu____13691 =
                   let uu____13693 =
                     let uu____13694 =
                       let uu____13698 =
                         let uu____13699 =
                           let uu____13705 =
                             let uu____13706 =
                               let uu____13709 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13709) in
                             FStar_SMTEncoding_Util.mkEq uu____13706 in
                           ([[b2t_x]], [xx], uu____13705) in
                         FStar_SMTEncoding_Util.mkForall uu____13699 in
                       (uu____13698, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13694 in
                   [uu____13693] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13691 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13726,uu____13727,uu____13728)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13736  ->
                  match uu___119_13736 with
                  | FStar_Syntax_Syntax.Discriminator uu____13737 -> true
                  | uu____13738 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13740,lids,uu____13742) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13751 =
                     let uu____13752 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13752.FStar_Ident.idText in
                   uu____13751 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13755  ->
                     match uu___120_13755 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13756 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13759,uu____13760)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13772  ->
                  match uu___121_13772 with
                  | FStar_Syntax_Syntax.Projector uu____13773 -> true
                  | uu____13776 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13779 = try_lookup_free_var env l in
          (match uu____13779 with
           | Some uu____13783 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13786 = se in
=======
                 let uu____14137 =
                   let uu____14139 =
                     let uu____14140 =
                       let uu____14144 =
                         let uu____14145 =
                           let uu____14151 =
                             let uu____14152 =
                               let uu____14155 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14155) in
                             FStar_SMTEncoding_Util.mkEq uu____14152 in
                           ([[b2t_x]], [xx], uu____14151) in
                         FStar_SMTEncoding_Util.mkForall uu____14145 in
                       (uu____14144, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14140 in
                   [uu____14139] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____14137 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14172,uu____14173,uu____14174)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_14180  ->
                  match uu___119_14180 with
                  | FStar_Syntax_Syntax.Discriminator uu____14181 -> true
                  | uu____14182 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14184,lids,uu____14186) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14193 =
                     let uu____14194 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14194.FStar_Ident.idText in
                   uu____14193 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_14196  ->
                     match uu___120_14196 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14197 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14200,uu____14201)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_14211  ->
                  match uu___121_14211 with
                  | FStar_Syntax_Syntax.Projector uu____14212 -> true
                  | uu____14215 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____14222 = try_lookup_free_var env l in
          (match uu____14222 with
           | Some uu____14226 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_14229 = se in
>>>>>>> origin/guido_tactics
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
<<<<<<< HEAD
                     (uu___153_13786.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13786.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13792,uu____13793) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13805) ->
          let uu____13810 = encode_sigelts env ses in
          (match uu____13810 with
           | (g,env1) ->
               let uu____13820 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13834  ->
                         match uu___122_13834 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13835;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13836;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13837;_}
                             -> false
                         | uu____13839 -> true)) in
               (match uu____13820 with
                | (g',inversions) ->
                    let uu____13848 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13860  ->
                              match uu___123_13860 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13861 ->
                                  true
                              | uu____13867 -> false)) in
                    (match uu____13848 with
=======
                     (uu___152_14229.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_14229.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____14235,uu____14236) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14248) ->
          let uu____14253 = encode_sigelts env ses in
          (match uu____14253 with
           | (g,env1) ->
               let uu____14263 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_14273  ->
                         match uu___122_14273 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____14274;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____14275;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____14276;_}
                             -> false
                         | uu____14278 -> true)) in
               (match uu____14263 with
                | (g',inversions) ->
                    let uu____14287 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_14297  ->
                              match uu___123_14297 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14298 ->
                                  true
                              | uu____14304 -> false)) in
                    (match uu____14287 with
>>>>>>> origin/guido_tactics
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
<<<<<<< HEAD
          (t,uu____13878,tps,k,uu____13881,datas) ->
=======
          (t,uu____14315,tps,k,uu____14318,datas) ->
>>>>>>> origin/guido_tactics
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
<<<<<<< HEAD
                 (fun uu___124_13892  ->
                    match uu___124_13892 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13893 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13900 = c in
              match uu____13900 with
              | (name,args,uu____13904,uu____13905,uu____13906) ->
                  let uu____13909 =
                    let uu____13910 =
                      let uu____13916 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13927  ->
                                match uu____13927 with
                                | (uu____13931,sort,uu____13933) -> sort)) in
                      (name, uu____13916, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13910 in
                  [uu____13909]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13951 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13956 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13956 FStar_Option.isNone)) in
            if uu____13951
            then []
            else
              (let uu____13973 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13973 with
               | (xxsym,xx) ->
                   let uu____13979 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14008  ->
                             fun l  ->
                               match uu____14008 with
                               | (out,decls) ->
                                   let uu____14020 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14020 with
                                    | (uu____14026,data_t) ->
                                        let uu____14028 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14028 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14057 =
                                                 let uu____14058 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14058.FStar_Syntax_Syntax.n in
                                               match uu____14057 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14066,indices) ->
                                                   indices
                                               | uu____14082 -> [] in
=======
                 (fun uu___124_14328  ->
                    match uu___124_14328 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14329 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14336 = c in
              match uu____14336 with
              | (name,args,uu____14340,uu____14341,uu____14342) ->
                  let uu____14345 =
                    let uu____14346 =
                      let uu____14352 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14359  ->
                                match uu____14359 with
                                | (uu____14363,sort,uu____14365) -> sort)) in
                      (name, uu____14352, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14346 in
                  [uu____14345]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____14383 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14386 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____14386 FStar_Option.isNone)) in
            if uu____14383
            then []
            else
              (let uu____14403 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14403 with
               | (xxsym,xx) ->
                   let uu____14409 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14420  ->
                             fun l  ->
                               match uu____14420 with
                               | (out,decls) ->
                                   let uu____14432 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14432 with
                                    | (uu____14438,data_t) ->
                                        let uu____14440 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14440 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14469 =
                                                 let uu____14470 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14470.FStar_Syntax_Syntax.n in
                                               match uu____14469 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14478,indices) ->
                                                   indices
                                               | uu____14494 -> [] in
>>>>>>> origin/guido_tactics
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
<<<<<<< HEAD
                                                       fun uu____14099  ->
                                                         match uu____14099
                                                         with
                                                         | (x,uu____14103) ->
                                                             let uu____14104
                                                               =
                                                               let uu____14105
                                                                 =
                                                                 let uu____14109
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14109,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14105 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14104)
                                                    env) in
                                             let uu____14111 =
                                               encode_args indices env1 in
                                             (match uu____14111 with
=======
                                                       fun uu____14506  ->
                                                         match uu____14506
                                                         with
                                                         | (x,uu____14510) ->
                                                             let uu____14511
                                                               =
                                                               let uu____14512
                                                                 =
                                                                 let uu____14516
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14516,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14512 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14511)
                                                    env) in
                                             let uu____14518 =
                                               encode_args indices env1 in
                                             (match uu____14518 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                                      let uu____14131 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14142
                                                                 =
                                                                 let uu____14145
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14145,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14142)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14131
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14147 =
                                                      let uu____14148 =
                                                        let uu____14151 =
                                                          let uu____14152 =
                                                            let uu____14155 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14155,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14152 in
                                                        (out, uu____14151) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14148 in
                                                    (uu____14147,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13979 with
                    | (data_ax,decls) ->
                        let uu____14163 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14163 with
=======
                                                      let uu____14542 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14550
                                                                 =
                                                                 let uu____14553
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14553,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14550)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14542
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14555 =
                                                      let uu____14556 =
                                                        let uu____14559 =
                                                          let uu____14560 =
                                                            let uu____14563 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14563,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14560 in
                                                        (out, uu____14559) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14556 in
                                                    (uu____14555,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14409 with
                    | (data_ax,decls) ->
                        let uu____14571 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14571 with
>>>>>>> origin/guido_tactics
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
<<<<<<< HEAD
                                   let uu____14174 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14174 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14177 =
                                 let uu____14181 =
                                   let uu____14182 =
                                     let uu____14188 =
=======
                                   let uu____14585 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14585 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14588 =
                                 let uu____14592 =
                                   let uu____14593 =
                                     let uu____14599 =
>>>>>>> origin/guido_tactics
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
<<<<<<< HEAD
                                     let uu____14196 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14188,
                                       uu____14196) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14182 in
                                 let uu____14204 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14181, (Some "inversion axiom"),
                                   uu____14204) in
                               FStar_SMTEncoding_Util.mkAssume uu____14177 in
                             let pattern_guarded_inversion =
                               let uu____14208 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14208
=======
                                     let uu____14607 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14599,
                                       uu____14607) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14593 in
                                 let uu____14615 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14592, (Some "inversion axiom"),
                                   uu____14615) in
                               FStar_SMTEncoding_Util.mkAssume uu____14588 in
                             let pattern_guarded_inversion =
                               let uu____14619 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14619
>>>>>>> origin/guido_tactics
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
<<<<<<< HEAD
                                 let uu____14216 =
                                   let uu____14217 =
                                     let uu____14221 =
                                       let uu____14222 =
                                         let uu____14228 =
=======
                                 let uu____14630 =
                                   let uu____14631 =
                                     let uu____14635 =
                                       let uu____14636 =
                                         let uu____14642 =
>>>>>>> origin/guido_tactics
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
<<<<<<< HEAD
                                         let uu____14236 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14228, uu____14236) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14222 in
                                     let uu____14244 =
=======
                                         let uu____14650 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14642, uu____14650) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14636 in
                                     let uu____14658 =
>>>>>>> origin/guido_tactics
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
<<<<<<< HEAD
                                     (uu____14221, (Some "inversion axiom"),
                                       uu____14244) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14217 in
                                 [uu____14216]
=======
                                     (uu____14635, (Some "inversion axiom"),
                                       uu____14658) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14631 in
                                 [uu____14630]
>>>>>>> origin/guido_tactics
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
<<<<<<< HEAD
          let uu____14247 =
            let uu____14255 =
              let uu____14256 = FStar_Syntax_Subst.compress k in
              uu____14256.FStar_Syntax_Syntax.n in
            match uu____14255 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14285 -> (tps, k) in
          (match uu____14247 with
           | (formals,res) ->
               let uu____14300 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14300 with
                | (formals1,res1) ->
                    let uu____14307 = encode_binders None formals1 env in
                    (match uu____14307 with
                     | (vars,guards,env',binder_decls,uu____14322) ->
                         let uu____14329 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14329 with
=======
          let uu____14661 =
            let uu____14669 =
              let uu____14670 = FStar_Syntax_Subst.compress k in
              uu____14670.FStar_Syntax_Syntax.n in
            match uu____14669 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14699 -> (tps, k) in
          (match uu____14661 with
           | (formals,res) ->
               let uu____14714 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14714 with
                | (formals1,res1) ->
                    let uu____14721 = encode_binders None formals1 env in
                    (match uu____14721 with
                     | (vars,guards,env',binder_decls,uu____14736) ->
                         let uu____14743 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14743 with
>>>>>>> origin/guido_tactics
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
<<<<<<< HEAD
                                let uu____14342 =
                                  let uu____14346 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14346) in
                                FStar_SMTEncoding_Util.mkApp uu____14342 in
                              let uu____14351 =
                                let tname_decl =
                                  let uu____14357 =
                                    let uu____14358 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14376  ->
                                              match uu____14376 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14384 = varops.next_id () in
                                    (tname, uu____14358,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14384, false) in
                                  constructor_or_logic_type_decl uu____14357 in
                                let uu____14389 =
                                  match vars with
                                  | [] ->
                                      let uu____14396 =
                                        let uu____14397 =
                                          let uu____14399 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14399 in
                                        push_free_var env1 t tname
                                          uu____14397 in
                                      ([], uu____14396)
                                  | uu____14403 ->
=======
                                let uu____14756 =
                                  let uu____14760 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14760) in
                                FStar_SMTEncoding_Util.mkApp uu____14756 in
                              let uu____14765 =
                                let tname_decl =
                                  let uu____14771 =
                                    let uu____14772 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14787  ->
                                              match uu____14787 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14795 = varops.next_id () in
                                    (tname, uu____14772,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14795, false) in
                                  constructor_or_logic_type_decl uu____14771 in
                                let uu____14800 =
                                  match vars with
                                  | [] ->
                                      let uu____14807 =
                                        let uu____14808 =
                                          let uu____14810 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  -> Some _0_44)
                                            uu____14810 in
                                        push_free_var env1 t tname
                                          uu____14808 in
                                      ([], uu____14807)
                                  | uu____14814 ->
>>>>>>> origin/guido_tactics
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
<<<<<<< HEAD
                                        let uu____14409 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14409 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14418 =
                                          let uu____14422 =
                                            let uu____14423 =
                                              let uu____14431 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14431) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14423 in
                                          (uu____14422,
=======
                                        let uu____14820 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14820 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14829 =
                                          let uu____14833 =
                                            let uu____14834 =
                                              let uu____14842 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14842) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14834 in
                                          (uu____14833,
>>>>>>> origin/guido_tactics
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                          uu____14418 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14389 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14351 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14454 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14454 with
=======
                                          uu____14829 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14800 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14765 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14865 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14865 with
>>>>>>> origin/guido_tactics
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
<<<<<<< HEAD
                                             let uu____14468 =
                                               let uu____14469 =
                                                 let uu____14473 =
                                                   let uu____14474 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14474 in
                                                 (uu____14473,
=======
                                             let uu____14882 =
                                               let uu____14883 =
                                                 let uu____14887 =
                                                   let uu____14888 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14888 in
                                                 (uu____14887,
>>>>>>> origin/guido_tactics
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                 uu____14469 in
                                             [uu____14468]
                                           else [] in
                                         let uu____14477 =
                                           let uu____14479 =
                                             let uu____14481 =
                                               let uu____14482 =
                                                 let uu____14486 =
                                                   let uu____14487 =
                                                     let uu____14493 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14493) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14487 in
                                                 (uu____14486, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14482 in
                                             [uu____14481] in
                                           FStar_List.append karr uu____14479 in
                                         FStar_List.append decls1 uu____14477 in
                                   let aux =
                                     let uu____14502 =
                                       let uu____14504 =
                                         inversion_axioms tapp vars in
                                       let uu____14506 =
                                         let uu____14508 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14508] in
                                       FStar_List.append uu____14504
                                         uu____14506 in
                                     FStar_List.append kindingAx uu____14502 in
=======
                                                 uu____14883 in
                                             [uu____14882]
                                           else [] in
                                         let uu____14891 =
                                           let uu____14893 =
                                             let uu____14895 =
                                               let uu____14896 =
                                                 let uu____14900 =
                                                   let uu____14901 =
                                                     let uu____14907 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14907) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14901 in
                                                 (uu____14900, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14896 in
                                             [uu____14895] in
                                           FStar_List.append karr uu____14893 in
                                         FStar_List.append decls1 uu____14891 in
                                   let aux =
                                     let uu____14916 =
                                       let uu____14918 =
                                         inversion_axioms tapp vars in
                                       let uu____14920 =
                                         let uu____14922 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14922] in
                                       FStar_List.append uu____14918
                                         uu____14920 in
                                     FStar_List.append kindingAx uu____14916 in
>>>>>>> origin/guido_tactics
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
          (d,uu____14513,uu____14514,uu____14515,uu____14516,uu____14517)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14522,t,uu____14524,n_tps,uu____14526) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14531 = new_term_constant_and_tok_from_lid env d in
          (match uu____14531 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14542 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14542 with
                | (formals,t_res) ->
                    let uu____14564 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14564 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14573 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14573 with
=======
          (d,uu____14927,uu____14928,uu____14929,uu____14930,uu____14931)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14936,t,uu____14938,n_tps,uu____14940) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14945 = new_term_constant_and_tok_from_lid env d in
          (match uu____14945 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14956 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14956 with
                | (formals,t_res) ->
                    let uu____14978 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14978 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14987 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14987 with
>>>>>>> origin/guido_tactics
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
<<<<<<< HEAD
                                          let uu____14615 =
                                            mk_term_projector_name d x in
                                          (uu____14615,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14617 =
                                  let uu____14627 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14627, true) in
                                FStar_All.pipe_right uu____14617
=======
                                          let uu____15025 =
                                            mk_term_projector_name d x in
                                          (uu____15025,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15027 =
                                  let uu____15037 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15037, true) in
                                FStar_All.pipe_right uu____15027
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                              let uu____14649 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14649 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14657::uu____14658 ->
=======
                              let uu____15059 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____15059 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15067::uu____15068 ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                         let uu____14683 =
                                           let uu____14689 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14689) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14683
                                     | uu____14702 -> tok_typing in
                                   let uu____14707 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14707 with
                                    | (vars',guards',env'',decls_formals,uu____14722)
                                        ->
                                        let uu____14729 =
=======
                                         let uu____15093 =
                                           let uu____15099 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15099) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15093
                                     | uu____15112 -> tok_typing in
                                   let uu____15117 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____15117 with
                                    | (vars',guards',env'',decls_formals,uu____15132)
                                        ->
                                        let uu____15139 =
>>>>>>> origin/guido_tactics
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
<<<<<<< HEAD
                                        (match uu____14729 with
=======
                                        (match uu____15139 with
>>>>>>> origin/guido_tactics
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
<<<<<<< HEAD
                                               | uu____14748 ->
                                                   let uu____14752 =
                                                     let uu____14753 =
=======
                                               | uu____15158 ->
                                                   let uu____15162 =
                                                     let uu____15163 =
>>>>>>> origin/guido_tactics
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
<<<<<<< HEAD
                                                       uu____14753 in
                                                   [uu____14752] in
                                             let encode_elim uu____14760 =
                                               let uu____14761 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14761 with
                                               | (head1,args) ->
                                                   let uu____14790 =
                                                     let uu____14791 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14791.FStar_Syntax_Syntax.n in
                                                   (match uu____14790 with
=======
                                                       uu____15163 in
                                                   [uu____15162] in
                                             let encode_elim uu____15170 =
                                               let uu____15171 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____15171 with
                                               | (head1,args) ->
                                                   let uu____15200 =
                                                     let uu____15201 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____15201.FStar_Syntax_Syntax.n in
                                                   (match uu____15200 with
>>>>>>> origin/guido_tactics
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
<<<<<<< HEAD
                                                             = uu____14798;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14799;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14800;_},uu____14801)
=======
                                                             = uu____15208;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____15209;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____15210;_},uu____15211)
>>>>>>> origin/guido_tactics
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
<<<<<<< HEAD
                                                        let uu____14807 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14807
=======
                                                        let uu____15221 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15221
>>>>>>> origin/guido_tactics
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
<<<<<<< HEAD
                                                                 | uu____14833
=======
                                                                 | uu____15247
>>>>>>> origin/guido_tactics
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____14844
                                                                    =
                                                                    let uu____14845
=======
                                                                    let uu____15255
                                                                    =
                                                                    let uu____15256
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
<<<<<<< HEAD
                                                                    uu____14845 in
                                                                    if
                                                                    uu____14844
                                                                    then
                                                                    let uu____14852
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14852]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14854
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14878
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14878
=======
                                                                    uu____15256 in
                                                                    if
                                                                    uu____15255
                                                                    then
                                                                    let uu____15263
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15263]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15265
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15278
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15278
>>>>>>> origin/guido_tactics
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____14900
                                                                    =
                                                                    let uu____14904
=======
                                                                    let uu____15300
                                                                    =
                                                                    let uu____15304
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
<<<<<<< HEAD
                                                                    uu____14904 in
                                                                    (match uu____14900
                                                                    with
                                                                    | 
                                                                    (uu____14911,xv,env3)
=======
                                                                    uu____15304 in
                                                                    (match uu____15300
                                                                    with
                                                                    | 
                                                                    (uu____15311,xv,env3)
>>>>>>> origin/guido_tactics
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
<<<<<<< HEAD
                                                                    let uu____14917
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14917
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14919
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14919
=======
                                                                    let uu____15317
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15317
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15319
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15319
>>>>>>> origin/guido_tactics
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
                                                                 encoded_args in
<<<<<<< HEAD
                                                             (match uu____14854
                                                              with
                                                              | (uu____14927,arg_vars,elim_eqns_or_guards,uu____14930)
=======
                                                             (match uu____15265
                                                              with
                                                              | (uu____15327,arg_vars,elim_eqns_or_guards,uu____15330)
>>>>>>> origin/guido_tactics
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
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
<<<<<<< HEAD
                                                                    let uu____14949
                                                                    =
                                                                    let uu____14953
                                                                    =
                                                                    let uu____14954
                                                                    =
                                                                    let uu____14960
=======
                                                                    let uu____15349
                                                                    =
                                                                    let uu____15353
                                                                    =
                                                                    let uu____15354
                                                                    =
                                                                    let uu____15360
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
<<<<<<< HEAD
                                                                    let uu____14966
                                                                    =
                                                                    let uu____14967
                                                                    =
                                                                    let uu____14970
=======
                                                                    let uu____15366
                                                                    =
                                                                    let uu____15367
                                                                    =
                                                                    let uu____15370
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
<<<<<<< HEAD
                                                                    uu____14970) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14967 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14960,
                                                                    uu____14966) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14954 in
                                                                    (uu____14953,
=======
                                                                    uu____15370) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15367 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15360,
                                                                    uu____15366) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15354 in
                                                                    (uu____15353,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____14949 in
=======
                                                                    uu____15349 in
>>>>>>> origin/guido_tactics
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
<<<<<<< HEAD
                                                                    let uu____14983
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14983,
=======
                                                                    let uu____15383
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15383,
>>>>>>> origin/guido_tactics
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
<<<<<<< HEAD
                                                                    let uu____14985
                                                                    =
                                                                    let uu____14989
                                                                    =
                                                                    let uu____14990
                                                                    =
                                                                    let uu____14996
                                                                    =
                                                                    let uu____14999
                                                                    =
                                                                    let uu____15001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15001] in
                                                                    [uu____14999] in
                                                                    let uu____15004
                                                                    =
                                                                    let uu____15005
                                                                    =
                                                                    let uu____15008
=======
                                                                    let uu____15385
                                                                    =
                                                                    let uu____15389
                                                                    =
                                                                    let uu____15390
                                                                    =
                                                                    let uu____15396
                                                                    =
                                                                    let uu____15399
                                                                    =
                                                                    let uu____15401
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15401] in
                                                                    [uu____15399] in
                                                                    let uu____15404
                                                                    =
                                                                    let uu____15405
                                                                    =
                                                                    let uu____15408
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
<<<<<<< HEAD
                                                                    let uu____15009
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15008,
                                                                    uu____15009) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15005 in
                                                                    (uu____14996,
                                                                    [x],
                                                                    uu____15004) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14990 in
                                                                    let uu____15019
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14989,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15019) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14985
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15024
=======
                                                                    let uu____15409
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15408,
                                                                    uu____15409) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15405 in
                                                                    (uu____15396,
                                                                    [x],
                                                                    uu____15404) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15390 in
                                                                    let uu____15419
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15389,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15419) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15385
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15424
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                                                    (let uu____15041
                                                                    =
                                                                    let uu____15042
=======
                                                                    (let uu____15439
                                                                    =
                                                                    let uu____15440
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
<<<<<<< HEAD
                                                                    uu____15042
                                                                    dapp1 in
                                                                    [uu____15041]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15024
                                                                    FStar_List.flatten in
                                                                    let uu____15046
                                                                    =
                                                                    let uu____15050
                                                                    =
                                                                    let uu____15051
                                                                    =
                                                                    let uu____15057
=======
                                                                    uu____15440
                                                                    dapp1 in
                                                                    [uu____15439]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15424
                                                                    FStar_List.flatten in
                                                                    let uu____15444
                                                                    =
                                                                    let uu____15448
                                                                    =
                                                                    let uu____15449
                                                                    =
                                                                    let uu____15455
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
<<<<<<< HEAD
                                                                    let uu____15063
                                                                    =
                                                                    let uu____15064
                                                                    =
                                                                    let uu____15067
=======
                                                                    let uu____15461
                                                                    =
                                                                    let uu____15462
                                                                    =
                                                                    let uu____15465
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
<<<<<<< HEAD
                                                                    uu____15067) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15064 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15057,
                                                                    uu____15063) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15051 in
                                                                    (uu____15050,
=======
                                                                    uu____15465) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15462 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15455,
                                                                    uu____15461) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15449 in
                                                                    (uu____15448,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____15046) in
=======
                                                                    uu____15444) in
>>>>>>> origin/guido_tactics
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
<<<<<<< HEAD
                                                        let uu____15079 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15079
=======
                                                        let uu____15481 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15481
>>>>>>> origin/guido_tactics
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
<<<<<<< HEAD
                                                                 | uu____15105
=======
                                                                 | uu____15507
>>>>>>> origin/guido_tactics
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____15116
                                                                    =
                                                                    let uu____15117
=======
                                                                    let uu____15515
                                                                    =
                                                                    let uu____15516
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
<<<<<<< HEAD
                                                                    uu____15117 in
                                                                    if
                                                                    uu____15116
                                                                    then
                                                                    let uu____15124
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15124]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15126
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15150
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15150
=======
                                                                    uu____15516 in
                                                                    if
                                                                    uu____15515
                                                                    then
                                                                    let uu____15523
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15523]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15525
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15538
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15538
>>>>>>> origin/guido_tactics
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
<<<<<<< HEAD
                                                                    let uu____15172
                                                                    =
                                                                    let uu____15176
=======
                                                                    let uu____15560
                                                                    =
                                                                    let uu____15564
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
<<<<<<< HEAD
                                                                    uu____15176 in
                                                                    (match uu____15172
                                                                    with
                                                                    | 
                                                                    (uu____15183,xv,env3)
=======
                                                                    uu____15564 in
                                                                    (match uu____15560
                                                                    with
                                                                    | 
                                                                    (uu____15571,xv,env3)
>>>>>>> origin/guido_tactics
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
<<<<<<< HEAD
                                                                    let uu____15189
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15189
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15191
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15191
=======
                                                                    let uu____15577
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15577
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15579
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15579
>>>>>>> origin/guido_tactics
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
                                                                 encoded_args in
<<<<<<< HEAD
                                                             (match uu____15126
                                                              with
                                                              | (uu____15199,arg_vars,elim_eqns_or_guards,uu____15202)
=======
                                                             (match uu____15525
                                                              with
                                                              | (uu____15587,arg_vars,elim_eqns_or_guards,uu____15590)
>>>>>>> origin/guido_tactics
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
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
<<<<<<< HEAD
                                                                    let uu____15221
                                                                    =
                                                                    let uu____15225
                                                                    =
                                                                    let uu____15226
                                                                    =
                                                                    let uu____15232
=======
                                                                    let uu____15609
                                                                    =
                                                                    let uu____15613
                                                                    =
                                                                    let uu____15614
                                                                    =
                                                                    let uu____15620
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
<<<<<<< HEAD
                                                                    let uu____15238
                                                                    =
                                                                    let uu____15239
                                                                    =
                                                                    let uu____15242
=======
                                                                    let uu____15626
                                                                    =
                                                                    let uu____15627
                                                                    =
                                                                    let uu____15630
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
<<<<<<< HEAD
                                                                    uu____15242) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15239 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15232,
                                                                    uu____15238) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15226 in
                                                                    (uu____15225,
=======
                                                                    uu____15630) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15627 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15620,
                                                                    uu____15626) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15614 in
                                                                    (uu____15613,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____15221 in
=======
                                                                    uu____15609 in
>>>>>>> origin/guido_tactics
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
<<<<<<< HEAD
                                                                    let uu____15255
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15255,
=======
                                                                    let uu____15643
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15643,
>>>>>>> origin/guido_tactics
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
<<<<<<< HEAD
                                                                    let uu____15257
                                                                    =
                                                                    let uu____15261
                                                                    =
                                                                    let uu____15262
                                                                    =
                                                                    let uu____15268
                                                                    =
                                                                    let uu____15271
                                                                    =
                                                                    let uu____15273
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15273] in
                                                                    [uu____15271] in
                                                                    let uu____15276
                                                                    =
                                                                    let uu____15277
                                                                    =
                                                                    let uu____15280
=======
                                                                    let uu____15645
                                                                    =
                                                                    let uu____15649
                                                                    =
                                                                    let uu____15650
                                                                    =
                                                                    let uu____15656
                                                                    =
                                                                    let uu____15659
                                                                    =
                                                                    let uu____15661
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15661] in
                                                                    [uu____15659] in
                                                                    let uu____15664
                                                                    =
                                                                    let uu____15665
                                                                    =
                                                                    let uu____15668
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
<<<<<<< HEAD
                                                                    let uu____15281
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15280,
                                                                    uu____15281) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15277 in
                                                                    (uu____15268,
                                                                    [x],
                                                                    uu____15276) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15262 in
                                                                    let uu____15291
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15261,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15291) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15257
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15296
=======
                                                                    let uu____15669
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15668,
                                                                    uu____15669) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15665 in
                                                                    (uu____15656,
                                                                    [x],
                                                                    uu____15664) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15650 in
                                                                    let uu____15679
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15649,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15679) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15645
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15684
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                                                    (let uu____15313
                                                                    =
                                                                    let uu____15314
=======
                                                                    (let uu____15699
                                                                    =
                                                                    let uu____15700
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
<<<<<<< HEAD
                                                                    uu____15314
                                                                    dapp1 in
                                                                    [uu____15313]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15296
                                                                    FStar_List.flatten in
                                                                    let uu____15318
                                                                    =
                                                                    let uu____15322
                                                                    =
                                                                    let uu____15323
                                                                    =
                                                                    let uu____15329
=======
                                                                    uu____15700
                                                                    dapp1 in
                                                                    [uu____15699]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15684
                                                                    FStar_List.flatten in
                                                                    let uu____15704
                                                                    =
                                                                    let uu____15708
                                                                    =
                                                                    let uu____15709
                                                                    =
                                                                    let uu____15715
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
<<<<<<< HEAD
                                                                    let uu____15335
                                                                    =
                                                                    let uu____15336
                                                                    =
                                                                    let uu____15339
=======
                                                                    let uu____15721
                                                                    =
                                                                    let uu____15722
                                                                    =
                                                                    let uu____15725
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
<<<<<<< HEAD
                                                                    uu____15339) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15336 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15329,
                                                                    uu____15335) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15323 in
                                                                    (uu____15322,
=======
                                                                    uu____15725) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15722 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15715,
                                                                    uu____15721) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15709 in
                                                                    (uu____15708,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____15318) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15349 ->
                                                        ((let uu____15351 =
                                                            let uu____15352 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15353 =
=======
                                                                    uu____15704) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15735 ->
                                                        ((let uu____15737 =
                                                            let uu____15738 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15739 =
>>>>>>> origin/guido_tactics
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
<<<<<<< HEAD
                                                              uu____15352
                                                              uu____15353 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15351);
                                                         ([], []))) in
                                             let uu____15356 = encode_elim () in
                                             (match uu____15356 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15368 =
                                                      let uu____15370 =
                                                        let uu____15372 =
                                                          let uu____15374 =
                                                            let uu____15376 =
                                                              let uu____15377
                                                                =
                                                                let uu____15383
                                                                  =
                                                                  let uu____15385
                                                                    =
                                                                    let uu____15386
=======
                                                              uu____15738
                                                              uu____15739 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15737);
                                                         ([], []))) in
                                             let uu____15742 = encode_elim () in
                                             (match uu____15742 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15754 =
                                                      let uu____15756 =
                                                        let uu____15758 =
                                                          let uu____15760 =
                                                            let uu____15762 =
                                                              let uu____15763
                                                                =
                                                                let uu____15769
                                                                  =
                                                                  let uu____15771
                                                                    =
                                                                    let uu____15772
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
<<<<<<< HEAD
                                                                    uu____15386 in
                                                                  Some
                                                                    uu____15385 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15383) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15377 in
                                                            [uu____15376] in
                                                          let uu____15389 =
                                                            let uu____15391 =
                                                              let uu____15393
                                                                =
                                                                let uu____15395
                                                                  =
                                                                  let uu____15397
                                                                    =
                                                                    let uu____15399
                                                                    =
                                                                    let uu____15401
                                                                    =
                                                                    let uu____15402
                                                                    =
                                                                    let uu____15406
                                                                    =
                                                                    let uu____15407
                                                                    =
                                                                    let uu____15413
=======
                                                                    uu____15772 in
                                                                  Some
                                                                    uu____15771 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15769) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15763 in
                                                            [uu____15762] in
                                                          let uu____15775 =
                                                            let uu____15777 =
                                                              let uu____15779
                                                                =
                                                                let uu____15781
                                                                  =
                                                                  let uu____15783
                                                                    =
                                                                    let uu____15785
                                                                    =
                                                                    let uu____15787
                                                                    =
                                                                    let uu____15788
                                                                    =
                                                                    let uu____15792
                                                                    =
                                                                    let uu____15793
                                                                    =
                                                                    let uu____15799
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
<<<<<<< HEAD
                                                                    uu____15413) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15407 in
                                                                    (uu____15406,
=======
                                                                    uu____15799) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15793 in
                                                                    (uu____15792,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____15402 in
                                                                    let uu____15420
                                                                    =
                                                                    let uu____15422
                                                                    =
                                                                    let uu____15423
                                                                    =
                                                                    let uu____15427
                                                                    =
                                                                    let uu____15428
                                                                    =
                                                                    let uu____15434
=======
                                                                    uu____15788 in
                                                                    let uu____15806
                                                                    =
                                                                    let uu____15808
                                                                    =
                                                                    let uu____15809
                                                                    =
                                                                    let uu____15813
                                                                    =
                                                                    let uu____15814
                                                                    =
                                                                    let uu____15820
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
<<<<<<< HEAD
                                                                    let uu____15440
=======
                                                                    let uu____15826
>>>>>>> origin/guido_tactics
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
<<<<<<< HEAD
                                                                    uu____15434,
                                                                    uu____15440) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15428 in
                                                                    (uu____15427,
=======
                                                                    uu____15820,
                                                                    uu____15826) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15814 in
                                                                    (uu____15813,
>>>>>>> origin/guido_tactics
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
<<<<<<< HEAD
                                                                    uu____15423 in
                                                                    [uu____15422] in
                                                                    uu____15401
                                                                    ::
                                                                    uu____15420 in
=======
                                                                    uu____15809 in
                                                                    [uu____15808] in
                                                                    uu____15787
                                                                    ::
                                                                    uu____15806 in
>>>>>>> origin/guido_tactics
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
<<<<<<< HEAD
                                                                    uu____15399 in
                                                                  FStar_List.append
                                                                    uu____15397
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15395 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15393 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15391 in
                                                          FStar_List.append
                                                            uu____15374
                                                            uu____15389 in
                                                        FStar_List.append
                                                          decls3 uu____15372 in
                                                      FStar_List.append
                                                        decls2 uu____15370 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15368 in
=======
                                                                    uu____15785 in
                                                                  FStar_List.append
                                                                    uu____15783
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15781 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15779 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15777 in
                                                          FStar_List.append
                                                            uu____15760
                                                            uu____15775 in
                                                        FStar_List.append
                                                          decls3 uu____15758 in
                                                      FStar_List.append
                                                        decls2 uu____15756 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15754 in
>>>>>>> origin/guido_tactics
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
<<<<<<< HEAD
           (fun uu____15468  ->
              fun se  ->
                match uu____15468 with
                | (g,env1) ->
                    let uu____15480 = encode_sigelt env1 se in
                    (match uu____15480 with
=======
           (fun uu____15847  ->
              fun se  ->
                match uu____15847 with
                | (g,env1) ->
                    let uu____15859 = encode_sigelt env1 se in
                    (match uu____15859 with
>>>>>>> origin/guido_tactics
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
<<<<<<< HEAD
      let encode_binding b uu____15516 =
        match uu____15516 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15534 ->
=======
      let encode_binding b uu____15897 =
        match uu____15897 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15915 ->
>>>>>>> origin/guido_tactics
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
<<<<<<< HEAD
                 ((let uu____15539 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15539
                   then
                     let uu____15540 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15541 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15542 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15540 uu____15541 uu____15542
                   else ());
                  (let uu____15544 = encode_term t1 env1 in
                   match uu____15544 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15554 =
                         let uu____15558 =
                           let uu____15559 =
                             let uu____15560 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15560
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15559 in
                         new_term_constant_from_string env1 x uu____15558 in
                       (match uu____15554 with
=======
                 ((let uu____15920 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15920
                   then
                     let uu____15921 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15922 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15923 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15921 uu____15922 uu____15923
                   else ());
                  (let uu____15925 = encode_term t1 env1 in
                   match uu____15925 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15935 =
                         let uu____15939 =
                           let uu____15940 =
                             let uu____15941 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15941
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15940 in
                         new_term_constant_from_string env1 x uu____15939 in
                       (match uu____15935 with
>>>>>>> origin/guido_tactics
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
<<<<<<< HEAD
                              let uu____15571 = FStar_Options.log_queries () in
                              if uu____15571
                              then
                                let uu____15573 =
                                  let uu____15574 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15575 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15576 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15574 uu____15575 uu____15576 in
                                Some uu____15573
=======
                              let uu____15952 = FStar_Options.log_queries () in
                              if uu____15952
                              then
                                let uu____15954 =
                                  let uu____15955 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15956 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15957 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15955 uu____15956 uu____15957 in
                                Some uu____15954
>>>>>>> origin/guido_tactics
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (Some a_name), a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
<<<<<<< HEAD
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15587,t)) ->
=======
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15968,t)) ->
>>>>>>> origin/guido_tactics
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
<<<<<<< HEAD
                 let uu____15596 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15596 with
=======
                 let uu____15977 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15977 with
>>>>>>> origin/guido_tactics
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
<<<<<<< HEAD
                 (uu____15609,se,uu____15611) ->
                 let uu____15614 = encode_sigelt env1 se in
                 (match uu____15614 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15624,se) ->
                 let uu____15628 = encode_sigelt env1 se in
                 (match uu____15628 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15638 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15638 with | (uu____15650,decls,env1) -> (decls, env1)
=======
                 (uu____15990,se,uu____15992) ->
                 let uu____15995 = encode_sigelt env1 se in
                 (match uu____15995 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16005,se) ->
                 let uu____16009 = encode_sigelt env1 se in
                 (match uu____16009 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16019 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16019 with | (uu____16031,decls,env1) -> (decls, env1)
>>>>>>> origin/guido_tactics
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
<<<<<<< HEAD
         (fun uu____15699  ->
            match uu____15699 with
            | (l,uu____15706,uu____15707) ->
=======
         (fun uu____16079  ->
            match uu____16079 with
            | (l,uu____16086,uu____16087) ->
>>>>>>> origin/guido_tactics
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
<<<<<<< HEAD
         (fun uu____15734  ->
            match uu____15734 with
            | (l,uu____15742,uu____15743) ->
                let uu____15748 =
=======
         (fun uu____16108  ->
            match uu____16108 with
            | (l,uu____16116,uu____16117) ->
                let uu____16122 =
>>>>>>> origin/guido_tactics
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45) (
                    fst l) in
<<<<<<< HEAD
                let uu____15749 =
                  let uu____15751 =
                    let uu____15752 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15752 in
                  [uu____15751] in
                uu____15748 :: uu____15749)) in
=======
                let uu____16123 =
                  let uu____16125 =
                    let uu____16126 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____16126 in
                  [uu____16125] in
                uu____16122 :: uu____16123)) in
>>>>>>> origin/guido_tactics
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
<<<<<<< HEAD
    let uu____15763 =
      let uu____15765 =
        let uu____15766 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15768 =
          let uu____15769 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15769 FStar_Ident.string_of_lid in
=======
    let uu____16138 =
      let uu____16140 =
        let uu____16141 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____16143 =
          let uu____16144 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____16144 FStar_Ident.string_of_lid in
>>>>>>> origin/guido_tactics
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
<<<<<<< HEAD
          cache = uu____15766;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15768
        } in
      [uu____15765] in
    FStar_ST.write last_env uu____15763
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15779 = FStar_ST.read last_env in
      match uu____15779 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15785 ->
          let uu___154_15787 = e in
          let uu____15788 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15787.bindings);
            depth = (uu___154_15787.depth);
            tcenv;
            warn = (uu___154_15787.warn);
            cache = (uu___154_15787.cache);
            nolabels = (uu___154_15787.nolabels);
            use_zfuel_name = (uu___154_15787.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15787.encode_non_total_function_typ);
            current_module_name = uu____15788
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15792 = FStar_ST.read last_env in
    match uu____15792 with
    | [] -> failwith "Empty env stack"
    | uu____15797::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15805  ->
    let uu____15806 = FStar_ST.read last_env in
    match uu____15806 with
=======
          cache = uu____16141;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____16143
        } in
      [uu____16140] in
    FStar_ST.write last_env uu____16138
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____16156 = FStar_ST.read last_env in
      match uu____16156 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16162 ->
          let uu___153_16164 = e in
          let uu____16165 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_16164.bindings);
            depth = (uu___153_16164.depth);
            tcenv;
            warn = (uu___153_16164.warn);
            cache = (uu___153_16164.cache);
            nolabels = (uu___153_16164.nolabels);
            use_zfuel_name = (uu___153_16164.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_16164.encode_non_total_function_typ);
            current_module_name = uu____16165
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____16170 = FStar_ST.read last_env in
    match uu____16170 with
    | [] -> failwith "Empty env stack"
    | uu____16175::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____16184  ->
    let uu____16185 = FStar_ST.read last_env in
    match uu____16185 with
>>>>>>> origin/guido_tactics
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
<<<<<<< HEAD
          let uu___155_15817 = hd1 in
          {
            bindings = (uu___155_15817.bindings);
            depth = (uu___155_15817.depth);
            tcenv = (uu___155_15817.tcenv);
            warn = (uu___155_15817.warn);
            cache = refs;
            nolabels = (uu___155_15817.nolabels);
            use_zfuel_name = (uu___155_15817.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15817.encode_non_total_function_typ);
            current_module_name = (uu___155_15817.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15823  ->
    let uu____15824 = FStar_ST.read last_env in
    match uu____15824 with
    | [] -> failwith "Popping an empty stack"
    | uu____15829::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15837  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15840  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15843  ->
    let uu____15844 = FStar_ST.read last_env in
    match uu____15844 with
    | hd1::uu____15850::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15856 -> failwith "Impossible"
=======
          let uu___154_16196 = hd1 in
          {
            bindings = (uu___154_16196.bindings);
            depth = (uu___154_16196.depth);
            tcenv = (uu___154_16196.tcenv);
            warn = (uu___154_16196.warn);
            cache = refs;
            nolabels = (uu___154_16196.nolabels);
            use_zfuel_name = (uu___154_16196.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_16196.encode_non_total_function_typ);
            current_module_name = (uu___154_16196.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____16203  ->
    let uu____16204 = FStar_ST.read last_env in
    match uu____16204 with
    | [] -> failwith "Popping an empty stack"
    | uu____16209::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____16218  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____16222  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____16226  ->
    let uu____16227 = FStar_ST.read last_env in
    match uu____16227 with
    | hd1::uu____16233::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____16239 -> failwith "Impossible"
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        | (uu____15905::uu____15906,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15912 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15912.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15912.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15912.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15913 -> d
=======
        | (uu____16298::uu____16299,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16303 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16303.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16303.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16303.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16304 -> d
>>>>>>> origin/guido_tactics
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
<<<<<<< HEAD
      let uu____15924 =
        let uu____15926 =
          let uu____15927 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15927 in
        let uu____15928 = open_fact_db_tags env in uu____15926 :: uu____15928 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15924
=======
      let uu____16317 =
        let uu____16319 =
          let uu____16320 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____16320 in
        let uu____16321 = open_fact_db_tags env in uu____16319 :: uu____16321 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16317
>>>>>>> origin/guido_tactics
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
<<<<<<< HEAD
      let uu____15943 = encode_sigelt env se in
      match uu____15943 with
=======
      let uu____16338 = encode_sigelt env se in
      match uu____16338 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____15968 = FStar_Options.log_queries () in
        if uu____15968
        then
          let uu____15970 =
            let uu____15971 =
              let uu____15972 =
                let uu____15973 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15973 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15972 in
            FStar_SMTEncoding_Term.Caption uu____15971 in
          uu____15970 :: decls
        else decls in
      let env =
        let uu____15980 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15980 tcenv in
      let uu____15981 = encode_top_level_facts env se in
      match uu____15981 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15990 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15990))
=======
        let uu____16365 = FStar_Options.log_queries () in
        if uu____16365
        then
          let uu____16367 =
            let uu____16368 =
              let uu____16369 =
                let uu____16370 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16370 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____16369 in
            FStar_SMTEncoding_Term.Caption uu____16368 in
          uu____16367 :: decls
        else decls in
      let env =
        let uu____16377 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16377 tcenv in
      let uu____16378 = encode_top_level_facts env se in
      match uu____16378 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16387 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____16387))
>>>>>>> origin/guido_tactics
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
<<<<<<< HEAD
      (let uu____16001 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16001
       then
         let uu____16002 =
=======
      (let uu____16400 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16400
       then
         let uu____16401 =
>>>>>>> origin/guido_tactics
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
<<<<<<< HEAD
           uu____16002
=======
           uu____16401
>>>>>>> origin/guido_tactics
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
<<<<<<< HEAD
              (fun uu____16030  ->
                 fun se  ->
                   match uu____16030 with
                   | (g,env2) ->
                       let uu____16042 = encode_top_level_facts env2 se in
                       (match uu____16042 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16055 =
         encode_signature
           (let uu___157_16061 = env in
            {
              bindings = (uu___157_16061.bindings);
              depth = (uu___157_16061.depth);
              tcenv = (uu___157_16061.tcenv);
              warn = false;
              cache = (uu___157_16061.cache);
              nolabels = (uu___157_16061.nolabels);
              use_zfuel_name = (uu___157_16061.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_16061.encode_non_total_function_typ);
              current_module_name = (uu___157_16061.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16055 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16073 = FStar_Options.log_queries () in
             if uu____16073
=======
              (fun uu____16424  ->
                 fun se  ->
                   match uu____16424 with
                   | (g,env2) ->
                       let uu____16436 = encode_top_level_facts env2 se in
                       (match uu____16436 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16449 =
         encode_signature
           (let uu___156_16453 = env in
            {
              bindings = (uu___156_16453.bindings);
              depth = (uu___156_16453.depth);
              tcenv = (uu___156_16453.tcenv);
              warn = false;
              cache = (uu___156_16453.cache);
              nolabels = (uu___156_16453.nolabels);
              use_zfuel_name = (uu___156_16453.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16453.encode_non_total_function_typ);
              current_module_name = (uu___156_16453.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16449 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16465 = FStar_Options.log_queries () in
             if uu____16465
>>>>>>> origin/guido_tactics
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
<<<<<<< HEAD
              (let uu___158_16080 = env1 in
               {
                 bindings = (uu___158_16080.bindings);
                 depth = (uu___158_16080.depth);
                 tcenv = (uu___158_16080.tcenv);
                 warn = true;
                 cache = (uu___158_16080.cache);
                 nolabels = (uu___158_16080.nolabels);
                 use_zfuel_name = (uu___158_16080.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_16080.encode_non_total_function_typ);
                 current_module_name = (uu___158_16080.current_module_name)
               });
            (let uu____16082 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16082
=======
              (let uu___157_16470 = env1 in
               {
                 bindings = (uu___157_16470.bindings);
                 depth = (uu___157_16470.depth);
                 tcenv = (uu___157_16470.tcenv);
                 warn = true;
                 cache = (uu___157_16470.cache);
                 nolabels = (uu___157_16470.nolabels);
                 use_zfuel_name = (uu___157_16470.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16470.encode_non_total_function_typ);
                 current_module_name = (uu___157_16470.current_module_name)
               });
            (let uu____16472 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16472
>>>>>>> origin/guido_tactics
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list*
          FStar_SMTEncoding_ErrorReporting.label Prims.list*
          FStar_SMTEncoding_Term.decl* FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
<<<<<<< HEAD
        (let uu____16117 =
           let uu____16118 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16118.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16117);
        (let env =
           let uu____16120 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16120 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16129 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16150 = aux rest in
                 (match uu____16150 with
                  | (out,rest1) ->
                      let t =
                        let uu____16168 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16168 with
                        | Some uu____16172 ->
                            let uu____16173 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16173
                              x.FStar_Syntax_Syntax.sort
                        | uu____16174 -> x.FStar_Syntax_Syntax.sort in
=======
        (let uu____16510 =
           let uu____16511 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16511.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16510);
        (let env =
           let uu____16513 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16513 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16520 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16541 = aux rest in
                 (match uu____16541 with
                  | (out,rest1) ->
                      let t =
                        let uu____16559 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16559 with
                        | Some uu____16563 ->
                            let uu____16564 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16564
                              x.FStar_Syntax_Syntax.sort
                        | uu____16565 -> x.FStar_Syntax_Syntax.sort in
>>>>>>> origin/guido_tactics
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
<<<<<<< HEAD
                      let uu____16177 =
                        let uu____16179 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_16182 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_16182.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_16182.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16179 :: out in
                      (uu____16177, rest1))
             | uu____16185 -> ([], bindings1) in
           let uu____16189 = aux bindings in
           match uu____16189 with
           | (closing,bindings1) ->
               let uu____16203 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16203, bindings1) in
         match uu____16129 with
         | (q1,bindings1) ->
             let uu____16216 =
               let uu____16219 =
                 FStar_List.filter
                   (fun uu___125_16223  ->
                      match uu___125_16223 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16224 ->
                          false
                      | uu____16228 -> true) bindings1 in
               encode_env_bindings env uu____16219 in
             (match uu____16216 with
              | (env_decls,env1) ->
                  ((let uu____16239 =
=======
                      let uu____16568 =
                        let uu____16570 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16571 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16571.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16571.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16570 :: out in
                      (uu____16568, rest1))
             | uu____16574 -> ([], bindings1) in
           let uu____16578 = aux bindings in
           match uu____16578 with
           | (closing,bindings1) ->
               let uu____16592 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16592, bindings1) in
         match uu____16520 with
         | (q1,bindings1) ->
             let uu____16605 =
               let uu____16608 =
                 FStar_List.filter
                   (fun uu___125_16610  ->
                      match uu___125_16610 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16611 ->
                          false
                      | uu____16615 -> true) bindings1 in
               encode_env_bindings env uu____16608 in
             (match uu____16605 with
              | (env_decls,env1) ->
                  ((let uu____16626 =
>>>>>>> origin/guido_tactics
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
<<<<<<< HEAD
                    if uu____16239
                    then
                      let uu____16240 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16240
                    else ());
                   (let uu____16242 = encode_formula q1 env1 in
                    match uu____16242 with
                    | (phi,qdecls) ->
                        let uu____16254 =
                          let uu____16257 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16257 phi in
                        (match uu____16254 with
                         | (labels,phi1) ->
                             let uu____16267 = encode_labels labels in
                             (match uu____16267 with
=======
                    if uu____16626
                    then
                      let uu____16627 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16627
                    else ());
                   (let uu____16629 = encode_formula q1 env1 in
                    match uu____16629 with
                    | (phi,qdecls) ->
                        let uu____16641 =
                          let uu____16644 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16644 phi in
                        (match uu____16641 with
                         | (labels,phi1) ->
                             let uu____16654 = encode_labels labels in
                             (match uu____16654 with
>>>>>>> origin/guido_tactics
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
<<<<<<< HEAD
                                    let uu____16288 =
                                      let uu____16292 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16293 =
                                        varops.mk_unique "@query" in
                                      (uu____16292, (Some "query"),
                                        uu____16293) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16288 in
=======
                                    let uu____16675 =
                                      let uu____16679 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16680 =
                                        varops.mk_unique "@query" in
                                      (uu____16679, (Some "query"),
                                        uu____16680) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16675 in
>>>>>>> origin/guido_tactics
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
<<<<<<< HEAD
        let uu____16306 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16306 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16308 = encode_formula q env in
       match uu____16308 with
       | (f,uu____16312) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16314) -> true
             | uu____16317 -> false)))
=======
        let uu____16695 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16695 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16697 = encode_formula q env in
       match uu____16697 with
       | (f,uu____16701) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16703) -> true
             | uu____16706 -> false)))
>>>>>>> origin/guido_tactics
