open Prims
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Term_sort
  | Fuel_sort
  | Array of (sort,sort) FStar_Pervasives_Native.tuple2
  | Arrow of (sort,sort) FStar_Pervasives_Native.tuple2
  | Sort of Prims.string
let uu___is_Bool_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____20 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____24 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____28 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____32 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____36 -> false
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____43 -> false
let __proj__Array__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____63 -> false
let __proj__Arrow__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____81 -> false
let __proj__Sort__item___0: sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0
let rec strSort: sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Fuel_sort  -> "Fuel"
    | Array (s1,s2) ->
        let uu____94 = strSort s1 in
        let uu____95 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____94 uu____95
    | Arrow (s1,s2) ->
        let uu____98 = strSort s1 in
        let uu____99 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____98 uu____99
    | Sort s -> s
type op =
  | TrueOp
  | FalseOp
  | Not
  | And
  | Or
  | Imp
  | Iff
  | Eq
  | LT
  | LTE
  | GT
  | GTE
  | Add
  | Sub
  | Div
  | Mul
  | Minus
  | Mod
  | ITE
  | Var of Prims.string
let uu___is_TrueOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____108 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____112 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____116 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____120 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____124 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____128 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____132 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____136 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____140 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____144 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____148 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____152 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____156 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____160 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____164 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____168 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____172 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____176 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____180 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____185 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____196 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____200 -> false
type term' =
  | Integer of Prims.string
  | BoundV of Prims.int
  | FreeV of (Prims.string,sort) FStar_Pervasives_Native.tuple2
  | App of (op,term Prims.list) FStar_Pervasives_Native.tuple2
  | Quant of
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
  sort Prims.list,term) FStar_Pervasives_Native.tuple5
  | Let of (term Prims.list,term) FStar_Pervasives_Native.tuple2
  | Labeled of (term,Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | LblPos of (term,Prims.string) FStar_Pervasives_Native.tuple2
and term =
  {
  tm: term';
  freevars:
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
      FStar_Syntax_Syntax.memo;
  rng: FStar_Range.range;}
let uu___is_Integer: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____276 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____288 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____302 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____323 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____353 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____395 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____419 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____442 -> false
let __proj__LblPos__item___0:
  term' -> (term,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LblPos _0 -> _0
type pat = term
type fv = (Prims.string,sort) FStar_Pervasives_Native.tuple2
type fvs = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
type caption = Prims.string FStar_Pervasives_Native.option
type binders = (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list
type constructor_field =
  (Prims.string,sort,Prims.bool) FStar_Pervasives_Native.tuple3
type constructor_t =
  (Prims.string,constructor_field Prims.list,sort,Prims.int,Prims.bool)
    FStar_Pervasives_Native.tuple5
type constructors = constructor_t Prims.list
type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____513 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____525 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____537 -> false
let __proj__Tag__item___0: fact_db_id -> Prims.string =
  fun projectee  -> match projectee with | Tag _0 -> _0
type assumption =
  {
  assumption_term: term;
  assumption_caption: caption;
  assumption_name: Prims.string;
  assumption_fact_ids: fact_db_id Prims.list;}
type decl =
  | DefPrelude
  | DeclFun of (Prims.string,sort Prims.list,sort,caption)
  FStar_Pervasives_Native.tuple4
  | DefineFun of (Prims.string,sort Prims.list,sort,term,caption)
  FStar_Pervasives_Native.tuple5
  | Assume of assumption
  | Caption of Prims.string
  | Eval of term
  | Echo of Prims.string
  | RetainAssumptions of Prims.string Prims.list
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption of (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  | GetStatistics
  | GetReasonUnknown
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____629 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____639 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____672 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____702 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____714 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____726 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____738 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____751 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____765 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____769 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____773 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____777 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____784 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____801 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____805 -> false
type decls_t = decl Prims.list
type error_label =
  (fv,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool =
  fun x  ->
    fun y  ->
      (FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y)
let fv_sort x = FStar_Pervasives_Native.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____842 -> false
let freevar_sort: term -> sort =
  fun uu___85_847  ->
    match uu___85_847 with
    | { tm = FreeV x; freevars = uu____849; rng = uu____850;_} -> fv_sort x
    | uu____857 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___86_860  ->
    match uu___86_860 with
    | { tm = FreeV fv; freevars = uu____862; rng = uu____863;_} -> fv
    | uu____870 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____880 -> []
    | BoundV uu____883 -> []
    | FreeV fv -> [fv]
    | App (uu____893,tms) -> FStar_List.collect freevars tms
    | Quant (uu____899,uu____900,uu____901,uu____902,t1) -> freevars t1
    | Labeled (t1,uu____913,uu____914) -> freevars t1
    | LblPos (t1,uu____916) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____926 = FStar_ST.read t.freevars in
    match uu____926 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____949 = freevars t in
          FStar_Util.remove_dups fv_eq uu____949 in
        (FStar_ST.write t.freevars (FStar_Pervasives_Native.Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___87_961  ->
    match uu___87_961 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___88_964  ->
    match uu___88_964 with
    | TrueOp  -> "true"
    | FalseOp  -> "false"
    | Not  -> "not"
    | And  -> "and"
    | Or  -> "or"
    | Imp  -> "implies"
    | Iff  -> "iff"
    | Eq  -> "="
    | LT  -> "<"
    | LTE  -> "<="
    | GT  -> ">"
    | GTE  -> ">="
    | Add  -> "+"
    | Sub  -> "-"
    | Div  -> "div"
    | Mul  -> "*"
    | Minus  -> "-"
    | Mod  -> "mod"
    | ITE  -> "ite"
    | Var s -> s
let weightToSmt: Prims.int FStar_Pervasives_Native.option -> Prims.string =
  fun uu___89_969  ->
    match uu___89_969 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____972 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____972
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____980 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____980
    | FreeV x ->
        let uu____984 =
          let uu____985 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____985 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____984
    | App (op,tms) ->
        let uu____990 =
          let uu____991 =
            let uu____992 =
              let uu____993 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____993 (FStar_String.concat " ") in
            Prims.strcat uu____992 ")" in
          Prims.strcat (op_to_string op) uu____991 in
        Prims.strcat "(" uu____990
    | Labeled (t1,r1,r2) ->
        let uu____999 = hash_of_term t1 in
        let uu____1000 =
          let uu____1001 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1001 in
        Prims.strcat uu____999 uu____1000
    | LblPos (t1,r) ->
        let uu____1004 =
          let uu____1005 = hash_of_term t1 in
          Prims.strcat uu____1005
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1004
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1019 =
          let uu____1020 =
            let uu____1021 =
              let uu____1022 =
                let uu____1023 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1023 (FStar_String.concat " ") in
              let uu____1026 =
                let uu____1027 =
                  let uu____1028 = hash_of_term body in
                  let uu____1029 =
                    let uu____1030 =
                      let uu____1031 = weightToSmt wopt in
                      let uu____1032 =
                        let uu____1033 =
                          let uu____1034 =
                            let uu____1035 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1043 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1043
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1035
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1034 "))" in
                        Prims.strcat " " uu____1033 in
                      Prims.strcat uu____1031 uu____1032 in
                    Prims.strcat " " uu____1030 in
                  Prims.strcat uu____1028 uu____1029 in
                Prims.strcat ")(! " uu____1027 in
              Prims.strcat uu____1022 uu____1026 in
            Prims.strcat " (" uu____1021 in
          Prims.strcat (qop_to_string qop) uu____1020 in
        Prims.strcat "(" uu____1019
    | Let (es,body) ->
        let uu____1051 =
          let uu____1052 =
            let uu____1053 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1053 (FStar_String.concat " ") in
          let uu____1056 =
            let uu____1057 =
              let uu____1058 = hash_of_term body in
              Prims.strcat uu____1058 ")" in
            Prims.strcat ") " uu____1057 in
          Prims.strcat uu____1052 uu____1056 in
        Prims.strcat "(let (" uu____1051
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1066 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1066; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1095 =
        let uu____1096 = FStar_Util.ensure_decimal i in Integer uu____1096 in
      mk uu____1095 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1103 = FStar_Util.string_of_int i in mkInteger uu____1103 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun x  -> fun r  -> mk (FreeV x) r
let mkApp':
  (op,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  = fun f  -> fun r  -> mk (App f) r
let mkApp:
  (Prims.string,term Prims.list) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____1139  ->
    fun r  -> match uu____1139 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1155) -> mkFalse r
      | App (FalseOp ,uu____1158) -> mkTrue r
      | uu____1161 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1169  ->
    fun r  ->
      match uu____1169 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1175),uu____1176) -> t2
           | (uu____1179,App (TrueOp ,uu____1180)) -> t1
           | (App (FalseOp ,uu____1183),uu____1184) -> mkFalse r
           | (uu____1187,App (FalseOp ,uu____1188)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1198,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1204) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1208 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1218  ->
    fun r  ->
      match uu____1218 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1224),uu____1225) -> mkTrue r
           | (uu____1228,App (TrueOp ,uu____1229)) -> mkTrue r
           | (App (FalseOp ,uu____1232),uu____1233) -> t2
           | (uu____1236,App (FalseOp ,uu____1237)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1247,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1253) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1257 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1267  ->
    fun r  ->
      match uu____1267 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____1273,App (TrueOp ,uu____1274)) -> mkTrue r
           | (App (FalseOp ,uu____1277),uu____1278) -> mkTrue r
           | (App (TrueOp ,uu____1281),uu____1282) -> t2
           | (uu____1285,App (Imp ,t1'::t2'::[])) ->
               let uu____1289 =
                 let uu____1293 =
                   let uu____1295 = mkAnd (t1, t1') r in [uu____1295; t2'] in
                 (Imp, uu____1293) in
               mkApp' uu____1289 r
           | uu____1297 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____1310  ->
      fun r  -> match uu____1310 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
let mkMinus: term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r
let mkIff:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Iff
let mkEq:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Eq
let mkLT:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LT
let mkLTE:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op LTE
let mkGT:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GT
let mkGTE:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op GTE
let mkAdd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Add
let mkSub:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Sub
let mkDiv:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Div
let mkMul:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mul
let mkMod:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  mk_bin_op Mod
let mkITE:
  (term,term,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____1397  ->
    fun r  ->
      match uu____1397 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1405) -> t2
           | App (FalseOp ,uu____1408) -> t3
           | uu____1411 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1412),App (TrueOp ,uu____1413)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1418),uu____1419) ->
                    let uu____1422 =
                      let uu____1425 = mkNot t1 t1.rng in (uu____1425, t3) in
                    mkImp uu____1422 r
                | (uu____1426,App (TrueOp ,uu____1427)) -> mkImp (t1, t2) r
                | (uu____1430,uu____1431) -> mkApp' (ITE, [t1; t2; t3]) r))
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
let mkQuant:
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____1459  ->
    fun r  ->
      match uu____1459 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1486) -> body
             | uu____1489 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____1501  ->
    fun r  ->
      match uu____1501 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1529 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1529 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____1543 = FStar_ST.read t1.freevars in
        match uu____1543 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____1559 ->
            (match t1.tm with
             | Integer uu____1564 -> t1
             | BoundV uu____1565 -> t1
             | FreeV x ->
                 let uu____1569 = index_of x in
                 (match uu____1569 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1576 =
                   let uu____1580 = FStar_List.map (aux ix) tms in
                   (op, uu____1580) in
                 mkApp' uu____1576 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1586 =
                   let uu____1587 =
                     let uu____1591 = aux ix t2 in (uu____1591, r1, r2) in
                   Labeled uu____1587 in
                 mk uu____1586 t2.rng
             | LblPos (t2,r) ->
                 let uu____1594 =
                   let uu____1595 =
                     let uu____1598 = aux ix t2 in (uu____1598, r) in
                   LblPos uu____1595 in
                 mk uu____1594 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____1614 =
                   let uu____1624 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____1635 = aux (ix + n1) body in
                   (qop, uu____1624, wopt, vars, uu____1635) in
                 mkQuant uu____1614 t1.rng
             | Let (es,body) ->
                 let uu____1646 =
                   FStar_List.fold_left
                     (fun uu____1653  ->
                        fun e  ->
                          match uu____1653 with
                          | (ix1,l) ->
                              let uu____1665 =
                                let uu____1667 = aux ix1 e in uu____1667 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____1665))
                     (ix, []) es in
                 (match uu____1646 with
                  | (ix1,es_rev) ->
                      let uu____1674 =
                        let uu____1678 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____1678) in
                      mkLet uu____1674 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____1699 -> t1
        | FreeV uu____1700 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____1711 =
              let uu____1715 = FStar_List.map (aux shift) tms2 in
              (op, uu____1715) in
            mkApp' uu____1711 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1721 =
              let uu____1722 =
                let uu____1726 = aux shift t2 in (uu____1726, r1, r2) in
              Labeled uu____1722 in
            mk uu____1721 t2.rng
        | LblPos (t2,r) ->
            let uu____1729 =
              let uu____1730 =
                let uu____1733 = aux shift t2 in (uu____1733, r) in
              LblPos uu____1730 in
            mk uu____1729 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____1752 =
              let uu____1762 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____1771 = aux shift1 body in
              (qop, uu____1762, wopt, vars, uu____1771) in
            mkQuant uu____1752 t1.rng
        | Let (es,body) ->
            let uu____1780 =
              FStar_List.fold_left
                (fun uu____1787  ->
                   fun e  ->
                     match uu____1787 with
                     | (ix,es1) ->
                         let uu____1799 =
                           let uu____1801 = aux shift e in uu____1801 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____1799))
                (shift, []) es in
            (match uu____1780 with
             | (shift1,es_rev) ->
                 let uu____1808 =
                   let uu____1812 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____1812) in
                 mkLet uu____1808 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____1823 = abstr [fv] t in inst [s] uu____1823
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____1837  ->
    match uu____1837 with
    | (qop,pats,wopt,vars,body) ->
        let uu____1862 =
          let uu____1872 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____1881 = FStar_List.map fv_sort vars in
          let uu____1885 = abstr vars body in
          (qop, uu____1872, wopt, uu____1881, uu____1885) in
        mkQuant uu____1862
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____1902  ->
    fun r  ->
      match uu____1902 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____1939  ->
    fun r  ->
      match uu____1939 with
      | (pats,wopt,vars,body) ->
          let uu____1958 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____1958 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____1973  ->
    fun r  ->
      match uu____1973 with
      | (pats,vars,body) ->
          let uu____1987 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____1987 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2002  ->
    fun r  ->
      match uu____2002 with
      | (pats,vars,body) ->
          let uu____2016 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2016 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____2031  ->
    fun r  ->
      match uu____2031 with
      | (bindings,body) ->
          let uu____2046 = FStar_List.split bindings in
          (match uu____2046 with
           | (vars,es) ->
               let uu____2057 =
                 let uu____2061 = abstr vars body in (es, uu____2061) in
               mkLet uu____2057 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____2073  ->
    match uu____2073 with
    | (nm,vars,s,tm,c) ->
        let uu____2093 =
          let uu____2100 = FStar_List.map fv_sort vars in
          let uu____2104 = abstr vars tm in
          (nm, uu____2100, s, uu____2104, c) in
        DefineFun uu____2093
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____2109 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____2109
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____2116  ->
    fun id  ->
      match uu____2116 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____2124 =
              let uu____2125 =
                let uu____2128 = mkInteger' id norng in
                let uu____2129 =
                  let uu____2130 =
                    let uu____2134 = constr_id_of_sort sort in
                    let uu____2135 =
                      let uu____2137 = mkApp (tok_name, []) norng in
                      [uu____2137] in
                    (uu____2134, uu____2135) in
                  mkApp uu____2130 norng in
                (uu____2128, uu____2129) in
              mkEq uu____2125 norng in
            {
              assumption_term = uu____2124;
              assumption_caption =
                (FStar_Pervasives_Native.Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            } in
          Assume a
let fresh_constructor:
  (Prims.string,sort Prims.list,sort,Prims.int)
    FStar_Pervasives_Native.tuple4 -> decl
  =
  fun uu____2147  ->
    match uu____2147 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2166 =
                      let uu____2169 =
                        let uu____2170 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2170 in
                      (uu____2169, s) in
                    mkFreeV uu____2166 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2176 =
            let uu____2180 = constr_id_of_sort sort in (uu____2180, [capp]) in
          mkApp uu____2176 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____2184 =
            let uu____2185 =
              let uu____2191 =
                let uu____2192 =
                  let uu____2195 = mkInteger id1 norng in
                  (uu____2195, cid_app) in
                mkEq uu____2192 norng in
              ([[capp]], bvar_names, uu____2191) in
            mkForall uu____2185 norng in
          {
            assumption_term = uu____2184;
            assumption_caption =
              (FStar_Pervasives_Native.Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          } in
        Assume a
let injective_constructor:
  (Prims.string,constructor_field Prims.list,sort)
    FStar_Pervasives_Native.tuple3 -> decl Prims.list
  =
  fun uu____2207  ->
    match uu____2207 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2223 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2223 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2240 = let uu____2243 = bvar_name i in (uu____2243, s) in
          mkFreeV uu____2240 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2252  ->
                    match uu____2252 with
                    | (uu____2256,s,uu____2258) ->
                        let uu____2259 = bvar i s in uu____2259 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2266 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2277  ->
                    match uu____2277 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____2292 =
                              let uu____2293 =
                                let uu____2299 =
                                  let uu____2300 =
                                    let uu____2303 =
                                      let uu____2304 = bvar i s in
                                      uu____2304 norng in
                                    (cproj_app, uu____2303) in
                                  mkEq uu____2300 norng in
                                ([[capp]], bvar_names, uu____2299) in
                              mkForall uu____2293 norng in
                            {
                              assumption_term = uu____2292;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____2266 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2318  ->
    match uu____2318 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2334  ->
                  match uu____2334 with
                  | (uu____2338,sort1,uu____2340) -> sort1)) in
        let cdecl =
          DeclFun
            (name, field_sorts, sort,
              (FStar_Pervasives_Native.Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____2353 =
              let uu____2356 =
                let uu____2357 =
                  let uu____2361 = constr_id_of_sort sort in
                  (uu____2361, [xx]) in
                mkApp uu____2357 norng in
              let uu____2363 =
                let uu____2364 = FStar_Util.string_of_int id in
                mkInteger uu____2364 norng in
              (uu____2356, uu____2363) in
            mkEq uu____2353 norng in
          let uu____2365 =
            let uu____2373 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2396  ->
                        match uu____2396 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2413 = mkApp (proj, [xx]) norng in
                              (uu____2413, [])
                            else
                              (let fi =
                                 let uu____2424 =
                                   let uu____2425 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2425 in
                                 (uu____2424, s) in
                               let uu____2426 = mkFreeV fi norng in
                               (uu____2426, [fi])))) in
            FStar_All.pipe_right uu____2373 FStar_List.split in
          match uu____2365 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____2469 =
                  let uu____2472 = mkApp (name, proj_terms) norng in
                  (xx, uu____2472) in
                mkEq uu____2469 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2477 -> mkExists ([], ex_vars1, disc_inv_body) norng in
              let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (FStar_Pervasives_Native.Some "Discriminator definition")) in
              def in
        let projs =
          if injective1
          then injective_constructor (name, fields, sort)
          else [] in
        let uu____2500 =
          let uu____2502 =
            let uu____2503 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____2503 in
          uu____2502 :: cdecl :: cid :: projs in
        let uu____2504 =
          let uu____2506 =
            let uu____2508 =
              let uu____2509 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____2509 in
            [uu____2508] in
          FStar_List.append [disc] uu____2506 in
        FStar_List.append uu____2500 uu____2504
let name_binders_inner:
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
            Prims.string Prims.list,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____2539 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2562  ->
                    fun s  ->
                      match uu____2562 with
                      | (names,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2590 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____2594 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____2594 in
                          let names1 = (nm, s) :: names in
                          let b =
                            let uu____2602 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____2602 in
                          (names1, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____2539 with
          | (names,binders,n1) -> (names, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____2644 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____2644 with
    | (names,binders,n1) -> ((FStar_List.rev names), binders)
let termToSmt: Prims.string -> term -> Prims.string =
  fun enclosing_name  ->
    fun t  ->
      let next_qid =
        let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
        fun depth  ->
          let n1 = FStar_ST.read ctr in
          FStar_Util.incr ctr;
          if n1 = (Prims.parse_int "0")
          then enclosing_name
          else
            (let uu____2698 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____2698) in
      let remove_guard_free pats =
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun ps  ->
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun tm  ->
                        match tm.tm with
                        | App
                            (Var
                             "Prims.guard_free",{ tm = BoundV uu____2720;
                                                  freevars = uu____2721;
                                                  rng = uu____2722;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____2730 -> tm)))) in
      let rec aux' depth n1 names t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____2766 = FStar_List.nth names i in
            FStar_All.pipe_right uu____2766 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____2776 =
              let uu____2777 = FStar_List.map (aux1 n1 names) tms in
              FStar_All.pipe_right uu____2777 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2776
        | Labeled (t2,uu____2781,uu____2782) -> aux1 n1 names t2
        | LblPos (t2,s) ->
            let uu____2785 = aux1 n1 names t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____2785 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____2800 =
              name_binders_inner FStar_Pervasives_Native.None names n1 sorts in
            (match uu____2800 with
             | (names1,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____2828 ->
                       let uu____2831 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____2839 =
                                   let uu____2840 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____2843 = aux1 n2 names1 p in
                                          FStar_Util.format1 "%s" uu____2843)
                                       pats2 in
                                   FStar_String.concat " " uu____2840 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____2839)) in
                       FStar_All.pipe_right uu____2831
                         (FStar_String.concat "\n") in
                 let uu____2845 =
                   let uu____2847 =
                     let uu____2849 =
                       let uu____2851 = aux1 n2 names1 body in
                       let uu____2852 =
                         let uu____2854 = weightToSmt wopt in
                         [uu____2854; pats_str; qid] in
                       uu____2851 :: uu____2852 in
                     binders1 :: uu____2849 in
                   (qop_to_string qop) :: uu____2847 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____2845)
        | Let (es,body) ->
            let uu____2859 =
              FStar_List.fold_left
                (fun uu____2874  ->
                   fun e  ->
                     match uu____2874 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____2902 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____2902 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____2910 = aux1 n1 names e in
                           FStar_Util.format2 "(%s %s)" nm uu____2910 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names, [], n1) es in
            (match uu____2859 with
             | (names1,binders,n2) ->
                 let uu____2928 = aux1 n2 names1 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____2928)
      and aux depth n1 names t1 =
        let s = aux' depth n1 names t1 in
        if t1.rng <> norng
        then
          let uu____2935 = FStar_Range.string_of_range t1.rng in
          let uu____2936 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2935
            uu____2936 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___90_2941  ->
    match uu___90_2941 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____2944 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____2953 -> (hd1, "...") in
        (match uu____2944 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____2970 = FStar_Options.log_queries () in
          if uu____2970
          then
            let uu____2971 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___91_2973  ->
                   match uu___91_2973 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____2971
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____2987 = caption_to_string c in
          let uu____2988 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2987 f
            (FStar_String.concat " " l) uu____2988
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2996 = name_macro_binders arg_sorts in
          (match uu____2996 with
           | (names,binders) ->
               let body1 =
                 let uu____3014 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names in
                 inst uu____3014 body in
               let uu____3021 = caption_to_string c in
               let uu____3022 = strSort retsort in
               let uu____3023 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____3021
                 f (FStar_String.concat " " binders) uu____3022 uu____3023)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___92_3034  ->
                    match uu___92_3034 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____3039 = FStar_Options.log_queries () in
            if uu____3039
            then
              let uu____3040 =
                let uu____3041 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____3041 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____3040
            else "" in
          let n1 = escape a.assumption_name in
          let uu____3045 = caption_to_string a.assumption_caption in
          let uu____3046 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3045 fids
            uu____3046 n1
      | Eval t ->
          let uu____3048 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____3048
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____3050 -> ""
      | CheckSat  -> "(check-sat)"
      | GetUnsatCore  ->
          "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
      | Push  -> "(push)"
      | Pop  -> "(pop)"
      | SetOption (s,v1) -> FStar_Util.format2 "(set-option :%s %s)" s v1
      | GetStatistics  ->
          "(echo \"<statistics>\")\n(get-info :all-statistics)\n(echo \"</statistics>\")"
      | GetReasonUnknown  ->
          "(echo \"<reason-unknown>\")\n(get-info :reason-unknown)\n(echo \"</reason-unknown>\")"
and mkPrelude: Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))" in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort, true)],
         String_sort, (Prims.parse_int "0"), true);
      ("Tm_type", [], Term_sort, (Prims.parse_int "2"), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
        (Prims.parse_int "3"), false);
      ("Tm_unit", [], Term_sort, (Prims.parse_int "6"), true);
      ("BoxInt", [("BoxInt_proj_0", Int_sort, true)], Term_sort,
        (Prims.parse_int "7"), true);
      ("BoxBool", [("BoxBool_proj_0", Bool_sort, true)], Term_sort,
        (Prims.parse_int "8"), true);
      ("BoxString", [("BoxString_proj_0", String_sort, true)], Term_sort,
        (Prims.parse_int "9"), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true)],
        Term_sort, (Prims.parse_int "11"), true)] in
    let bcons =
      let uu____3216 =
        let uu____3218 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3218
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3216 (FStar_String.concat "\n") in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n" in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)
let mk_Range_const: term = mkApp ("Range_const", []) norng
let mk_Term_type: term = mkApp ("Tm_type", []) norng
let mk_Term_app: term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r
let mk_Term_uvar: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3243 =
        let uu____3247 = let uu____3249 = mkInteger' i norng in [uu____3249] in
        ("Tm_uvar", uu____3247) in
      mkApp uu____3243 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        match t.tm with
        | App (Var v',t1::[]) when
            (v1 = v') && (FStar_Options.smtencoding_elim_box ()) -> t1
        | uu____3264 -> mkApp (u, [t]) t.rng
let boxInt: term -> term =
  fun t  -> maybe_elim_box "BoxInt" "BoxInt_proj_0" t
let unboxInt: term -> term =
  fun t  -> maybe_elim_box "BoxInt_proj_0" "BoxInt" t
let boxBool: term -> term =
  fun t  -> maybe_elim_box "BoxBool" "BoxBool_proj_0" t
let unboxBool: term -> term =
  fun t  -> maybe_elim_box "BoxBool_proj_0" "BoxBool" t
let boxString: term -> term =
  fun t  -> maybe_elim_box "BoxString" "BoxString_proj_0" t
let unboxString: term -> term =
  fun t  -> maybe_elim_box "BoxString_proj_0" "BoxString" t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | uu____3290 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | uu____3297 -> raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3305::t1::t2::[]);
                       freevars = uu____3308; rng = uu____3309;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3316::t1::t2::[]);
                       freevars = uu____3319; rng = uu____3320;_}::[])
        -> let uu____3327 = mkEq (t1, t2) norng in mkNot uu____3327 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3330; rng = uu____3331;_}::[])
        ->
        let uu____3338 =
          let uu____3341 = unboxInt t1 in
          let uu____3342 = unboxInt t2 in (uu____3341, uu____3342) in
        mkLTE uu____3338 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3345; rng = uu____3346;_}::[])
        ->
        let uu____3353 =
          let uu____3356 = unboxInt t1 in
          let uu____3357 = unboxInt t2 in (uu____3356, uu____3357) in
        mkLT uu____3353 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3360; rng = uu____3361;_}::[])
        ->
        let uu____3368 =
          let uu____3371 = unboxInt t1 in
          let uu____3372 = unboxInt t2 in (uu____3371, uu____3372) in
        mkGTE uu____3368 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3375; rng = uu____3376;_}::[])
        ->
        let uu____3383 =
          let uu____3386 = unboxInt t1 in
          let uu____3387 = unboxInt t2 in (uu____3386, uu____3387) in
        mkGT uu____3383 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3390; rng = uu____3391;_}::[])
        ->
        let uu____3398 =
          let uu____3401 = unboxBool t1 in
          let uu____3402 = unboxBool t2 in (uu____3401, uu____3402) in
        mkAnd uu____3398 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3405; rng = uu____3406;_}::[])
        ->
        let uu____3413 =
          let uu____3416 = unboxBool t1 in
          let uu____3417 = unboxBool t2 in (uu____3416, uu____3417) in
        mkOr uu____3413 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3419; rng = uu____3420;_}::[])
        -> let uu____3427 = unboxBool t1 in mkNot uu____3427 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___93_3430 = unboxBool t1 in
        {
          tm = (uu___93_3430.tm);
          freevars = (uu___93_3430.freevars);
          rng = (t.rng)
        }
    | uu____3433 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3462 = FStar_Options.unthrottle_inductives () in
        if uu____3462
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let mk_HasTypeWithFuel:
  term FStar_Pervasives_Native.option -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | FStar_Pervasives_Native.None  -> mk_HasType v1 t
        | FStar_Pervasives_Native.Some f1 -> mk_HasTypeFuel f1 v1 t
let mk_NoHoist: term -> term -> term =
  fun dummy  -> fun b  -> mkApp ("NoHoist", [dummy; b]) b.rng
let mk_Destruct: term -> FStar_Range.range -> term =
  fun v1  -> mkApp ("Destruct", [v1])
let mk_Rank: term -> FStar_Range.range -> term =
  fun x  -> mkApp ("Rank", [x])
let mk_tester: Prims.string -> term -> term =
  fun n1  -> fun t  -> mkApp ((Prims.strcat "is-" n1), [t]) t.rng
let mk_ApplyTF: term -> term -> term =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng
let mk_ApplyTT: term -> term -> FStar_Range.range -> term =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r
let mk_String_const: Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3526 =
        let uu____3530 = let uu____3532 = mkInteger' i norng in [uu____3532] in
        ("FString_const", uu____3530) in
      mkApp uu____3526 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3543 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____3543 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3560 =
         let uu____3564 =
           let uu____3566 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____3566] in
         ("SFuel", uu____3564) in
       mkApp uu____3560 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term FStar_Pervasives_Native.option ->
    term FStar_Pervasives_Native.option ->
      FStar_Range.range -> term FStar_Pervasives_Native.option
  =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (FStar_Pervasives_Native.Some p11,FStar_Pervasives_Native.Some p21)
            ->
            let uu____3589 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____3589
        | (FStar_Pervasives_Native.Some p,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some p) ->
            FStar_Pervasives_Native.Some p
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            FStar_Pervasives_Native.None
let mk_and_opt_l:
  term FStar_Pervasives_Native.option Prims.list ->
    FStar_Range.range -> term FStar_Pervasives_Native.option
  =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        FStar_Pervasives_Native.None
let mk_and_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3623 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3623
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3634 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3634
let mk_haseq: term -> term =
  fun t  ->
    let uu____3640 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____3640
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3654 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____3654
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____3662 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3662
    | Labeled (t1,r1,r2) ->
        let uu____3666 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3666
    | LblPos (t1,s) ->
        let uu____3669 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3669
    | Quant (qop,l,uu____3672,uu____3673,t1) ->
        let uu____3683 = print_smt_term_list_list l in
        let uu____3684 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3683
          uu____3684
    | Let (es,body) ->
        let uu____3689 = print_smt_term_list es in
        let uu____3690 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____3689 uu____3690
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____3693 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____3693 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3703 =
             let uu____3704 =
               let uu____3705 = print_smt_term_list l1 in
               Prims.strcat uu____3705 " ] " in
             Prims.strcat "; [ " uu____3704 in
           Prims.strcat s uu____3703) "" l