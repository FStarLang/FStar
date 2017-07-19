open Prims
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Ref_sort
  | Term_sort
  | Fuel_sort
  | Array of (sort,sort) FStar_Pervasives_Native.tuple2
  | Arrow of (sort,sort) FStar_Pervasives_Native.tuple2
  | Sort of Prims.string
let uu___is_Bool_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____24 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____28 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____32 -> false
let uu___is_Ref_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____36 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____40 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____44 -> false
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____53 -> false
let __proj__Array__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____81 -> false
let __proj__Arrow__item___0:
  sort -> (sort,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____105 -> false
let __proj__Sort__item___0: sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0
let rec strSort: sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Ref_sort  -> "Ref"
    | Fuel_sort  -> "Fuel"
    | Array (s1,s2) ->
        let uu____118 = strSort s1 in
        let uu____119 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____118 uu____119
    | Arrow (s1,s2) ->
        let uu____122 = strSort s1 in
        let uu____123 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____122 uu____123
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
    match projectee with | TrueOp  -> true | uu____132 -> false
let uu___is_FalseOp: op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____136 -> false
let uu___is_Not: op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____140 -> false
let uu___is_And: op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____144 -> false
let uu___is_Or: op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____148 -> false
let uu___is_Imp: op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____152 -> false
let uu___is_Iff: op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____156 -> false
let uu___is_Eq: op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____160 -> false
let uu___is_LT: op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____164 -> false
let uu___is_LTE: op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____168 -> false
let uu___is_GT: op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____172 -> false
let uu___is_GTE: op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____176 -> false
let uu___is_Add: op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____180 -> false
let uu___is_Sub: op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____184 -> false
let uu___is_Div: op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____188 -> false
let uu___is_Mul: op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____192 -> false
let uu___is_Minus: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____196 -> false
let uu___is_Mod: op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____200 -> false
let uu___is_ITE: op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____204 -> false
let uu___is_Var: op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____209 -> false
let __proj__Var__item___0: op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0
type qop =
  | Forall
  | Exists
let uu___is_Forall: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____220 -> false
let uu___is_Exists: qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____224 -> false
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
    match projectee with | Integer _0 -> true | uu____326 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____338 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____354 -> false
let __proj__FreeV__item___0:
  term' -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____384 -> false
let __proj__App__item___0:
  term' -> (op,term Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____432 -> false
let __proj__Quant__item___0:
  term' ->
    (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
      sort Prims.list,term) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____504 -> false
let __proj__Let__item___0:
  term' -> (term Prims.list,term) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____540 -> false
let __proj__Labeled__item___0:
  term' ->
    (term,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____574 -> false
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
    match projectee with | Name _0 -> true | uu____678 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____690 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____702 -> false
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
    match projectee with | DefPrelude  -> true | uu____811 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____826 -> false
let __proj__DeclFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,caption)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____880 -> false
let __proj__DefineFun__item___0:
  decl ->
    (Prims.string,sort Prims.list,sort,term,caption)
      FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____928 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____940 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____952 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____964 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____978 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____995 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____999 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____1003 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____1007 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____1016 -> false
let __proj__SetOption__item___0:
  decl -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____1039 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____1043 -> false
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
      | uu____1093 -> false
let freevar_sort: term -> sort =
  fun uu___85_1100  ->
    match uu___85_1100 with
    | { tm = FreeV x; freevars = uu____1102; rng = uu____1103;_} -> fv_sort x
    | uu____1116 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___86_1119  ->
    match uu___86_1119 with
    | { tm = FreeV fv; freevars = uu____1121; rng = uu____1122;_} -> fv
    | uu____1135 -> failwith "impossible"
let rec freevars:
  term -> (Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list =
  fun t  ->
    match t.tm with
    | Integer uu____1151 -> []
    | BoundV uu____1156 -> []
    | FreeV fv -> [fv]
    | App (uu____1174,tms) -> FStar_List.collect freevars tms
    | Quant (uu____1184,uu____1185,uu____1186,uu____1187,t1) -> freevars t1
    | Labeled (t1,uu____1206,uu____1207) -> freevars t1
    | LblPos (t1,uu____1209) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____1223 = FStar_ST.read t.freevars in
    match uu____1223 with
    | FStar_Pervasives_Native.Some b -> b
    | FStar_Pervasives_Native.None  ->
        let fvs =
          let uu____1262 = freevars t in
          FStar_Util.remove_dups fv_eq uu____1262 in
        (FStar_ST.write t.freevars (FStar_Pervasives_Native.Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___87_1278  ->
    match uu___87_1278 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___88_1281  ->
    match uu___88_1281 with
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
  fun uu___89_1287  ->
    match uu___89_1287 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some i ->
        let uu____1291 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____1291
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____1299 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____1299
    | FreeV x ->
        let uu____1305 =
          let uu____1306 = strSort (FStar_Pervasives_Native.snd x) in
          Prims.strcat ":" uu____1306 in
        Prims.strcat (FStar_Pervasives_Native.fst x) uu____1305
    | App (op,tms) ->
        let uu____1313 =
          let uu____1314 =
            let uu____1315 =
              let uu____1316 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____1316 (FStar_String.concat " ") in
            Prims.strcat uu____1315 ")" in
          Prims.strcat (op_to_string op) uu____1314 in
        Prims.strcat "(" uu____1313
    | Labeled (t1,r1,r2) ->
        let uu____1324 = hash_of_term t1 in
        let uu____1325 =
          let uu____1326 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____1326 in
        Prims.strcat uu____1324 uu____1325
    | LblPos (t1,r) ->
        let uu____1329 =
          let uu____1330 = hash_of_term t1 in
          Prims.strcat uu____1330
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____1329
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____1352 =
          let uu____1353 =
            let uu____1354 =
              let uu____1355 =
                let uu____1356 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____1356 (FStar_String.concat " ") in
              let uu____1361 =
                let uu____1362 =
                  let uu____1363 = hash_of_term body in
                  let uu____1364 =
                    let uu____1365 =
                      let uu____1366 = weightToSmt wopt in
                      let uu____1367 =
                        let uu____1368 =
                          let uu____1369 =
                            let uu____1370 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1384 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1384
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1370
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1369 "))" in
                        Prims.strcat " " uu____1368 in
                      Prims.strcat uu____1366 uu____1367 in
                    Prims.strcat " " uu____1365 in
                  Prims.strcat uu____1363 uu____1364 in
                Prims.strcat ")(! " uu____1362 in
              Prims.strcat uu____1355 uu____1361 in
            Prims.strcat " (" uu____1354 in
          Prims.strcat (qop_to_string qop) uu____1353 in
        Prims.strcat "(" uu____1352
    | Let (es,body) ->
        let uu____1397 =
          let uu____1398 =
            let uu____1399 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1399 (FStar_String.concat " ") in
          let uu____1404 =
            let uu____1405 =
              let uu____1406 = hash_of_term body in
              Prims.strcat uu____1406 ")" in
            Prims.strcat ") " uu____1405 in
          Prims.strcat uu____1398 uu____1404 in
        Prims.strcat "(let (" uu____1397
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1414 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
      { tm = t; freevars = uu____1414; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1455 =
        let uu____1456 = FStar_Util.ensure_decimal i in Integer uu____1456 in
      mk uu____1455 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1463 = FStar_Util.string_of_int i in mkInteger uu____1463 r
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
  fun uu____1512  ->
    fun r  -> match uu____1512 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1534) -> mkFalse r
      | App (FalseOp ,uu____1539) -> mkTrue r
      | uu____1544 -> mkApp' (Not, [t]) r
let mkAnd:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1555  ->
    fun r  ->
      match uu____1555 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1563),uu____1564) -> t2
           | (uu____1569,App (TrueOp ,uu____1570)) -> t1
           | (App (FalseOp ,uu____1575),uu____1576) -> mkFalse r
           | (uu____1581,App (FalseOp ,uu____1582)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1599,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1608) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1615 -> mkApp' (And, [t1; t2]) r)
let mkOr:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1630  ->
    fun r  ->
      match uu____1630 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1638),uu____1639) -> mkTrue r
           | (uu____1644,App (TrueOp ,uu____1645)) -> mkTrue r
           | (App (FalseOp ,uu____1650),uu____1651) -> t2
           | (uu____1656,App (FalseOp ,uu____1657)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1674,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1683) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1690 -> mkApp' (Or, [t1; t2]) r)
let mkImp:
  (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term =
  fun uu____1705  ->
    fun r  ->
      match uu____1705 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (uu____1713,App (TrueOp ,uu____1714)) -> mkTrue r
           | (App (FalseOp ,uu____1719),uu____1720) -> mkTrue r
           | (App (TrueOp ,uu____1725),uu____1726) -> t2
           | (uu____1731,App (Imp ,t1'::t2'::[])) ->
               let uu____1736 =
                 let uu____1743 =
                   let uu____1746 = mkAnd (t1, t1') r in [uu____1746; t2'] in
                 (Imp, uu____1743) in
               mkApp' uu____1736 r
           | uu____1749 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op:
  op ->
    (term,term) FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun op  ->
    fun uu____1767  ->
      fun r  -> match uu____1767 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
  fun uu____1883  ->
    fun r  ->
      match uu____1883 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1894) -> t2
           | App (FalseOp ,uu____1899) -> t3
           | uu____1904 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1905),App (TrueOp ,uu____1906)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1915),uu____1916) ->
                    let uu____1921 =
                      let uu____1926 = mkNot t1 t1.rng in (uu____1926, t3) in
                    mkImp uu____1921 r
                | (uu____1927,App (TrueOp ,uu____1928)) -> mkImp (t1, t2) r
                | (uu____1933,uu____1934) -> mkApp' (ITE, [t1; t2; t3]) r))
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
  fun uu____1975  ->
    fun r  ->
      match uu____1975 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____2017) -> body
             | uu____2022 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet:
  (term Prims.list,term) FStar_Pervasives_Native.tuple2 ->
    FStar_Range.range -> term
  =
  fun uu____2041  ->
    fun r  ->
      match uu____2041 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____2075 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____2075 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some
              (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____2091 = FStar_ST.read t1.freevars in
        match uu____2091 with
        | FStar_Pervasives_Native.Some [] -> t1
        | uu____2118 ->
            (match t1.tm with
             | Integer uu____2127 -> t1
             | BoundV uu____2128 -> t1
             | FreeV x ->
                 let uu____2134 = index_of x in
                 (match uu____2134 with
                  | FStar_Pervasives_Native.None  -> t1
                  | FStar_Pervasives_Native.Some i ->
                      mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____2144 =
                   let uu____2151 = FStar_List.map (aux ix) tms in
                   (op, uu____2151) in
                 mkApp' uu____2144 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____2159 =
                   let uu____2160 =
                     let uu____2167 = aux ix t2 in (uu____2167, r1, r2) in
                   Labeled uu____2160 in
                 mk uu____2159 t2.rng
             | LblPos (t2,r) ->
                 let uu____2170 =
                   let uu____2171 =
                     let uu____2176 = aux ix t2 in (uu____2176, r) in
                   LblPos uu____2171 in
                 mk uu____2170 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____2199 =
                   let uu____2218 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____2237 = aux (ix + n1) body in
                   (qop, uu____2218, wopt, vars, uu____2237) in
                 mkQuant uu____2199 t1.rng
             | Let (es,body) ->
                 let uu____2254 =
                   FStar_List.fold_left
                     (fun uu____2267  ->
                        fun e  ->
                          match uu____2267 with
                          | (ix1,l) ->
                              let uu____2287 =
                                let uu____2290 = aux ix1 e in uu____2290 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____2287))
                     (ix, []) es in
                 (match uu____2254 with
                  | (ix1,es_rev) ->
                      let uu____2301 =
                        let uu____2308 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____2308) in
                      mkLet uu____2301 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer uu____2332 -> t1
        | FreeV uu____2333 -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____2348 =
              let uu____2355 = FStar_List.map (aux shift) tms2 in
              (op, uu____2355) in
            mkApp' uu____2348 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____2363 =
              let uu____2364 =
                let uu____2371 = aux shift t2 in (uu____2371, r1, r2) in
              Labeled uu____2364 in
            mk uu____2363 t2.rng
        | LblPos (t2,r) ->
            let uu____2374 =
              let uu____2375 =
                let uu____2380 = aux shift t2 in (uu____2380, r) in
              LblPos uu____2375 in
            mk uu____2374 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____2406 =
              let uu____2425 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____2442 = aux shift1 body in
              (qop, uu____2425, wopt, vars, uu____2442) in
            mkQuant uu____2406 t1.rng
        | Let (es,body) ->
            let uu____2457 =
              FStar_List.fold_left
                (fun uu____2470  ->
                   fun e  ->
                     match uu____2470 with
                     | (ix,es1) ->
                         let uu____2490 =
                           let uu____2493 = aux shift e in uu____2493 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____2490))
                (shift, []) es in
            (match uu____2457 with
             | (shift1,es_rev) ->
                 let uu____2504 =
                   let uu____2511 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____2511) in
                 mkLet uu____2504 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____2523 = abstr [fv] t in inst [s] uu____2523
let mkQuant':
  (qop,term Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fv Prims.list,term) FStar_Pervasives_Native.tuple5 ->
    FStar_Range.range -> term
  =
  fun uu____2546  ->
    match uu____2546 with
    | (qop,pats,wopt,vars,body) ->
        let uu____2588 =
          let uu____2607 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____2624 = FStar_List.map fv_sort vars in
          let uu____2631 = abstr vars body in
          (qop, uu____2607, wopt, uu____2624, uu____2631) in
        mkQuant uu____2588
let mkForall'':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    sort Prims.list,term) FStar_Pervasives_Native.tuple4 ->
    FStar_Range.range -> term
  =
  fun uu____2660  ->
    fun r  ->
      match uu____2660 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list,Prims.int FStar_Pervasives_Native.option,
    fvs,term) FStar_Pervasives_Native.tuple4 -> FStar_Range.range -> term
  =
  fun uu____2724  ->
    fun r  ->
      match uu____2724 with
      | (pats,wopt,vars,body) ->
          let uu____2756 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____2756 r
let mkForall:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2779  ->
    fun r  ->
      match uu____2779 with
      | (pats,vars,body) ->
          let uu____2802 =
            mkQuant' (Forall, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2802 r
let mkExists:
  (pat Prims.list Prims.list,fvs,term) FStar_Pervasives_Native.tuple3 ->
    FStar_Range.range -> term
  =
  fun uu____2825  ->
    fun r  ->
      match uu____2825 with
      | (pats,vars,body) ->
          let uu____2848 =
            mkQuant' (Exists, pats, FStar_Pervasives_Native.None, vars, body) in
          uu____2848 r
let mkLet':
  ((fv,term) FStar_Pervasives_Native.tuple2 Prims.list,term)
    FStar_Pervasives_Native.tuple2 -> FStar_Range.range -> term
  =
  fun uu____2871  ->
    fun r  ->
      match uu____2871 with
      | (bindings,body) ->
          let uu____2897 = FStar_List.split bindings in
          (match uu____2897 with
           | (vars,es) ->
               let uu____2916 =
                 let uu____2923 = abstr vars body in (es, uu____2923) in
               mkLet uu____2916 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string,(Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,
    sort,term,caption) FStar_Pervasives_Native.tuple5 -> decl
  =
  fun uu____2944  ->
    match uu____2944 with
    | (nm,vars,s,tm,c) ->
        let uu____2978 =
          let uu____2991 = FStar_List.map fv_sort vars in
          let uu____2998 = abstr vars tm in
          (nm, uu____2991, s, uu____2998, c) in
        DefineFun uu____2978
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____3004 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____3004
let fresh_token:
  (Prims.string,sort) FStar_Pervasives_Native.tuple2 -> Prims.int -> decl =
  fun uu____3013  ->
    fun id  ->
      match uu____3013 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____3023 =
              let uu____3024 =
                let uu____3029 = mkInteger' id norng in
                let uu____3030 =
                  let uu____3031 =
                    let uu____3038 = constr_id_of_sort sort in
                    let uu____3039 =
                      let uu____3042 = mkApp (tok_name, []) norng in
                      [uu____3042] in
                    (uu____3038, uu____3039) in
                  mkApp uu____3031 norng in
                (uu____3029, uu____3030) in
              mkEq uu____3024 norng in
            {
              assumption_term = uu____3023;
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
  fun uu____3059  ->
    match uu____3059 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____3088 =
                      let uu____3093 =
                        let uu____3094 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____3094 in
                      (uu____3093, s) in
                    mkFreeV uu____3088 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____3102 =
            let uu____3109 = constr_id_of_sort sort in (uu____3109, [capp]) in
          mkApp uu____3102 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____3114 =
            let uu____3115 =
              let uu____3126 =
                let uu____3127 =
                  let uu____3132 = mkInteger id1 norng in
                  (uu____3132, cid_app) in
                mkEq uu____3127 norng in
              ([[capp]], bvar_names, uu____3126) in
            mkForall uu____3115 norng in
          {
            assumption_term = uu____3114;
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
  fun uu____3153  ->
    match uu____3153 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____3174 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____3174 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____3191 = let uu____3196 = bvar_name i in (uu____3196, s) in
          mkFreeV uu____3191 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3211  ->
                    match uu____3211 with
                    | (uu____3218,s,uu____3220) ->
                        let uu____3221 = bvar i s in uu____3221 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____3230 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____3250  ->
                    match uu____3250 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun
                            (name1, [sort], s,
                              (FStar_Pervasives_Native.Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____3273 =
                              let uu____3274 =
                                let uu____3285 =
                                  let uu____3286 =
                                    let uu____3291 =
                                      let uu____3292 = bvar i s in
                                      uu____3292 norng in
                                    (cproj_app, uu____3291) in
                                  mkEq uu____3286 norng in
                                ([[capp]], bvar_names, uu____3285) in
                              mkForall uu____3274 norng in
                            {
                              assumption_term = uu____3273;
                              assumption_caption =
                                (FStar_Pervasives_Native.Some
                                   "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____3230 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____3314  ->
    match uu____3314 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____3338  ->
                  match uu____3338 with
                  | (uu____3345,sort1,uu____3347) -> sort1)) in
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
            let uu____3365 =
              let uu____3370 =
                let uu____3371 =
                  let uu____3378 = constr_id_of_sort sort in
                  (uu____3378, [xx]) in
                mkApp uu____3371 norng in
              let uu____3381 =
                let uu____3382 = FStar_Util.string_of_int id in
                mkInteger uu____3382 norng in
              (uu____3370, uu____3381) in
            mkEq uu____3365 norng in
          let uu____3383 =
            let uu____3398 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____3442  ->
                        match uu____3442 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____3472 = mkApp (proj, [xx]) norng in
                              (uu____3472, [])
                            else
                              (let fi =
                                 let uu____3491 =
                                   let uu____3492 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____3492 in
                                 (uu____3491, s) in
                               let uu____3493 = mkFreeV fi norng in
                               (uu____3493, [fi])))) in
            FStar_All.pipe_right uu____3398 FStar_List.split in
          match uu____3383 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____3574 =
                  let uu____3579 = mkApp (name, proj_terms) norng in
                  (xx, uu____3579) in
                mkEq uu____3574 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____3587 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____3628 =
          let uu____3631 =
            let uu____3632 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____3632 in
          uu____3631 :: cdecl :: cid :: projs in
        let uu____3633 =
          let uu____3636 =
            let uu____3639 =
              let uu____3640 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____3640 in
            [uu____3639] in
          FStar_List.append [disc] uu____3636 in
        FStar_List.append uu____3628 uu____3633
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
          let uu____3687 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____3732  ->
                    fun s  ->
                      match uu____3732 with
                      | (names,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____3782 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | FStar_Pervasives_Native.None  -> prefix1
                            | FStar_Pervasives_Native.Some p ->
                                Prims.strcat p prefix1 in
                          let nm =
                            let uu____3786 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____3786 in
                          let names1 = (nm, s) :: names in
                          let b =
                            let uu____3799 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____3799 in
                          (names1, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____3687 with
          | (names,binders,n1) -> (names, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string,sort) FStar_Pervasives_Native.tuple2 Prims.list,Prims.string
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun sorts  ->
    let uu____3876 =
      name_binders_inner (FStar_Pervasives_Native.Some "__") []
        (Prims.parse_int "0") sorts in
    match uu____3876 with
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
            (let uu____3959 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____3959) in
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
                             "Prims.guard_free",{ tm = BoundV uu____3996;
                                                  freevars = uu____3997;
                                                  rng = uu____3998;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____4012 -> tm)))) in
      let rec aux' depth n1 names t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____4052 = FStar_List.nth names i in
            FStar_All.pipe_right uu____4052 FStar_Pervasives_Native.fst
        | FreeV x -> FStar_Pervasives_Native.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____4067 =
              let uu____4068 = FStar_List.map (aux1 n1 names) tms in
              FStar_All.pipe_right uu____4068 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____4067
        | Labeled (t2,uu____4074,uu____4075) -> aux1 n1 names t2
        | LblPos (t2,s) ->
            let uu____4078 = aux1 n1 names t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____4078 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____4101 =
              name_binders_inner FStar_Pervasives_Native.None names n1 sorts in
            (match uu____4101 with
             | (names1,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[] -> ";;no pats"
                   | [] -> ";;no pats"
                   | uu____4150 ->
                       let uu____4155 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____4169 =
                                   let uu____4170 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____4174 = aux1 n2 names1 p in
                                          FStar_Util.format1 "%s" uu____4174)
                                       pats2 in
                                   FStar_String.concat " " uu____4170 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____4169)) in
                       FStar_All.pipe_right uu____4155
                         (FStar_String.concat "\n") in
                 let uu____4177 =
                   let uu____4180 =
                     let uu____4183 =
                       let uu____4186 = aux1 n2 names1 body in
                       let uu____4187 =
                         let uu____4190 = weightToSmt wopt in
                         [uu____4190; pats_str; qid] in
                       uu____4186 :: uu____4187 in
                     binders1 :: uu____4183 in
                   (qop_to_string qop) :: uu____4180 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____4177)
        | Let (es,body) ->
            let uu____4197 =
              FStar_List.fold_left
                (fun uu____4226  ->
                   fun e  ->
                     match uu____4226 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____4276 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____4276 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____4289 = aux1 n1 names e in
                           FStar_Util.format2 "(%s %s)" nm uu____4289 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names, [], n1) es in
            (match uu____4197 with
             | (names1,binders,n2) ->
                 let uu____4321 = aux1 n2 names1 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____4321)
      and aux depth n1 names t1 =
        let s = aux' depth n1 names t1 in
        if t1.rng <> norng
        then
          let uu____4329 = FStar_Range.string_of_range t1.rng in
          let uu____4330 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____4329
            uu____4330 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string:
  Prims.string FStar_Pervasives_Native.option -> Prims.string =
  fun uu___90_4336  ->
    match uu___90_4336 with
    | FStar_Pervasives_Native.None  -> ""
    | FStar_Pervasives_Native.Some c ->
        let uu____4340 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____4355 -> (hd1, "...") in
        (match uu____4340 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____4373 = FStar_Options.log_queries () in
          if uu____4373
          then
            let uu____4374 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___91_4377  ->
                   match uu___91_4377 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____4374
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____4396 = caption_to_string c in
          let uu____4397 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____4396 f
            (FStar_String.concat " " l) uu____4397
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____4407 = name_macro_binders arg_sorts in
          (match uu____4407 with
           | (names,binders) ->
               let body1 =
                 let uu____4439 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names in
                 inst uu____4439 body in
               let uu____4451 = caption_to_string c in
               let uu____4452 = strSort retsort in
               let uu____4453 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____4451
                 f (FStar_String.concat " " binders) uu____4452 uu____4453)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___92_4469  ->
                    match uu___92_4469 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____4474 = FStar_Options.log_queries () in
            if uu____4474
            then
              let uu____4475 =
                let uu____4476 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____4476 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____4475
            else "" in
          let n1 = escape a.assumption_name in
          let uu____4481 = caption_to_string a.assumption_caption in
          let uu____4482 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____4481 fids
            uu____4482 n1
      | Eval t ->
          let uu____4484 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____4484
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____4486 -> ""
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
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(declare-fun Tm_uvar (Int) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(declare-fun _mod (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_mod x y) (mod x y)) :pattern ((_mod x y)))))" in
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
      ("BoxRef", [("BoxRef_proj_0", Ref_sort, true)], Term_sort,
        (Prims.parse_int "10"), true);
      ("LexCons",
        [("LexCons_0", Term_sort, true); ("LexCons_1", Term_sort, true)],
        Term_sort, (Prims.parse_int "11"), true)] in
    let bcons =
      let uu____4849 =
        let uu____4852 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____4852
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____4849 (FStar_String.concat "\n") in
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
      let uu____4885 =
        let uu____4892 = let uu____4895 = mkInteger' i norng in [uu____4895] in
        ("Tm_uvar", uu____4892) in
      mkApp uu____4885 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        match t.tm with
        | App (Var v',t1::[]) when
            (v1 = v') && (FStar_Options.smtencoding_elim_box ()) -> t1
        | uu____4913 -> mkApp (u, [t]) t.rng
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
let boxRef: term -> term =
  fun t  -> maybe_elim_box "BoxRef" "BoxRef_proj_0" t
let unboxRef: term -> term =
  fun t  -> maybe_elim_box "BoxRef_proj_0" "BoxRef" t
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | uu____4946 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____4953 -> raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____4962::t1::t2::[]);
                       freevars = uu____4965; rng = uu____4966;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____4979::t1::t2::[]);
                       freevars = uu____4982; rng = uu____4983;_}::[])
        -> let uu____4996 = mkEq (t1, t2) norng in mkNot uu____4996 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____4999; rng = uu____5000;_}::[])
        ->
        let uu____5013 =
          let uu____5018 = unboxInt t1 in
          let uu____5019 = unboxInt t2 in (uu____5018, uu____5019) in
        mkLTE uu____5013 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____5022; rng = uu____5023;_}::[])
        ->
        let uu____5036 =
          let uu____5041 = unboxInt t1 in
          let uu____5042 = unboxInt t2 in (uu____5041, uu____5042) in
        mkLT uu____5036 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____5045; rng = uu____5046;_}::[])
        ->
        let uu____5059 =
          let uu____5064 = unboxInt t1 in
          let uu____5065 = unboxInt t2 in (uu____5064, uu____5065) in
        mkGTE uu____5059 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____5068; rng = uu____5069;_}::[])
        ->
        let uu____5082 =
          let uu____5087 = unboxInt t1 in
          let uu____5088 = unboxInt t2 in (uu____5087, uu____5088) in
        mkGT uu____5082 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____5091; rng = uu____5092;_}::[])
        ->
        let uu____5105 =
          let uu____5110 = unboxBool t1 in
          let uu____5111 = unboxBool t2 in (uu____5110, uu____5111) in
        mkAnd uu____5105 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____5114; rng = uu____5115;_}::[])
        ->
        let uu____5128 =
          let uu____5133 = unboxBool t1 in
          let uu____5134 = unboxBool t2 in (uu____5133, uu____5134) in
        mkOr uu____5128 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____5136; rng = uu____5137;_}::[])
        -> let uu____5150 = unboxBool t1 in mkNot uu____5150 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___93_5154 = unboxBool t1 in
        {
          tm = (uu___93_5154.tm);
          freevars = (uu___93_5154.freevars);
          rng = (t.rng)
        }
    | uu____5155 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____5188 = FStar_Options.unthrottle_inductives () in
        if uu____5188
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
      let uu____5261 =
        let uu____5268 = let uu____5271 = mkInteger' i norng in [uu____5271] in
        ("FString_const", uu____5268) in
      mkApp uu____5261 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____5283 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____5283 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____5303 =
         let uu____5310 =
           let uu____5313 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____5313] in
         ("SFuel", uu____5310) in
       mkApp uu____5303 norng)
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
            let uu____5347 = mkAnd (p11, p21) r in
            FStar_Pervasives_Native.Some uu____5347
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
      let uu____5398 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____5398
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____5411 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____5411
let mk_haseq: term -> term =
  fun t  ->
    let uu____5417 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____5417
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____5435 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____5435
    | FreeV fv ->
        FStar_Util.format1 "(FreeV %s)" (FStar_Pervasives_Native.fst fv)
    | App (op,l) ->
        let uu____5447 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____5447
    | Labeled (t1,r1,r2) ->
        let uu____5451 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____5451
    | LblPos (t1,s) ->
        let uu____5454 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____5454
    | Quant (qop,l,uu____5457,uu____5458,t1) ->
        let uu____5476 = print_smt_term_list_list l in
        let uu____5477 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____5476
          uu____5477
    | Let (es,body) ->
        let uu____5484 = print_smt_term_list es in
        let uu____5485 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____5484 uu____5485
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____5489 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____5489 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____5505 =
             let uu____5506 =
               let uu____5507 = print_smt_term_list l1 in
               Prims.strcat uu____5507 " ] " in
             Prims.strcat "; [ " uu____5506 in
           Prims.strcat s uu____5505) "" l