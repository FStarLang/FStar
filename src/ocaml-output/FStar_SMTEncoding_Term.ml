open Prims
type sort =
  | Bool_sort
  | Int_sort
  | String_sort
  | Ref_sort
  | Term_sort
  | Fuel_sort
  | Array of (sort* sort)
  | Arrow of (sort* sort)
  | Sort of Prims.string
let uu___is_Bool_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____17 -> false
let uu___is_Int_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____21 -> false
let uu___is_String_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____25 -> false
let uu___is_Ref_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____29 -> false
let uu___is_Term_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____33 -> false
let uu___is_Fuel_sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____37 -> false
let uu___is_Array: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____44 -> false
let __proj__Array__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Array _0 -> _0
let uu___is_Arrow: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____64 -> false
let __proj__Arrow__item___0: sort -> (sort* sort) =
  fun projectee  -> match projectee with | Arrow _0 -> _0
let uu___is_Sort: sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____82 -> false
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
        let uu____95 = strSort s1 in
        let uu____96 = strSort s2 in
        FStar_Util.format2 "(Array %s %s)" uu____95 uu____96
    | Arrow (s1,s2) ->
        let uu____99 = strSort s1 in
        let uu____100 = strSort s2 in
        FStar_Util.format2 "(%s -> %s)" uu____99 uu____100
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
  | FreeV of (Prims.string* sort)
  | App of (op* term Prims.list)
  | Quant of (qop* term Prims.list Prims.list* Prims.int option* sort
  Prims.list* term)
  | Let of (term Prims.list* term)
  | Labeled of (term* Prims.string* FStar_Range.range)
  | LblPos of (term* Prims.string)
and term =
  {
  tm: term';
  freevars: (Prims.string* sort) Prims.list FStar_Syntax_Syntax.memo;
  rng: FStar_Range.range;}
let uu___is_Integer: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____265 -> false
let __proj__Integer__item___0: term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0
let uu___is_BoundV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____277 -> false
let __proj__BoundV__item___0: term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0
let uu___is_FreeV: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____291 -> false
let __proj__FreeV__item___0: term' -> (Prims.string* sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0
let uu___is_App: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____312 -> false
let __proj__App__item___0: term' -> (op* term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Quant: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____342 -> false
let __proj__Quant__item___0:
  term' ->
    (qop* term Prims.list Prims.list* Prims.int option* sort Prims.list*
      term)
  = fun projectee  -> match projectee with | Quant _0 -> _0
let uu___is_Let: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____384 -> false
let __proj__Let__item___0: term' -> (term Prims.list* term) =
  fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Labeled: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____408 -> false
let __proj__Labeled__item___0:
  term' -> (term* Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0
let uu___is_LblPos: term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____431 -> false
let __proj__LblPos__item___0: term' -> (term* Prims.string) =
  fun projectee  -> match projectee with | LblPos _0 -> _0
type pat = term
type fv = (Prims.string* sort)
type fvs = (Prims.string* sort) Prims.list
type caption = Prims.string option
type binders = (Prims.string* sort) Prims.list
type constructor_field = (Prims.string* sort* Prims.bool)
type constructor_t =
  (Prims.string* constructor_field Prims.list* sort* Prims.int* Prims.bool)
type constructors = constructor_t Prims.list
type fact_db_id =
  | Name of FStar_Ident.lid
  | Namespace of FStar_Ident.lid
  | Tag of Prims.string
let uu___is_Name: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____499 -> false
let __proj__Name__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_Namespace: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____511 -> false
let __proj__Namespace__item___0: fact_db_id -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Namespace _0 -> _0
let uu___is_Tag: fact_db_id -> Prims.bool =
  fun projectee  ->
    match projectee with | Tag _0 -> true | uu____523 -> false
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
  | DeclFun of (Prims.string* sort Prims.list* sort* caption)
  | DefineFun of (Prims.string* sort Prims.list* sort* term* caption)
  | Assume of assumption
  | Caption of Prims.string
  | Eval of term
  | Echo of Prims.string
  | RetainAssumptions of Prims.string Prims.list
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption of (Prims.string* Prims.string)
  | GetStatistics
  | GetReasonUnknown
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____603 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____613 -> false
let __proj__DeclFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____646 -> false
let __proj__DefineFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* term* caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____676 -> false
let __proj__Assume__item___0: decl -> assumption =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____688 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____700 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____712 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_RetainAssumptions: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | RetainAssumptions _0 -> true | uu____725 -> false
let __proj__RetainAssumptions__item___0: decl -> Prims.string Prims.list =
  fun projectee  -> match projectee with | RetainAssumptions _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____739 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____743 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____747 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____751 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____758 -> false
let __proj__SetOption__item___0: decl -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____775 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____779 -> false
type decls_t = decl Prims.list
type error_label = (fv* Prims.string* FStar_Range.range)
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool = fun x  -> fun y  -> (fst x) = (fst y)
let fv_sort x = snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____816 -> false
let freevar_sort: term -> sort =
  fun uu___85_821  ->
    match uu___85_821 with
    | { tm = FreeV x; freevars = uu____823; rng = uu____824;_} -> fv_sort x
    | uu____831 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___86_834  ->
    match uu___86_834 with
    | { tm = FreeV fv; freevars = uu____836; rng = uu____837;_} -> fv
    | uu____844 -> failwith "impossible"
let rec freevars: term -> (Prims.string* sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer _|BoundV _ -> []
    | FreeV fv -> [fv]
    | App (uu____865,tms) -> FStar_List.collect freevars tms
    | Quant (_,_,_,_,t1)|Labeled (t1,_,_)|LblPos (t1,_) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____892 = FStar_ST.read t.freevars in
    match uu____892 with
    | Some b -> b
    | None  ->
        let fvs =
          let uu____915 = freevars t in
          FStar_Util.remove_dups fv_eq uu____915 in
        (FStar_ST.write t.freevars (Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___87_927  ->
    match uu___87_927 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___88_930  ->
    match uu___88_930 with
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
let weightToSmt: Prims.int option -> Prims.string =
  fun uu___89_935  ->
    match uu___89_935 with
    | None  -> ""
    | Some i ->
        let uu____938 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____938
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____946 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____946
    | FreeV x ->
        let uu____950 =
          let uu____951 = strSort (snd x) in Prims.strcat ":" uu____951 in
        Prims.strcat (fst x) uu____950
    | App (op,tms) ->
        let uu____956 =
          let uu____957 =
            let uu____958 =
              let uu____959 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____959 (FStar_String.concat " ") in
            Prims.strcat uu____958 ")" in
          Prims.strcat (op_to_string op) uu____957 in
        Prims.strcat "(" uu____956
    | Labeled (t1,r1,r2) ->
        let uu____965 = hash_of_term t1 in
        let uu____966 =
          let uu____967 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____967 in
        Prims.strcat uu____965 uu____966
    | LblPos (t1,r) ->
        let uu____970 =
          let uu____971 = hash_of_term t1 in
          Prims.strcat uu____971
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____970
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____985 =
          let uu____986 =
            let uu____987 =
              let uu____988 =
                let uu____989 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____989 (FStar_String.concat " ") in
              let uu____992 =
                let uu____993 =
                  let uu____994 = hash_of_term body in
                  let uu____995 =
                    let uu____996 =
                      let uu____997 = weightToSmt wopt in
                      let uu____998 =
                        let uu____999 =
                          let uu____1000 =
                            let uu____1001 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____1009 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____1009
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____1001
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____1000 "))" in
                        Prims.strcat " " uu____999 in
                      Prims.strcat uu____997 uu____998 in
                    Prims.strcat " " uu____996 in
                  Prims.strcat uu____994 uu____995 in
                Prims.strcat ")(! " uu____993 in
              Prims.strcat uu____988 uu____992 in
            Prims.strcat " (" uu____987 in
          Prims.strcat (qop_to_string qop) uu____986 in
        Prims.strcat "(" uu____985
    | Let (es,body) ->
        let uu____1017 =
          let uu____1018 =
            let uu____1019 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____1019 (FStar_String.concat " ") in
          let uu____1022 =
            let uu____1023 =
              let uu____1024 = hash_of_term body in
              Prims.strcat uu____1024 ")" in
            Prims.strcat ") " uu____1023 in
          Prims.strcat uu____1018 uu____1022 in
        Prims.strcat "(let (" uu____1017
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____1032 = FStar_Util.mk_ref None in
      { tm = t; freevars = uu____1032; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1061 =
        let uu____1062 = FStar_Util.ensure_decimal i in Integer uu____1062 in
      mk uu____1061 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____1069 = FStar_Util.string_of_int i in mkInteger uu____1069 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV: (Prims.string* sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r
let mkApp': (op* term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r
let mkApp: (Prims.string* term Prims.list) -> FStar_Range.range -> term =
  fun uu____1105  ->
    fun r  -> match uu____1105 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1121) -> mkFalse r
      | App (FalseOp ,uu____1124) -> mkTrue r
      | uu____1127 -> mkApp' (Not, [t]) r
let mkAnd: (term* term) -> FStar_Range.range -> term =
  fun uu____1135  ->
    fun r  ->
      match uu____1135 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1141),uu____1142) -> t2
           | (uu____1145,App (TrueOp ,uu____1146)) -> t1
           | (App (FalseOp ,_),_)|(_,App (FalseOp ,_)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1162,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1168) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1172 -> mkApp' (And, [t1; t2]) r)
let mkOr: (term* term) -> FStar_Range.range -> term =
  fun uu____1182  ->
    fun r  ->
      match uu____1182 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,_),_)|(_,App (TrueOp ,_)) -> mkTrue r
           | (App (FalseOp ,uu____1194),uu____1195) -> t2
           | (uu____1198,App (FalseOp ,uu____1199)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1209,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1215) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1219 -> mkApp' (Or, [t1; t2]) r)
let mkImp: (term* term) -> FStar_Range.range -> term =
  fun uu____1229  ->
    fun r  ->
      match uu____1229 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (_,App (TrueOp ,_))|(App (FalseOp ,_),_) -> mkTrue r
           | (App (TrueOp ,uu____1241),uu____1242) -> t2
           | (uu____1245,App (Imp ,t1'::t2'::[])) ->
               let uu____1249 =
                 let uu____1253 =
                   let uu____1255 = mkAnd (t1, t1') r in [uu____1255; t2'] in
                 (Imp, uu____1253) in
               mkApp' uu____1249 r
           | uu____1257 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op: op -> (term* term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1270  ->
      fun r  -> match uu____1270 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
let mkMinus: term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r
let mkIff: (term* term) -> FStar_Range.range -> term = mk_bin_op Iff
let mkEq: (term* term) -> FStar_Range.range -> term = mk_bin_op Eq
let mkLT: (term* term) -> FStar_Range.range -> term = mk_bin_op LT
let mkLTE: (term* term) -> FStar_Range.range -> term = mk_bin_op LTE
let mkGT: (term* term) -> FStar_Range.range -> term = mk_bin_op GT
let mkGTE: (term* term) -> FStar_Range.range -> term = mk_bin_op GTE
let mkAdd: (term* term) -> FStar_Range.range -> term = mk_bin_op Add
let mkSub: (term* term) -> FStar_Range.range -> term = mk_bin_op Sub
let mkDiv: (term* term) -> FStar_Range.range -> term = mk_bin_op Div
let mkMul: (term* term) -> FStar_Range.range -> term = mk_bin_op Mul
let mkMod: (term* term) -> FStar_Range.range -> term = mk_bin_op Mod
let mkITE: (term* term* term) -> FStar_Range.range -> term =
  fun uu____1357  ->
    fun r  ->
      match uu____1357 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1365) -> t2
           | App (FalseOp ,uu____1368) -> t3
           | uu____1371 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1372),App (TrueOp ,uu____1373)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1378),uu____1379) ->
                    let uu____1382 =
                      let uu____1385 = mkNot t1 t1.rng in (uu____1385, t3) in
                    mkImp uu____1382 r
                | (uu____1386,App (TrueOp ,uu____1387)) -> mkImp (t1, t2) r
                | (uu____1390,uu____1391) -> mkApp' (ITE, [t1; t2; t3]) r))
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
let mkQuant:
  (qop* term Prims.list Prims.list* Prims.int option* sort Prims.list* term)
    -> FStar_Range.range -> term
  =
  fun uu____1419  ->
    fun r  ->
      match uu____1419 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1446) -> body
             | uu____1449 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet: (term Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1461  ->
    fun r  ->
      match uu____1461 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1489 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1489 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____1503 = FStar_ST.read t1.freevars in
        match uu____1503 with
        | Some [] -> t1
        | uu____1519 ->
            (match t1.tm with
             | Integer _|BoundV _ -> t1
             | FreeV x ->
                 let uu____1529 = index_of x in
                 (match uu____1529 with
                  | None  -> t1
                  | Some i -> mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1536 =
                   let uu____1540 = FStar_List.map (aux ix) tms in
                   (op, uu____1540) in
                 mkApp' uu____1536 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1546 =
                   let uu____1547 =
                     let uu____1551 = aux ix t2 in (uu____1551, r1, r2) in
                   Labeled uu____1547 in
                 mk uu____1546 t2.rng
             | LblPos (t2,r) ->
                 let uu____1554 =
                   let uu____1555 =
                     let uu____1558 = aux ix t2 in (uu____1558, r) in
                   LblPos uu____1555 in
                 mk uu____1554 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____1574 =
                   let uu____1584 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____1595 = aux (ix + n1) body in
                   (qop, uu____1584, wopt, vars, uu____1595) in
                 mkQuant uu____1574 t1.rng
             | Let (es,body) ->
                 let uu____1606 =
                   FStar_List.fold_left
                     (fun uu____1613  ->
                        fun e  ->
                          match uu____1613 with
                          | (ix1,l) ->
                              let uu____1625 =
                                let uu____1627 = aux ix1 e in uu____1627 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____1625))
                     (ix, []) es in
                 (match uu____1606 with
                  | (ix1,es_rev) ->
                      let uu____1634 =
                        let uu____1638 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____1638) in
                      mkLet uu____1634 t1.rng)) in
      aux (Prims.parse_int "0") t
let inst: term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms in
      let n1 = FStar_List.length tms1 in
      let rec aux shift t1 =
        match t1.tm with
        | Integer _|FreeV _ -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____1669 =
              let uu____1673 = FStar_List.map (aux shift) tms2 in
              (op, uu____1673) in
            mkApp' uu____1669 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1679 =
              let uu____1680 =
                let uu____1684 = aux shift t2 in (uu____1684, r1, r2) in
              Labeled uu____1680 in
            mk uu____1679 t2.rng
        | LblPos (t2,r) ->
            let uu____1687 =
              let uu____1688 =
                let uu____1691 = aux shift t2 in (uu____1691, r) in
              LblPos uu____1688 in
            mk uu____1687 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____1710 =
              let uu____1720 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____1729 = aux shift1 body in
              (qop, uu____1720, wopt, vars, uu____1729) in
            mkQuant uu____1710 t1.rng
        | Let (es,body) ->
            let uu____1738 =
              FStar_List.fold_left
                (fun uu____1745  ->
                   fun e  ->
                     match uu____1745 with
                     | (ix,es1) ->
                         let uu____1757 =
                           let uu____1759 = aux shift e in uu____1759 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____1757))
                (shift, []) es in
            (match uu____1738 with
             | (shift1,es_rev) ->
                 let uu____1766 =
                   let uu____1770 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____1770) in
                 mkLet uu____1766 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____1781 = abstr [fv] t in inst [s] uu____1781
let mkQuant':
  (qop* term Prims.list Prims.list* Prims.int option* fv Prims.list* term) ->
    FStar_Range.range -> term
  =
  fun uu____1795  ->
    match uu____1795 with
    | (qop,pats,wopt,vars,body) ->
        let uu____1820 =
          let uu____1830 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____1839 = FStar_List.map fv_sort vars in
          let uu____1843 = abstr vars body in
          (qop, uu____1830, wopt, uu____1839, uu____1843) in
        mkQuant uu____1820
let mkForall'':
  (pat Prims.list Prims.list* Prims.int option* sort Prims.list* term) ->
    FStar_Range.range -> term
  =
  fun uu____1860  ->
    fun r  ->
      match uu____1860 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list* Prims.int option* fvs* term) ->
    FStar_Range.range -> term
  =
  fun uu____1897  ->
    fun r  ->
      match uu____1897 with
      | (pats,wopt,vars,body) ->
          let uu____1916 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____1916 r
let mkForall:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1931  ->
    fun r  ->
      match uu____1931 with
      | (pats,vars,body) ->
          let uu____1945 = mkQuant' (Forall, pats, None, vars, body) in
          uu____1945 r
let mkExists:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1960  ->
    fun r  ->
      match uu____1960 with
      | (pats,vars,body) ->
          let uu____1974 = mkQuant' (Exists, pats, None, vars, body) in
          uu____1974 r
let mkLet': ((fv* term) Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1989  ->
    fun r  ->
      match uu____1989 with
      | (bindings,body) ->
          let uu____2004 = FStar_List.split bindings in
          (match uu____2004 with
           | (vars,es) ->
               let uu____2015 =
                 let uu____2019 = abstr vars body in (es, uu____2019) in
               mkLet uu____2015 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string* (Prims.string* sort) Prims.list* sort* term* caption) ->
    decl
  =
  fun uu____2031  ->
    match uu____2031 with
    | (nm,vars,s,tm,c) ->
        let uu____2051 =
          let uu____2058 = FStar_List.map fv_sort vars in
          let uu____2062 = abstr vars tm in
          (nm, uu____2058, s, uu____2062, c) in
        DefineFun uu____2051
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____2067 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____2067
let fresh_token: (Prims.string* sort) -> Prims.int -> decl =
  fun uu____2074  ->
    fun id  ->
      match uu____2074 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let a =
            let uu____2082 =
              let uu____2083 =
                let uu____2086 = mkInteger' id norng in
                let uu____2087 =
                  let uu____2088 =
                    let uu____2092 = constr_id_of_sort sort in
                    let uu____2093 =
                      let uu____2095 = mkApp (tok_name, []) norng in
                      [uu____2095] in
                    (uu____2092, uu____2093) in
                  mkApp uu____2088 norng in
                (uu____2086, uu____2087) in
              mkEq uu____2083 norng in
            {
              assumption_term = uu____2082;
              assumption_caption = (Some "fresh token");
              assumption_name = a_name;
              assumption_fact_ids = []
            } in
          Assume a
let fresh_constructor:
  (Prims.string* sort Prims.list* sort* Prims.int) -> decl =
  fun uu____2105  ->
    match uu____2105 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2124 =
                      let uu____2127 =
                        let uu____2128 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2128 in
                      (uu____2127, s) in
                    mkFreeV uu____2124 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2134 =
            let uu____2138 = constr_id_of_sort sort in (uu____2138, [capp]) in
          mkApp uu____2134 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let a =
          let uu____2142 =
            let uu____2143 =
              let uu____2149 =
                let uu____2150 =
                  let uu____2153 = mkInteger id1 norng in
                  (uu____2153, cid_app) in
                mkEq uu____2150 norng in
              ([[capp]], bvar_names, uu____2149) in
            mkForall uu____2143 norng in
          {
            assumption_term = uu____2142;
            assumption_caption = (Some "Consrtructor distinct");
            assumption_name = a_name;
            assumption_fact_ids = []
          } in
        Assume a
let injective_constructor:
  (Prims.string* constructor_field Prims.list* sort) -> decl Prims.list =
  fun uu____2165  ->
    match uu____2165 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2181 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2181 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2198 = let uu____2201 = bvar_name i in (uu____2201, s) in
          mkFreeV uu____2198 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2210  ->
                    match uu____2210 with
                    | (uu____2214,s,uu____2216) ->
                        let uu____2217 = bvar i s in uu____2217 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2224 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2235  ->
                    match uu____2235 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun (name1, [sort], s, (Some "Projector")) in
                        if projectible
                        then
                          let a =
                            let uu____2250 =
                              let uu____2251 =
                                let uu____2257 =
                                  let uu____2258 =
                                    let uu____2261 =
                                      let uu____2262 = bvar i s in
                                      uu____2262 norng in
                                    (cproj_app, uu____2261) in
                                  mkEq uu____2258 norng in
                                ([[capp]], bvar_names, uu____2257) in
                              mkForall uu____2251 norng in
                            {
                              assumption_term = uu____2250;
                              assumption_caption =
                                (Some "Projection inverse");
                              assumption_name =
                                (Prims.strcat "projection_inverse_" name1);
                              assumption_fact_ids = []
                            } in
                          [proj_name; Assume a]
                        else [proj_name])) in
        FStar_All.pipe_right uu____2224 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2276  ->
    match uu____2276 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2292  ->
                  match uu____2292 with
                  | (uu____2296,sort1,uu____2298) -> sort1)) in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____2311 =
              let uu____2314 =
                let uu____2315 =
                  let uu____2319 = constr_id_of_sort sort in
                  (uu____2319, [xx]) in
                mkApp uu____2315 norng in
              let uu____2321 =
                let uu____2322 = FStar_Util.string_of_int id in
                mkInteger uu____2322 norng in
              (uu____2314, uu____2321) in
            mkEq uu____2311 norng in
          let uu____2323 =
            let uu____2331 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2354  ->
                        match uu____2354 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2371 = mkApp (proj, [xx]) norng in
                              (uu____2371, [])
                            else
                              (let fi =
                                 let uu____2382 =
                                   let uu____2383 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2383 in
                                 (uu____2382, s) in
                               let uu____2384 = mkFreeV fi norng in
                               (uu____2384, [fi])))) in
            FStar_All.pipe_right uu____2331 FStar_List.split in
          match uu____2323 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____2427 =
                  let uu____2430 = mkApp (name, proj_terms) norng in
                  (xx, uu____2430) in
                mkEq uu____2427 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2435 -> mkExists ([], ex_vars1, disc_inv_body) norng in
              let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (Some "Discriminator definition")) in
              def in
        let projs =
          if injective1
          then injective_constructor (name, fields, sort)
          else [] in
        let uu____2458 =
          let uu____2460 =
            let uu____2461 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____2461 in
          uu____2460 :: cdecl :: cid :: projs in
        let uu____2462 =
          let uu____2464 =
            let uu____2466 =
              let uu____2467 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____2467 in
            [uu____2466] in
          FStar_List.append [disc] uu____2464 in
        FStar_List.append uu____2458 uu____2462
let name_binders_inner:
  Prims.string option ->
    (Prims.string* sort) Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string* sort) Prims.list* Prims.string Prims.list*
            Prims.int)
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____2497 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2520  ->
                    fun s  ->
                      match uu____2520 with
                      | (names,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2548 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | None  -> prefix1
                            | Some p -> Prims.strcat p prefix1 in
                          let nm =
                            let uu____2552 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____2552 in
                          let names1 = (nm, s) :: names in
                          let b =
                            let uu____2560 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____2560 in
                          (names1, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____2497 with
          | (names,binders,n1) -> (names, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string* sort) Prims.list* Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2602 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts in
    match uu____2602 with
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
            (let uu____2656 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____2656) in
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
                             "Prims.guard_free",{ tm = BoundV uu____2678;
                                                  freevars = uu____2679;
                                                  rng = uu____2680;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____2688 -> tm)))) in
      let rec aux' depth n1 names t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____2724 = FStar_List.nth names i in
            FStar_All.pipe_right uu____2724 FStar_Pervasives.fst
        | FreeV x -> fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____2734 =
              let uu____2735 = FStar_List.map (aux1 n1 names) tms in
              FStar_All.pipe_right uu____2735 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2734
        | Labeled (t2,uu____2739,uu____2740) -> aux1 n1 names t2
        | LblPos (t2,s) ->
            let uu____2743 = aux1 n1 names t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____2743 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____2758 = name_binders_inner None names n1 sorts in
            (match uu____2758 with
             | (names1,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[]|[] -> ";;no pats"
                   | uu____2786 ->
                       let uu____2789 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____2797 =
                                   let uu____2798 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____2801 = aux1 n2 names1 p in
                                          FStar_Util.format1 "%s" uu____2801)
                                       pats2 in
                                   FStar_String.concat " " uu____2798 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____2797)) in
                       FStar_All.pipe_right uu____2789
                         (FStar_String.concat "\n") in
                 let uu____2803 =
                   let uu____2805 =
                     let uu____2807 =
                       let uu____2809 = aux1 n2 names1 body in
                       let uu____2810 =
                         let uu____2812 = weightToSmt wopt in
                         [uu____2812; pats_str; qid] in
                       uu____2809 :: uu____2810 in
                     binders1 :: uu____2807 in
                   (qop_to_string qop) :: uu____2805 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____2803)
        | Let (es,body) ->
            let uu____2817 =
              FStar_List.fold_left
                (fun uu____2832  ->
                   fun e  ->
                     match uu____2832 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____2860 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____2860 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____2868 = aux1 n1 names e in
                           FStar_Util.format2 "(%s %s)" nm uu____2868 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names, [], n1) es in
            (match uu____2817 with
             | (names1,binders,n2) ->
                 let uu____2886 = aux1 n2 names1 body in
                 FStar_Util.format2 "(let (%s)\n%s)"
                   (FStar_String.concat " " binders) uu____2886)
      and aux depth n1 names t1 =
        let s = aux' depth n1 names t1 in
        if t1.rng <> norng
        then
          let uu____2893 = FStar_Range.string_of_range t1.rng in
          let uu____2894 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2893
            uu____2894 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string: Prims.string option -> Prims.string =
  fun uu___90_2899  ->
    match uu___90_2899 with
    | None  -> ""
    | Some c ->
        let uu____2902 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____2911 -> (hd1, "...") in
        (match uu____2902 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____2928 = FStar_Options.log_queries () in
          if uu____2928
          then
            let uu____2929 =
              FStar_All.pipe_right (FStar_Util.splitlines c)
                (fun uu___91_2931  ->
                   match uu___91_2931 with | [] -> "" | h::t -> h) in
            FStar_Util.format1 "\n; %s" uu____2929
          else ""
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____2945 = caption_to_string c in
          let uu____2946 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2945 f
            (FStar_String.concat " " l) uu____2946
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2954 = name_macro_binders arg_sorts in
          (match uu____2954 with
           | (names,binders) ->
               let body1 =
                 let uu____2972 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names in
                 inst uu____2972 body in
               let uu____2979 = caption_to_string c in
               let uu____2980 = strSort retsort in
               let uu____2981 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2979
                 f (FStar_String.concat " " binders) uu____2980 uu____2981)
      | Assume a ->
          let fact_ids_to_string ids =
            FStar_All.pipe_right ids
              (FStar_List.map
                 (fun uu___92_2992  ->
                    match uu___92_2992 with
                    | Name n1 ->
                        Prims.strcat "Name " (FStar_Ident.text_of_lid n1)
                    | Namespace ns ->
                        Prims.strcat "Namespace "
                          (FStar_Ident.text_of_lid ns)
                    | Tag t -> Prims.strcat "Tag " t)) in
          let fids =
            let uu____2997 = FStar_Options.log_queries () in
            if uu____2997
            then
              let uu____2998 =
                let uu____2999 = fact_ids_to_string a.assumption_fact_ids in
                FStar_String.concat "; " uu____2999 in
              FStar_Util.format1 ";;; Fact-ids: %s\n" uu____2998
            else "" in
          let n1 = escape a.assumption_name in
          let uu____3003 = caption_to_string a.assumption_caption in
          let uu____3004 = termToSmt n1 a.assumption_term in
          FStar_Util.format4 "%s%s(assert (! %s\n:named %s))" uu____3003 fids
            uu____3004 n1
      | Eval t ->
          let uu____3006 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____3006
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | RetainAssumptions uu____3008 -> ""
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
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n(declare-fun _mul (Int Int) Int)\n(declare-fun _div (Int Int) Int)\n(assert (forall ((x Int) (y Int)) (! (= (_mul x y) (* x y)) :pattern ((_mul x y)))))\n(assert (forall ((x Int) (y Int)) (! (= (_div x y) (div x y)) :pattern ((_div x y)))))" in
    let constrs =
      [("FString_const", [("FString_const_proj_0", Int_sort, true)],
         String_sort, (Prims.parse_int "0"), true);
      ("Tm_type", [], Term_sort, (Prims.parse_int "2"), true);
      ("Tm_arrow", [("Tm_arrow_id", Int_sort, true)], Term_sort,
        (Prims.parse_int "3"), false);
      ("Tm_uvar", [("Tm_uvar_fst", Int_sort, true)], Term_sort,
        (Prims.parse_int "5"), true);
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
      let uu____3212 =
        let uu____3214 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3214
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3212 (FStar_String.concat "\n") in
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
      let uu____3239 =
        let uu____3243 = let uu____3245 = mkInteger' i norng in [uu____3245] in
        ("Tm_uvar", uu____3243) in
      mkApp uu____3239 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let maybe_elim_box: Prims.string -> Prims.string -> term -> term =
  fun u  ->
    fun v1  ->
      fun t  ->
        match t.tm with
        | App (Var v',t1::[]) when
            (v1 = v') && (FStar_Options.smtencoding_elim_box ()) -> t1
        | uu____3260 -> mkApp (u, [t]) t.rng
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
      | uu____3292 -> raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____3299 -> raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3307::t1::t2::[]);
                       freevars = uu____3310; rng = uu____3311;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3318::t1::t2::[]);
                       freevars = uu____3321; rng = uu____3322;_}::[])
        -> let uu____3329 = mkEq (t1, t2) norng in mkNot uu____3329 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3332; rng = uu____3333;_}::[])
        ->
        let uu____3340 =
          let uu____3343 = unboxInt t1 in
          let uu____3344 = unboxInt t2 in (uu____3343, uu____3344) in
        mkLTE uu____3340 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3347; rng = uu____3348;_}::[])
        ->
        let uu____3355 =
          let uu____3358 = unboxInt t1 in
          let uu____3359 = unboxInt t2 in (uu____3358, uu____3359) in
        mkLT uu____3355 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3362; rng = uu____3363;_}::[])
        ->
        let uu____3370 =
          let uu____3373 = unboxInt t1 in
          let uu____3374 = unboxInt t2 in (uu____3373, uu____3374) in
        mkGTE uu____3370 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3377; rng = uu____3378;_}::[])
        ->
        let uu____3385 =
          let uu____3388 = unboxInt t1 in
          let uu____3389 = unboxInt t2 in (uu____3388, uu____3389) in
        mkGT uu____3385 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3392; rng = uu____3393;_}::[])
        ->
        let uu____3400 =
          let uu____3403 = unboxBool t1 in
          let uu____3404 = unboxBool t2 in (uu____3403, uu____3404) in
        mkAnd uu____3400 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3407; rng = uu____3408;_}::[])
        ->
        let uu____3415 =
          let uu____3418 = unboxBool t1 in
          let uu____3419 = unboxBool t2 in (uu____3418, uu____3419) in
        mkOr uu____3415 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3421; rng = uu____3422;_}::[])
        -> let uu____3429 = unboxBool t1 in mkNot uu____3429 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___93_3432 = unboxBool t1 in
        {
          tm = (uu___93_3432.tm);
          freevars = (uu___93_3432.freevars);
          rng = (t.rng)
        }
    | uu____3435 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3464 = FStar_Options.unthrottle_inductives () in
        if uu____3464
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let mk_HasTypeWithFuel: term option -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | None  -> mk_HasType v1 t
        | Some f1 -> mk_HasTypeFuel f1 v1 t
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
      let uu____3528 =
        let uu____3532 = let uu____3534 = mkInteger' i norng in [uu____3534] in
        ("FString_const", uu____3532) in
      mkApp uu____3528 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3545 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____3545 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3562 =
         let uu____3566 =
           let uu____3568 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____3568] in
         ("SFuel", uu____3566) in
       mkApp uu____3562 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term option -> term option -> FStar_Range.range -> term option =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (Some p11,Some p21) ->
            let uu____3591 = mkAnd (p11, p21) r in Some uu____3591
        | (Some p,None )|(None ,Some p) -> Some p
        | (None ,None ) -> None
let mk_and_opt_l: term option Prims.list -> FStar_Range.range -> term option
  =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        None
let mk_and_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3624 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3624
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3635 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3635
let mk_haseq: term -> term =
  fun t  ->
    let uu____3641 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____3641
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3655 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____3655
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (fst fv)
    | App (op,l) ->
        let uu____3663 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3663
    | Labeled (t1,r1,r2) ->
        let uu____3667 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3667
    | LblPos (t1,s) ->
        let uu____3670 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3670
    | Quant (qop,l,uu____3673,uu____3674,t1) ->
        let uu____3684 = print_smt_term_list_list l in
        let uu____3685 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3684
          uu____3685
    | Let (es,body) ->
        let uu____3690 = print_smt_term_list es in
        let uu____3691 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____3690 uu____3691
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____3694 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____3694 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3704 =
             let uu____3705 =
               let uu____3706 = print_smt_term_list l1 in
               Prims.strcat uu____3706 " ] " in
             Prims.strcat "; [ " uu____3705 in
           Prims.strcat s uu____3704) "" l