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
  | Quant of (qop* term Prims.list Prims.list* Prims.int Prims.option* sort
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
    (qop* term Prims.list Prims.list* Prims.int Prims.option* sort
      Prims.list* term)
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
type caption = Prims.string Prims.option
type binders = (Prims.string* sort) Prims.list
type constructor_field = (Prims.string* sort* Prims.bool)
type constructor_t =
  (Prims.string* constructor_field Prims.list* sort* Prims.int* Prims.bool)
type constructors = constructor_t Prims.list
type decl =
  | DefPrelude
  | DeclFun of (Prims.string* sort Prims.list* sort* caption)
  | DefineFun of (Prims.string* sort Prims.list* sort* term* caption)
  | Assume of (term* caption* Prims.string)
  | Caption of Prims.string
  | Eval of term
  | Echo of Prims.string
  | Push
  | Pop
  | CheckSat
  | GetUnsatCore
  | SetOption of (Prims.string* Prims.string)
  | GetStatistics
  | GetReasonUnknown
let uu___is_DefPrelude: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____526 -> false
let uu___is_DeclFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____536 -> false
let __proj__DeclFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0
let uu___is_DefineFun: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____569 -> false
let __proj__DefineFun__item___0:
  decl -> (Prims.string* sort Prims.list* sort* term* caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0
let uu___is_Assume: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____602 -> false
let __proj__Assume__item___0: decl -> (term* caption* Prims.string) =
  fun projectee  -> match projectee with | Assume _0 -> _0
let uu___is_Caption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____623 -> false
let __proj__Caption__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0
let uu___is_Eval: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____635 -> false
let __proj__Eval__item___0: decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0
let uu___is_Echo: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____647 -> false
let __proj__Echo__item___0: decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0
let uu___is_Push: decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____658 -> false
let uu___is_Pop: decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____662 -> false
let uu___is_CheckSat: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____666 -> false
let uu___is_GetUnsatCore: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____670 -> false
let uu___is_SetOption: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____677 -> false
let __proj__SetOption__item___0: decl -> (Prims.string* Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0
let uu___is_GetStatistics: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetStatistics  -> true | uu____694 -> false
let uu___is_GetReasonUnknown: decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetReasonUnknown  -> true | uu____698 -> false
type decls_t = decl Prims.list
type error_label = (fv* Prims.string* FStar_Range.range)
type error_labels = error_label Prims.list
let fv_eq: fv -> fv -> Prims.bool =
  fun x  -> fun y  -> (Prims.fst x) = (Prims.fst y)
let fv_sort x = Prims.snd x
let freevar_eq: term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____735 -> false
let freevar_sort: term -> sort =
  fun uu___89_740  ->
    match uu___89_740 with
    | { tm = FreeV x; freevars = uu____742; rng = uu____743;_} -> fv_sort x
    | uu____750 -> failwith "impossible"
let fv_of_term: term -> fv =
  fun uu___90_753  ->
    match uu___90_753 with
    | { tm = FreeV fv; freevars = uu____755; rng = uu____756;_} -> fv
    | uu____763 -> failwith "impossible"
let rec freevars: term -> (Prims.string* sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer _|BoundV _ -> []
    | FreeV fv -> [fv]
    | App (uu____784,tms) -> FStar_List.collect freevars tms
    | Quant (_,_,_,_,t1)|Labeled (t1,_,_)|LblPos (t1,_) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
let free_variables: term -> fvs =
  fun t  ->
    let uu____811 = FStar_ST.read t.freevars in
    match uu____811 with
    | Some b -> b
    | None  ->
        let fvs =
          let uu____834 = freevars t in
          FStar_Util.remove_dups fv_eq uu____834 in
        (FStar_ST.write t.freevars (Some fvs); fvs)
let qop_to_string: qop -> Prims.string =
  fun uu___91_846  ->
    match uu___91_846 with | Forall  -> "forall" | Exists  -> "exists"
let op_to_string: op -> Prims.string =
  fun uu___92_849  ->
    match uu___92_849 with
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
let weightToSmt: Prims.int Prims.option -> Prims.string =
  fun uu___93_854  ->
    match uu___93_854 with
    | None  -> ""
    | Some i ->
        let uu____857 = FStar_Util.string_of_int i in
        FStar_Util.format1 ":weight %s\n" uu____857
let rec hash_of_term': term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____865 = FStar_Util.string_of_int i in
        Prims.strcat "@" uu____865
    | FreeV x ->
        let uu____869 =
          let uu____870 = strSort (Prims.snd x) in Prims.strcat ":" uu____870 in
        Prims.strcat (Prims.fst x) uu____869
    | App (op,tms) ->
        let uu____875 =
          let uu____876 =
            let uu____877 =
              let uu____878 = FStar_List.map hash_of_term tms in
              FStar_All.pipe_right uu____878 (FStar_String.concat " ") in
            Prims.strcat uu____877 ")" in
          Prims.strcat (op_to_string op) uu____876 in
        Prims.strcat "(" uu____875
    | Labeled (t1,r1,r2) ->
        let uu____884 = hash_of_term t1 in
        let uu____885 =
          let uu____886 = FStar_Range.string_of_range r2 in
          Prims.strcat r1 uu____886 in
        Prims.strcat uu____884 uu____885
    | LblPos (t1,r) ->
        let uu____889 =
          let uu____890 = hash_of_term t1 in
          Prims.strcat uu____890
            (Prims.strcat " :lblpos " (Prims.strcat r ")")) in
        Prims.strcat "(! " uu____889
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____904 =
          let uu____905 =
            let uu____906 =
              let uu____907 =
                let uu____908 = FStar_List.map strSort sorts in
                FStar_All.pipe_right uu____908 (FStar_String.concat " ") in
              let uu____911 =
                let uu____912 =
                  let uu____913 = hash_of_term body in
                  let uu____914 =
                    let uu____915 =
                      let uu____916 = weightToSmt wopt in
                      let uu____917 =
                        let uu____918 =
                          let uu____919 =
                            let uu____920 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____928 =
                                        FStar_List.map hash_of_term pats1 in
                                      FStar_All.pipe_right uu____928
                                        (FStar_String.concat " "))) in
                            FStar_All.pipe_right uu____920
                              (FStar_String.concat "; ") in
                          Prims.strcat uu____919 "))" in
                        Prims.strcat " " uu____918 in
                      Prims.strcat uu____916 uu____917 in
                    Prims.strcat " " uu____915 in
                  Prims.strcat uu____913 uu____914 in
                Prims.strcat ")(! " uu____912 in
              Prims.strcat uu____907 uu____911 in
            Prims.strcat " (" uu____906 in
          Prims.strcat (qop_to_string qop) uu____905 in
        Prims.strcat "(" uu____904
    | Let (es,body) ->
        let uu____936 =
          let uu____937 =
            let uu____938 = FStar_List.map hash_of_term es in
            FStar_All.pipe_right uu____938 (FStar_String.concat " ") in
          let uu____941 =
            let uu____942 =
              let uu____943 = hash_of_term body in Prims.strcat uu____943 ")" in
            Prims.strcat ") " uu____942 in
          Prims.strcat uu____937 uu____941 in
        Prims.strcat "(let (" uu____936
and hash_of_term: term -> Prims.string = fun tm  -> hash_of_term' tm.tm
let mk: term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____951 = FStar_Util.mk_ref None in
      { tm = t; freevars = uu____951; rng = r }
let mkTrue: FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r
let mkFalse: FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r
let mkInteger: Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____980 =
        let uu____981 = FStar_Util.ensure_decimal i in Integer uu____981 in
      mk uu____980 r
let mkInteger': Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____988 = FStar_Util.string_of_int i in mkInteger uu____988 r
let mkBoundV: Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r
let mkFreeV: (Prims.string* sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r
let mkApp': (op* term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r
let mkApp: (Prims.string* term Prims.list) -> FStar_Range.range -> term =
  fun uu____1024  ->
    fun r  -> match uu____1024 with | (s,args) -> mk (App ((Var s), args)) r
let mkNot: term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1040) -> mkFalse r
      | App (FalseOp ,uu____1043) -> mkTrue r
      | uu____1046 -> mkApp' (Not, [t]) r
let mkAnd: (term* term) -> FStar_Range.range -> term =
  fun uu____1054  ->
    fun r  ->
      match uu____1054 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1060),uu____1061) -> t2
           | (uu____1064,App (TrueOp ,uu____1065)) -> t1
           | (App (FalseOp ,_),_)|(_,App (FalseOp ,_)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1081,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1087) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1091 -> mkApp' (And, [t1; t2]) r)
let mkOr: (term* term) -> FStar_Range.range -> term =
  fun uu____1101  ->
    fun r  ->
      match uu____1101 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,_),_)|(_,App (TrueOp ,_)) -> mkTrue r
           | (App (FalseOp ,uu____1113),uu____1114) -> t2
           | (uu____1117,App (FalseOp ,uu____1118)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1128,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1134) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1138 -> mkApp' (Or, [t1; t2]) r)
let mkImp: (term* term) -> FStar_Range.range -> term =
  fun uu____1148  ->
    fun r  ->
      match uu____1148 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (_,App (TrueOp ,_))|(App (FalseOp ,_),_) -> mkTrue r
           | (App (TrueOp ,uu____1160),uu____1161) -> t2
           | (uu____1164,App (Imp ,t1'::t2'::[])) ->
               let uu____1168 =
                 let uu____1172 =
                   let uu____1174 = mkAnd (t1, t1') r in [uu____1174; t2'] in
                 (Imp, uu____1172) in
               mkApp' uu____1168 r
           | uu____1176 -> mkApp' (Imp, [t1; t2]) r)
let mk_bin_op: op -> (term* term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1189  ->
      fun r  -> match uu____1189 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
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
  fun uu____1276  ->
    fun r  ->
      match uu____1276 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1284) -> t2
           | App (FalseOp ,uu____1287) -> t3
           | uu____1290 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1291),App (TrueOp ,uu____1292)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1297),uu____1298) ->
                    let uu____1301 =
                      let uu____1304 = mkNot t1 t1.rng in (uu____1304, t3) in
                    mkImp uu____1301 r
                | (uu____1305,App (TrueOp ,uu____1306)) -> mkImp (t1, t2) r
                | (uu____1309,uu____1310) -> mkApp' (ITE, [t1; t2; t3]) r))
let mkCases: term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
let mkQuant:
  (qop* term Prims.list Prims.list* Prims.int Prims.option* sort Prims.list*
    term) -> FStar_Range.range -> term
  =
  fun uu____1338  ->
    fun r  ->
      match uu____1338 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1365) -> body
             | uu____1368 -> mk (Quant (qop, pats, wopt, vars, body)) r)
let mkLet: (term Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1380  ->
    fun r  ->
      match uu____1380 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
let abstr: fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs in
      let index_of fv =
        let uu____1408 = FStar_Util.try_find_index (fv_eq fv) fvs in
        match uu____1408 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1"))) in
      let rec aux ix t1 =
        let uu____1422 = FStar_ST.read t1.freevars in
        match uu____1422 with
        | Some [] -> t1
        | uu____1438 ->
            (match t1.tm with
             | Integer _|BoundV _ -> t1
             | FreeV x ->
                 let uu____1448 = index_of x in
                 (match uu____1448 with
                  | None  -> t1
                  | Some i -> mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1455 =
                   let uu____1459 = FStar_List.map (aux ix) tms in
                   (op, uu____1459) in
                 mkApp' uu____1455 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1465 =
                   let uu____1466 =
                     let uu____1470 = aux ix t2 in (uu____1470, r1, r2) in
                   Labeled uu____1466 in
                 mk uu____1465 t2.rng
             | LblPos (t2,r) ->
                 let uu____1473 =
                   let uu____1474 =
                     let uu____1477 = aux ix t2 in (uu____1477, r) in
                   LblPos uu____1474 in
                 mk uu____1473 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars in
                 let uu____1493 =
                   let uu____1503 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1)))) in
                   let uu____1514 = aux (ix + n1) body in
                   (qop, uu____1503, wopt, vars, uu____1514) in
                 mkQuant uu____1493 t1.rng
             | Let (es,body) ->
                 let uu____1525 =
                   FStar_List.fold_left
                     (fun uu____1532  ->
                        fun e  ->
                          match uu____1532 with
                          | (ix1,l) ->
                              let uu____1544 =
                                let uu____1546 = aux ix1 e in uu____1546 :: l in
                              ((ix1 + (Prims.parse_int "1")), uu____1544))
                     (ix, []) es in
                 (match uu____1525 with
                  | (ix1,es_rev) ->
                      let uu____1553 =
                        let uu____1557 = aux ix1 body in
                        ((FStar_List.rev es_rev), uu____1557) in
                      mkLet uu____1553 t1.rng)) in
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
            let uu____1588 =
              let uu____1592 = FStar_List.map (aux shift) tms2 in
              (op, uu____1592) in
            mkApp' uu____1588 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1598 =
              let uu____1599 =
                let uu____1603 = aux shift t2 in (uu____1603, r1, r2) in
              Labeled uu____1599 in
            mk uu____1598 t2.rng
        | LblPos (t2,r) ->
            let uu____1606 =
              let uu____1607 =
                let uu____1610 = aux shift t2 in (uu____1610, r) in
              LblPos uu____1607 in
            mk uu____1606 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars in
            let shift1 = shift + m in
            let uu____1629 =
              let uu____1639 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1))) in
              let uu____1648 = aux shift1 body in
              (qop, uu____1639, wopt, vars, uu____1648) in
            mkQuant uu____1629 t1.rng
        | Let (es,body) ->
            let uu____1657 =
              FStar_List.fold_left
                (fun uu____1664  ->
                   fun e  ->
                     match uu____1664 with
                     | (ix,es1) ->
                         let uu____1676 =
                           let uu____1678 = aux shift e in uu____1678 :: es1 in
                         ((shift + (Prims.parse_int "1")), uu____1676))
                (shift, []) es in
            (match uu____1657 with
             | (shift1,es_rev) ->
                 let uu____1685 =
                   let uu____1689 = aux shift1 body in
                   ((FStar_List.rev es_rev), uu____1689) in
                 mkLet uu____1685 t1.rng) in
      aux (Prims.parse_int "0") t
let subst: term -> fv -> term -> term =
  fun t  ->
    fun fv  -> fun s  -> let uu____1700 = abstr [fv] t in inst [s] uu____1700
let mkQuant':
  (qop* term Prims.list Prims.list* Prims.int Prims.option* fv Prims.list*
    term) -> FStar_Range.range -> term
  =
  fun uu____1714  ->
    match uu____1714 with
    | (qop,pats,wopt,vars,body) ->
        let uu____1739 =
          let uu____1749 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars))) in
          let uu____1758 = FStar_List.map fv_sort vars in
          let uu____1762 = abstr vars body in
          (qop, uu____1749, wopt, uu____1758, uu____1762) in
        mkQuant uu____1739
let mkForall'':
  (pat Prims.list Prims.list* Prims.int Prims.option* sort Prims.list* term)
    -> FStar_Range.range -> term
  =
  fun uu____1779  ->
    fun r  ->
      match uu____1779 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
let mkForall':
  (pat Prims.list Prims.list* Prims.int Prims.option* fvs* term) ->
    FStar_Range.range -> term
  =
  fun uu____1816  ->
    fun r  ->
      match uu____1816 with
      | (pats,wopt,vars,body) ->
          let uu____1835 = mkQuant' (Forall, pats, wopt, vars, body) in
          uu____1835 r
let mkForall:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1850  ->
    fun r  ->
      match uu____1850 with
      | (pats,vars,body) ->
          let uu____1864 = mkQuant' (Forall, pats, None, vars, body) in
          uu____1864 r
let mkExists:
  (pat Prims.list Prims.list* fvs* term) -> FStar_Range.range -> term =
  fun uu____1879  ->
    fun r  ->
      match uu____1879 with
      | (pats,vars,body) ->
          let uu____1893 = mkQuant' (Exists, pats, None, vars, body) in
          uu____1893 r
let mkLet': ((fv* term) Prims.list* term) -> FStar_Range.range -> term =
  fun uu____1908  ->
    fun r  ->
      match uu____1908 with
      | (bindings,body) ->
          let uu____1923 = FStar_List.split bindings in
          (match uu____1923 with
           | (vars,es) ->
               let uu____1934 =
                 let uu____1938 = abstr vars body in (es, uu____1938) in
               mkLet uu____1934 r)
let norng: FStar_Range.range = FStar_Range.dummyRange
let mkDefineFun:
  (Prims.string* (Prims.string* sort) Prims.list* sort* term* caption) ->
    decl
  =
  fun uu____1950  ->
    match uu____1950 with
    | (nm,vars,s,tm,c) ->
        let uu____1970 =
          let uu____1977 = FStar_List.map fv_sort vars in
          let uu____1981 = abstr vars tm in
          (nm, uu____1977, s, uu____1981, c) in
        DefineFun uu____1970
let constr_id_of_sort: sort -> Prims.string =
  fun sort  ->
    let uu____1986 = strSort sort in
    FStar_Util.format1 "%s_constr_id" uu____1986
let fresh_token: (Prims.string* sort) -> Prims.int -> decl =
  fun uu____1993  ->
    fun id  ->
      match uu____1993 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name in
          let uu____2000 =
            let uu____2004 =
              let uu____2005 =
                let uu____2008 = mkInteger' id norng in
                let uu____2009 =
                  let uu____2010 =
                    let uu____2014 = constr_id_of_sort sort in
                    let uu____2015 =
                      let uu____2017 = mkApp (tok_name, []) norng in
                      [uu____2017] in
                    (uu____2014, uu____2015) in
                  mkApp uu____2010 norng in
                (uu____2008, uu____2009) in
              mkEq uu____2005 norng in
            (uu____2004, (Some "fresh token"), a_name) in
          Assume uu____2000
let fresh_constructor:
  (Prims.string* sort Prims.list* sort* Prims.int) -> decl =
  fun uu____2028  ->
    match uu____2028 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2047 =
                      let uu____2050 =
                        let uu____2051 = FStar_Util.string_of_int i in
                        Prims.strcat "x_" uu____2051 in
                      (uu____2050, s) in
                    mkFreeV uu____2047 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let cid_app =
          let uu____2057 =
            let uu____2061 = constr_id_of_sort sort in (uu____2061, [capp]) in
          mkApp uu____2057 norng in
        let a_name = Prims.strcat "constructor_distinct_" name in
        let uu____2064 =
          let uu____2068 =
            let uu____2069 =
              let uu____2075 =
                let uu____2076 =
                  let uu____2079 = mkInteger id1 norng in
                  (uu____2079, cid_app) in
                mkEq uu____2076 norng in
              ([[capp]], bvar_names, uu____2075) in
            mkForall uu____2069 norng in
          (uu____2068, (Some "Constructor distinct"), a_name) in
        Assume uu____2064
let injective_constructor:
  (Prims.string* constructor_field Prims.list* sort) -> decl Prims.list =
  fun uu____2092  ->
    match uu____2092 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields in
        let bvar_name i =
          let uu____2108 = FStar_Util.string_of_int i in
          Prims.strcat "x_" uu____2108 in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1")) in
        let bvar i s =
          let uu____2125 = let uu____2128 = bvar_name i in (uu____2128, s) in
          mkFreeV uu____2125 in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2137  ->
                    match uu____2137 with
                    | (uu____2141,s,uu____2143) ->
                        let uu____2144 = bvar i s in uu____2144 norng)) in
        let bvar_names = FStar_List.map fv_of_term bvars in
        let capp = mkApp (name, bvars) norng in
        let uu____2151 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2162  ->
                    match uu____2162 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng in
                        let proj_name =
                          DeclFun (name1, [sort], s, (Some "Projector")) in
                        if projectible
                        then
                          let a_name =
                            Prims.strcat "projection_inverse_" name1 in
                          let uu____2177 =
                            let uu____2179 =
                              let uu____2180 =
                                let uu____2184 =
                                  let uu____2185 =
                                    let uu____2191 =
                                      let uu____2192 =
                                        let uu____2195 =
                                          let uu____2196 = bvar i s in
                                          uu____2196 norng in
                                        (cproj_app, uu____2195) in
                                      mkEq uu____2192 norng in
                                    ([[capp]], bvar_names, uu____2191) in
                                  mkForall uu____2185 norng in
                                (uu____2184, (Some "Projection inverse"),
                                  a_name) in
                              Assume uu____2180 in
                            [uu____2179] in
                          proj_name :: uu____2177
                        else [proj_name])) in
        FStar_All.pipe_right uu____2151 FStar_List.flatten
let constructor_to_decl: constructor_t -> decl Prims.list =
  fun uu____2211  ->
    match uu____2211 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2227  ->
                  match uu____2227 with
                  | (uu____2231,sort1,uu____2233) -> sort1)) in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor")) in
        let cid = fresh_constructor (name, field_sorts, sort, id) in
        let disc =
          let disc_name = Prims.strcat "is-" name in
          let xfv = ("x", sort) in
          let xx = mkFreeV xfv norng in
          let disc_eq =
            let uu____2246 =
              let uu____2249 =
                let uu____2250 =
                  let uu____2254 = constr_id_of_sort sort in
                  (uu____2254, [xx]) in
                mkApp uu____2250 norng in
              let uu____2256 =
                let uu____2257 = FStar_Util.string_of_int id in
                mkInteger uu____2257 norng in
              (uu____2249, uu____2256) in
            mkEq uu____2246 norng in
          let uu____2258 =
            let uu____2266 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2289  ->
                        match uu____2289 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2306 = mkApp (proj, [xx]) norng in
                              (uu____2306, [])
                            else
                              (let fi =
                                 let uu____2317 =
                                   let uu____2318 =
                                     FStar_Util.string_of_int i in
                                   Prims.strcat "f_" uu____2318 in
                                 (uu____2317, s) in
                               let uu____2319 = mkFreeV fi norng in
                               (uu____2319, [fi])))) in
            FStar_All.pipe_right uu____2266 FStar_List.split in
          match uu____2258 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars in
              let disc_inv_body =
                let uu____2362 =
                  let uu____2365 = mkApp (name, proj_terms) norng in
                  (xx, uu____2365) in
                mkEq uu____2362 norng in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2370 -> mkExists ([], ex_vars1, disc_inv_body) norng in
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
        let uu____2393 =
          let uu____2395 =
            let uu____2396 = FStar_Util.format1 "<start constructor %s>" name in
            Caption uu____2396 in
          uu____2395 :: cdecl :: cid :: projs in
        let uu____2397 =
          let uu____2399 =
            let uu____2401 =
              let uu____2402 =
                FStar_Util.format1 "</end constructor %s>" name in
              Caption uu____2402 in
            [uu____2401] in
          FStar_List.append [disc] uu____2399 in
        FStar_List.append uu____2393 uu____2397
let name_binders_inner:
  Prims.string Prims.option ->
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
          let uu____2432 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2455  ->
                    fun s  ->
                      match uu____2455 with
                      | (names,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2483 -> "@u" in
                          let prefix2 =
                            match prefix_opt with
                            | None  -> prefix1
                            | Some p -> Prims.strcat p prefix1 in
                          let nm =
                            let uu____2487 = FStar_Util.string_of_int n1 in
                            Prims.strcat prefix2 uu____2487 in
                          let names1 = (nm, s) :: names in
                          let b =
                            let uu____2495 = strSort s in
                            FStar_Util.format2 "(%s %s)" nm uu____2495 in
                          (names1, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start)) in
          match uu____2432 with
          | (names,binders,n1) -> (names, (FStar_List.rev binders), n1)
let name_macro_binders:
  sort Prims.list ->
    ((Prims.string* sort) Prims.list* Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2537 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts in
    match uu____2537 with
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
            (let uu____2591 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "%s.%s" enclosing_name uu____2591) in
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
                             "Prims.guard_free",{ tm = BoundV uu____2613;
                                                  freevars = uu____2614;
                                                  rng = uu____2615;_}::[])
                            -> tm
                        | App (Var "Prims.guard_free",p::[]) -> p
                        | uu____2623 -> tm)))) in
      let rec aux' depth n1 names t1 =
        let aux1 = aux (depth + (Prims.parse_int "1")) in
        match t1.tm with
        | Integer i -> i
        | BoundV i ->
            let uu____2659 = FStar_List.nth names i in
            FStar_All.pipe_right uu____2659 Prims.fst
        | FreeV x -> Prims.fst x
        | App (op,[]) -> op_to_string op
        | App (op,tms) ->
            let uu____2669 =
              let uu____2670 = FStar_List.map (aux1 n1 names) tms in
              FStar_All.pipe_right uu____2670 (FStar_String.concat "\n") in
            FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2669
        | Labeled (t2,uu____2674,uu____2675) -> aux1 n1 names t2
        | LblPos (t2,s) ->
            let uu____2678 = aux1 n1 names t2 in
            FStar_Util.format2 "(! %s :lblpos %s)" uu____2678 s
        | Quant (qop,pats,wopt,sorts,body) ->
            let qid = next_qid () in
            let uu____2693 = name_binders_inner None names n1 sorts in
            (match uu____2693 with
             | (names1,binders,n2) ->
                 let binders1 =
                   FStar_All.pipe_right binders (FStar_String.concat " ") in
                 let pats1 = remove_guard_free pats in
                 let pats_str =
                   match pats1 with
                   | []::[]|[] -> ";;no pats"
                   | uu____2721 ->
                       let uu____2724 =
                         FStar_All.pipe_right pats1
                           (FStar_List.map
                              (fun pats2  ->
                                 let uu____2732 =
                                   let uu____2733 =
                                     FStar_List.map
                                       (fun p  ->
                                          let uu____2736 = aux1 n2 names1 p in
                                          FStar_Util.format1 "%s" uu____2736)
                                       pats2 in
                                   FStar_String.concat " " uu____2733 in
                                 FStar_Util.format1 "\n:pattern (%s)"
                                   uu____2732)) in
                       FStar_All.pipe_right uu____2724
                         (FStar_String.concat "\n") in
                 let uu____2738 =
                   let uu____2740 =
                     let uu____2742 =
                       let uu____2744 = aux1 n2 names1 body in
                       let uu____2745 =
                         let uu____2747 = weightToSmt wopt in
                         [uu____2747; pats_str; qid] in
                       uu____2744 :: uu____2745 in
                     binders1 :: uu____2742 in
                   (qop_to_string qop) :: uu____2740 in
                 FStar_Util.format "(%s (%s)\n (! %s\n %s\n%s\n:qid %s))"
                   uu____2738)
        | Let (es,body) ->
            let uu____2752 =
              FStar_List.fold_left
                (fun uu____2767  ->
                   fun e  ->
                     match uu____2767 with
                     | (names0,binders,n0) ->
                         let nm =
                           let uu____2795 = FStar_Util.string_of_int n0 in
                           Prims.strcat "@lb" uu____2795 in
                         let names01 = (nm, Term_sort) :: names0 in
                         let b =
                           let uu____2803 = aux1 n1 names e in
                           FStar_Util.format2 "(%s %s)" nm uu____2803 in
                         (names01, (b :: binders),
                           (n0 + (Prims.parse_int "1")))) (names, [], n1) es in
            (match uu____2752 with
             | (names1,binders,n2) ->
                 let uu____2821 = aux1 n2 names1 body in
                 FStar_Util.format2 "(let (%s) %s)"
                   (FStar_String.concat " " binders) uu____2821)
      and aux depth n1 names t1 =
        let s = aux' depth n1 names t1 in
        if t1.rng <> norng
        then
          let uu____2828 = FStar_Range.string_of_range t1.rng in
          let uu____2829 = FStar_Range.string_of_use_range t1.rng in
          FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2828
            uu____2829 s
        else s in
      aux (Prims.parse_int "0") (Prims.parse_int "0") [] t
let caption_to_string: Prims.string Prims.option -> Prims.string =
  fun uu___94_2834  ->
    match uu___94_2834 with
    | None  -> ""
    | Some c ->
        let uu____2837 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____2846 -> (hd1, "...") in
        (match uu____2837 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
let rec declToSmt: Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_' in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____2863 =
            FStar_All.pipe_right (FStar_Util.splitlines c)
              (fun uu___95_2865  ->
                 match uu___95_2865 with | [] -> "" | h::t -> h) in
          FStar_Util.format1 "\n; %s" uu____2863
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts in
          let uu____2878 = caption_to_string c in
          let uu____2879 = strSort retsort in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2878 f
            (FStar_String.concat " " l) uu____2879
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2887 = name_macro_binders arg_sorts in
          (match uu____2887 with
           | (names,binders) ->
               let body1 =
                 let uu____2905 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names in
                 inst uu____2905 body in
               let uu____2912 = caption_to_string c in
               let uu____2913 = strSort retsort in
               let uu____2914 = termToSmt (escape f) body1 in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2912
                 f (FStar_String.concat " " binders) uu____2913 uu____2914)
      | Assume (t,c,n1) ->
          let n2 = escape n1 in
          let uu____2919 = caption_to_string c in
          let uu____2920 = termToSmt n2 t in
          FStar_Util.format3 "%s(assert (! %s\n:named %s))" uu____2919
            uu____2920 n2
      | Eval t ->
          let uu____2922 = termToSmt "eval" t in
          FStar_Util.format1 "(eval %s)" uu____2922
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
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
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(declare-fun NoHoist (Term Bool) Bool)\n;;no-hoist\n(assert (forall ((dummy Term) (b Bool))\n(! (= (NoHoist dummy b)\nb)\n:pattern ((NoHoist dummy b)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n" in
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
      let uu____3126 =
        let uu____3128 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl) in
        FStar_All.pipe_right uu____3128
          (FStar_List.map (declToSmt z3options)) in
      FStar_All.pipe_right uu____3126 (FStar_String.concat "\n") in
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
      let uu____3153 =
        let uu____3157 = let uu____3159 = mkInteger' i norng in [uu____3159] in
        ("Tm_uvar", uu____3157) in
      mkApp uu____3153 r
let mk_Term_unit: term = mkApp ("Tm_unit", []) norng
let boxInt: term -> term = fun t  -> mkApp ("BoxInt", [t]) t.rng
let unboxInt: term -> term = fun t  -> mkApp ("BoxInt_proj_0", [t]) t.rng
let boxBool: term -> term = fun t  -> mkApp ("BoxBool", [t]) t.rng
let unboxBool: term -> term = fun t  -> mkApp ("BoxBool_proj_0", [t]) t.rng
let boxString: term -> term = fun t  -> mkApp ("BoxString", [t]) t.rng
let unboxString: term -> term =
  fun t  -> mkApp ("BoxString_proj_0", [t]) t.rng
let boxRef: term -> term = fun t  -> mkApp ("BoxRef", [t]) t.rng
let unboxRef: term -> term = fun t  -> mkApp ("BoxRef_proj_0", [t]) t.rng
let boxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | uu____3200 -> Prims.raise FStar_Util.Impos
let unboxTerm: sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____3207 -> Prims.raise FStar_Util.Impos
let mk_PreType: term -> term = fun t  -> mkApp ("PreType", [t]) t.rng
let mk_Valid: term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3215::t1::t2::[]);
                       freevars = uu____3218; rng = uu____3219;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3226::t1::t2::[]);
                       freevars = uu____3229; rng = uu____3230;_}::[])
        -> let uu____3237 = mkEq (t1, t2) norng in mkNot uu____3237 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3240; rng = uu____3241;_}::[])
        ->
        let uu____3248 =
          let uu____3251 = unboxInt t1 in
          let uu____3252 = unboxInt t2 in (uu____3251, uu____3252) in
        mkLTE uu____3248 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3255; rng = uu____3256;_}::[])
        ->
        let uu____3263 =
          let uu____3266 = unboxInt t1 in
          let uu____3267 = unboxInt t2 in (uu____3266, uu____3267) in
        mkLT uu____3263 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3270; rng = uu____3271;_}::[])
        ->
        let uu____3278 =
          let uu____3281 = unboxInt t1 in
          let uu____3282 = unboxInt t2 in (uu____3281, uu____3282) in
        mkGTE uu____3278 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3285; rng = uu____3286;_}::[])
        ->
        let uu____3293 =
          let uu____3296 = unboxInt t1 in
          let uu____3297 = unboxInt t2 in (uu____3296, uu____3297) in
        mkGT uu____3293 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3300; rng = uu____3301;_}::[])
        ->
        let uu____3308 =
          let uu____3311 = unboxBool t1 in
          let uu____3312 = unboxBool t2 in (uu____3311, uu____3312) in
        mkAnd uu____3308 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3315; rng = uu____3316;_}::[])
        ->
        let uu____3323 =
          let uu____3326 = unboxBool t1 in
          let uu____3327 = unboxBool t2 in (uu____3326, uu____3327) in
        mkOr uu____3323 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3329; rng = uu____3330;_}::[])
        -> let uu____3337 = unboxBool t1 in mkNot uu____3337 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___96_3340 = unboxBool t1 in
        {
          tm = (uu___96_3340.tm);
          freevars = (uu___96_3340.freevars);
          rng = (t.rng)
        }
    | uu____3343 -> mkApp ("Valid", [t]) t.rng
let mk_HasType: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng
let mk_HasTypeZ: term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng
let mk_IsTyped: term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng
let mk_HasTypeFuel: term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3372 = FStar_Options.unthrottle_inductives () in
        if uu____3372
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
let mk_HasTypeWithFuel: term Prims.option -> term -> term -> term =
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
      let uu____3436 =
        let uu____3440 = let uu____3442 = mkInteger' i norng in [uu____3442] in
        ("FString_const", uu____3440) in
      mkApp uu____3436 r
let mk_Precedes: term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3453 = mkApp ("Precedes", [x1; x2]) r in
        FStar_All.pipe_right uu____3453 mk_Valid
let mk_LexCons: term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r
let rec n_fuel: Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3470 =
         let uu____3474 =
           let uu____3476 = n_fuel (n1 - (Prims.parse_int "1")) in
           [uu____3476] in
         ("SFuel", uu____3474) in
       mkApp uu____3470 norng)
let fuel_2: term = n_fuel (Prims.parse_int "2")
let fuel_100: term = n_fuel (Prims.parse_int "100")
let mk_and_opt:
  term Prims.option ->
    term Prims.option -> FStar_Range.range -> term Prims.option
  =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (Some p11,Some p21) ->
            let uu____3499 = mkAnd (p11, p21) r in Some uu____3499
        | (Some p,None )|(None ,Some p) -> Some p
        | (None ,None ) -> None
let mk_and_opt_l:
  term Prims.option Prims.list -> FStar_Range.range -> term Prims.option =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        None
let mk_and_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3532 = mkTrue r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3532
let mk_or_l: term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3543 = mkFalse r in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3543
let mk_haseq: term -> term =
  fun t  ->
    let uu____3549 = mkApp ("Prims.hasEq", [t]) t.rng in mk_Valid uu____3549
let rec print_smt_term: term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3563 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "(BoundV %s)" uu____3563
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (Prims.fst fv)
    | App (op,l) ->
        let uu____3571 = print_smt_term_list l in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3571
    | Labeled (t1,r1,r2) ->
        let uu____3575 = print_smt_term t1 in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3575
    | LblPos (t1,s) ->
        let uu____3578 = print_smt_term t1 in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3578
    | Quant (qop,l,uu____3581,uu____3582,t1) ->
        let uu____3592 = print_smt_term_list_list l in
        let uu____3593 = print_smt_term t1 in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3592
          uu____3593
    | Let (es,body) ->
        let uu____3598 = print_smt_term_list es in
        let uu____3599 = print_smt_term body in
        FStar_Util.format2 "(let %s %s)" uu____3598 uu____3599
and print_smt_term_list: term Prims.list -> Prims.string =
  fun l  ->
    let uu____3602 = FStar_List.map print_smt_term l in
    FStar_All.pipe_right uu____3602 (FStar_String.concat " ")
and print_smt_term_list_list: term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3612 =
             let uu____3613 =
               let uu____3614 = print_smt_term_list l1 in
               Prims.strcat uu____3614 " ] " in
             Prims.strcat "; [ " uu____3613 in
           Prims.strcat s uu____3612) "" l