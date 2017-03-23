open Prims
type sort =
  | Bool_sort 
  | Int_sort 
  | String_sort 
  | Ref_sort 
  | Term_sort 
  | Fuel_sort 
  | Array of (sort * sort) 
  | Arrow of (sort * sort) 
  | Sort of Prims.string 
let uu___is_Bool_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool_sort  -> true | uu____17 -> false
  
let uu___is_Int_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Int_sort  -> true | uu____21 -> false
  
let uu___is_String_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | String_sort  -> true | uu____25 -> false
  
let uu___is_Ref_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Ref_sort  -> true | uu____29 -> false
  
let uu___is_Term_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_sort  -> true | uu____33 -> false
  
let uu___is_Fuel_sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Fuel_sort  -> true | uu____37 -> false
  
let uu___is_Array : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Array _0 -> true | uu____44 -> false
  
let __proj__Array__item___0 : sort -> (sort * sort) =
  fun projectee  -> match projectee with | Array _0 -> _0 
let uu___is_Arrow : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____64 -> false
  
let __proj__Arrow__item___0 : sort -> (sort * sort) =
  fun projectee  -> match projectee with | Arrow _0 -> _0 
let uu___is_Sort : sort -> Prims.bool =
  fun projectee  ->
    match projectee with | Sort _0 -> true | uu____82 -> false
  
let __proj__Sort__item___0 : sort -> Prims.string =
  fun projectee  -> match projectee with | Sort _0 -> _0 
let rec strSort : sort -> Prims.string =
  fun x  ->
    match x with
    | Bool_sort  -> "Bool"
    | Int_sort  -> "Int"
    | Term_sort  -> "Term"
    | String_sort  -> "FString"
    | Ref_sort  -> "Ref"
    | Fuel_sort  -> "Fuel"
    | Array (s1,s2) ->
        let uu____95 = strSort s1  in
        let uu____96 = strSort s2  in
        FStar_Util.format2 "(Array %s %s)" uu____95 uu____96
    | Arrow (s1,s2) ->
        let uu____99 = strSort s1  in
        let uu____100 = strSort s2  in
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
let uu___is_TrueOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | TrueOp  -> true | uu____108 -> false
  
let uu___is_FalseOp : op -> Prims.bool =
  fun projectee  ->
    match projectee with | FalseOp  -> true | uu____112 -> false
  
let uu___is_Not : op -> Prims.bool =
  fun projectee  -> match projectee with | Not  -> true | uu____116 -> false 
let uu___is_And : op -> Prims.bool =
  fun projectee  -> match projectee with | And  -> true | uu____120 -> false 
let uu___is_Or : op -> Prims.bool =
  fun projectee  -> match projectee with | Or  -> true | uu____124 -> false 
let uu___is_Imp : op -> Prims.bool =
  fun projectee  -> match projectee with | Imp  -> true | uu____128 -> false 
let uu___is_Iff : op -> Prims.bool =
  fun projectee  -> match projectee with | Iff  -> true | uu____132 -> false 
let uu___is_Eq : op -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____136 -> false 
let uu___is_LT : op -> Prims.bool =
  fun projectee  -> match projectee with | LT  -> true | uu____140 -> false 
let uu___is_LTE : op -> Prims.bool =
  fun projectee  -> match projectee with | LTE  -> true | uu____144 -> false 
let uu___is_GT : op -> Prims.bool =
  fun projectee  -> match projectee with | GT  -> true | uu____148 -> false 
let uu___is_GTE : op -> Prims.bool =
  fun projectee  -> match projectee with | GTE  -> true | uu____152 -> false 
let uu___is_Add : op -> Prims.bool =
  fun projectee  -> match projectee with | Add  -> true | uu____156 -> false 
let uu___is_Sub : op -> Prims.bool =
  fun projectee  -> match projectee with | Sub  -> true | uu____160 -> false 
let uu___is_Div : op -> Prims.bool =
  fun projectee  -> match projectee with | Div  -> true | uu____164 -> false 
let uu___is_Mul : op -> Prims.bool =
  fun projectee  -> match projectee with | Mul  -> true | uu____168 -> false 
let uu___is_Minus : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Minus  -> true | uu____172 -> false
  
let uu___is_Mod : op -> Prims.bool =
  fun projectee  -> match projectee with | Mod  -> true | uu____176 -> false 
let uu___is_ITE : op -> Prims.bool =
  fun projectee  -> match projectee with | ITE  -> true | uu____180 -> false 
let uu___is_Var : op -> Prims.bool =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____185 -> false
  
let __proj__Var__item___0 : op -> Prims.string =
  fun projectee  -> match projectee with | Var _0 -> _0 
type qop =
  | Forall 
  | Exists 
let uu___is_Forall : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall  -> true | uu____196 -> false
  
let uu___is_Exists : qop -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists  -> true | uu____200 -> false
  
type term' =
  | Integer of Prims.string 
  | BoundV of Prims.int 
  | FreeV of (Prims.string * sort) 
  | App of (op * term Prims.list) 
  | Quant of (qop * term Prims.list Prims.list * Prims.int Prims.option *
  sort Prims.list * term) 
  | Let of (term Prims.list * term) 
  | Labeled of (term * Prims.string * FStar_Range.range) 
  | LblPos of (term * Prims.string) 
and term =
  {
  tm: term' ;
  freevars: (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo ;
  rng: FStar_Range.range }
let uu___is_Integer : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____265 -> false
  
let __proj__Integer__item___0 : term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let uu___is_BoundV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____277 -> false
  
let __proj__BoundV__item___0 : term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let uu___is_FreeV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____291 -> false
  
let __proj__FreeV__item___0 : term' -> (Prims.string * sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____312 -> false
  
let __proj__App__item___0 : term' -> (op * term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Quant : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____342 -> false
  
let __proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int Prims.option * sort
      Prims.list * term)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let uu___is_Let : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____384 -> false
  
let __proj__Let__item___0 : term' -> (term Prims.list * term) =
  fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____408 -> false
  
let __proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_LblPos : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____431 -> false
  
let __proj__LblPos__item___0 : term' -> (term * Prims.string) =
  fun projectee  -> match projectee with | LblPos _0 -> _0 
type pat = term
type fv = (Prims.string * sort)
type fvs = (Prims.string * sort) Prims.list
type caption = Prims.string Prims.option
type binders = (Prims.string * sort) Prims.list
type constructor_field = (Prims.string * sort * Prims.bool)
type constructor_t =
  (Prims.string * constructor_field Prims.list * sort * Prims.int *
    Prims.bool)
type constructors = constructor_t Prims.list
type decl =
  | DefPrelude 
  | DeclFun of (Prims.string * sort Prims.list * sort * caption) 
  | DefineFun of (Prims.string * sort Prims.list * sort * term * caption) 
  | Assume of (term * caption * Prims.string Prims.option) 
  | Caption of Prims.string 
  | Eval of term 
  | Echo of Prims.string 
  | Push 
  | Pop 
  | CheckSat 
  | GetUnsatCore 
  | SetOption of (Prims.string * Prims.string) 
  | PrintStats 
let uu___is_DefPrelude : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefPrelude  -> true | uu____527 -> false
  
let uu___is_DeclFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____537 -> false
  
let __proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let uu___is_DefineFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____570 -> false
  
let __proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let uu___is_Assume : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____604 -> false
  
let __proj__Assume__item___0 :
  decl -> (term * caption * Prims.string Prims.option) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_Caption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____628 -> false
  
let __proj__Caption__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let uu___is_Eval : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____640 -> false
  
let __proj__Eval__item___0 : decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let uu___is_Echo : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____652 -> false
  
let __proj__Echo__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let uu___is_Push : decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____663 -> false 
let uu___is_Pop : decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____667 -> false 
let uu___is_CheckSat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____671 -> false
  
let uu___is_GetUnsatCore : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____675 -> false
  
let uu___is_SetOption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____682 -> false
  
let __proj__SetOption__item___0 : decl -> (Prims.string * Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let uu___is_PrintStats : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | PrintStats  -> true | uu____699 -> false
  
type decls_t = decl Prims.list
type error_label = (fv * Prims.string * FStar_Range.range)
type error_labels = error_label Prims.list
let fv_eq : fv -> fv -> Prims.bool =
  fun x  -> fun y  -> (Prims.fst x) = (Prims.fst y) 
let fv_sort x = Prims.snd x 
let freevar_eq : term -> term -> Prims.bool =
  fun x  ->
    fun y  ->
      match ((x.tm), (y.tm)) with
      | (FreeV x1,FreeV y1) -> fv_eq x1 y1
      | uu____736 -> false
  
let freevar_sort : term -> sort =
  fun uu___83_741  ->
    match uu___83_741 with
    | { tm = FreeV x; freevars = uu____743; rng = uu____744;_} -> fv_sort x
    | uu____751 -> failwith "impossible"
  
let fv_of_term : term -> fv =
  fun uu___84_754  ->
    match uu___84_754 with
    | { tm = FreeV fv; freevars = uu____756; rng = uu____757;_} -> fv
    | uu____764 -> failwith "impossible"
  
let rec freevars : term -> (Prims.string * sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer _|BoundV _ -> []
    | FreeV fv -> [fv]
    | App (uu____785,tms) -> FStar_List.collect freevars tms
    | Quant (_,_,_,_,t1)|Labeled (t1,_,_)|LblPos (t1,_) -> freevars t1
    | Let (es,body) -> FStar_List.collect freevars (body :: es)
  
let free_variables : term -> fvs =
  fun t  ->
    let uu____812 = FStar_ST.read t.freevars  in
    match uu____812 with
    | Some b -> b
    | None  ->
        let fvs =
          let uu____835 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____835  in
        (FStar_ST.write t.freevars (Some fvs); fvs)
  
let qop_to_string : qop -> Prims.string =
  fun uu___85_847  ->
    match uu___85_847 with | Forall  -> "forall" | Exists  -> "exists"
  
let op_to_string : op -> Prims.string =
  fun uu___86_850  ->
    match uu___86_850 with
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
  
let weightToSmt : Prims.int Prims.option -> Prims.string =
  fun uu___87_855  ->
    match uu___87_855 with
    | None  -> ""
    | Some i ->
        let uu____858 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____858
  
let rec hash_of_term' : term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____866 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____866
    | FreeV x ->
        let uu____870 =
          let uu____871 = strSort (Prims.snd x)  in
          Prims.strcat ":" uu____871  in
        Prims.strcat (Prims.fst x) uu____870
    | App (op,tms) ->
        let uu____876 =
          let uu____877 =
            let uu____878 =
              let uu____879 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____879 (FStar_String.concat " ")  in
            Prims.strcat uu____878 ")"  in
          Prims.strcat (op_to_string op) uu____877  in
        Prims.strcat "(" uu____876
    | Labeled (t1,r1,r2) ->
        let uu____885 = hash_of_term t1  in
        let uu____886 =
          let uu____887 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____887  in
        Prims.strcat uu____885 uu____886
    | LblPos (t1,r) ->
        let uu____890 =
          let uu____891 = hash_of_term t1  in
          Prims.strcat uu____891
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____890
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____905 =
          let uu____906 =
            let uu____907 =
              let uu____908 =
                let uu____909 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____909 (FStar_String.concat " ")  in
              let uu____912 =
                let uu____913 =
                  let uu____914 = hash_of_term body  in
                  let uu____915 =
                    let uu____916 =
                      let uu____917 = weightToSmt wopt  in
                      let uu____918 =
                        let uu____919 =
                          let uu____920 =
                            let uu____921 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____929 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____929
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____921
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____920 "))"  in
                        Prims.strcat " " uu____919  in
                      Prims.strcat uu____917 uu____918  in
                    Prims.strcat " " uu____916  in
                  Prims.strcat uu____914 uu____915  in
                Prims.strcat ")(! " uu____913  in
              Prims.strcat uu____908 uu____912  in
            Prims.strcat " (" uu____907  in
          Prims.strcat (qop_to_string qop) uu____906  in
        Prims.strcat "(" uu____905
    | Let (es,body) ->
        let uu____937 =
          let uu____938 =
            let uu____939 = FStar_List.map hash_of_term es  in
            FStar_All.pipe_right uu____939 (FStar_String.concat " ")  in
          let uu____942 =
            let uu____943 =
              let uu____944 = hash_of_term body  in
              Prims.strcat uu____944 ")"  in
            Prims.strcat ") " uu____943  in
          Prims.strcat uu____938 uu____942  in
        Prims.strcat "(let (" uu____937

and hash_of_term : term -> Prims.string = fun tm  -> hash_of_term' tm.tm

let mk : term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____952 = FStar_Util.mk_ref None  in
      { tm = t; freevars = uu____952; rng = r }
  
let mkTrue : FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r 
let mkFalse : FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r 
let mkInteger : Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____981 =
        let uu____982 = FStar_Util.ensure_decimal i  in Integer uu____982  in
      mk uu____981 r
  
let mkInteger' : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____989 = FStar_Util.string_of_int i  in mkInteger uu____989 r
  
let mkBoundV : Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r 
let mkFreeV : (Prims.string * sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r 
let mkApp' : (op * term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r 
let mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term =
  fun uu____1025  ->
    fun r  -> match uu____1025 with | (s,args) -> mk (App ((Var s), args)) r
  
let mkNot : term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____1041) -> mkFalse r
      | App (FalseOp ,uu____1044) -> mkTrue r
      | uu____1047 -> mkApp' (Not, [t]) r
  
let mkAnd : (term * term) -> FStar_Range.range -> term =
  fun uu____1055  ->
    fun r  ->
      match uu____1055 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1061),uu____1062) -> t2
           | (uu____1065,App (TrueOp ,uu____1066)) -> t1
           | (App (FalseOp ,_),_)|(_,App (FalseOp ,_)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1082,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1088) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1092 -> mkApp' (And, [t1; t2]) r)
  
let mkOr : (term * term) -> FStar_Range.range -> term =
  fun uu____1102  ->
    fun r  ->
      match uu____1102 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,_),_)|(_,App (TrueOp ,_)) -> mkTrue r
           | (App (FalseOp ,uu____1114),uu____1115) -> t2
           | (uu____1118,App (FalseOp ,uu____1119)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1129,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1135) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1139 -> mkApp' (Or, [t1; t2]) r)
  
let mkImp : (term * term) -> FStar_Range.range -> term =
  fun uu____1149  ->
    fun r  ->
      match uu____1149 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (_,App (TrueOp ,_))|(App (FalseOp ,_),_) -> mkTrue r
           | (App (TrueOp ,uu____1161),uu____1162) -> t2
           | (uu____1165,App (Imp ,t1'::t2'::[])) ->
               let uu____1169 =
                 let uu____1173 =
                   let uu____1175 = mkAnd (t1, t1') r  in [uu____1175; t2']
                    in
                 (Imp, uu____1173)  in
               mkApp' uu____1169 r
           | uu____1177 -> mkApp' (Imp, [t1; t2]) r)
  
let mk_bin_op : op -> (term * term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1190  ->
      fun r  -> match uu____1190 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
let mkMinus : term -> FStar_Range.range -> term =
  fun t  -> fun r  -> mkApp' (Minus, [t]) r 
let mkIff : (term * term) -> FStar_Range.range -> term = mk_bin_op Iff 
let mkEq : (term * term) -> FStar_Range.range -> term = mk_bin_op Eq 
let mkLT : (term * term) -> FStar_Range.range -> term = mk_bin_op LT 
let mkLTE : (term * term) -> FStar_Range.range -> term = mk_bin_op LTE 
let mkGT : (term * term) -> FStar_Range.range -> term = mk_bin_op GT 
let mkGTE : (term * term) -> FStar_Range.range -> term = mk_bin_op GTE 
let mkAdd : (term * term) -> FStar_Range.range -> term = mk_bin_op Add 
let mkSub : (term * term) -> FStar_Range.range -> term = mk_bin_op Sub 
let mkDiv : (term * term) -> FStar_Range.range -> term = mk_bin_op Div 
let mkMul : (term * term) -> FStar_Range.range -> term = mk_bin_op Mul 
let mkMod : (term * term) -> FStar_Range.range -> term = mk_bin_op Mod 
let mkITE : (term * term * term) -> FStar_Range.range -> term =
  fun uu____1277  ->
    fun r  ->
      match uu____1277 with
      | (t1,t2,t3) ->
          (match t1.tm with
           | App (TrueOp ,uu____1285) -> t2
           | App (FalseOp ,uu____1288) -> t3
           | uu____1291 ->
               (match ((t2.tm), (t3.tm)) with
                | (App (TrueOp ,uu____1292),App (TrueOp ,uu____1293)) ->
                    mkTrue r
                | (App (TrueOp ,uu____1298),uu____1299) ->
                    let uu____1302 =
                      let uu____1305 = mkNot t1 t1.rng  in (uu____1305, t3)
                       in
                    mkImp uu____1302 r
                | (uu____1306,App (TrueOp ,uu____1307)) -> mkImp (t1, t2) r
                | (uu____1310,uu____1311) -> mkApp' (ITE, [t1; t2; t3]) r))
  
let mkCases : term Prims.list -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t with
      | [] -> failwith "Impos"
      | hd1::tl1 ->
          FStar_List.fold_left (fun out  -> fun t1  -> mkAnd (out, t1) r) hd1
            tl1
  
let mkQuant :
  (qop * term Prims.list Prims.list * Prims.int Prims.option * sort
    Prims.list * term) -> FStar_Range.range -> term
  =
  fun uu____1339  ->
    fun r  ->
      match uu____1339 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1366) -> body
             | uu____1369 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let mkLet : (term Prims.list * term) -> FStar_Range.range -> term =
  fun uu____1381  ->
    fun r  ->
      match uu____1381 with
      | (es,body) ->
          if (FStar_List.length es) = (Prims.parse_int "0")
          then body
          else mk (Let (es, body)) r
  
let abstr : fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____1409 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____1409 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1")))  in
      let rec aux ix t1 =
        let uu____1423 = FStar_ST.read t1.freevars  in
        match uu____1423 with
        | Some [] -> t1
        | uu____1439 ->
            (match t1.tm with
             | Integer _|BoundV _ -> t1
             | FreeV x ->
                 let uu____1449 = index_of x  in
                 (match uu____1449 with
                  | None  -> t1
                  | Some i -> mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1456 =
                   let uu____1460 = FStar_List.map (aux ix) tms  in
                   (op, uu____1460)  in
                 mkApp' uu____1456 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1466 =
                   let uu____1467 =
                     let uu____1471 = aux ix t2  in (uu____1471, r1, r2)  in
                   Labeled uu____1467  in
                 mk uu____1466 t2.rng
             | LblPos (t2,r) ->
                 let uu____1474 =
                   let uu____1475 =
                     let uu____1478 = aux ix t2  in (uu____1478, r)  in
                   LblPos uu____1475  in
                 mk uu____1474 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____1494 =
                   let uu____1504 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____1515 = aux (ix + n1) body  in
                   (qop, uu____1504, wopt, vars, uu____1515)  in
                 mkQuant uu____1494 t1.rng
             | Let (es,body) ->
                 let uu____1526 =
                   FStar_List.fold_left
                     (fun uu____1533  ->
                        fun e  ->
                          match uu____1533 with
                          | (ix1,l) ->
                              let uu____1545 =
                                let uu____1547 = aux ix1 e  in uu____1547 ::
                                  l
                                 in
                              ((ix1 + (Prims.parse_int "1")), uu____1545))
                     (ix, []) es
                    in
                 (match uu____1526 with
                  | (ix1,es_rev) ->
                      let uu____1554 =
                        let uu____1558 = aux ix1 body  in
                        ((FStar_List.rev es_rev), uu____1558)  in
                      mkLet uu____1554 t1.rng))
         in
      aux (Prims.parse_int "0") t
  
let inst : term Prims.list -> term -> term =
  fun tms  ->
    fun t  ->
      let tms1 = FStar_List.rev tms  in
      let n1 = FStar_List.length tms1  in
      let rec aux shift t1 =
        match t1.tm with
        | Integer _|FreeV _ -> t1
        | BoundV i ->
            if ((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n1)
            then FStar_List.nth tms1 (i - shift)
            else t1
        | App (op,tms2) ->
            let uu____1589 =
              let uu____1593 = FStar_List.map (aux shift) tms2  in
              (op, uu____1593)  in
            mkApp' uu____1589 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1599 =
              let uu____1600 =
                let uu____1604 = aux shift t2  in (uu____1604, r1, r2)  in
              Labeled uu____1600  in
            mk uu____1599 t2.rng
        | LblPos (t2,r) ->
            let uu____1607 =
              let uu____1608 =
                let uu____1611 = aux shift t2  in (uu____1611, r)  in
              LblPos uu____1608  in
            mk uu____1607 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____1630 =
              let uu____1640 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____1649 = aux shift1 body  in
              (qop, uu____1640, wopt, vars, uu____1649)  in
            mkQuant uu____1630 t1.rng
        | Let (es,body) ->
            let uu____1658 =
              FStar_List.fold_left
                (fun uu____1665  ->
                   fun e  ->
                     match uu____1665 with
                     | (ix,es1) ->
                         let uu____1677 =
                           let uu____1679 = aux shift e  in uu____1679 :: es1
                            in
                         ((shift + (Prims.parse_int "1")), uu____1677))
                (shift, []) es
               in
            (match uu____1658 with
             | (shift1,es_rev) ->
                 let uu____1686 =
                   let uu____1690 = aux shift1 body  in
                   ((FStar_List.rev es_rev), uu____1690)  in
                 mkLet uu____1686 t1.rng)
         in
      aux (Prims.parse_int "0") t
  
let subst : term -> fv -> term -> term =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____1701 = abstr [fv] t  in inst [s] uu____1701
  
let mkQuant' :
  (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list
    * term) -> FStar_Range.range -> term
  =
  fun uu____1715  ->
    match uu____1715 with
    | (qop,pats,wopt,vars,body) ->
        let uu____1740 =
          let uu____1750 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____1759 = FStar_List.map fv_sort vars  in
          let uu____1763 = abstr vars body  in
          (qop, uu____1750, wopt, uu____1759, uu____1763)  in
        mkQuant uu____1740
  
let mkForall'' :
  (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list *
    term) -> FStar_Range.range -> term
  =
  fun uu____1780  ->
    fun r  ->
      match uu____1780 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let mkForall' :
  (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term) ->
    FStar_Range.range -> term
  =
  fun uu____1817  ->
    fun r  ->
      match uu____1817 with
      | (pats,wopt,vars,body) ->
          let uu____1836 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____1836 r
  
let mkForall :
  (pat Prims.list Prims.list * fvs * term) -> FStar_Range.range -> term =
  fun uu____1851  ->
    fun r  ->
      match uu____1851 with
      | (pats,vars,body) ->
          let uu____1865 = mkQuant' (Forall, pats, None, vars, body)  in
          uu____1865 r
  
let mkExists :
  (pat Prims.list Prims.list * fvs * term) -> FStar_Range.range -> term =
  fun uu____1880  ->
    fun r  ->
      match uu____1880 with
      | (pats,vars,body) ->
          let uu____1894 = mkQuant' (Exists, pats, None, vars, body)  in
          uu____1894 r
  
let mkLet' : ((fv * term) Prims.list * term) -> FStar_Range.range -> term =
  fun uu____1909  ->
    fun r  ->
      match uu____1909 with
      | (bindings,body) ->
          let uu____1924 = FStar_List.split bindings  in
          (match uu____1924 with
           | (vars,es) ->
               let uu____1935 =
                 let uu____1939 = abstr vars body  in (es, uu____1939)  in
               mkLet uu____1935 r)
  
let norng : FStar_Range.range = FStar_Range.dummyRange 
let mkDefineFun :
  (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)
    -> decl
  =
  fun uu____1951  ->
    match uu____1951 with
    | (nm,vars,s,tm,c) ->
        let uu____1971 =
          let uu____1978 = FStar_List.map fv_sort vars  in
          let uu____1982 = abstr vars tm  in
          (nm, uu____1978, s, uu____1982, c)  in
        DefineFun uu____1971
  
let constr_id_of_sort : sort -> Prims.string =
  fun sort  ->
    let uu____1987 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____1987
  
let fresh_token : (Prims.string * sort) -> Prims.int -> decl =
  fun uu____1994  ->
    fun id  ->
      match uu____1994 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let uu____2001 =
            let uu____2006 =
              let uu____2007 =
                let uu____2010 = mkInteger' id norng  in
                let uu____2011 =
                  let uu____2012 =
                    let uu____2016 = constr_id_of_sort sort  in
                    let uu____2017 =
                      let uu____2019 = mkApp (tok_name, []) norng  in
                      [uu____2019]  in
                    (uu____2016, uu____2017)  in
                  mkApp uu____2012 norng  in
                (uu____2010, uu____2011)  in
              mkEq uu____2007 norng  in
            (uu____2006, (Some "fresh token"), (Some a_name))  in
          Assume uu____2001
  
let fresh_constructor :
  (Prims.string * sort Prims.list * sort * Prims.int) -> decl =
  fun uu____2031  ->
    match uu____2031 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____2050 =
                      let uu____2053 =
                        let uu____2054 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____2054  in
                      (uu____2053, s)  in
                    mkFreeV uu____2050 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____2060 =
            let uu____2064 = constr_id_of_sort sort  in (uu____2064, [capp])
             in
          mkApp uu____2060 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let uu____2067 =
          let uu____2072 =
            let uu____2073 =
              let uu____2079 =
                let uu____2080 =
                  let uu____2083 = mkInteger id1 norng  in
                  (uu____2083, cid_app)  in
                mkEq uu____2080 norng  in
              ([[capp]], bvar_names, uu____2079)  in
            mkForall uu____2073 norng  in
          (uu____2072, (Some "Constructor distinct"), (Some a_name))  in
        Assume uu____2067
  
let injective_constructor :
  (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list =
  fun uu____2097  ->
    match uu____2097 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____2113 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____2113  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s =
          let uu____2130 = let uu____2133 = bvar_name i  in (uu____2133, s)
             in
          mkFreeV uu____2130  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2142  ->
                    match uu____2142 with
                    | (uu____2146,s,uu____2148) ->
                        let uu____2149 = bvar i s  in uu____2149 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____2156 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____2167  ->
                    match uu____2167 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng  in
                        let proj_name =
                          DeclFun (name1, [sort], s, (Some "Projector"))  in
                        if projectible
                        then
                          let a_name =
                            Prims.strcat "projection_inverse_" name1  in
                          let uu____2182 =
                            let uu____2184 =
                              let uu____2185 =
                                let uu____2190 =
                                  let uu____2191 =
                                    let uu____2197 =
                                      let uu____2198 =
                                        let uu____2201 =
                                          let uu____2202 = bvar i s  in
                                          uu____2202 norng  in
                                        (cproj_app, uu____2201)  in
                                      mkEq uu____2198 norng  in
                                    ([[capp]], bvar_names, uu____2197)  in
                                  mkForall uu____2191 norng  in
                                (uu____2190, (Some "Projection inverse"),
                                  (Some a_name))
                                 in
                              Assume uu____2185  in
                            [uu____2184]  in
                          proj_name :: uu____2182
                        else [proj_name]))
           in
        FStar_All.pipe_right uu____2156 FStar_List.flatten
  
let constructor_to_decl : constructor_t -> decl Prims.list =
  fun uu____2218  ->
    match uu____2218 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2234  ->
                  match uu____2234 with
                  | (uu____2238,sort1,uu____2240) -> sort1))
           in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor"))
           in
        let cid = fresh_constructor (name, field_sorts, sort, id)  in
        let disc =
          let disc_name = Prims.strcat "is-" name  in
          let xfv = ("x", sort)  in
          let xx = mkFreeV xfv norng  in
          let disc_eq =
            let uu____2253 =
              let uu____2256 =
                let uu____2257 =
                  let uu____2261 = constr_id_of_sort sort  in
                  (uu____2261, [xx])  in
                mkApp uu____2257 norng  in
              let uu____2263 =
                let uu____2264 = FStar_Util.string_of_int id  in
                mkInteger uu____2264 norng  in
              (uu____2256, uu____2263)  in
            mkEq uu____2253 norng  in
          let uu____2265 =
            let uu____2273 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2296  ->
                        match uu____2296 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2313 = mkApp (proj, [xx]) norng  in
                              (uu____2313, [])
                            else
                              (let fi =
                                 let uu____2324 =
                                   let uu____2325 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____2325  in
                                 (uu____2324, s)  in
                               let uu____2326 = mkFreeV fi norng  in
                               (uu____2326, [fi]))))
               in
            FStar_All.pipe_right uu____2273 FStar_List.split  in
          match uu____2265 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____2369 =
                  let uu____2372 = mkApp (name, proj_terms) norng  in
                  (xx, uu____2372)  in
                mkEq uu____2369 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2377 -> mkExists ([], ex_vars1, disc_inv_body) norng
                 in
              let disc_ax = mkAnd (disc_eq, disc_inv_body1) norng  in
              let def =
                mkDefineFun
                  (disc_name, [xfv], Bool_sort, disc_ax,
                    (Some "Discriminator definition"))
                 in
              def
           in
        let projs =
          if injective1
          then injective_constructor (name, fields, sort)
          else []  in
        let uu____2400 =
          let uu____2402 =
            let uu____2403 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____2403  in
          uu____2402 :: cdecl :: cid :: projs  in
        let uu____2404 =
          let uu____2406 =
            let uu____2408 =
              let uu____2409 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____2409  in
            [uu____2408]  in
          FStar_List.append [disc] uu____2406  in
        FStar_List.append uu____2400 uu____2404
  
let name_binders_inner :
  Prims.string Prims.option ->
    (Prims.string * sort) Prims.list ->
      Prims.int ->
        sort Prims.list ->
          ((Prims.string * sort) Prims.list * Prims.string Prims.list *
            Prims.int)
  =
  fun prefix_opt  ->
    fun outer_names  ->
      fun start  ->
        fun sorts  ->
          let uu____2439 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2462  ->
                    fun s  ->
                      match uu____2462 with
                      | (names,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2490 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | None  -> prefix1
                            | Some p -> Prims.strcat p prefix1  in
                          let nm =
                            let uu____2494 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____2494  in
                          let names1 = (nm, s) :: names  in
                          let b =
                            let uu____2502 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____2502  in
                          (names1, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____2439 with
          | (names,binders,n1) -> (names, (FStar_List.rev binders), n1)
  
let name_macro_binders :
  sort Prims.list ->
    ((Prims.string * sort) Prims.list * Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2544 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts  in
    match uu____2544 with
    | (names,binders,n1) -> ((FStar_List.rev names), binders)
  
let termToSmt : term -> Prims.string =
  fun t  ->
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
                           "Prims.guard_free",{ tm = BoundV uu____2601;
                                                freevars = uu____2602;
                                                rng = uu____2603;_}::[])
                          -> tm
                      | App (Var "Prims.guard_free",p::[]) -> p
                      | uu____2611 -> tm))))
       in
    let rec aux' n1 names t1 =
      match t1.tm with
      | Integer i -> i
      | BoundV i ->
          let uu____2634 = FStar_List.nth names i  in
          FStar_All.pipe_right uu____2634 Prims.fst
      | FreeV x -> Prims.fst x
      | App (op,[]) -> op_to_string op
      | App (op,tms) ->
          let uu____2644 =
            let uu____2645 = FStar_List.map (aux n1 names) tms  in
            FStar_All.pipe_right uu____2645 (FStar_String.concat "\n")  in
          FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2644
      | Labeled (t2,uu____2649,uu____2650) -> aux n1 names t2
      | LblPos (t2,s) ->
          let uu____2653 = aux n1 names t2  in
          FStar_Util.format2 "(! %s :lblpos %s)" uu____2653 s
      | Quant (qop,pats,wopt,sorts,body) ->
          let uu____2667 = name_binders_inner None names n1 sorts  in
          (match uu____2667 with
           | (names1,binders,n2) ->
               let binders1 =
                 FStar_All.pipe_right binders (FStar_String.concat " ")  in
               let pats1 = remove_guard_free pats  in
               let pats_str =
                 match pats1 with
                 | []::[]|[] -> ""
                 | uu____2695 ->
                     let uu____2698 =
                       FStar_All.pipe_right pats1
                         (FStar_List.map
                            (fun pats2  ->
                               let uu____2706 =
                                 let uu____2707 =
                                   FStar_List.map
                                     (fun p  ->
                                        let uu____2710 = aux n2 names1 p  in
                                        FStar_Util.format1 "%s" uu____2710)
                                     pats2
                                    in
                                 FStar_String.concat " " uu____2707  in
                               FStar_Util.format1 "\n:pattern (%s)"
                                 uu____2706))
                        in
                     FStar_All.pipe_right uu____2698
                       (FStar_String.concat "\n")
                  in
               (match (pats1, wopt) with
                | ([]::[],None )|([],None ) ->
                    let uu____2724 = aux n2 names1 body  in
                    FStar_Util.format3 "(%s (%s)\n %s);;no pats\n"
                      (qop_to_string qop) binders1 uu____2724
                | uu____2725 ->
                    let uu____2731 = aux n2 names1 body  in
                    let uu____2732 = weightToSmt wopt  in
                    FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))"
                      (qop_to_string qop) binders1 uu____2731 uu____2732
                      pats_str))
      | Let (es,body) ->
          let uu____2737 =
            FStar_List.fold_left
              (fun uu____2752  ->
                 fun e  ->
                   match uu____2752 with
                   | (names0,binders,n0) ->
                       let nm =
                         let uu____2780 = FStar_Util.string_of_int n0  in
                         Prims.strcat "@lb" uu____2780  in
                       let names01 = (nm, Term_sort) :: names0  in
                       let b =
                         let uu____2788 = aux n1 names e  in
                         FStar_Util.format2 "(%s %s)" nm uu____2788  in
                       (names01, (b :: binders),
                         (n0 + (Prims.parse_int "1")))) (names, [], n1) es
             in
          (match uu____2737 with
           | (names1,binders,n2) ->
               let uu____2806 = aux n2 names1 body  in
               FStar_Util.format2 "(let (%s) %s)"
                 (FStar_String.concat " " binders) uu____2806)
    
    and aux n1 names t1 =
      let s = aux' n1 names t1  in
      if t1.rng <> norng
      then
        let uu____2812 = FStar_Range.string_of_range t1.rng  in
        let uu____2813 = FStar_Range.string_of_use_range t1.rng  in
        FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2812 uu____2813
          s
      else s
     in aux (Prims.parse_int "0") [] t
  
let caption_to_string : Prims.string Prims.option -> Prims.string =
  fun uu___88_2818  ->
    match uu___88_2818 with
    | None  -> ""
    | Some c ->
        let uu____2821 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____2830 -> (hd1, "...")  in
        (match uu____2821 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
  
let rec declToSmt : Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_'  in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____2847 =
            FStar_All.pipe_right (FStar_Util.splitlines c)
              (fun uu___89_2849  ->
                 match uu___89_2849 with | [] -> "" | h::t -> h)
             in
          FStar_Util.format1 "\n; %s" uu____2847
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts  in
          let uu____2862 = caption_to_string c  in
          let uu____2863 = strSort retsort  in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2862 f
            (FStar_String.concat " " l) uu____2863
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2871 = name_macro_binders arg_sorts  in
          (match uu____2871 with
           | (names,binders) ->
               let body1 =
                 let uu____2889 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names  in
                 inst uu____2889 body  in
               let uu____2896 = caption_to_string c  in
               let uu____2897 = strSort retsort  in
               let uu____2898 = termToSmt body1  in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2896
                 f (FStar_String.concat " " binders) uu____2897 uu____2898)
      | Assume (t,c,Some n1) ->
          let uu____2903 = caption_to_string c  in
          let uu____2904 = termToSmt t  in
          FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" uu____2903
            uu____2904 (escape n1)
      | Assume (t,c,None ) ->
          let uu____2908 = caption_to_string c  in
          let uu____2909 = termToSmt t  in
          FStar_Util.format2 "%s(assert %s)" uu____2908 uu____2909
      | Eval t ->
          let uu____2911 = termToSmt t  in
          FStar_Util.format1 "(eval %s)" uu____2911
      | Echo s -> FStar_Util.format1 "(echo \"%s\")" s
      | CheckSat  -> "(check-sat)"
      | GetUnsatCore  ->
          "(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
      | Push  -> "(push)"
      | Pop  -> "(pop)"
      | SetOption (s,v1) -> FStar_Util.format2 "(set-option :%s %s)" s v1
      | PrintStats  -> "(get-info :all-statistics)"

and mkPrelude : Prims.string -> Prims.string =
  fun z3options  ->
    let basic =
      Prims.strcat z3options
        "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n"
       in
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
        Term_sort, (Prims.parse_int "11"), true)]
       in
    let bcons =
      let uu____3115 =
        let uu____3117 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____3117
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____3115 (FStar_String.concat "\n")  in
    let lex_ordering =
      "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
       in
    Prims.strcat basic (Prims.strcat bcons lex_ordering)

let mk_Range_const : term = mkApp ("Range_const", []) norng 
let mk_Term_type : term = mkApp ("Tm_type", []) norng 
let mk_Term_app : term -> term -> FStar_Range.range -> term =
  fun t1  -> fun t2  -> fun r  -> mkApp ("Tm_app", [t1; t2]) r 
let mk_Term_uvar : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3142 =
        let uu____3146 = let uu____3148 = mkInteger' i norng  in [uu____3148]
           in
        ("Tm_uvar", uu____3146)  in
      mkApp uu____3142 r
  
let mk_Term_unit : term = mkApp ("Tm_unit", []) norng 
let boxInt : term -> term = fun t  -> mkApp ("BoxInt", [t]) t.rng 
let unboxInt : term -> term = fun t  -> mkApp ("BoxInt_proj_0", [t]) t.rng 
let boxBool : term -> term = fun t  -> mkApp ("BoxBool", [t]) t.rng 
let unboxBool : term -> term = fun t  -> mkApp ("BoxBool_proj_0", [t]) t.rng 
let boxString : term -> term = fun t  -> mkApp ("BoxString", [t]) t.rng 
let unboxString : term -> term =
  fun t  -> mkApp ("BoxString_proj_0", [t]) t.rng 
let boxRef : term -> term = fun t  -> mkApp ("BoxRef", [t]) t.rng 
let unboxRef : term -> term = fun t  -> mkApp ("BoxRef_proj_0", [t]) t.rng 
let boxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> boxInt t
      | Bool_sort  -> boxBool t
      | String_sort  -> boxString t
      | Ref_sort  -> boxRef t
      | uu____3189 -> Prims.raise FStar_Util.Impos
  
let unboxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____3196 -> Prims.raise FStar_Util.Impos
  
let mk_PreType : term -> term = fun t  -> mkApp ("PreType", [t]) t.rng 
let mk_Valid : term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____3204::t1::t2::[]);
                       freevars = uu____3207; rng = uu____3208;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____3215::t1::t2::[]);
                       freevars = uu____3218; rng = uu____3219;_}::[])
        -> let uu____3226 = mkEq (t1, t2) norng  in mkNot uu____3226 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____3229; rng = uu____3230;_}::[])
        ->
        let uu____3237 =
          let uu____3240 = unboxInt t1  in
          let uu____3241 = unboxInt t2  in (uu____3240, uu____3241)  in
        mkLTE uu____3237 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____3244; rng = uu____3245;_}::[])
        ->
        let uu____3252 =
          let uu____3255 = unboxInt t1  in
          let uu____3256 = unboxInt t2  in (uu____3255, uu____3256)  in
        mkLT uu____3252 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____3259; rng = uu____3260;_}::[])
        ->
        let uu____3267 =
          let uu____3270 = unboxInt t1  in
          let uu____3271 = unboxInt t2  in (uu____3270, uu____3271)  in
        mkGTE uu____3267 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3274; rng = uu____3275;_}::[])
        ->
        let uu____3282 =
          let uu____3285 = unboxInt t1  in
          let uu____3286 = unboxInt t2  in (uu____3285, uu____3286)  in
        mkGT uu____3282 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3289; rng = uu____3290;_}::[])
        ->
        let uu____3297 =
          let uu____3300 = unboxBool t1  in
          let uu____3301 = unboxBool t2  in (uu____3300, uu____3301)  in
        mkAnd uu____3297 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3304; rng = uu____3305;_}::[])
        ->
        let uu____3312 =
          let uu____3315 = unboxBool t1  in
          let uu____3316 = unboxBool t2  in (uu____3315, uu____3316)  in
        mkOr uu____3312 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3318; rng = uu____3319;_}::[])
        -> let uu____3326 = unboxBool t1  in mkNot uu____3326 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___90_3329 = unboxBool t1  in
        {
          tm = (uu___90_3329.tm);
          freevars = (uu___90_3329.freevars);
          rng = (t.rng)
        }
    | uu____3332 -> mkApp ("Valid", [t]) t.rng
  
let mk_HasType : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let mk_HasTypeZ : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let mk_IsTyped : term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let mk_HasTypeFuel : term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3361 = FStar_Options.unthrottle_inductives ()  in
        if uu____3361
        then mk_HasType v1 t
        else mkApp ("HasTypeFuel", [f; v1; t]) t.rng
  
let mk_HasTypeWithFuel : term Prims.option -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        match f with
        | None  -> mk_HasType v1 t
        | Some f1 -> mk_HasTypeFuel f1 v1 t
  
let mk_Destruct : term -> FStar_Range.range -> term =
  fun v1  -> mkApp ("Destruct", [v1]) 
let mk_Rank : term -> FStar_Range.range -> term =
  fun x  -> mkApp ("Rank", [x]) 
let mk_tester : Prims.string -> term -> term =
  fun n1  -> fun t  -> mkApp ((Prims.strcat "is-" n1), [t]) t.rng 
let mk_ApplyTF : term -> term -> term =
  fun t  -> fun t'  -> mkApp ("ApplyTF", [t; t']) t.rng 
let mk_ApplyTT : term -> term -> FStar_Range.range -> term =
  fun t  -> fun t'  -> fun r  -> mkApp ("ApplyTT", [t; t']) r 
let mk_String_const : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____3418 =
        let uu____3422 = let uu____3424 = mkInteger' i norng  in [uu____3424]
           in
        ("FString_const", uu____3422)  in
      mkApp uu____3418 r
  
let mk_Precedes : term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3435 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____3435 mk_Valid
  
let mk_LexCons : term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec n_fuel : Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3452 =
         let uu____3456 =
           let uu____3458 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____3458]  in
         ("SFuel", uu____3456)  in
       mkApp uu____3452 norng)
  
let fuel_2 : term = n_fuel (Prims.parse_int "2") 
let fuel_100 : term = n_fuel (Prims.parse_int "100") 
let mk_and_opt :
  term Prims.option ->
    term Prims.option -> FStar_Range.range -> term Prims.option
  =
  fun p1  ->
    fun p2  ->
      fun r  ->
        match (p1, p2) with
        | (Some p11,Some p21) ->
            let uu____3481 = mkAnd (p11, p21) r  in Some uu____3481
        | (Some p,None )|(None ,Some p) -> Some p
        | (None ,None ) -> None
  
let mk_and_opt_l :
  term Prims.option Prims.list -> FStar_Range.range -> term Prims.option =
  fun pl  ->
    fun r  ->
      FStar_List.fold_right (fun p  -> fun out  -> mk_and_opt p out r) pl
        None
  
let mk_and_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3514 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3514
  
let mk_or_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3525 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3525
  
let mk_haseq : term -> term =
  fun t  ->
    let uu____3531 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____3531
  
let rec print_smt_term : term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3545 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____3545
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (Prims.fst fv)
    | App (op,l) ->
        let uu____3553 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3553
    | Labeled (t1,r1,r2) ->
        let uu____3557 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3557
    | LblPos (t1,s) ->
        let uu____3560 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3560
    | Quant (qop,l,uu____3563,uu____3564,t1) ->
        let uu____3574 = print_smt_term_list_list l  in
        let uu____3575 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3574
          uu____3575
    | Let (es,body) ->
        let uu____3580 = print_smt_term_list es  in
        let uu____3581 = print_smt_term body  in
        FStar_Util.format2 "(let %s %s)" uu____3580 uu____3581

and print_smt_term_list : term Prims.list -> Prims.string =
  fun l  ->
    let uu____3584 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____3584 (FStar_String.concat " ")

and print_smt_term_list_list : term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3594 =
             let uu____3595 =
               let uu____3596 = print_smt_term_list l1  in
               Prims.strcat uu____3596 " ] "  in
             Prims.strcat "; [ " uu____3595  in
           Prims.strcat s uu____3594) "" l
