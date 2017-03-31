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
  | Labeled of (term * Prims.string * FStar_Range.range) 
  | LblPos of (term * Prims.string) 
and term =
  {
  tm: term' ;
  freevars: (Prims.string * sort) Prims.list FStar_Syntax_Syntax.memo ;
  rng: FStar_Range.range }
let uu___is_Integer : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Integer _0 -> true | uu____259 -> false
  
let __proj__Integer__item___0 : term' -> Prims.string =
  fun projectee  -> match projectee with | Integer _0 -> _0 
let uu___is_BoundV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | BoundV _0 -> true | uu____271 -> false
  
let __proj__BoundV__item___0 : term' -> Prims.int =
  fun projectee  -> match projectee with | BoundV _0 -> _0 
let uu___is_FreeV : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeV _0 -> true | uu____285 -> false
  
let __proj__FreeV__item___0 : term' -> (Prims.string * sort) =
  fun projectee  -> match projectee with | FreeV _0 -> _0 
let uu___is_App : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____306 -> false
  
let __proj__App__item___0 : term' -> (op * term Prims.list) =
  fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Quant : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Quant _0 -> true | uu____336 -> false
  
let __proj__Quant__item___0 :
  term' ->
    (qop * term Prims.list Prims.list * Prims.int Prims.option * sort
      Prims.list * term)
  = fun projectee  -> match projectee with | Quant _0 -> _0 
let uu___is_Labeled : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | Labeled _0 -> true | uu____378 -> false
  
let __proj__Labeled__item___0 :
  term' -> (term * Prims.string * FStar_Range.range) =
  fun projectee  -> match projectee with | Labeled _0 -> _0 
let uu___is_LblPos : term' -> Prims.bool =
  fun projectee  ->
    match projectee with | LblPos _0 -> true | uu____401 -> false
  
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
    match projectee with | DefPrelude  -> true | uu____497 -> false
  
let uu___is_DeclFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DeclFun _0 -> true | uu____507 -> false
  
let __proj__DeclFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * caption) =
  fun projectee  -> match projectee with | DeclFun _0 -> _0 
let uu___is_DefineFun : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | DefineFun _0 -> true | uu____540 -> false
  
let __proj__DefineFun__item___0 :
  decl -> (Prims.string * sort Prims.list * sort * term * caption) =
  fun projectee  -> match projectee with | DefineFun _0 -> _0 
let uu___is_Assume : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Assume _0 -> true | uu____574 -> false
  
let __proj__Assume__item___0 :
  decl -> (term * caption * Prims.string Prims.option) =
  fun projectee  -> match projectee with | Assume _0 -> _0 
let uu___is_Caption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Caption _0 -> true | uu____598 -> false
  
let __proj__Caption__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Caption _0 -> _0 
let uu___is_Eval : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Eval _0 -> true | uu____610 -> false
  
let __proj__Eval__item___0 : decl -> term =
  fun projectee  -> match projectee with | Eval _0 -> _0 
let uu___is_Echo : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Echo _0 -> true | uu____622 -> false
  
let __proj__Echo__item___0 : decl -> Prims.string =
  fun projectee  -> match projectee with | Echo _0 -> _0 
let uu___is_Push : decl -> Prims.bool =
  fun projectee  -> match projectee with | Push  -> true | uu____633 -> false 
let uu___is_Pop : decl -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____637 -> false 
let uu___is_CheckSat : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckSat  -> true | uu____641 -> false
  
let uu___is_GetUnsatCore : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | GetUnsatCore  -> true | uu____645 -> false
  
let uu___is_SetOption : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | SetOption _0 -> true | uu____652 -> false
  
let __proj__SetOption__item___0 : decl -> (Prims.string * Prims.string) =
  fun projectee  -> match projectee with | SetOption _0 -> _0 
let uu___is_PrintStats : decl -> Prims.bool =
  fun projectee  ->
    match projectee with | PrintStats  -> true | uu____669 -> false
  
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
      | uu____706 -> false
  
let freevar_sort : term -> sort =
  fun uu___82_711  ->
    match uu___82_711 with
    | { tm = FreeV x; freevars = uu____713; rng = uu____714;_} -> fv_sort x
    | uu____721 -> failwith "impossible"
  
let fv_of_term : term -> fv =
  fun uu___83_724  ->
    match uu___83_724 with
    | { tm = FreeV fv; freevars = uu____726; rng = uu____727;_} -> fv
    | uu____734 -> failwith "impossible"
  
let rec freevars : term -> (Prims.string * sort) Prims.list =
  fun t  ->
    match t.tm with
    | Integer _|BoundV _ -> []
    | FreeV fv -> [fv]
    | App (uu____755,tms) -> FStar_List.collect freevars tms
    | Quant (_,_,_,_,t1)|Labeled (t1,_,_)|LblPos (t1,_) -> freevars t1
  
let free_variables : term -> fvs =
  fun t  ->
    let uu____776 = FStar_ST.read t.freevars  in
    match uu____776 with
    | Some b -> b
    | None  ->
        let fvs =
          let uu____799 = freevars t  in
          FStar_Util.remove_dups fv_eq uu____799  in
        (FStar_ST.write t.freevars (Some fvs); fvs)
  
let qop_to_string : qop -> Prims.string =
  fun uu___84_811  ->
    match uu___84_811 with | Forall  -> "forall" | Exists  -> "exists"
  
let op_to_string : op -> Prims.string =
  fun uu___85_814  ->
    match uu___85_814 with
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
  fun uu___86_819  ->
    match uu___86_819 with
    | None  -> ""
    | Some i ->
        let uu____822 = FStar_Util.string_of_int i  in
        FStar_Util.format1 ":weight %s\n" uu____822
  
let rec hash_of_term' : term' -> Prims.string =
  fun t  ->
    match t with
    | Integer i -> i
    | BoundV i ->
        let uu____830 = FStar_Util.string_of_int i  in
        Prims.strcat "@" uu____830
    | FreeV x ->
        let uu____834 =
          let uu____835 = strSort (Prims.snd x)  in
          Prims.strcat ":" uu____835  in
        Prims.strcat (Prims.fst x) uu____834
    | App (op,tms) ->
        let uu____840 =
          let uu____841 =
            let uu____842 =
              let uu____843 = FStar_List.map hash_of_term tms  in
              FStar_All.pipe_right uu____843 (FStar_String.concat " ")  in
            Prims.strcat uu____842 ")"  in
          Prims.strcat (op_to_string op) uu____841  in
        Prims.strcat "(" uu____840
    | Labeled (t1,r1,r2) ->
        let uu____849 = hash_of_term t1  in
        let uu____850 =
          let uu____851 = FStar_Range.string_of_range r2  in
          Prims.strcat r1 uu____851  in
        Prims.strcat uu____849 uu____850
    | LblPos (t1,r) ->
        let uu____854 =
          let uu____855 = hash_of_term t1  in
          Prims.strcat uu____855
            (Prims.strcat " :lblpos " (Prims.strcat r ")"))
           in
        Prims.strcat "(! " uu____854
    | Quant (qop,pats,wopt,sorts,body) ->
        let uu____869 =
          let uu____870 =
            let uu____871 =
              let uu____872 =
                let uu____873 = FStar_List.map strSort sorts  in
                FStar_All.pipe_right uu____873 (FStar_String.concat " ")  in
              let uu____876 =
                let uu____877 =
                  let uu____878 = hash_of_term body  in
                  let uu____879 =
                    let uu____880 =
                      let uu____881 = weightToSmt wopt  in
                      let uu____882 =
                        let uu____883 =
                          let uu____884 =
                            let uu____885 =
                              FStar_All.pipe_right pats
                                (FStar_List.map
                                   (fun pats1  ->
                                      let uu____893 =
                                        FStar_List.map hash_of_term pats1  in
                                      FStar_All.pipe_right uu____893
                                        (FStar_String.concat " ")))
                               in
                            FStar_All.pipe_right uu____885
                              (FStar_String.concat "; ")
                             in
                          Prims.strcat uu____884 "))"  in
                        Prims.strcat " " uu____883  in
                      Prims.strcat uu____881 uu____882  in
                    Prims.strcat " " uu____880  in
                  Prims.strcat uu____878 uu____879  in
                Prims.strcat ")(! " uu____877  in
              Prims.strcat uu____872 uu____876  in
            Prims.strcat " (" uu____871  in
          Prims.strcat (qop_to_string qop) uu____870  in
        Prims.strcat "(" uu____869

and hash_of_term : term -> Prims.string = fun tm  -> hash_of_term' tm.tm

let mk : term' -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      let uu____904 = FStar_Util.mk_ref None  in
      { tm = t; freevars = uu____904; rng = r }
  
let mkTrue : FStar_Range.range -> term = fun r  -> mk (App (TrueOp, [])) r 
let mkFalse : FStar_Range.range -> term = fun r  -> mk (App (FalseOp, [])) r 
let mkInteger : Prims.string -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____933 =
        let uu____934 = FStar_Util.ensure_decimal i  in Integer uu____934  in
      mk uu____933 r
  
let mkInteger' : Prims.int -> FStar_Range.range -> term =
  fun i  ->
    fun r  ->
      let uu____941 = FStar_Util.string_of_int i  in mkInteger uu____941 r
  
let mkBoundV : Prims.int -> FStar_Range.range -> term =
  fun i  -> fun r  -> mk (BoundV i) r 
let mkFreeV : (Prims.string * sort) -> FStar_Range.range -> term =
  fun x  -> fun r  -> mk (FreeV x) r 
let mkApp' : (op * term Prims.list) -> FStar_Range.range -> term =
  fun f  -> fun r  -> mk (App f) r 
let mkApp : (Prims.string * term Prims.list) -> FStar_Range.range -> term =
  fun uu____977  ->
    fun r  -> match uu____977 with | (s,args) -> mk (App ((Var s), args)) r
  
let mkNot : term -> FStar_Range.range -> term =
  fun t  ->
    fun r  ->
      match t.tm with
      | App (TrueOp ,uu____993) -> mkFalse r
      | App (FalseOp ,uu____996) -> mkTrue r
      | uu____999 -> mkApp' (Not, [t]) r
  
let mkAnd : (term * term) -> FStar_Range.range -> term =
  fun uu____1007  ->
    fun r  ->
      match uu____1007 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,uu____1013),uu____1014) -> t2
           | (uu____1017,App (TrueOp ,uu____1018)) -> t1
           | (App (FalseOp ,_),_)|(_,App (FalseOp ,_)) -> mkFalse r
           | (App (And ,ts1),App (And ,ts2)) ->
               mkApp' (And, (FStar_List.append ts1 ts2)) r
           | (uu____1034,App (And ,ts2)) -> mkApp' (And, (t1 :: ts2)) r
           | (App (And ,ts1),uu____1040) ->
               mkApp' (And, (FStar_List.append ts1 [t2])) r
           | uu____1044 -> mkApp' (And, [t1; t2]) r)
  
let mkOr : (term * term) -> FStar_Range.range -> term =
  fun uu____1054  ->
    fun r  ->
      match uu____1054 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (App (TrueOp ,_),_)|(_,App (TrueOp ,_)) -> mkTrue r
           | (App (FalseOp ,uu____1066),uu____1067) -> t2
           | (uu____1070,App (FalseOp ,uu____1071)) -> t1
           | (App (Or ,ts1),App (Or ,ts2)) ->
               mkApp' (Or, (FStar_List.append ts1 ts2)) r
           | (uu____1081,App (Or ,ts2)) -> mkApp' (Or, (t1 :: ts2)) r
           | (App (Or ,ts1),uu____1087) ->
               mkApp' (Or, (FStar_List.append ts1 [t2])) r
           | uu____1091 -> mkApp' (Or, [t1; t2]) r)
  
let mkImp : (term * term) -> FStar_Range.range -> term =
  fun uu____1101  ->
    fun r  ->
      match uu____1101 with
      | (t1,t2) ->
          (match ((t1.tm), (t2.tm)) with
           | (_,App (TrueOp ,_))|(App (FalseOp ,_),_) -> mkTrue r
           | (App (TrueOp ,uu____1113),uu____1114) -> t2
           | (uu____1117,App (Imp ,t1'::t2'::[])) ->
               let uu____1121 =
                 let uu____1125 =
                   let uu____1127 = mkAnd (t1, t1') r  in [uu____1127; t2']
                    in
                 (Imp, uu____1125)  in
               mkApp' uu____1121 r
           | uu____1129 -> mkApp' (Imp, [t1; t2]) r)
  
let mk_bin_op : op -> (term * term) -> FStar_Range.range -> term =
  fun op  ->
    fun uu____1142  ->
      fun r  -> match uu____1142 with | (t1,t2) -> mkApp' (op, [t1; t2]) r
  
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
  fun uu____1229  ->
    fun r  ->
      match uu____1229 with
      | (t1,t2,t3) ->
          (match ((t2.tm), (t3.tm)) with
           | (App (TrueOp ,uu____1237),App (TrueOp ,uu____1238)) -> mkTrue r
           | (App (TrueOp ,uu____1243),uu____1244) ->
               let uu____1247 =
                 let uu____1250 = mkNot t1 t1.rng  in (uu____1250, t3)  in
               mkImp uu____1247 r
           | (uu____1251,App (TrueOp ,uu____1252)) -> mkImp (t1, t2) r
           | (uu____1255,uu____1256) -> mkApp' (ITE, [t1; t2; t3]) r)
  
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
  fun uu____1284  ->
    fun r  ->
      match uu____1284 with
      | (qop,pats,wopt,vars,body) ->
          if (FStar_List.length vars) = (Prims.parse_int "0")
          then body
          else
            (match body.tm with
             | App (TrueOp ,uu____1311) -> body
             | uu____1314 -> mk (Quant (qop, pats, wopt, vars, body)) r)
  
let abstr : fv Prims.list -> term -> term =
  fun fvs  ->
    fun t  ->
      let nvars = FStar_List.length fvs  in
      let index_of fv =
        let uu____1334 = FStar_Util.try_find_index (fv_eq fv) fvs  in
        match uu____1334 with
        | None  -> None
        | Some i -> Some (nvars - (i + (Prims.parse_int "1")))  in
      let rec aux ix t1 =
        let uu____1348 = FStar_ST.read t1.freevars  in
        match uu____1348 with
        | Some [] -> t1
        | uu____1364 ->
            (match t1.tm with
             | Integer _|BoundV _ -> t1
             | FreeV x ->
                 let uu____1374 = index_of x  in
                 (match uu____1374 with
                  | None  -> t1
                  | Some i -> mkBoundV (i + ix) t1.rng)
             | App (op,tms) ->
                 let uu____1381 =
                   let uu____1385 = FStar_List.map (aux ix) tms  in
                   (op, uu____1385)  in
                 mkApp' uu____1381 t1.rng
             | Labeled (t2,r1,r2) ->
                 let uu____1391 =
                   let uu____1392 =
                     let uu____1396 = aux ix t2  in (uu____1396, r1, r2)  in
                   Labeled uu____1392  in
                 mk uu____1391 t2.rng
             | LblPos (t2,r) ->
                 let uu____1399 =
                   let uu____1400 =
                     let uu____1403 = aux ix t2  in (uu____1403, r)  in
                   LblPos uu____1400  in
                 mk uu____1399 t2.rng
             | Quant (qop,pats,wopt,vars,body) ->
                 let n1 = FStar_List.length vars  in
                 let uu____1419 =
                   let uu____1429 =
                     FStar_All.pipe_right pats
                       (FStar_List.map (FStar_List.map (aux (ix + n1))))
                      in
                   let uu____1440 = aux (ix + n1) body  in
                   (qop, uu____1429, wopt, vars, uu____1440)  in
                 mkQuant uu____1419 t1.rng)
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
            let uu____1476 =
              let uu____1480 = FStar_List.map (aux shift) tms2  in
              (op, uu____1480)  in
            mkApp' uu____1476 t1.rng
        | Labeled (t2,r1,r2) ->
            let uu____1486 =
              let uu____1487 =
                let uu____1491 = aux shift t2  in (uu____1491, r1, r2)  in
              Labeled uu____1487  in
            mk uu____1486 t2.rng
        | LblPos (t2,r) ->
            let uu____1494 =
              let uu____1495 =
                let uu____1498 = aux shift t2  in (uu____1498, r)  in
              LblPos uu____1495  in
            mk uu____1494 t2.rng
        | Quant (qop,pats,wopt,vars,body) ->
            let m = FStar_List.length vars  in
            let shift1 = shift + m  in
            let uu____1517 =
              let uu____1527 =
                FStar_All.pipe_right pats
                  (FStar_List.map (FStar_List.map (aux shift1)))
                 in
              let uu____1536 = aux shift1 body  in
              (qop, uu____1527, wopt, vars, uu____1536)  in
            mkQuant uu____1517 t1.rng
         in
      aux (Prims.parse_int "0") t
  
let subst : term -> fv -> term -> term =
  fun t  ->
    fun fv  ->
      fun s  -> let uu____1550 = abstr [fv] t  in inst [s] uu____1550
  
let mkQuant' :
  (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list
    * term) -> FStar_Range.range -> term
  =
  fun uu____1564  ->
    match uu____1564 with
    | (qop,pats,wopt,vars,body) ->
        let uu____1589 =
          let uu____1599 =
            FStar_All.pipe_right pats
              (FStar_List.map (FStar_List.map (abstr vars)))
             in
          let uu____1608 = FStar_List.map fv_sort vars  in
          let uu____1612 = abstr vars body  in
          (qop, uu____1599, wopt, uu____1608, uu____1612)  in
        mkQuant uu____1589
  
let mkForall'' :
  (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list *
    term) -> FStar_Range.range -> term
  =
  fun uu____1629  ->
    fun r  ->
      match uu____1629 with
      | (pats,wopt,sorts,body) -> mkQuant (Forall, pats, wopt, sorts, body) r
  
let mkForall' :
  (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term) ->
    FStar_Range.range -> term
  =
  fun uu____1666  ->
    fun r  ->
      match uu____1666 with
      | (pats,wopt,vars,body) ->
          let uu____1685 = mkQuant' (Forall, pats, wopt, vars, body)  in
          uu____1685 r
  
let mkForall :
  (pat Prims.list Prims.list * fvs * term) -> FStar_Range.range -> term =
  fun uu____1700  ->
    fun r  ->
      match uu____1700 with
      | (pats,vars,body) ->
          let uu____1714 = mkQuant' (Forall, pats, None, vars, body)  in
          uu____1714 r
  
let mkExists :
  (pat Prims.list Prims.list * fvs * term) -> FStar_Range.range -> term =
  fun uu____1729  ->
    fun r  ->
      match uu____1729 with
      | (pats,vars,body) ->
          let uu____1743 = mkQuant' (Exists, pats, None, vars, body)  in
          uu____1743 r
  
let norng : FStar_Range.range = FStar_Range.dummyRange 
let mkDefineFun :
  (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)
    -> decl
  =
  fun uu____1759  ->
    match uu____1759 with
    | (nm,vars,s,tm,c) ->
        let uu____1779 =
          let uu____1786 = FStar_List.map fv_sort vars  in
          let uu____1790 = abstr vars tm  in
          (nm, uu____1786, s, uu____1790, c)  in
        DefineFun uu____1779
  
let constr_id_of_sort : sort -> Prims.string =
  fun sort  ->
    let uu____1795 = strSort sort  in
    FStar_Util.format1 "%s_constr_id" uu____1795
  
let fresh_token : (Prims.string * sort) -> Prims.int -> decl =
  fun uu____1802  ->
    fun id  ->
      match uu____1802 with
      | (tok_name,sort) ->
          let a_name = Prims.strcat "fresh_token_" tok_name  in
          let uu____1809 =
            let uu____1814 =
              let uu____1815 =
                let uu____1818 = mkInteger' id norng  in
                let uu____1819 =
                  let uu____1820 =
                    let uu____1824 = constr_id_of_sort sort  in
                    let uu____1825 =
                      let uu____1827 = mkApp (tok_name, []) norng  in
                      [uu____1827]  in
                    (uu____1824, uu____1825)  in
                  mkApp uu____1820 norng  in
                (uu____1818, uu____1819)  in
              mkEq uu____1815 norng  in
            (uu____1814, (Some "fresh token"), (Some a_name))  in
          Assume uu____1809
  
let fresh_constructor :
  (Prims.string * sort Prims.list * sort * Prims.int) -> decl =
  fun uu____1839  ->
    match uu____1839 with
    | (name,arg_sorts,sort,id) ->
        let id1 = FStar_Util.string_of_int id  in
        let bvars =
          FStar_All.pipe_right arg_sorts
            (FStar_List.mapi
               (fun i  ->
                  fun s  ->
                    let uu____1858 =
                      let uu____1861 =
                        let uu____1862 = FStar_Util.string_of_int i  in
                        Prims.strcat "x_" uu____1862  in
                      (uu____1861, s)  in
                    mkFreeV uu____1858 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let cid_app =
          let uu____1868 =
            let uu____1872 = constr_id_of_sort sort  in (uu____1872, [capp])
             in
          mkApp uu____1868 norng  in
        let a_name = Prims.strcat "constructor_distinct_" name  in
        let uu____1875 =
          let uu____1880 =
            let uu____1881 =
              let uu____1887 =
                let uu____1888 =
                  let uu____1891 = mkInteger id1 norng  in
                  (uu____1891, cid_app)  in
                mkEq uu____1888 norng  in
              ([[capp]], bvar_names, uu____1887)  in
            mkForall uu____1881 norng  in
          (uu____1880, (Some "Constructor distinct"), (Some a_name))  in
        Assume uu____1875
  
let injective_constructor :
  (Prims.string * constructor_field Prims.list * sort) -> decl Prims.list =
  fun uu____1905  ->
    match uu____1905 with
    | (name,fields,sort) ->
        let n_bvars = FStar_List.length fields  in
        let bvar_name i =
          let uu____1921 = FStar_Util.string_of_int i  in
          Prims.strcat "x_" uu____1921  in
        let bvar_index i = n_bvars - (i + (Prims.parse_int "1"))  in
        let bvar i s =
          let uu____1938 = let uu____1941 = bvar_name i  in (uu____1941, s)
             in
          mkFreeV uu____1938  in
        let bvars =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____1950  ->
                    match uu____1950 with
                    | (uu____1954,s,uu____1956) ->
                        let uu____1957 = bvar i s  in uu____1957 norng))
           in
        let bvar_names = FStar_List.map fv_of_term bvars  in
        let capp = mkApp (name, bvars) norng  in
        let uu____1964 =
          FStar_All.pipe_right fields
            (FStar_List.mapi
               (fun i  ->
                  fun uu____1975  ->
                    match uu____1975 with
                    | (name1,s,projectible) ->
                        let cproj_app = mkApp (name1, [capp]) norng  in
                        let proj_name =
                          DeclFun (name1, [sort], s, (Some "Projector"))  in
                        if projectible
                        then
                          let a_name =
                            Prims.strcat "projection_inverse_" name1  in
                          let uu____1990 =
                            let uu____1992 =
                              let uu____1993 =
                                let uu____1998 =
                                  let uu____1999 =
                                    let uu____2005 =
                                      let uu____2006 =
                                        let uu____2009 =
                                          let uu____2010 = bvar i s  in
                                          uu____2010 norng  in
                                        (cproj_app, uu____2009)  in
                                      mkEq uu____2006 norng  in
                                    ([[capp]], bvar_names, uu____2005)  in
                                  mkForall uu____1999 norng  in
                                (uu____1998, (Some "Projection inverse"),
                                  (Some a_name))
                                 in
                              Assume uu____1993  in
                            [uu____1992]  in
                          proj_name :: uu____1990
                        else [proj_name]))
           in
        FStar_All.pipe_right uu____1964 FStar_List.flatten
  
let constructor_to_decl : constructor_t -> decl Prims.list =
  fun uu____2026  ->
    match uu____2026 with
    | (name,fields,sort,id,injective) ->
        let injective1 = injective || true  in
        let field_sorts =
          FStar_All.pipe_right fields
            (FStar_List.map
               (fun uu____2042  ->
                  match uu____2042 with
                  | (uu____2046,sort1,uu____2048) -> sort1))
           in
        let cdecl = DeclFun (name, field_sorts, sort, (Some "Constructor"))
           in
        let cid = fresh_constructor (name, field_sorts, sort, id)  in
        let disc =
          let disc_name = Prims.strcat "is-" name  in
          let xfv = ("x", sort)  in
          let xx = mkFreeV xfv norng  in
          let disc_eq =
            let uu____2061 =
              let uu____2064 =
                let uu____2065 =
                  let uu____2069 = constr_id_of_sort sort  in
                  (uu____2069, [xx])  in
                mkApp uu____2065 norng  in
              let uu____2071 =
                let uu____2072 = FStar_Util.string_of_int id  in
                mkInteger uu____2072 norng  in
              (uu____2064, uu____2071)  in
            mkEq uu____2061 norng  in
          let uu____2073 =
            let uu____2081 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____2104  ->
                        match uu____2104 with
                        | (proj,s,projectible) ->
                            if projectible
                            then
                              let uu____2121 = mkApp (proj, [xx]) norng  in
                              (uu____2121, [])
                            else
                              (let fi =
                                 let uu____2132 =
                                   let uu____2133 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "f_" uu____2133  in
                                 (uu____2132, s)  in
                               let uu____2134 = mkFreeV fi norng  in
                               (uu____2134, [fi]))))
               in
            FStar_All.pipe_right uu____2081 FStar_List.split  in
          match uu____2073 with
          | (proj_terms,ex_vars) ->
              let ex_vars1 = FStar_List.flatten ex_vars  in
              let disc_inv_body =
                let uu____2177 =
                  let uu____2180 = mkApp (name, proj_terms) norng  in
                  (xx, uu____2180)  in
                mkEq uu____2177 norng  in
              let disc_inv_body1 =
                match ex_vars1 with
                | [] -> disc_inv_body
                | uu____2185 -> mkExists ([], ex_vars1, disc_inv_body) norng
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
        let uu____2208 =
          let uu____2210 =
            let uu____2211 = FStar_Util.format1 "<start constructor %s>" name
               in
            Caption uu____2211  in
          uu____2210 :: cdecl :: cid :: projs  in
        let uu____2212 =
          let uu____2214 =
            let uu____2216 =
              let uu____2217 =
                FStar_Util.format1 "</end constructor %s>" name  in
              Caption uu____2217  in
            [uu____2216]  in
          FStar_List.append [disc] uu____2214  in
        FStar_List.append uu____2208 uu____2212
  
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
          let uu____2247 =
            FStar_All.pipe_right sorts
              (FStar_List.fold_left
                 (fun uu____2270  ->
                    fun s  ->
                      match uu____2270 with
                      | (names,binders,n1) ->
                          let prefix1 =
                            match s with
                            | Term_sort  -> "@x"
                            | uu____2298 -> "@u"  in
                          let prefix2 =
                            match prefix_opt with
                            | None  -> prefix1
                            | Some p -> Prims.strcat p prefix1  in
                          let nm =
                            let uu____2302 = FStar_Util.string_of_int n1  in
                            Prims.strcat prefix2 uu____2302  in
                          let names1 = (nm, s) :: names  in
                          let b =
                            let uu____2310 = strSort s  in
                            FStar_Util.format2 "(%s %s)" nm uu____2310  in
                          (names1, (b :: binders),
                            (n1 + (Prims.parse_int "1"))))
                 (outer_names, [], start))
             in
          match uu____2247 with
          | (names,binders,n1) -> (names, (FStar_List.rev binders), n1)
  
let name_macro_binders :
  sort Prims.list ->
    ((Prims.string * sort) Prims.list * Prims.string Prims.list)
  =
  fun sorts  ->
    let uu____2352 =
      name_binders_inner (Some "__") [] (Prims.parse_int "0") sorts  in
    match uu____2352 with
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
                           "Prims.guard_free",{ tm = BoundV uu____2409;
                                                freevars = uu____2410;
                                                rng = uu____2411;_}::[])
                          -> tm
                      | App (Var "Prims.guard_free",p::[]) -> p
                      | uu____2419 -> tm))))
       in
    let rec aux' n1 names t1 =
      match t1.tm with
      | Integer i -> i
      | BoundV i ->
          let uu____2442 = FStar_List.nth names i  in
          FStar_All.pipe_right uu____2442 Prims.fst
      | FreeV x -> Prims.fst x
      | App (op,[]) -> op_to_string op
      | App (op,tms) ->
          let uu____2452 =
            let uu____2453 = FStar_List.map (aux n1 names) tms  in
            FStar_All.pipe_right uu____2453 (FStar_String.concat "\n")  in
          FStar_Util.format2 "(%s %s)" (op_to_string op) uu____2452
      | Labeled (t2,uu____2457,uu____2458) -> aux n1 names t2
      | LblPos (t2,s) ->
          let uu____2461 = aux n1 names t2  in
          FStar_Util.format2 "(! %s :lblpos %s)" uu____2461 s
      | Quant (qop,pats,wopt,sorts,body) ->
          let uu____2475 = name_binders_inner None names n1 sorts  in
          (match uu____2475 with
           | (names1,binders,n2) ->
               let binders1 =
                 FStar_All.pipe_right binders (FStar_String.concat " ")  in
               let pats1 = remove_guard_free pats  in
               let pats_str =
                 match pats1 with
                 | []::[]|[] -> ""
                 | uu____2503 ->
                     let uu____2506 =
                       FStar_All.pipe_right pats1
                         (FStar_List.map
                            (fun pats2  ->
                               let uu____2514 =
                                 let uu____2515 =
                                   FStar_List.map
                                     (fun p  ->
                                        let uu____2518 = aux n2 names1 p  in
                                        FStar_Util.format1 "%s" uu____2518)
                                     pats2
                                    in
                                 FStar_String.concat " " uu____2515  in
                               FStar_Util.format1 "\n:pattern (%s)"
                                 uu____2514))
                        in
                     FStar_All.pipe_right uu____2506
                       (FStar_String.concat "\n")
                  in
               (match (pats1, wopt) with
                | ([]::[],None )|([],None ) ->
                    let uu____2532 = aux n2 names1 body  in
                    FStar_Util.format3 "(%s (%s)\n %s);;no pats\n"
                      (qop_to_string qop) binders1 uu____2532
                | uu____2533 ->
                    let uu____2539 = aux n2 names1 body  in
                    let uu____2540 = weightToSmt wopt  in
                    FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))"
                      (qop_to_string qop) binders1 uu____2539 uu____2540
                      pats_str))
    
    and aux n1 names t1 =
      let s = aux' n1 names t1  in
      if t1.rng <> norng
      then
        let uu____2546 = FStar_Range.string_of_range t1.rng  in
        let uu____2547 = FStar_Range.string_of_use_range t1.rng  in
        FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" uu____2546 uu____2547
          s
      else s
     in aux (Prims.parse_int "0") [] t
  
let caption_to_string : Prims.string Prims.option -> Prims.string =
  fun uu___87_2552  ->
    match uu___87_2552 with
    | None  -> ""
    | Some c ->
        let uu____2555 =
          match FStar_Util.splitlines c with
          | [] -> failwith "Impossible"
          | hd1::[] -> (hd1, "")
          | hd1::uu____2564 -> (hd1, "...")  in
        (match uu____2555 with
         | (hd1,suffix) ->
             FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd1 suffix)
  
let rec declToSmt : Prims.string -> decl -> Prims.string =
  fun z3options  ->
    fun decl  ->
      let escape s = FStar_Util.replace_char s '\'' '_'  in
      match decl with
      | DefPrelude  -> mkPrelude z3options
      | Caption c ->
          let uu____2581 =
            FStar_All.pipe_right (FStar_Util.splitlines c)
              (fun uu___88_2583  ->
                 match uu___88_2583 with | [] -> "" | h::t -> h)
             in
          FStar_Util.format1 "\n; %s" uu____2581
      | DeclFun (f,argsorts,retsort,c) ->
          let l = FStar_List.map strSort argsorts  in
          let uu____2596 = caption_to_string c  in
          let uu____2597 = strSort retsort  in
          FStar_Util.format4 "%s(declare-fun %s (%s) %s)" uu____2596 f
            (FStar_String.concat " " l) uu____2597
      | DefineFun (f,arg_sorts,retsort,body,c) ->
          let uu____2605 = name_macro_binders arg_sorts  in
          (match uu____2605 with
           | (names,binders) ->
               let body1 =
                 let uu____2623 =
                   FStar_List.map (fun x  -> mkFreeV x norng) names  in
                 inst uu____2623 body  in
               let uu____2630 = caption_to_string c  in
               let uu____2631 = strSort retsort  in
               let uu____2632 = termToSmt body1  in
               FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" uu____2630
                 f (FStar_String.concat " " binders) uu____2631 uu____2632)
      | Assume (t,c,Some n1) ->
          let uu____2637 = caption_to_string c  in
          let uu____2638 = termToSmt t  in
          FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" uu____2637
            uu____2638 (escape n1)
      | Assume (t,c,None ) ->
          let uu____2642 = caption_to_string c  in
          let uu____2643 = termToSmt t  in
          FStar_Util.format2 "%s(assert %s)" uu____2642 uu____2643
      | Eval t ->
          let uu____2645 = termToSmt t  in
          FStar_Util.format1 "(eval %s)" uu____2645
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
      let uu____2849 =
        let uu____2851 =
          FStar_All.pipe_right constrs
            (FStar_List.collect constructor_to_decl)
           in
        FStar_All.pipe_right uu____2851
          (FStar_List.map (declToSmt z3options))
         in
      FStar_All.pipe_right uu____2849 (FStar_String.concat "\n")  in
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
      let uu____2876 =
        let uu____2880 = let uu____2882 = mkInteger' i norng  in [uu____2882]
           in
        ("Tm_uvar", uu____2880)  in
      mkApp uu____2876 r
  
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
      | uu____2923 -> Prims.raise FStar_Util.Impos
  
let unboxTerm : sort -> term -> term =
  fun sort  ->
    fun t  ->
      match sort with
      | Int_sort  -> unboxInt t
      | Bool_sort  -> unboxBool t
      | String_sort  -> unboxString t
      | Ref_sort  -> unboxRef t
      | uu____2930 -> Prims.raise FStar_Util.Impos
  
let mk_PreType : term -> term = fun t  -> mkApp ("PreType", [t]) t.rng 
let mk_Valid : term -> term =
  fun t  ->
    match t.tm with
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_Equality",uu____2938::t1::t2::[]);
                       freevars = uu____2941; rng = uu____2942;_}::[])
        -> mkEq (t1, t2) t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_disEquality",uu____2949::t1::t2::[]);
                       freevars = uu____2952; rng = uu____2953;_}::[])
        -> let uu____2960 = mkEq (t1, t2) norng  in mkNot uu____2960 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThanOrEqual",t1::t2::[]);
                       freevars = uu____2963; rng = uu____2964;_}::[])
        ->
        let uu____2971 =
          let uu____2974 = unboxInt t1  in
          let uu____2975 = unboxInt t2  in (uu____2974, uu____2975)  in
        mkLTE uu____2971 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_LessThan",t1::t2::[]);
                       freevars = uu____2978; rng = uu____2979;_}::[])
        ->
        let uu____2986 =
          let uu____2989 = unboxInt t1  in
          let uu____2990 = unboxInt t2  in (uu____2989, uu____2990)  in
        mkLT uu____2986 t.rng
    | App
        (Var
         "Prims.b2t",{
                       tm = App
                         (Var "Prims.op_GreaterThanOrEqual",t1::t2::[]);
                       freevars = uu____2993; rng = uu____2994;_}::[])
        ->
        let uu____3001 =
          let uu____3004 = unboxInt t1  in
          let uu____3005 = unboxInt t2  in (uu____3004, uu____3005)  in
        mkGTE uu____3001 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_GreaterThan",t1::t2::[]);
                       freevars = uu____3008; rng = uu____3009;_}::[])
        ->
        let uu____3016 =
          let uu____3019 = unboxInt t1  in
          let uu____3020 = unboxInt t2  in (uu____3019, uu____3020)  in
        mkGT uu____3016 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_AmpAmp",t1::t2::[]);
                       freevars = uu____3023; rng = uu____3024;_}::[])
        ->
        let uu____3031 =
          let uu____3034 = unboxBool t1  in
          let uu____3035 = unboxBool t2  in (uu____3034, uu____3035)  in
        mkAnd uu____3031 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_BarBar",t1::t2::[]);
                       freevars = uu____3038; rng = uu____3039;_}::[])
        ->
        let uu____3046 =
          let uu____3049 = unboxBool t1  in
          let uu____3050 = unboxBool t2  in (uu____3049, uu____3050)  in
        mkOr uu____3046 t.rng
    | App
        (Var
         "Prims.b2t",{ tm = App (Var "Prims.op_Negation",t1::[]);
                       freevars = uu____3052; rng = uu____3053;_}::[])
        -> let uu____3060 = unboxBool t1  in mkNot uu____3060 t1.rng
    | App (Var "Prims.b2t",t1::[]) ->
        let uu___89_3063 = unboxBool t1  in
        {
          tm = (uu___89_3063.tm);
          freevars = (uu___89_3063.freevars);
          rng = (t.rng)
        }
    | uu____3066 -> mkApp ("Valid", [t]) t.rng
  
let mk_HasType : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasType", [v1; t]) t.rng 
let mk_HasTypeZ : term -> term -> term =
  fun v1  -> fun t  -> mkApp ("HasTypeZ", [v1; t]) t.rng 
let mk_IsTyped : term -> term = fun v1  -> mkApp ("IsTyped", [v1]) norng 
let mk_HasTypeFuel : term -> term -> term -> term =
  fun f  ->
    fun v1  ->
      fun t  ->
        let uu____3095 = FStar_Options.unthrottle_inductives ()  in
        if uu____3095
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
      let uu____3152 =
        let uu____3156 = let uu____3158 = mkInteger' i norng  in [uu____3158]
           in
        ("FString_const", uu____3156)  in
      mkApp uu____3152 r
  
let mk_Precedes : term -> term -> FStar_Range.range -> term =
  fun x1  ->
    fun x2  ->
      fun r  ->
        let uu____3169 = mkApp ("Precedes", [x1; x2]) r  in
        FStar_All.pipe_right uu____3169 mk_Valid
  
let mk_LexCons : term -> term -> FStar_Range.range -> term =
  fun x1  -> fun x2  -> fun r  -> mkApp ("LexCons", [x1; x2]) r 
let rec n_fuel : Prims.int -> term =
  fun n1  ->
    if n1 = (Prims.parse_int "0")
    then mkApp ("ZFuel", []) norng
    else
      (let uu____3186 =
         let uu____3190 =
           let uu____3192 = n_fuel (n1 - (Prims.parse_int "1"))  in
           [uu____3192]  in
         ("SFuel", uu____3190)  in
       mkApp uu____3186 norng)
  
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
            let uu____3215 = mkAnd (p11, p21) r  in Some uu____3215
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
      let uu____3248 = mkTrue r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkAnd (p1, p2) r) l
        uu____3248
  
let mk_or_l : term Prims.list -> FStar_Range.range -> term =
  fun l  ->
    fun r  ->
      let uu____3259 = mkFalse r  in
      FStar_List.fold_right (fun p1  -> fun p2  -> mkOr (p1, p2) r) l
        uu____3259
  
let mk_haseq : term -> term =
  fun t  ->
    let uu____3265 = mkApp ("Prims.hasEq", [t]) t.rng  in mk_Valid uu____3265
  
let rec print_smt_term : term -> Prims.string =
  fun t  ->
    match t.tm with
    | Integer n1 -> FStar_Util.format1 "(Integer %s)" n1
    | BoundV n1 ->
        let uu____3279 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "(BoundV %s)" uu____3279
    | FreeV fv -> FStar_Util.format1 "(FreeV %s)" (Prims.fst fv)
    | App (op,l) ->
        let uu____3287 = print_smt_term_list l  in
        FStar_Util.format2 "(%s %s)" (op_to_string op) uu____3287
    | Labeled (t1,r1,r2) ->
        let uu____3291 = print_smt_term t1  in
        FStar_Util.format2 "(Labeled '%s' %s)" r1 uu____3291
    | LblPos (t1,s) ->
        let uu____3294 = print_smt_term t1  in
        FStar_Util.format2 "(LblPos %s %s)" s uu____3294
    | Quant (qop,l,uu____3297,uu____3298,t1) ->
        let uu____3308 = print_smt_term_list_list l  in
        let uu____3309 = print_smt_term t1  in
        FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) uu____3308
          uu____3309

and print_smt_term_list : term Prims.list -> Prims.string =
  fun l  ->
    let uu____3312 = FStar_List.map print_smt_term l  in
    FStar_All.pipe_right uu____3312 (FStar_String.concat " ")

and print_smt_term_list_list : term Prims.list Prims.list -> Prims.string =
  fun l  ->
    FStar_List.fold_left
      (fun s  ->
         fun l1  ->
           let uu____3322 =
             let uu____3323 =
               let uu____3324 = print_smt_term_list l1  in
               Prims.strcat uu____3324 " ] "  in
             Prims.strcat "; [ " uu____3323  in
           Prims.strcat s uu____3322) "" l
