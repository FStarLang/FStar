open Prims
let mkAssume:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.caption* Prims.string)
    -> FStar_SMTEncoding_Term.decl
  =
  fun uu____6  ->
    match uu____6 with
    | (tm,cap,nm) ->
        FStar_SMTEncoding_Term.Assume
          {
            FStar_SMTEncoding_Term.assumption_term = tm;
            FStar_SMTEncoding_Term.assumption_caption = cap;
            FStar_SMTEncoding_Term.assumption_name = nm;
            FStar_SMTEncoding_Term.assumption_fact_ids = []
          }
let norng f x = f x FStar_Range.dummyRange
let mkTrue: FStar_SMTEncoding_Term.term =
  FStar_SMTEncoding_Term.mkTrue FStar_Range.dummyRange
let mkFalse: FStar_SMTEncoding_Term.term =
  FStar_SMTEncoding_Term.mkFalse FStar_Range.dummyRange
let mkInteger: Prims.string -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mkInteger
let mkInteger': Prims.int -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mkInteger'
let mkBoundV: Prims.int -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mkBoundV
let mkFreeV:
  (Prims.string* FStar_SMTEncoding_Term.sort) -> FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkFreeV
let mkApp':
  (FStar_SMTEncoding_Term.op* FStar_SMTEncoding_Term.term Prims.list) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkApp'
let mkApp:
  (Prims.string* FStar_SMTEncoding_Term.term Prims.list) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkApp
let mkNot: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mkNot
let mkMinus: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mkMinus
let mkAnd:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkAnd
let mkOr:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkOr
let mkImp:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkImp
let mkIff:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkIff
let mkEq:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkEq
let mkLT:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkLT
let mkLTE:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkLTE
let mkGT:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkGT
let mkGTE:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkGTE
let mkAdd:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkAdd
let mkSub:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkSub
let mkDiv:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkDiv
let mkMul:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkMul
let mkMod:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkMod
let mkITE:
  (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.term*
    FStar_SMTEncoding_Term.term) -> FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkITE
let mkCases:
  FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mkCases
let mkForall:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkForall
let mkForall':
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list* Prims.int option*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkForall'
let mkForall'':
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list* Prims.int option*
    FStar_SMTEncoding_Term.sort Prims.list* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkForall''
let mkExists:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = norng FStar_SMTEncoding_Term.mkExists
let norng2 f x y = f x y FStar_Range.dummyRange
let mk_Term_app:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  = norng2 FStar_SMTEncoding_Term.mk_Term_app
let mk_Term_uvar: Prims.int -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mk_Term_uvar
let mk_and_l:
  FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mk_and_l
let mk_or_l:
  FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mk_or_l
let mk_ApplyTT:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  = norng2 FStar_SMTEncoding_Term.mk_ApplyTT
let mk_String_const: Prims.int -> FStar_SMTEncoding_Term.term =
  norng FStar_SMTEncoding_Term.mk_String_const
let mk_Precedes:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  = norng2 FStar_SMTEncoding_Term.mk_Precedes
let mk_LexCons:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  = norng2 FStar_SMTEncoding_Term.mk_LexCons