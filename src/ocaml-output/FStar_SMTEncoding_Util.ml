
open Prims
open FStar_Pervasives

let mkAssume : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.caption * Prims.string)  ->  FStar_SMTEncoding_Term.decl = (fun uu____10 -> (match (uu____10) with
| (tm, cap, nm) -> begin
FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = tm; FStar_SMTEncoding_Term.assumption_caption = cap; FStar_SMTEncoding_Term.assumption_name = nm; FStar_SMTEncoding_Term.assumption_fact_ids = []})
end))


let norng : 'Auu____28 'Auu____29 . ('Auu____29  ->  FStar_Range.range  ->  'Auu____28)  ->  'Auu____29  ->  'Auu____28 = (fun f x -> (f x FStar_Range.dummyRange))


let mkTrue : FStar_SMTEncoding_Term.term = (FStar_SMTEncoding_Term.mkTrue FStar_Range.dummyRange)


let mkFalse : FStar_SMTEncoding_Term.term = (FStar_SMTEncoding_Term.mkFalse FStar_Range.dummyRange)


let mkInteger : Prims.string  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkInteger)


let mkInteger' : Prims.int  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkInteger')


let mkBoundV : Prims.int  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkBoundV)


let mkFreeV : (Prims.string * FStar_SMTEncoding_Term.sort)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkFreeV)


let mkApp' : (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkApp')


let mkApp : (Prims.string * FStar_SMTEncoding_Term.term Prims.list)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkApp)


let mkNot : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkNot)


let mkMinus : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkMinus)


let mkAnd : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkAnd)


let mkOr : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkOr)


let mkImp : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkImp)


let mkIff : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkIff)


let mkEq : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkEq)


let mkLT : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkLT)


let mkLTE : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkLTE)


let mkGT : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkGT)


let mkGTE : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkGTE)


let mkAdd : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkAdd)


let mkSub : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkSub)


let mkDiv : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkDiv)


let mkMul : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkMul)


let mkMod : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkMod)


let mkNatToBv : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun sz -> (norng (FStar_SMTEncoding_Term.mkNatToBv sz)))


let mkBvAnd : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkBvAnd)


let mkBvXor : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkBvXor)


let mkBvOr : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkBvOr)


let mkBvShl : Prims.int  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun sz -> (norng (FStar_SMTEncoding_Term.mkBvShl sz)))


let mkBvShr : Prims.int  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun sz -> (norng (FStar_SMTEncoding_Term.mkBvShr sz)))


let mkBvUdiv : Prims.int  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun sz -> (norng (FStar_SMTEncoding_Term.mkBvUdiv sz)))


let mkBvMod : Prims.int  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun sz -> (norng (FStar_SMTEncoding_Term.mkBvMod sz)))


let mkBvMul : Prims.int  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun sz -> (norng (FStar_SMTEncoding_Term.mkBvMul sz)))


let mkBvUlt : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkBvUlt)


let mkBvUext : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun sz -> (norng (FStar_SMTEncoding_Term.mkBvUext sz)))


let mkBvToNat : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkBvToNat)


let mkITE : (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkITE)


let mkCases : FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkCases)


let mkForall : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkForall)


let mkForall' : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkForall')


let mkForall'' : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * Prims.int FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkForall'')


let mkExists : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mkExists)


let norng2 : 'Auu____540 'Auu____541 'Auu____542 . ('Auu____542  ->  'Auu____541  ->  FStar_Range.range  ->  'Auu____540)  ->  'Auu____542  ->  'Auu____541  ->  'Auu____540 = (fun f x y -> (f x y FStar_Range.dummyRange))


let mk_Term_app : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (norng2 FStar_SMTEncoding_Term.mk_Term_app)


let mk_Term_uvar : Prims.int  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mk_Term_uvar)


let mk_and_l : FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mk_and_l)


let mk_or_l : FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mk_or_l)


let mk_ApplyTT : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (norng2 FStar_SMTEncoding_Term.mk_ApplyTT)


let mk_String_const : Prims.int  ->  FStar_SMTEncoding_Term.term = (norng FStar_SMTEncoding_Term.mk_String_const)


let mk_Precedes : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (norng2 FStar_SMTEncoding_Term.mk_Precedes)


let mk_LexCons : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (norng2 FStar_SMTEncoding_Term.mk_LexCons)




