
open Prims
open FStar_Pervasives

let embed_unit : Prims.unit  ->  FStar_Syntax_Syntax.term = (fun u -> FStar_Syntax_Util.exp_unit)


let unembed_unit : FStar_Syntax_Syntax.term  ->  Prims.unit = (fun uu____8 -> ())


let embed_bool : Prims.bool  ->  FStar_Syntax_Syntax.term = (fun b -> (match (b) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____13 -> begin
FStar_Syntax_Util.exp_false_bool
end))


let unembed_bool : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____18 = (

let uu____19 = (

let uu____22 = (FStar_Syntax_Util.unmeta t)
in (FStar_Syntax_Subst.compress uu____22))
in uu____19.FStar_Syntax_Syntax.n)
in (match (uu____18) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (b)) -> begin
b
end
| uu____24 -> begin
(failwith "Not an embedded bool")
end)))


let embed_int : Prims.int  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____29 = (FStar_Util.string_of_int i)
in (FStar_Syntax_Util.exp_int uu____29)))


let unembed_int : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (

let uu____34 = (

let uu____35 = (

let uu____38 = (FStar_Syntax_Util.unmeta t)
in (FStar_Syntax_Subst.compress uu____38))
in uu____35.FStar_Syntax_Syntax.n)
in (match (uu____34) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu____40)) -> begin
(FStar_Util.int_of_string s)
end
| uu____53 -> begin
(failwith "Not an embedded int")
end)))


let embed_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((s), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let unembed_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____64)) -> begin
s
end
| uu____65 -> begin
(

let uu____66 = (

let uu____67 = (

let uu____68 = (FStar_Syntax_Print.term_to_string t1)
in (Prims.strcat uu____68 ")"))
in (Prims.strcat "Not an embedded string (" uu____67))
in (failwith uu____66))
end)))


let embed_pair : 'a 'b . ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  ('b  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  ('a * 'b)  ->  FStar_Syntax_Syntax.term = (fun embed_a t_a embed_b t_b x -> (

let uu____123 = (

let uu____124 = (

let uu____125 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____125 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____126 = (

let uu____127 = (FStar_Syntax_Syntax.iarg t_a)
in (

let uu____128 = (

let uu____131 = (FStar_Syntax_Syntax.iarg t_b)
in (

let uu____132 = (

let uu____135 = (

let uu____136 = (embed_a (FStar_Pervasives_Native.fst x))
in (FStar_Syntax_Syntax.as_arg uu____136))
in (

let uu____137 = (

let uu____140 = (

let uu____141 = (embed_b (FStar_Pervasives_Native.snd x))
in (FStar_Syntax_Syntax.as_arg uu____141))
in (uu____140)::[])
in (uu____135)::uu____137))
in (uu____131)::uu____132))
in (uu____127)::uu____128))
in (FStar_Syntax_Syntax.mk_Tm_app uu____124 uu____126)))
in (uu____123 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let unembed_pair : 'a 'b . (FStar_Syntax_Syntax.term  ->  'a)  ->  (FStar_Syntax_Syntax.term  ->  'b)  ->  FStar_Syntax_Syntax.term  ->  ('a * 'b) = (fun unembed_a unembed_b pair -> (

let pairs = (FStar_Syntax_Util.unmeta pair)
in (

let uu____183 = (FStar_Syntax_Util.head_and_args pair)
in (match (uu____183) with
| (hd1, args) -> begin
(

let uu____224 = (

let uu____237 = (

let uu____238 = (FStar_Syntax_Util.un_uinst hd1)
in uu____238.FStar_Syntax_Syntax.n)
in ((uu____237), (args)))
in (match (uu____224) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____254)::(uu____255)::((a, uu____257))::((b, uu____259))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lid_Mktuple2) -> begin
(

let uu____318 = (unembed_a a)
in (

let uu____319 = (unembed_b b)
in ((uu____318), (uu____319))))
end
| uu____320 -> begin
(failwith "Not an embedded pair")
end))
end))))


let embed_option : 'a . ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term = (fun embed_a typ o -> (match (o) with
| FStar_Pervasives_Native.None -> begin
(

let uu____367 = (

let uu____368 = (

let uu____369 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____369 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____370 = (

let uu____371 = (FStar_Syntax_Syntax.iarg typ)
in (uu____371)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____368 uu____370)))
in (uu____367 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Pervasives_Native.Some (a) -> begin
(

let uu____375 = (

let uu____376 = (

let uu____377 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____377 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____378 = (

let uu____379 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____380 = (

let uu____383 = (

let uu____384 = (embed_a a)
in (FStar_Syntax_Syntax.as_arg uu____384))
in (uu____383)::[])
in (uu____379)::uu____380))
in (FStar_Syntax_Syntax.mk_Tm_app uu____376 uu____378)))
in (uu____375 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_option : 'a . (FStar_Syntax_Syntax.term  ->  'a)  ->  FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option = (fun unembed_a o -> (

let uu____409 = (

let uu____424 = (FStar_Syntax_Util.unmeta o)
in (FStar_Syntax_Util.head_and_args uu____424))
in (match (uu____409) with
| (hd1, args) -> begin
(

let uu____449 = (

let uu____462 = (

let uu____463 = (FStar_Syntax_Util.un_uinst hd1)
in uu____463.FStar_Syntax_Syntax.n)
in ((uu____462), (args)))
in (match (uu____449) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____477) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____495)::((a, uu____497))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid) -> begin
(

let uu____534 = (unembed_a a)
in FStar_Pervasives_Native.Some (uu____534))
end
| uu____535 -> begin
(failwith "Not an embedded option")
end))
end)))


let rec embed_list : 'a . ('a  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term  ->  'a Prims.list  ->  FStar_Syntax_Syntax.term = (fun embed_a typ l -> (match (l) with
| [] -> begin
(

let uu____580 = (

let uu____581 = (

let uu____582 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____582 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____583 = (

let uu____584 = (FStar_Syntax_Syntax.iarg typ)
in (uu____584)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____581 uu____583)))
in (uu____580 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| (hd1)::tl1 -> begin
(

let uu____591 = (

let uu____592 = (

let uu____593 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____593 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____594 = (

let uu____595 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____596 = (

let uu____599 = (

let uu____600 = (embed_a hd1)
in (FStar_Syntax_Syntax.as_arg uu____600))
in (

let uu____601 = (

let uu____604 = (

let uu____605 = (embed_list embed_a typ tl1)
in (FStar_Syntax_Syntax.as_arg uu____605))
in (uu____604)::[])
in (uu____599)::uu____601))
in (uu____595)::uu____596))
in (FStar_Syntax_Syntax.mk_Tm_app uu____592 uu____594)))
in (uu____591 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let rec unembed_list : 'a . (FStar_Syntax_Syntax.term  ->  'a)  ->  FStar_Syntax_Syntax.term  ->  'a Prims.list = (fun unembed_a l -> (

let l1 = (FStar_Syntax_Util.unmeta l)
in (

let uu____631 = (FStar_Syntax_Util.head_and_args l1)
in (match (uu____631) with
| (hd1, args) -> begin
(

let uu____670 = (

let uu____683 = (

let uu____684 = (FStar_Syntax_Util.un_uinst hd1)
in uu____684.FStar_Syntax_Syntax.n)
in ((uu____683), (args)))
in (match (uu____670) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____698) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_t)::((hd2, uu____718))::((tl1, uu____720))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____767 = (unembed_a hd2)
in (

let uu____768 = (unembed_list unembed_a tl1)
in (uu____767)::uu____768))
end
| uu____771 -> begin
(

let uu____784 = (

let uu____785 = (FStar_Syntax_Print.tag_of_term l1)
in (

let uu____786 = (FStar_Syntax_Print.term_to_string l1)
in (FStar_Util.format2 "(%s) Not an embedded list: %s" uu____785 uu____786)))
in (failwith uu____784))
end))
end))))


let embed_string_list : Prims.string Prims.list  ->  FStar_Syntax_Syntax.term = (fun ss -> (embed_list embed_string FStar_Syntax_Syntax.t_string ss))


let unembed_string_list : FStar_Syntax_Syntax.term  ->  Prims.string Prims.list = (fun t -> (unembed_list unembed_string t))

type norm_step =
| Simpl
| WHNF
| Primops
| Delta
| Zeta
| Iota
| UnfoldOnly of Prims.string Prims.list


let uu___is_Simpl : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simpl -> begin
true
end
| uu____813 -> begin
false
end))


let uu___is_WHNF : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WHNF -> begin
true
end
| uu____818 -> begin
false
end))


let uu___is_Primops : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____823 -> begin
false
end))


let uu___is_Delta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta -> begin
true
end
| uu____828 -> begin
false
end))


let uu___is_Zeta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____833 -> begin
false
end))


let uu___is_Iota : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____838 -> begin
false
end))


let uu___is_UnfoldOnly : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____846 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : norm_step  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let steps_Simpl : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl)


let steps_WHNF : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_whnf)


let steps_Primops : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops)


let steps_Delta : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta)


let steps_Zeta : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta)


let steps_Iota : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota)


let steps_UnfoldOnly : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly)


let embed_norm_step : norm_step  ->  FStar_Syntax_Syntax.term = (fun n1 -> (match (n1) with
| Simpl -> begin
steps_Simpl
end
| WHNF -> begin
steps_WHNF
end
| Primops -> begin
steps_Primops
end
| Delta -> begin
steps_Delta
end
| Zeta -> begin
steps_Zeta
end
| Iota -> begin
steps_Iota
end
| UnfoldOnly (l) -> begin
(

let uu____868 = (

let uu____869 = (

let uu____870 = (

let uu____871 = (embed_list embed_string FStar_Syntax_Syntax.t_string l)
in (FStar_Syntax_Syntax.as_arg uu____871))
in (uu____870)::[])
in (FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____869))
in (uu____868 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_norm_step : FStar_Syntax_Syntax.term  ->  norm_step = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____879 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____879) with
| (hd1, args) -> begin
(

let uu____916 = (

let uu____929 = (

let uu____930 = (FStar_Syntax_Util.un_uinst hd1)
in uu____930.FStar_Syntax_Syntax.n)
in ((uu____929), (args)))
in (match (uu____916) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl) -> begin
Simpl
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_whnf) -> begin
WHNF
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops) -> begin
Primops
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta) -> begin
Delta
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta) -> begin
Zeta
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota) -> begin
Iota
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____1033))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly) -> begin
(

let uu____1058 = (unembed_list unembed_string l)
in UnfoldOnly (uu____1058))
end
| uu____1061 -> begin
(failwith "not an embedded norm_step")
end))
end))))




