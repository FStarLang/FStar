
open Prims
open FStar_Pervasives

let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun a b -> (match ((a > b)) with
| true -> begin
a
end
| uu____11 -> begin
b
end))


let map_rev : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list = (fun f l -> (

let rec aux = (fun l1 acc -> (match (l1) with
| [] -> begin
acc
end
| (x)::xs -> begin
(

let uu____70 = (

let uu____73 = (f x)
in (uu____73)::acc)
in (aux xs uu____70))
end))
in (aux l [])))


let map_rev_append : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list  ->  'b Prims.list = (fun f l1 l2 -> (

let rec aux = (fun l acc -> (match (l) with
| [] -> begin
l2
end
| (x)::xs -> begin
(

let uu____143 = (

let uu____146 = (f x)
in (uu____146)::acc)
in (aux xs uu____143))
end))
in (aux l1 l2)))


let rec map_append : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list  ->  'b Prims.list = (fun f l1 l2 -> (match (l1) with
| [] -> begin
l2
end
| (x)::xs -> begin
(

let uu____195 = (f x)
in (

let uu____196 = (map_append f xs l2)
in (uu____195)::uu____196))
end))


let rec drop : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list = (fun p l -> (match (l) with
| [] -> begin
[]
end
| (x)::xs -> begin
(

let uu____232 = (p x)
in (match (uu____232) with
| true -> begin
(x)::xs
end
| uu____235 -> begin
(drop p xs)
end))
end))


let fmap_opt : 'a 'b . ('a  ->  'b)  ->  'a FStar_Pervasives_Native.option  ->  'b FStar_Pervasives_Native.option = (fun f x -> (FStar_Util.bind_opt x (fun x1 -> (

let uu____270 = (f x1)
in FStar_Pervasives_Native.Some (uu____270)))))


let drop_until : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list = (fun f l -> (

let rec aux = (fun l1 -> (match (l1) with
| [] -> begin
[]
end
| (x)::xs -> begin
(

let uu____317 = (f x)
in (match (uu____317) with
| true -> begin
l1
end
| uu____320 -> begin
(aux xs)
end))
end))
in (aux l)))


let trim : Prims.bool Prims.list  ->  Prims.bool Prims.list = (fun l -> (

let uu____334 = (drop_until FStar_Pervasives.id (FStar_List.rev l))
in (FStar_List.rev uu____334)))


let implies : Prims.bool  ->  Prims.bool  ->  Prims.bool = (fun b1 b2 -> (match (((b1), (b2))) with
| (false, uu____347) -> begin
true
end
| (true, b21) -> begin
b21
end))


let debug : FStar_TypeChecker_Cfg.cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (

let uu____364 = (

let uu____365 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in (FStar_TypeChecker_Env.debug uu____365 (FStar_Options.Other ("NBE"))))
in (match (uu____364) with
| true -> begin
(f ())
end
| uu____366 -> begin
()
end)))


let debug_term : FStar_Syntax_Syntax.term  ->  unit = (fun t -> (

let uu____372 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "%s\n" uu____372)))


let debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap  ->  unit = (fun m -> (FStar_Util.smap_fold m (fun k v1 u -> (

let uu____389 = (FStar_Syntax_Print.sigelt_to_string_short v1)
in (FStar_Util.print2 "%s -> %%s\n" k uu____389))) ()))


let unlazy : FStar_TypeChecker_NBETerm.t  ->  FStar_TypeChecker_NBETerm.t = (fun t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (uu____395, t1) -> begin
(FStar_Common.force_thunk t1)
end
| t1 -> begin
t1
end))


let pickBranch : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_NBETerm.t Prims.list) FStar_Pervasives_Native.option = (fun cfg scrut branches -> (

let rec pickBranch_aux = (fun scrut1 branches1 branches0 -> (

let rec matches_pat = (fun scrutinee0 p -> ((debug cfg (fun uu____560 -> (

let uu____561 = (FStar_TypeChecker_NBETerm.t_to_string scrutinee0)
in (

let uu____562 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "matches_pat (%s, %s)\n" uu____561 uu____562)))));
(

let scrutinee = (unlazy scrutinee0)
in (

let r = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((scrutinee0)::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((scrutinee0)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____583) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let matches_const = (fun c s1 -> ((debug cfg (fun uu____608 -> (

let uu____609 = (FStar_TypeChecker_NBETerm.t_to_string c)
in (

let uu____610 = (FStar_Syntax_Print.const_to_string s1)
in (FStar_Util.print2 "Testing term %s against pattern %s\n" uu____609 uu____610)))));
(match (c) with
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit) -> begin
(Prims.op_Equality s1 FStar_Const.Const_unit)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool (b)) -> begin
(match (s1) with
| FStar_Const.Const_bool (p1) -> begin
(Prims.op_Equality b p1)
end
| uu____613 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i)) -> begin
(match (s1) with
| FStar_Const.Const_int (p1, FStar_Pervasives_Native.None) -> begin
(

let uu____626 = (FStar_BigInt.big_int_of_string p1)
in (Prims.op_Equality i uu____626))
end
| uu____627 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String (st, uu____629)) -> begin
(match (s1) with
| FStar_Const.Const_string (p1, uu____631) -> begin
(Prims.op_Equality st p1)
end
| uu____632 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char (c1)) -> begin
(match (s1) with
| FStar_Const.Const_char (p1) -> begin
(Prims.op_Equality c1 p1)
end
| uu____638 -> begin
false
end)
end
| uu____639 -> begin
false
end);
))
in (

let uu____640 = (matches_const scrutinee s)
in (match (uu____640) with
| true -> begin
FStar_Util.Inl ([])
end
| uu____649 -> begin
FStar_Util.Inr (false)
end)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let rec matches_args = (fun out a p1 -> (match (((a), (p1))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, uu____761))::rest_a, ((p2, uu____764))::rest_p) -> begin
(

let uu____798 = (matches_pat t p2)
in (match (uu____798) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____823 -> begin
FStar_Util.Inr (false)
end))
in (match (scrutinee) with
| FStar_TypeChecker_NBETerm.Construct (fv', _us, args_rev) -> begin
(

let uu____867 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (match (uu____867) with
| true -> begin
(matches_args [] (FStar_List.rev args_rev) arg_pats)
end
| uu____878 -> begin
FStar_Util.Inr (false)
end))
end
| uu____881 -> begin
FStar_Util.Inr (true)
end))
end)
in (

let res_to_string = (fun uu___260_895 -> (match (uu___260_895) with
| FStar_Util.Inr (b) -> begin
(

let uu____905 = (FStar_Util.string_of_bool b)
in (Prims.strcat "Inr " uu____905))
end
| FStar_Util.Inl (bs) -> begin
(

let uu____911 = (FStar_Util.string_of_int (FStar_List.length bs))
in (Prims.strcat "Inl " uu____911))
end))
in ((debug cfg (fun uu____917 -> (

let uu____918 = (FStar_TypeChecker_NBETerm.t_to_string scrutinee)
in (

let uu____919 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____920 = (res_to_string r)
in (FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____918 uu____919 uu____920))))));
r;
))));
))
in (match (branches1) with
| [] -> begin
(failwith "Branch not found")
end
| ((p, _wopt, e))::branches2 -> begin
(

let uu____959 = (matches_pat scrut1 p)
in (match (uu____959) with
| FStar_Util.Inl (matches) -> begin
((debug cfg (fun uu____982 -> (

let uu____983 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print1 "Pattern %s matches\n" uu____983))));
FStar_Pervasives_Native.Some (((e), (matches)));
)
end
| FStar_Util.Inr (false) -> begin
(pickBranch_aux scrut1 branches2 branches0)
end
| FStar_Util.Inr (true) -> begin
FStar_Pervasives_Native.None
end))
end)))
in (pickBranch_aux scrut branches branches)))


let test_args : (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list  ->  Prims.bool Prims.list  ->  (Prims.bool * FStar_TypeChecker_NBETerm.args * FStar_TypeChecker_NBETerm.args) = (fun ts ar_list -> (

let rec aux = (fun ts1 ar_list1 acc res -> (match (((ts1), (ar_list1))) with
| (uu____1133, []) -> begin
((true), ((FStar_List.rev acc)), (ts1))
end
| ([], (uu____1164)::uu____1165) -> begin
((false), ((FStar_List.rev acc)), ([]))
end
| ((t)::ts2, (b)::bs) -> begin
(

let uu____1228 = (res && (

let uu____1230 = (

let uu____1231 = (FStar_TypeChecker_NBETerm.isAccu (FStar_Pervasives_Native.fst t))
in (not (uu____1231)))
in (implies b uu____1230)))
in (aux ts2 bs ((t)::acc) uu____1228))
end))
in (aux ts ar_list [] true)))


let find_sigelt_in_gamma : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun cfg env lid -> (

let mapper = (fun uu____1284 -> (match (uu____1284) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inr (elt, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some (elt)
end
| FStar_Util.Inr (elt, FStar_Pervasives_Native.Some (us)) -> begin
((debug cfg (fun uu____1367 -> (

let uu____1368 = (FStar_Syntax_Print.univs_to_string us)
in (FStar_Util.print1 "Universes in local declaration: %s\n" uu____1368))));
FStar_Pervasives_Native.Some (elt);
)
end
| uu____1369 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____1384 = (FStar_TypeChecker_Env.lookup_qname env lid)
in (FStar_Util.bind_opt uu____1384 mapper))))


let is_univ : FStar_TypeChecker_NBETerm.t  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_TypeChecker_NBETerm.Univ (uu____1428) -> begin
true
end
| uu____1429 -> begin
false
end))


let un_univ : FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.universe = (fun tm -> (match (tm) with
| FStar_TypeChecker_NBETerm.Univ (u) -> begin
u
end
| t -> begin
(

let uu____1437 = (

let uu____1438 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (Prims.strcat "Not a universe: " uu____1438))
in (failwith uu____1437))
end))


let is_constr_fv : FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun fvar1 -> (Prims.op_Equality fvar1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))


let is_constr : FStar_TypeChecker_Env.qninfo  ->  Prims.bool = (fun q -> (match (q) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____1451, uu____1452, uu____1453, uu____1454, uu____1455, uu____1456); FStar_Syntax_Syntax.sigrng = uu____1457; FStar_Syntax_Syntax.sigquals = uu____1458; FStar_Syntax_Syntax.sigmeta = uu____1459; FStar_Syntax_Syntax.sigattrs = uu____1460}, uu____1461), uu____1462) -> begin
true
end
| uu____1517 -> begin
false
end))


let translate_univ : FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun bs u -> (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (i) -> begin
(match ((i < (FStar_List.length bs))) with
| true -> begin
(

let u' = (FStar_List.nth bs i)
in (un_univ u'))
end
| uu____1541 -> begin
(failwith "Universe index out of bounds")
end)
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1543 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1543))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1547 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1547))
end
| FStar_Syntax_Syntax.U_unknown -> begin
u2
end
| FStar_Syntax_Syntax.U_name (uu____1550) -> begin
u2
end
| FStar_Syntax_Syntax.U_unif (uu____1551) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end)))
in (aux u)))


let find_let : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option = (fun lbs fvar1 -> (FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1581) -> begin
(failwith "find_let : impossible")
end
| FStar_Util.Inr (name) -> begin
(

let uu____1585 = (FStar_Syntax_Syntax.fv_eq name fvar1)
in (match (uu____1585) with
| true -> begin
FStar_Pervasives_Native.Some (lb)
end
| uu____1588 -> begin
FStar_Pervasives_Native.None
end))
end))))


let rec iapp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_TypeChecker_NBETerm.args  ->  FStar_TypeChecker_NBETerm.t = (fun cfg f args -> (match (f) with
| FStar_TypeChecker_NBETerm.Lam (f1, targs, n1, res) -> begin
(

let m = (FStar_List.length args)
in (match ((m < n1)) with
| true -> begin
(

let uu____1931 = (FStar_List.splitAt m targs)
in (match (uu____1931) with
| (uu____1971, targs') -> begin
(

let targs'1 = (FStar_List.map (fun targ l -> (

let uu____2062 = (

let uu____2065 = (map_append FStar_Pervasives_Native.fst args l)
in (FStar_List.rev uu____2065))
in (targ uu____2062))) targs')
in FStar_TypeChecker_NBETerm.Lam ((((fun l -> (

let uu____2098 = (map_append FStar_Pervasives_Native.fst args l)
in (f1 uu____2098)))), (targs'1), ((n1 - m)), (res))))
end))
end
| uu____2109 -> begin
(match ((Prims.op_Equality m n1)) with
| true -> begin
(

let uu____2114 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (f1 uu____2114))
end
| uu____2121 -> begin
(

let uu____2122 = (FStar_List.splitAt n1 args)
in (match (uu____2122) with
| (args1, args') -> begin
(

let uu____2169 = (

let uu____2170 = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (f1 uu____2170))
in (iapp cfg uu____2169 args'))
end))
end)
end))
end
| FStar_TypeChecker_NBETerm.Accu (a, ts) -> begin
FStar_TypeChecker_NBETerm.Accu (((a), ((FStar_List.rev_append args ts))))
end
| FStar_TypeChecker_NBETerm.Construct (i, us, ts) -> begin
(

let rec aux = (fun args1 us1 ts1 -> (match (args1) with
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2289))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2333 = (aux args us ts)
in (match (uu____2333) with
| (us', ts') -> begin
FStar_TypeChecker_NBETerm.Construct (((i), (us'), (ts')))
end)))
end
| FStar_TypeChecker_NBETerm.FV (i, us, ts) -> begin
(

let rec aux = (fun args1 us1 ts1 -> (match (args1) with
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2460))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2504 = (aux args us ts)
in (match (uu____2504) with
| (us', ts') -> begin
FStar_TypeChecker_NBETerm.FV (((i), (us'), (ts')))
end)))
end
| FStar_TypeChecker_NBETerm.Rec (lb, lbs, bs, acc, ar, ar_lst, tr_lb) -> begin
(

let no_args = (FStar_List.length args)
in (match ((ar > no_args)) with
| true -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), ((FStar_List.append acc args)), ((ar - no_args)), (ar_lst), (tr_lb)))
end
| uu____2627 -> begin
(match ((Prims.op_Equality ar (Prims.parse_int "0"))) with
| true -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), ((FStar_List.append acc args)), (ar), (ar_lst), (tr_lb)))
end
| uu____2652 -> begin
(

let full_args = (FStar_List.append acc args)
in (

let uu____2664 = (test_args full_args ar_lst)
in (match (uu____2664) with
| (can_unfold, args1, res) -> begin
(match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta))) with
| true -> begin
((debug cfg (fun uu____2677 -> (

let uu____2678 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Zeta is not set; will not unfold %s\n" uu____2678))));
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)));
)
end
| uu____2699 -> begin
(match (can_unfold) with
| true -> begin
((debug cfg (fun uu____2703 -> (

let uu____2704 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Beta reducing recursive function %s\n" uu____2704))));
(match (res) with
| [] -> begin
(

let uu____2709 = (

let uu____2710 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2710 lb))
in (iapp cfg uu____2709 args1))
end
| (uu____2713)::uu____2714 -> begin
(

let t = (

let uu____2730 = (

let uu____2731 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2731 lb))
in (iapp cfg uu____2730 args1))
in (iapp cfg t res))
end);
)
end
| uu____2734 -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)))
end)
end)
end)))
end)
end))
end
| FStar_TypeChecker_NBETerm.Quote (uu____2755) -> begin
(

let uu____2760 = (

let uu____2761 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2761))
in (failwith uu____2760))
end
| FStar_TypeChecker_NBETerm.Reflect (uu____2762) -> begin
(

let uu____2763 = (

let uu____2764 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2764))
in (failwith uu____2763))
end
| FStar_TypeChecker_NBETerm.Lazy (uu____2765) -> begin
(

let uu____2780 = (

let uu____2781 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2781))
in (failwith uu____2780))
end
| FStar_TypeChecker_NBETerm.Constant (uu____2782) -> begin
(

let uu____2783 = (

let uu____2784 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2784))
in (failwith uu____2783))
end
| FStar_TypeChecker_NBETerm.Univ (uu____2785) -> begin
(

let uu____2786 = (

let uu____2787 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2787))
in (failwith uu____2786))
end
| FStar_TypeChecker_NBETerm.Type_t (uu____2788) -> begin
(

let uu____2789 = (

let uu____2790 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2790))
in (failwith uu____2789))
end
| FStar_TypeChecker_NBETerm.Unknown -> begin
(

let uu____2791 = (

let uu____2792 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2792))
in (failwith uu____2791))
end
| FStar_TypeChecker_NBETerm.Refinement (uu____2793) -> begin
(

let uu____2808 = (

let uu____2809 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2809))
in (failwith uu____2808))
end
| FStar_TypeChecker_NBETerm.Arrow (uu____2810) -> begin
(

let uu____2831 = (

let uu____2832 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____2832))
in (failwith uu____2831))
end))
and translate_fv : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs fvar1 -> (

let debug1 = (debug cfg)
in (

let qninfo = (

let uu____2847 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in (

let uu____2848 = (FStar_Syntax_Syntax.lid_of_fv fvar1)
in (FStar_TypeChecker_Env.lookup_qname uu____2847 uu____2848)))
in (

let uu____2849 = ((is_constr qninfo) || (is_constr_fv fvar1))
in (match (uu____2849) with
| true -> begin
(FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] [])
end
| uu____2854 -> begin
(

let uu____2855 = (FStar_TypeChecker_Normalize.should_unfold cfg (fun uu____2857 -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1 qninfo)
in (match (uu____2855) with
| FStar_TypeChecker_Normalize.Should_unfold_fully -> begin
(failwith "Not yet handled")
end
| FStar_TypeChecker_Normalize.Should_unfold_no -> begin
((debug1 (fun uu____2863 -> (

let uu____2864 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(1) Decided to not unfold %s\n" uu____2864))));
(

let uu____2865 = (FStar_TypeChecker_Cfg.find_prim_step cfg fvar1)
in (match (uu____2865) with
| FStar_Pervasives_Native.Some (prim_step) when prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok -> begin
(

let arity = (prim_step.FStar_TypeChecker_Cfg.arity + prim_step.FStar_TypeChecker_Cfg.univ_arity)
in ((debug1 (fun uu____2875 -> (

let uu____2876 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Found a primop %s\n" uu____2876))));
(

let uu____2877 = (

let uu____2907 = (

let f = (fun uu____2934 uu____2935 -> ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))
in (FStar_Common.tabulate arity f))
in (((fun args -> (

let args' = (FStar_List.map FStar_TypeChecker_NBETerm.as_arg args)
in (

let callbacks = {FStar_TypeChecker_NBETerm.iapp = (iapp cfg); FStar_TypeChecker_NBETerm.translate = (translate cfg bs)}
in (

let uu____2993 = (prim_step.FStar_TypeChecker_Cfg.interpretation_nbe callbacks args')
in (match (uu____2993) with
| FStar_Pervasives_Native.Some (x) -> begin
((debug1 (fun uu____3004 -> (

let uu____3005 = (FStar_Syntax_Print.fv_to_string fvar1)
in (

let uu____3006 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print2 "Primitive operator %s returned %s\n" uu____3005 uu____3006)))));
x;
)
end
| FStar_Pervasives_Native.None -> begin
((debug1 (fun uu____3012 -> (

let uu____3013 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Primitive operator %s failed\n" uu____3013))));
(

let uu____3014 = (FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
in (iapp cfg uu____3014 args'));
)
end)))))), (uu____2907), (arity), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____2877));
))
end
| FStar_Pervasives_Native.Some (uu____3022) -> begin
((debug1 (fun uu____3028 -> (

let uu____3029 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(2) Decided to not unfold %s\n" uu____3029))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end
| uu____3034 -> begin
((debug1 (fun uu____3042 -> (

let uu____3043 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(3) Decided to not unfold %s\n" uu____3043))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end));
)
end
| FStar_TypeChecker_Normalize.Should_unfold_reify -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3051; FStar_Syntax_Syntax.sigquals = uu____3052; FStar_Syntax_Syntax.sigmeta = uu____3053; FStar_Syntax_Syntax.sigattrs = uu____3054}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3119 -> begin
((debug1 (fun uu____3123 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3131 -> (

let uu____3132 = (

let uu____3133 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3133))
in (

let uu____3134 = (

let uu____3135 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3135))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3132 uu____3134)))));
(debug1 (fun uu____3143 -> (

let uu____3144 = (

let uu____3145 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3145))
in (

let uu____3146 = (

let uu____3147 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3147))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3144 uu____3146)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3148 -> begin
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
end)
end
| FStar_TypeChecker_Normalize.Should_unfold_yes -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3156; FStar_Syntax_Syntax.sigquals = uu____3157; FStar_Syntax_Syntax.sigmeta = uu____3158; FStar_Syntax_Syntax.sigattrs = uu____3159}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3224 -> begin
((debug1 (fun uu____3228 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3236 -> (

let uu____3237 = (

let uu____3238 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3238))
in (

let uu____3239 = (

let uu____3240 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3240))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3237 uu____3239)))));
(debug1 (fun uu____3248 -> (

let uu____3249 = (

let uu____3250 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3250))
in (

let uu____3251 = (

let uu____3252 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3252))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3249 uu____3251)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3253 -> begin
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
end)
end))
end)))))
and translate_letbinding : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs lb -> (

let debug1 = (debug cfg)
in (

let us = lb.FStar_Syntax_Syntax.lbunivs
in (

let id1 = (fun x -> x)
in (match (us) with
| [] -> begin
(translate cfg bs lb.FStar_Syntax_Syntax.lbdef)
end
| uu____3298 -> begin
(

let uu____3301 = (

let uu____3331 = (FStar_List.map (fun uu____3356 _ts -> (FStar_All.pipe_left id1 ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))) us)
in (((fun us1 -> (translate cfg (FStar_List.rev_append us1 bs) lb.FStar_Syntax_Syntax.lbdef))), (uu____3331), ((FStar_List.length us)), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____3301))
end)))))
and mkRec' : (FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_TypeChecker_NBETerm.t)  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun callback b bs env -> (

let uu____3416 = (FStar_Syntax_Util.let_rec_arity b)
in (match (uu____3416) with
| (ar, maybe_lst) -> begin
(

let uu____3435 = (match (maybe_lst) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3450 = (FStar_Common.tabulate ar (fun uu____3454 -> true))
in ((ar), (uu____3450)))
end
| FStar_Pervasives_Native.Some (lst) -> begin
(

let l = (trim lst)
in (((FStar_List.length l)), (l)))
end)
in (match (uu____3435) with
| (ar1, ar_lst) -> begin
FStar_TypeChecker_NBETerm.Rec (((b), (bs), (env), ([]), (ar1), (ar_lst), (callback)))
end))
end)))
and mkRec : FStar_TypeChecker_Cfg.cfg  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun cfg b bs env -> (mkRec' (translate_letbinding cfg) b bs env))
and make_rec_env : (FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_TypeChecker_NBETerm.t)  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_TypeChecker_NBETerm.t Prims.list = (fun callback lbs bs -> (

let rec aux = (fun lbs1 lbs0 bs1 bs0 -> (match (lbs1) with
| [] -> begin
bs1
end
| (lb)::lbs' -> begin
(

let uu____3565 = (

let uu____3568 = (mkRec' callback lb lbs0 bs0)
in (uu____3568)::bs1)
in (aux lbs' lbs0 uu____3565 bs0))
end))
in (aux lbs lbs bs bs)))
and translate_constant : FStar_Syntax_Syntax.sconst  ->  FStar_TypeChecker_NBETerm.constant = (fun c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_NBETerm.Unit
end
| FStar_Const.Const_bool (b) -> begin
FStar_TypeChecker_NBETerm.Bool (b)
end
| FStar_Const.Const_int (s, FStar_Pervasives_Native.None) -> begin
(

let uu____3582 = (FStar_BigInt.big_int_of_string s)
in FStar_TypeChecker_NBETerm.Int (uu____3582))
end
| FStar_Const.Const_string (s, r) -> begin
FStar_TypeChecker_NBETerm.String (((s), (r)))
end
| FStar_Const.Const_char (c1) -> begin
FStar_TypeChecker_NBETerm.Char (c1)
end
| FStar_Const.Const_range (r) -> begin
FStar_TypeChecker_NBETerm.Range (r)
end
| uu____3588 -> begin
(

let uu____3589 = (

let uu____3590 = (

let uu____3591 = (FStar_Syntax_Print.const_to_string c)
in (Prims.strcat uu____3591 ": Not yet implemented"))
in (Prims.strcat "Tm_constant " uu____3590))
in (failwith uu____3589))
end))
and translate : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs e -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____3612 -> (

let uu____3613 = (

let uu____3614 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____3614))
in (

let uu____3615 = (

let uu____3616 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.term_to_string uu____3616))
in (FStar_Util.print2 "Term: %s - %s\n" uu____3613 uu____3615)))));
(debug1 (fun uu____3622 -> (

let uu____3623 = (

let uu____3624 = (FStar_List.map (fun x -> (FStar_TypeChecker_NBETerm.t_to_string x)) bs)
in (FStar_String.concat ";; " uu____3624))
in (FStar_Util.print1 "BS list: %s\n" uu____3623))));
(

let uu____3629 = (

let uu____3630 = (FStar_Syntax_Subst.compress e)
in uu____3630.FStar_Syntax_Syntax.n)
in (match (uu____3629) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3633, uu____3634) -> begin
(failwith "Tm_delayed: Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_TypeChecker_NBETerm.Unknown
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____3672 = (translate_constant c)
in FStar_TypeChecker_NBETerm.Constant (uu____3672))
end
| FStar_Syntax_Syntax.Tm_bvar (db) -> begin
(match ((db.FStar_Syntax_Syntax.index < (FStar_List.length bs))) with
| true -> begin
(FStar_List.nth bs db.FStar_Syntax_Syntax.index)
end
| uu____3674 -> begin
(failwith "de Bruijn index out of bounds")
end)
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
((debug1 (fun uu____3688 -> (

let uu____3689 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____3690 = (

let uu____3691 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_All.pipe_right uu____3691 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n" uu____3689 uu____3690)))));
(

let uu____3696 = (translate cfg bs t)
in (

let uu____3697 = (FStar_List.map (fun x -> (

let uu____3701 = (

let uu____3702 = (translate_univ bs x)
in FStar_TypeChecker_NBETerm.Univ (uu____3702))
in (FStar_TypeChecker_NBETerm.as_arg uu____3701))) us)
in (iapp cfg uu____3696 uu____3697)));
)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____3704 = (translate_univ bs u)
in FStar_TypeChecker_NBETerm.Type_t (uu____3704))
end
| FStar_Syntax_Syntax.Tm_arrow (xs, c) -> begin
(

let uu____3727 = (

let uu____3748 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____3818 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____3818), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (((fun ys -> (translate_comp cfg (FStar_List.rev_append ys bs) c))), (uu____3748)))
in FStar_TypeChecker_NBETerm.Arrow (uu____3727))
end
| FStar_Syntax_Syntax.Tm_refine (bv, tm) -> begin
FStar_TypeChecker_NBETerm.Refinement ((((fun y -> (translate cfg ((y)::bs) tm))), ((fun uu____3887 -> (

let uu____3888 = (translate cfg bs bv.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_NBETerm.as_arg uu____3888))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____3890, uu____3891) -> begin
(translate cfg bs t)
end
| FStar_Syntax_Syntax.Tm_uvar (uvar, t) -> begin
((debug_term e);
(failwith "Tm_uvar: Not yet implemented");
)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_TypeChecker_NBETerm.mkAccuVar x)
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____3952, uu____3953) -> begin
(failwith "Impossible: abstraction with no binders")
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, resc) -> begin
(

let uu____4003 = (

let uu____4033 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____4103 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____4103), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (

let uu____4132 = (FStar_Util.map_opt resc (fun c uu____4144 -> (translate_residual_comp cfg bs c)))
in (((fun ys -> (translate cfg (FStar_List.rev_append ys bs) body))), (uu____4033), ((FStar_List.length xs)), (uu____4132))))
in FStar_TypeChecker_NBETerm.Lam (uu____4003))
end
| FStar_Syntax_Syntax.Tm_fvar (fvar1) -> begin
(translate_fv cfg bs fvar1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4177; FStar_Syntax_Syntax.vars = uu____4178}, (arg)::(more)::args) -> begin
(

let uu____4238 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4238) with
| (head1, uu____4256) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4300 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4300)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4309)); FStar_Syntax_Syntax.pos = uu____4310; FStar_Syntax_Syntax.vars = uu____4311}, (arg)::(more)::args) -> begin
(

let uu____4371 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4371) with
| (head1, uu____4389) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4433 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4433)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4442)); FStar_Syntax_Syntax.pos = uu____4443; FStar_Syntax_Syntax.vars = uu____4444}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.reifying -> begin
(

let cfg1 = (

let uu___262_4485 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___262_4485.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___262_4485.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___262_4485.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___262_4485.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___262_4485.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___262_4485.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___262_4485.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___262_4485.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4490)); FStar_Syntax_Syntax.pos = uu____4491; FStar_Syntax_Syntax.vars = uu____4492}, (arg)::[]) -> begin
(

let uu____4532 = (translate cfg bs (FStar_Pervasives_Native.fst arg))
in FStar_TypeChecker_NBETerm.Reflect (uu____4532))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4537; FStar_Syntax_Syntax.vars = uu____4538}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.reify_ -> begin
(

let cfg1 = (

let uu___263_4580 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___263_4580.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___263_4580.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___263_4580.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___263_4580.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___263_4580.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___263_4580.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___263_4580.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___263_4580.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = true})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug1 (fun uu____4618 -> (

let uu____4619 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____4620 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Application: %s @ %s\n" uu____4619 uu____4620)))));
(

let uu____4621 = (translate cfg bs head1)
in (

let uu____4622 = (FStar_List.map (fun x -> (

let uu____4644 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____4644), ((FStar_Pervasives_Native.snd x))))) args)
in (iapp cfg uu____4621 uu____4622)));
)
end
| FStar_Syntax_Syntax.Tm_match (scrut, branches) -> begin
(

let make_branches = (fun readback1 -> (

let cfg1 = (

let uu___264_4705 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___265_4708 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___265_4708.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___265_4708.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = false; FStar_TypeChecker_Cfg.weak = uu___265_4708.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___265_4708.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___265_4708.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___265_4708.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___265_4708.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___265_4708.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___265_4708.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___265_4708.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___265_4708.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___265_4708.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___265_4708.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___265_4708.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___265_4708.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___265_4708.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___265_4708.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___265_4708.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___265_4708.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___265_4708.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___265_4708.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___265_4708.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___265_4708.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___265_4708.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___265_4708.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___264_4705.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___264_4705.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___264_4705.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___264_4705.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___264_4705.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___264_4705.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___264_4705.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___264_4705.FStar_TypeChecker_Cfg.reifying})
in (

let rec process_pattern = (fun bs1 p -> (

let uu____4736 = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
((bs1), (FStar_Syntax_Syntax.Pat_constant (c)))
end
| FStar_Syntax_Syntax.Pat_cons (fvar1, args) -> begin
(

let uu____4770 = (FStar_List.fold_left (fun uu____4808 uu____4809 -> (match (((uu____4808), (uu____4809))) with
| ((bs2, args1), (arg, b)) -> begin
(

let uu____4890 = (process_pattern bs2 arg)
in (match (uu____4890) with
| (bs', arg') -> begin
((bs'), ((((arg'), (b)))::args1))
end))
end)) ((bs1), ([])) args)
in (match (uu____4770) with
| (bs', args') -> begin
((bs'), (FStar_Syntax_Syntax.Pat_cons (((fvar1), ((FStar_List.rev args'))))))
end))
end
| FStar_Syntax_Syntax.Pat_var (bvar) -> begin
(

let x = (

let uu____4979 = (

let uu____4980 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____4980))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4979))
in (

let uu____4981 = (

let uu____4984 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____4984)::bs1)
in ((uu____4981), (FStar_Syntax_Syntax.Pat_var (x)))))
end
| FStar_Syntax_Syntax.Pat_wild (bvar) -> begin
(

let x = (

let uu____4989 = (

let uu____4990 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____4990))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____4989))
in (

let uu____4991 = (

let uu____4994 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____4994)::bs1)
in ((uu____4991), (FStar_Syntax_Syntax.Pat_wild (x)))))
end
| FStar_Syntax_Syntax.Pat_dot_term (bvar, tm) -> begin
(

let x = (

let uu____5004 = (

let uu____5005 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5005))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5004))
in (

let uu____5006 = (

let uu____5007 = (

let uu____5014 = (

let uu____5017 = (translate cfg1 bs1 tm)
in (readback1 uu____5017))
in ((x), (uu____5014)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____5007))
in ((bs1), (uu____5006))))
end)
in (match (uu____4736) with
| (bs2, p_new) -> begin
((bs2), ((

let uu___266_5037 = p
in {FStar_Syntax_Syntax.v = p_new; FStar_Syntax_Syntax.p = uu___266_5037.FStar_Syntax_Syntax.p})))
end)))
in (FStar_List.map (fun uu____5056 -> (match (uu____5056) with
| (pat, when_clause, e1) -> begin
(

let uu____5078 = (process_pattern bs pat)
in (match (uu____5078) with
| (bs', pat') -> begin
(

let uu____5091 = (

let uu____5092 = (

let uu____5095 = (translate cfg1 bs' e1)
in (readback1 uu____5095))
in ((pat'), (when_clause), (uu____5092)))
in (FStar_Syntax_Util.branch uu____5091))
end))
end)) branches))))
in (

let rec case = (fun scrut1 -> ((debug1 (fun uu____5117 -> (

let uu____5118 = (

let uu____5119 = (readback cfg scrut1)
in (FStar_Syntax_Print.term_to_string uu____5119))
in (

let uu____5120 = (FStar_TypeChecker_NBETerm.t_to_string scrut1)
in (FStar_Util.print2 "Match case: (%s) -- (%s)\n" uu____5118 uu____5120)))));
(

let scrut2 = (unlazy scrut1)
in (match (scrut2) with
| FStar_TypeChecker_NBETerm.Construct (c, us, args) -> begin
((debug1 (fun uu____5146 -> (

let uu____5147 = (

let uu____5148 = (FStar_All.pipe_right args (FStar_List.map (fun uu____5171 -> (match (uu____5171) with
| (x, q) -> begin
(

let uu____5184 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (Prims.strcat (match ((FStar_Util.is_some q)) with
| true -> begin
"#"
end
| uu____5185 -> begin
""
end) uu____5184))
end))))
in (FStar_All.pipe_right uu____5148 (FStar_String.concat "; ")))
in (FStar_Util.print1 "Match args: %s\n" uu____5147))));
(

let uu____5188 = (pickBranch cfg scrut2 branches)
in (match (uu____5188) with
| FStar_Pervasives_Native.Some (branch1, args1) -> begin
(

let uu____5209 = (FStar_List.fold_left (fun bs1 x -> (x)::bs1) bs args1)
in (translate cfg uu____5209 branch1))
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
)
end
| FStar_TypeChecker_NBETerm.Constant (c) -> begin
((debug1 (fun uu____5232 -> (

let uu____5233 = (FStar_TypeChecker_NBETerm.t_to_string scrut2)
in (FStar_Util.print1 "Match constant : %s\n" uu____5233))));
(

let uu____5234 = (pickBranch cfg scrut2 branches)
in (match (uu____5234) with
| FStar_Pervasives_Native.Some (branch1, []) -> begin
(translate cfg bs branch1)
end
| FStar_Pervasives_Native.Some (branch1, (arg)::[]) -> begin
(translate cfg ((arg)::bs) branch1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end
| FStar_Pervasives_Native.Some (uu____5268, (hd1)::tl1) -> begin
(failwith "Impossible: Matching on constants cannot bind more than one variable")
end));
)
end
| uu____5281 -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
))
in (

let uu____5282 = (translate cfg bs scrut)
in (case uu____5282))))
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (m, t)) when cfg.FStar_TypeChecker_Cfg.reifying -> begin
(translate_monadic ((m), (t)) cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t)) when cfg.FStar_TypeChecker_Cfg.reifying -> begin
(translate_monadic_lift ((m), (m'), (t)) cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_let ((false, lbs), body) -> begin
(

let bs' = (FStar_List.fold_left (fun bs' lb -> (

let b = (translate_letbinding cfg bs lb)
in (b)::bs')) bs lbs)
in (translate cfg bs' body))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) -> begin
(

let uu____5355 = (make_rec_env (translate_letbinding cfg) lbs bs)
in (translate cfg uu____5355 body))
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____5359) -> begin
(translate cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let close1 = (fun t -> (

let bvs = (FStar_List.map (fun uu____5380 -> (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)) bs)
in (

let s1 = (FStar_List.mapi (fun i bv -> FStar_Syntax_Syntax.DB (((i), (bv)))) bvs)
in (

let s2 = (

let uu____5391 = (FStar_List.zip bvs bs)
in (FStar_List.map (fun uu____5406 -> (match (uu____5406) with
| (bv, t1) -> begin
(

let uu____5413 = (

let uu____5420 = (readback cfg t1)
in ((bv), (uu____5420)))
in FStar_Syntax_Syntax.NT (uu____5413))
end)) uu____5391))
in (

let uu____5425 = (FStar_Syntax_Subst.subst s1 t)
in (FStar_Syntax_Subst.subst s2 uu____5425))))))
in (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let qt1 = (close1 qt)
in FStar_TypeChecker_NBETerm.Quote (((qt1), (qi))))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted close1 qi)
in FStar_TypeChecker_NBETerm.Quote (((qt), (qi1))))
end))
end
| FStar_Syntax_Syntax.Tm_lazy (li) -> begin
(

let f = (fun uu____5434 -> (

let t = (FStar_Syntax_Util.unfold_lazy li)
in ((debug1 (fun uu____5441 -> (

let uu____5442 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n" uu____5442))));
(translate cfg bs t);
)))
in (

let uu____5443 = (

let uu____5458 = (FStar_Common.mk_thunk f)
in ((FStar_Util.Inl (li)), (uu____5458)))
in FStar_TypeChecker_NBETerm.Lazy (uu____5443)))
end));
)))
and translate_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_NBETerm.comp = (fun cfg bs c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (typ, u) -> begin
(

let uu____5530 = (

let uu____5537 = (translate cfg bs typ)
in (

let uu____5538 = (fmap_opt (translate_univ bs) u)
in ((uu____5537), (uu____5538))))
in FStar_TypeChecker_NBETerm.Tot (uu____5530))
end
| FStar_Syntax_Syntax.GTotal (typ, u) -> begin
(

let uu____5553 = (

let uu____5560 = (translate cfg bs typ)
in (

let uu____5561 = (fmap_opt (translate_univ bs) u)
in ((uu____5560), (uu____5561))))
in FStar_TypeChecker_NBETerm.GTot (uu____5553))
end
| FStar_Syntax_Syntax.Comp (ctyp) -> begin
(

let uu____5567 = (translate_comp_typ cfg bs ctyp)
in FStar_TypeChecker_NBETerm.Comp (uu____5567))
end))
and readback_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg c -> (

let c' = (match (c) with
| FStar_TypeChecker_NBETerm.Tot (typ, u) -> begin
(

let uu____5577 = (

let uu____5586 = (readback cfg typ)
in ((uu____5586), (u)))
in FStar_Syntax_Syntax.Total (uu____5577))
end
| FStar_TypeChecker_NBETerm.GTot (typ, u) -> begin
(

let uu____5599 = (

let uu____5608 = (readback cfg typ)
in ((uu____5608), (u)))
in FStar_Syntax_Syntax.GTotal (uu____5599))
end
| FStar_TypeChecker_NBETerm.Comp (ctyp) -> begin
(

let uu____5616 = (readback_comp_typ cfg ctyp)
in FStar_Syntax_Syntax.Comp (uu____5616))
end)
in (FStar_Syntax_Syntax.mk c' FStar_Pervasives_Native.None FStar_Range.dummyRange)))
and translate_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_TypeChecker_NBETerm.comp_typ = (fun cfg bs c -> (

let uu____5622 = c
in (match (uu____5622) with
| {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags1} -> begin
(

let uu____5642 = (FStar_List.map (translate_univ bs) comp_univs)
in (

let uu____5643 = (translate cfg bs result_typ)
in (

let uu____5644 = (FStar_List.map (fun x -> (

let uu____5672 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____5672), ((FStar_Pervasives_Native.snd x))))) effect_args)
in (

let uu____5679 = (FStar_List.map (translate_flag cfg bs) flags1)
in {FStar_TypeChecker_NBETerm.comp_univs = uu____5642; FStar_TypeChecker_NBETerm.effect_name = effect_name; FStar_TypeChecker_NBETerm.result_typ = uu____5643; FStar_TypeChecker_NBETerm.effect_args = uu____5644; FStar_TypeChecker_NBETerm.flags = uu____5679}))))
end)))
and readback_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun cfg c -> (

let uu____5684 = (readback cfg c.FStar_TypeChecker_NBETerm.result_typ)
in (

let uu____5687 = (FStar_List.map (fun x -> (

let uu____5713 = (readback cfg (FStar_Pervasives_Native.fst x))
in ((uu____5713), ((FStar_Pervasives_Native.snd x))))) c.FStar_TypeChecker_NBETerm.effect_args)
in (

let uu____5714 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags)
in {FStar_Syntax_Syntax.comp_univs = c.FStar_TypeChecker_NBETerm.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_TypeChecker_NBETerm.effect_name; FStar_Syntax_Syntax.result_typ = uu____5684; FStar_Syntax_Syntax.effect_args = uu____5687; FStar_Syntax_Syntax.flags = uu____5714}))))
and translate_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.residual_comp  ->  FStar_TypeChecker_NBETerm.residual_comp = (fun cfg bs c -> (

let uu____5722 = c
in (match (uu____5722) with
| {FStar_Syntax_Syntax.residual_effect = residual_effect; FStar_Syntax_Syntax.residual_typ = residual_typ; FStar_Syntax_Syntax.residual_flags = residual_flags} -> begin
(

let uu____5732 = (FStar_Util.map_opt residual_typ (translate cfg bs))
in (

let uu____5737 = (FStar_List.map (translate_flag cfg bs) residual_flags)
in {FStar_TypeChecker_NBETerm.residual_effect = residual_effect; FStar_TypeChecker_NBETerm.residual_typ = uu____5732; FStar_TypeChecker_NBETerm.residual_flags = uu____5737}))
end)))
and readback_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.residual_comp  ->  FStar_Syntax_Syntax.residual_comp = (fun cfg c -> (

let uu____5742 = (FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ (readback cfg))
in (

let uu____5749 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = c.FStar_TypeChecker_NBETerm.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____5742; FStar_Syntax_Syntax.residual_flags = uu____5749})))
and translate_flag : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.cflag  ->  FStar_TypeChecker_NBETerm.cflag = (fun cfg bs f -> (match (f) with
| FStar_Syntax_Syntax.TOTAL -> begin
FStar_TypeChecker_NBETerm.TOTAL
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
FStar_TypeChecker_NBETerm.MLEFFECT
end
| FStar_Syntax_Syntax.RETURN -> begin
FStar_TypeChecker_NBETerm.RETURN
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
FStar_TypeChecker_NBETerm.PARTIAL_RETURN
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
FStar_TypeChecker_NBETerm.SOMETRIVIAL
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION
end
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE
end
| FStar_Syntax_Syntax.LEMMA -> begin
FStar_TypeChecker_NBETerm.LEMMA
end
| FStar_Syntax_Syntax.CPS -> begin
FStar_TypeChecker_NBETerm.CPS
end
| FStar_Syntax_Syntax.DECREASES (tm) -> begin
(

let uu____5760 = (translate cfg bs tm)
in FStar_TypeChecker_NBETerm.DECREASES (uu____5760))
end))
and readback_flag : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.cflag  ->  FStar_Syntax_Syntax.cflag = (fun cfg f -> (match (f) with
| FStar_TypeChecker_NBETerm.TOTAL -> begin
FStar_Syntax_Syntax.TOTAL
end
| FStar_TypeChecker_NBETerm.MLEFFECT -> begin
FStar_Syntax_Syntax.MLEFFECT
end
| FStar_TypeChecker_NBETerm.RETURN -> begin
FStar_Syntax_Syntax.RETURN
end
| FStar_TypeChecker_NBETerm.PARTIAL_RETURN -> begin
FStar_Syntax_Syntax.PARTIAL_RETURN
end
| FStar_TypeChecker_NBETerm.SOMETRIVIAL -> begin
FStar_Syntax_Syntax.SOMETRIVIAL
end
| FStar_TypeChecker_NBETerm.TRIVIAL_POSTCONDITION -> begin
FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION
end
| FStar_TypeChecker_NBETerm.SHOULD_NOT_INLINE -> begin
FStar_Syntax_Syntax.SHOULD_NOT_INLINE
end
| FStar_TypeChecker_NBETerm.LEMMA -> begin
FStar_Syntax_Syntax.LEMMA
end
| FStar_TypeChecker_NBETerm.CPS -> begin
FStar_Syntax_Syntax.CPS
end
| FStar_TypeChecker_NBETerm.DECREASES (t) -> begin
(

let uu____5764 = (readback cfg t)
in FStar_Syntax_Syntax.DECREASES (uu____5764))
end))
and translate_monadic : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____5767 cfg bs e -> (match (uu____5767) with
| (m, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let uu____5802 = (

let uu____5811 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv m)
in (FStar_TypeChecker_Env.effect_decl_opt cfg.FStar_TypeChecker_Cfg.tcenv uu____5811))
in (match (uu____5802) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5818 = (

let uu____5819 = (FStar_Ident.string_of_lid m)
in (FStar_Util.format1 "Effect declaration not found: %s" uu____5819))
in (failwith uu____5818))
end
| FStar_Pervasives_Native.Some (ed, q) -> begin
(

let cfg' = (

let uu___267_5833 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___267_5833.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___267_5833.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___267_5833.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___267_5833.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___267_5833.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___267_5833.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___267_5833.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___267_5833.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let body_lam = (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (ty); FStar_Syntax_Syntax.residual_flags = []}
in (

let uu____5840 = (

let uu____5847 = (

let uu____5848 = (

let uu____5867 = (

let uu____5876 = (

let uu____5883 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____5883), (FStar_Pervasives_Native.None)))
in (uu____5876)::[])
in ((uu____5867), (body), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____5848))
in (FStar_Syntax_Syntax.mk uu____5847))
in (uu____5840 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos)))
in (

let maybe_range_arg = (

let uu____5920 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____5920) with
| true -> begin
(

let uu____5927 = (

let uu____5932 = (

let uu____5933 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (translate cfg [] uu____5933))
in ((uu____5932), (FStar_Pervasives_Native.None)))
in (

let uu____5934 = (

let uu____5941 = (

let uu____5946 = (

let uu____5947 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range body.FStar_Syntax_Syntax.pos body.FStar_Syntax_Syntax.pos)
in (translate cfg [] uu____5947))
in ((uu____5946), (FStar_Pervasives_Native.None)))
in (uu____5941)::[])
in (uu____5927)::uu____5934))
end
| uu____5960 -> begin
[]
end))
in (

let t = (

let uu____5966 = (

let uu____5967 = (

let uu____5968 = (FStar_Syntax_Util.un_uinst (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (translate cfg' [] uu____5968))
in (iapp cfg uu____5967 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::(((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____5985 = (

let uu____5986 = (

let uu____5993 = (

let uu____5998 = (translate cfg' bs lb.FStar_Syntax_Syntax.lbtyp)
in ((uu____5998), (FStar_Pervasives_Native.None)))
in (

let uu____5999 = (

let uu____6006 = (

let uu____6011 = (translate cfg' bs ty)
in ((uu____6011), (FStar_Pervasives_Native.None)))
in (uu____6006)::[])
in (uu____5993)::uu____5999))
in (

let uu____6024 = (

let uu____6031 = (

let uu____6038 = (

let uu____6045 = (

let uu____6050 = (translate cfg bs lb.FStar_Syntax_Syntax.lbdef)
in ((uu____6050), (FStar_Pervasives_Native.None)))
in (

let uu____6051 = (

let uu____6058 = (

let uu____6065 = (

let uu____6070 = (translate cfg bs body_lam)
in ((uu____6070), (FStar_Pervasives_Native.None)))
in (uu____6065)::[])
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6058)
in (uu____6045)::uu____6051))
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6038)
in (FStar_List.append maybe_range_arg uu____6031))
in (FStar_List.append uu____5986 uu____6024)))
in (iapp cfg uu____5966 uu____5985)))
in ((debug cfg (fun uu____6102 -> (

let uu____6103 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic: %s\n" uu____6103))));
t;
)))))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6104)); FStar_Syntax_Syntax.pos = uu____6105; FStar_Syntax_Syntax.vars = uu____6106}, ((e2, uu____6108))::[]) -> begin
(translate (

let uu___268_6149 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___268_6149.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___268_6149.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___268_6149.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___268_6149.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___268_6149.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___268_6149.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___268_6149.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___268_6149.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug cfg (fun uu____6180 -> (

let uu____6181 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____6182 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "translate_monadic app (%s) @ (%s)\n" uu____6181 uu____6182)))));
(

let fallback1 = (fun uu____6188 -> (translate cfg bs e1))
in (

let fallback2 = (fun uu____6194 -> (

let uu____6195 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_monadic (((m), (ty))))))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___269_6202 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___269_6202.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___269_6202.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___269_6202.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___269_6202.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___269_6202.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___269_6202.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___269_6202.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___269_6202.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs uu____6195)))
in (

let uu____6203 = (

let uu____6204 = (FStar_Syntax_Util.un_uinst head1)
in uu____6204.FStar_Syntax_Syntax.n)
in (match (uu____6203) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____6210 = (

let uu____6211 = (FStar_TypeChecker_Env.is_action cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (not (uu____6211)))
in (match (uu____6210) with
| true -> begin
(fallback1 ())
end
| uu____6212 -> begin
(

let uu____6213 = (

let uu____6214 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (FStar_Option.isNone uu____6214))
in (match (uu____6213) with
| true -> begin
(fallback2 ())
end
| uu____6225 -> begin
(

let e2 = (

let uu____6229 = (

let uu____6234 = (FStar_Syntax_Util.mk_reify head1)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6234 args))
in (uu____6229 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (translate (

let uu___270_6239 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___270_6239.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___270_6239.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___270_6239.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___270_6239.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___270_6239.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___270_6239.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___270_6239.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___270_6239.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2))
end))
end))))
end
| uu____6240 -> begin
(fallback1 ())
end))));
)
end
| FStar_Syntax_Syntax.Tm_match (sc, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____6361 -> (match (uu____6361) with
| (pat, wopt, tm) -> begin
(

let uu____6409 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____6409)))
end))))
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), (branches1)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___271_6443 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___271_6443.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___271_6443.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___271_6443.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___271_6443.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___271_6443.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___271_6443.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___271_6443.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___271_6443.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs tm)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____6445)) -> begin
(translate_monadic ((m), (ty)) cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty')) -> begin
(translate_monadic_lift ((msrc), (mtgt), (ty')) cfg bs e1)
end
| uu____6472 -> begin
(

let uu____6473 = (

let uu____6474 = (FStar_Syntax_Print.tag_of_term e1)
in (FStar_Util.format1 "Unexpected case in translate_monadic: %s" uu____6474))
in (failwith uu____6473))
end))
end))
and translate_monadic_lift : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____6475 cfg bs e -> (match (uu____6475) with
| (msrc, mtgt, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (

let uu____6499 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____6499) with
| true -> begin
(

let ed = (

let uu____6501 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl cfg.FStar_TypeChecker_Cfg.tcenv uu____6501))
in (

let ret1 = (

let uu____6503 = (

let uu____6504 = (FStar_Syntax_Subst.compress (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in uu____6504.FStar_Syntax_Syntax.n)
in (match (uu____6503) with
| FStar_Syntax_Syntax.Tm_uinst (ret1, (uu____6512)::[]) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((ret1), ((FStar_Syntax_Syntax.U_unknown)::[])))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
end
| uu____6519 -> begin
(failwith "NYI: Reification of indexed effect (NBE)")
end))
in (

let cfg' = (

let uu___272_6521 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___272_6521.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___272_6521.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___272_6521.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___272_6521.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___272_6521.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___272_6521.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___272_6521.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___272_6521.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____6523 = (

let uu____6524 = (translate cfg' [] ret1)
in (iapp cfg' uu____6524 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____6533 = (

let uu____6534 = (

let uu____6539 = (translate cfg' bs ty)
in ((uu____6539), (FStar_Pervasives_Native.None)))
in (

let uu____6540 = (

let uu____6547 = (

let uu____6552 = (translate cfg' bs e1)
in ((uu____6552), (FStar_Pervasives_Native.None)))
in (uu____6547)::[])
in (uu____6534)::uu____6540))
in (iapp cfg' uu____6523 uu____6533)))
in ((debug cfg (fun uu____6568 -> (

let uu____6569 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(1): %s\n" uu____6569))));
t;
)))))
end
| uu____6570 -> begin
(

let uu____6571 = (FStar_TypeChecker_Env.monad_leq cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt)
in (match (uu____6571) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6574 = (

let uu____6575 = (FStar_Ident.text_of_lid msrc)
in (

let uu____6576 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____6575 uu____6576)))
in (failwith uu____6574))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____6577; FStar_TypeChecker_Env.mtarget = uu____6578; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____6579; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____6601 = (

let uu____6602 = (FStar_Ident.text_of_lid msrc)
in (

let uu____6603 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____6602 uu____6603)))
in (failwith uu____6601))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____6604; FStar_TypeChecker_Env.mtarget = uu____6605; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____6606; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let lift_lam = (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let uu____6645 = (

let uu____6648 = (FStar_Syntax_Syntax.bv_to_name x)
in (lift FStar_Syntax_Syntax.U_unknown ty FStar_Syntax_Syntax.tun uu____6648))
in (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) uu____6645 FStar_Pervasives_Native.None)))
in (

let cfg' = (

let uu___273_6664 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___273_6664.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___273_6664.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___273_6664.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___273_6664.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___273_6664.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___273_6664.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___273_6664.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___273_6664.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____6666 = (translate cfg' [] lift_lam)
in (

let uu____6667 = (

let uu____6668 = (

let uu____6673 = (translate cfg bs e1)
in ((uu____6673), (FStar_Pervasives_Native.None)))
in (uu____6668)::[])
in (iapp cfg uu____6666 uu____6667)))
in ((debug cfg (fun uu____6685 -> (

let uu____6686 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(2): %s\n" uu____6686))));
t;
))))
end))
end)))
end))
and readback : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.term = (fun cfg x -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____6702 -> (

let uu____6703 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print1 "Readback: %s\n" uu____6703))));
(match (x) with
| FStar_TypeChecker_NBETerm.Univ (u) -> begin
(failwith "Readback of universes should not occur")
end
| FStar_TypeChecker_NBETerm.Unknown -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit) -> begin
FStar_Syntax_Syntax.unit_const
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool (true)) -> begin
FStar_Syntax_Util.exp_true_bool
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool (false)) -> begin
FStar_Syntax_Util.exp_false_bool
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i)) -> begin
(

let uu____6706 = (FStar_BigInt.string_of_big_int i)
in (FStar_All.pipe_right uu____6706 FStar_Syntax_Util.exp_int))
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String (s, r)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((s), (r))))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char (c)) -> begin
(FStar_Syntax_Util.exp_char c)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Range (r)) -> begin
(FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range r FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Type_t (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lam (f, targs, arity, resc) -> begin
(

let uu____6759 = (FStar_List.fold_left (fun uu____6802 tf -> (match (uu____6802) with
| (args_rev, accus_rev) -> begin
(

let uu____6854 = (tf accus_rev)
in (match (uu____6854) with
| (xt, q) -> begin
(

let x1 = (

let uu____6874 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____6874))
in (

let uu____6875 = (

let uu____6878 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____6878)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____6875))))
end))
end)) (([]), ([])) targs)
in (match (uu____6759) with
| (args_rev, accus_rev) -> begin
(

let body = (

let uu____6922 = (f (FStar_List.rev accus_rev))
in (readback cfg uu____6922))
in (

let uu____6923 = (FStar_Util.map_opt resc (fun thunk -> (

let uu____6934 = (thunk ())
in (readback_residual_comp cfg uu____6934))))
in (FStar_Syntax_Util.abs (FStar_List.rev args_rev) body uu____6923)))
end))
end
| FStar_TypeChecker_NBETerm.Refinement (f, targ) -> begin
(

let x1 = (

let uu____6962 = (

let uu____6963 = (

let uu____6964 = (targ ())
in (FStar_Pervasives_Native.fst uu____6964))
in (readback cfg uu____6963))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____6962))
in (

let body = (

let uu____6970 = (

let uu____6971 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (f uu____6971))
in (readback cfg uu____6970))
in (FStar_Syntax_Util.refine x1 body)))
end
| FStar_TypeChecker_NBETerm.Reflect (t) -> begin
(

let tm = (readback cfg t)
in (FStar_Syntax_Util.mk_reflect tm))
end
| FStar_TypeChecker_NBETerm.Arrow (f, targs) -> begin
(

let uu____7008 = (FStar_List.fold_left (fun uu____7051 tf -> (match (uu____7051) with
| (args_rev, accus_rev) -> begin
(

let uu____7103 = (tf accus_rev)
in (match (uu____7103) with
| (xt, q) -> begin
(

let x1 = (

let uu____7123 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7123))
in (

let uu____7124 = (

let uu____7127 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____7127)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____7124))))
end))
end)) (([]), ([])) targs)
in (match (uu____7008) with
| (args_rev, accus_rev) -> begin
(

let cmp = (

let uu____7171 = (f (FStar_List.rev accus_rev))
in (readback_comp cfg uu____7171))
in (FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp))
end))
end
| FStar_TypeChecker_NBETerm.Construct (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7214 -> (match (uu____7214) with
| (x1, q) -> begin
(

let uu____7225 = (readback cfg x1)
in ((uu____7225), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7244 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7251)::uu____7252 -> begin
(

let uu____7255 = (

let uu____7258 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7258 (FStar_List.rev us)))
in (apply1 uu____7255))
end
| [] -> begin
(

let uu____7259 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7259))
end)))
end
| FStar_TypeChecker_NBETerm.FV (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7300 -> (match (uu____7300) with
| (x1, q) -> begin
(

let uu____7311 = (readback cfg x1)
in ((uu____7311), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7330 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7337)::uu____7338 -> begin
(

let uu____7341 = (

let uu____7344 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7344 (FStar_List.rev us)))
in (apply1 uu____7341))
end
| [] -> begin
(

let uu____7345 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7345))
end)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), []) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), ts) -> begin
(

let args = (map_rev (fun uu____7392 -> (match (uu____7392) with
| (x1, q) -> begin
(

let uu____7403 = (readback cfg x1)
in ((uu____7403), (q)))
end)) ts)
in (

let uu____7404 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Util.mk_app uu____7404 args)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Match (scrut, cases, make_branches), ts) -> begin
(

let args = (map_rev (fun uu____7464 -> (match (uu____7464) with
| (x1, q) -> begin
(

let uu____7475 = (readback cfg x1)
in ((uu____7475), (q)))
end)) ts)
in (

let head1 = (

let scrut_new = (readback cfg scrut)
in (

let branches_new = (make_branches (readback cfg))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrut_new), (branches_new)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (match (ts) with
| [] -> begin
head1
end
| uu____7505 -> begin
(FStar_Syntax_Util.mk_app head1 args)
end)))
end
| FStar_TypeChecker_NBETerm.Rec (lb, lbs, bs, args, _ar, _ar_lst, _cfg) -> begin
(

let head1 = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (bv) -> begin
(failwith "Reading back of local recursive definitions is not supported yet.")
end
| FStar_Util.Inr (fv) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end)
in (

let args1 = (map_rev (fun uu____7587 -> (match (uu____7587) with
| (x1, q) -> begin
(

let uu____7598 = (readback cfg x1)
in ((uu____7598), (q)))
end)) args)
in (match (args1) with
| [] -> begin
head1
end
| uu____7603 -> begin
(FStar_Syntax_Util.mk_app head1 args1)
end)))
end
| FStar_TypeChecker_NBETerm.Quote (qt, qi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl (li), uu____7615) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (li)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (uu____7632, thunk) -> begin
(

let uu____7654 = (FStar_Common.force_thunk thunk)
in (readback cfg uu____7654))
end);
)))

type step =
| Primops
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| UnfoldOnly of FStar_Ident.lid Prims.list
| UnfoldAttr of FStar_Ident.lid Prims.list
| UnfoldTac
| Reify


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____7719 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____7726 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_UnfoldOnly : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____7742 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldAttr : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
true
end
| uu____7764 -> begin
false
end))


let __proj__UnfoldAttr__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
_0
end))


let uu___is_UnfoldTac : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____7783 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____7789 -> begin
false
end))


let step_as_normalizer_step : step  ->  FStar_TypeChecker_Env.step = (fun uu___261_7794 -> (match (uu___261_7794) with
| Primops -> begin
FStar_TypeChecker_Env.Primops
end
| UnfoldUntil (d) -> begin
FStar_TypeChecker_Env.UnfoldUntil (d)
end
| UnfoldOnly (lids) -> begin
FStar_TypeChecker_Env.UnfoldOnly (lids)
end
| UnfoldAttr (lids) -> begin
FStar_TypeChecker_Env.UnfoldAttr (lids)
end
| UnfoldTac -> begin
FStar_TypeChecker_Env.UnfoldTac
end
| Reify -> begin
FStar_TypeChecker_Env.Reify
end))


let normalize : FStar_TypeChecker_Cfg.primitive_step Prims.list  ->  FStar_TypeChecker_Env.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun psteps steps env e -> (

let cfg = (FStar_TypeChecker_Cfg.config' psteps steps env)
in (

let cfg1 = (

let uu___274_7832 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___275_7835 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___275_7835.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___275_7835.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___275_7835.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___275_7835.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___275_7835.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___275_7835.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___275_7835.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___275_7835.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___275_7835.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___275_7835.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___275_7835.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___275_7835.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___275_7835.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___275_7835.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___275_7835.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___275_7835.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___275_7835.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___275_7835.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___275_7835.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___275_7835.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___275_7835.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___275_7835.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___275_7835.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___275_7835.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___275_7835.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___274_7832.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___274_7832.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___274_7832.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___274_7832.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___274_7832.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___274_7832.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___274_7832.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___274_7832.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____7839 -> (

let uu____7840 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____7840))));
(

let r = (

let uu____7842 = (translate cfg1 [] e)
in (readback cfg1 uu____7842))
in ((debug cfg1 (fun uu____7846 -> (

let uu____7847 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____7847))));
r;
));
))))


let normalize_for_unit_test : FStar_TypeChecker_Env.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun steps env e -> (

let cfg = (FStar_TypeChecker_Cfg.config steps env)
in (

let cfg1 = (

let uu___276_7869 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___277_7872 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___277_7872.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___277_7872.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___277_7872.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___277_7872.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___277_7872.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___277_7872.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___277_7872.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___277_7872.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___277_7872.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___277_7872.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___277_7872.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___277_7872.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___277_7872.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___277_7872.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___277_7872.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___277_7872.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___277_7872.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___277_7872.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___277_7872.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___277_7872.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___277_7872.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___277_7872.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___277_7872.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___277_7872.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___277_7872.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___276_7869.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___276_7869.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___276_7869.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___276_7869.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___276_7869.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___276_7869.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___276_7869.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___276_7869.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____7876 -> (

let uu____7877 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____7877))));
(

let r = (

let uu____7879 = (translate cfg1 [] e)
in (readback cfg1 uu____7879))
in ((debug cfg1 (fun uu____7883 -> (

let uu____7884 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____7884))));
r;
));
))))




