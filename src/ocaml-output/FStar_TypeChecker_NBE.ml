
open Prims
open FStar_Pervasives

let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun a b -> (match ((a > b)) with
| true -> begin
a
end
| uu____17 -> begin
b
end))


let map_rev : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list = (fun f l -> (

let rec aux = (fun l1 acc -> (match (l1) with
| [] -> begin
acc
end
| (x)::xs -> begin
(

let uu____78 = (

let uu____81 = (f x)
in (uu____81)::acc)
in (aux xs uu____78))
end))
in (aux l [])))


let map_rev_append : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list  ->  'b Prims.list = (fun f l1 l2 -> (

let rec aux = (fun l acc -> (match (l) with
| [] -> begin
l2
end
| (x)::xs -> begin
(

let uu____152 = (

let uu____155 = (f x)
in (uu____155)::acc)
in (aux xs uu____152))
end))
in (aux l1 l2)))


let rec map_append : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list  ->  'b Prims.list = (fun f l1 l2 -> (match (l1) with
| [] -> begin
l2
end
| (x)::xs -> begin
(

let uu____205 = (f x)
in (

let uu____206 = (map_append f xs l2)
in (uu____205)::uu____206))
end))


let rec drop : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list = (fun p l -> (match (l) with
| [] -> begin
[]
end
| (x)::xs -> begin
(

let uu____245 = (p x)
in (match (uu____245) with
| true -> begin
(x)::xs
end
| uu____250 -> begin
(drop p xs)
end))
end))


let fmap_opt : 'a 'b . ('a  ->  'b)  ->  'a FStar_Pervasives_Native.option  ->  'b FStar_Pervasives_Native.option = (fun f x -> (FStar_Util.bind_opt x (fun x1 -> (

let uu____287 = (f x1)
in FStar_Pervasives_Native.Some (uu____287)))))


let drop_until : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list = (fun f l -> (

let rec aux = (fun l1 -> (match (l1) with
| [] -> begin
[]
end
| (x)::xs -> begin
(

let uu____337 = (f x)
in (match (uu____337) with
| true -> begin
l1
end
| uu____342 -> begin
(aux xs)
end))
end))
in (aux l)))


let trim : Prims.bool Prims.list  ->  Prims.bool Prims.list = (fun l -> (

let uu____362 = (drop_until FStar_Pervasives.id (FStar_List.rev l))
in (FStar_List.rev uu____362)))


let implies : Prims.bool  ->  Prims.bool  ->  Prims.bool = (fun b1 b2 -> (match (((b1), (b2))) with
| (false, uu____389) -> begin
true
end
| (true, b21) -> begin
b21
end))


let debug : FStar_TypeChecker_Cfg.cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (

let uu____416 = (

let uu____418 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in (FStar_TypeChecker_Env.debug uu____418 (FStar_Options.Other ("NBE"))))
in (match (uu____416) with
| true -> begin
(f ())
end
| uu____421 -> begin
()
end)))


let debug_term : FStar_Syntax_Syntax.term  ->  unit = (fun t -> (

let uu____429 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "%s\n" uu____429)))


let debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap  ->  unit = (fun m -> (FStar_Util.smap_fold m (fun k v1 u -> (

let uu____450 = (FStar_Syntax_Print.sigelt_to_string_short v1)
in (FStar_Util.print2 "%s -> %%s\n" k uu____450))) ()))


let unlazy : FStar_TypeChecker_NBETerm.t  ->  FStar_TypeChecker_NBETerm.t = (fun t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (uu____459, t1) -> begin
(FStar_Common.force_thunk t1)
end
| t1 -> begin
t1
end))


let pickBranch : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_NBETerm.t Prims.list) FStar_Pervasives_Native.option = (fun cfg scrut branches -> (

let rec pickBranch_aux = (fun scrut1 branches1 branches0 -> (

let rec matches_pat = (fun scrutinee0 p -> ((debug cfg (fun uu____587 -> (

let uu____588 = (FStar_TypeChecker_NBETerm.t_to_string scrutinee0)
in (

let uu____590 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "matches_pat (%s, %s)\n" uu____588 uu____590)))));
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____617) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let matches_const = (fun c s1 -> ((debug cfg (fun uu____644 -> (

let uu____645 = (FStar_TypeChecker_NBETerm.t_to_string c)
in (

let uu____647 = (FStar_Syntax_Print.const_to_string s1)
in (FStar_Util.print2 "Testing term %s against pattern %s\n" uu____645 uu____647)))));
(match (c) with
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit) -> begin
(Prims.op_Equality s1 FStar_Const.Const_unit)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool (b)) -> begin
(match (s1) with
| FStar_Const.Const_bool (p1) -> begin
(Prims.op_Equality b p1)
end
| uu____657 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i)) -> begin
(match (s1) with
| FStar_Const.Const_int (p1, FStar_Pervasives_Native.None) -> begin
(

let uu____674 = (FStar_BigInt.big_int_of_string p1)
in (Prims.op_Equality i uu____674))
end
| uu____675 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String (st, uu____678)) -> begin
(match (s1) with
| FStar_Const.Const_string (p1, uu____683) -> begin
(Prims.op_Equality st p1)
end
| uu____687 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char (c1)) -> begin
(match (s1) with
| FStar_Const.Const_char (p1) -> begin
(Prims.op_Equality c1 p1)
end
| uu____695 -> begin
false
end)
end
| uu____697 -> begin
false
end);
))
in (

let uu____699 = (matches_const scrutinee s)
in (match (uu____699) with
| true -> begin
FStar_Util.Inl ([])
end
| uu____712 -> begin
FStar_Util.Inr (false)
end)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let rec matches_args = (fun out a p1 -> (match (((a), (p1))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, uu____837))::rest_a, ((p2, uu____840))::rest_p) -> begin
(

let uu____879 = (matches_pat t p2)
in (match (uu____879) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____908 -> begin
FStar_Util.Inr (false)
end))
in (match (scrutinee) with
| FStar_TypeChecker_NBETerm.Construct (fv', _us, args_rev) -> begin
(

let uu____956 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (match (uu____956) with
| true -> begin
(matches_args [] (FStar_List.rev args_rev) arg_pats)
end
| uu____970 -> begin
FStar_Util.Inr (false)
end))
end
| uu____976 -> begin
FStar_Util.Inr (true)
end))
end)
in (

let res_to_string = (fun uu___0_994 -> (match (uu___0_994) with
| FStar_Util.Inr (b) -> begin
(

let uu____1008 = (FStar_Util.string_of_bool b)
in (Prims.op_Hat "Inr " uu____1008))
end
| FStar_Util.Inl (bs) -> begin
(

let uu____1017 = (FStar_Util.string_of_int (FStar_List.length bs))
in (Prims.op_Hat "Inl " uu____1017))
end))
in ((debug cfg (fun uu____1025 -> (

let uu____1026 = (FStar_TypeChecker_NBETerm.t_to_string scrutinee)
in (

let uu____1028 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____1030 = (res_to_string r)
in (FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1026 uu____1028 uu____1030))))));
r;
))));
))
in (match (branches1) with
| [] -> begin
(failwith "Branch not found")
end
| ((p, _wopt, e))::branches2 -> begin
(

let uu____1072 = (matches_pat scrut1 p)
in (match (uu____1072) with
| FStar_Util.Inl (matches) -> begin
((debug cfg (fun uu____1097 -> (

let uu____1098 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print1 "Pattern %s matches\n" uu____1098))));
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
| (uu____1266, []) -> begin
((true), ((FStar_List.rev acc)), (ts1))
end
| ([], (uu____1301)::uu____1302) -> begin
((false), ((FStar_List.rev acc)), ([]))
end
| ((t)::ts2, (b)::bs) -> begin
(

let uu____1375 = (res && (

let uu____1378 = (

let uu____1380 = (FStar_TypeChecker_NBETerm.isAccu (FStar_Pervasives_Native.fst t))
in (not (uu____1380)))
in (implies b uu____1378)))
in (aux ts2 bs ((t)::acc) uu____1375))
end))
in (aux ts ar_list [] true)))


let find_sigelt_in_gamma : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun cfg env lid -> (

let mapper = (fun uu____1436 -> (match (uu____1436) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inr (elt, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some (elt)
end
| FStar_Util.Inr (elt, FStar_Pervasives_Native.Some (us)) -> begin
((debug cfg (fun uu____1519 -> (

let uu____1520 = (FStar_Syntax_Print.univs_to_string us)
in (FStar_Util.print1 "Universes in local declaration: %s\n" uu____1520))));
FStar_Pervasives_Native.Some (elt);
)
end
| uu____1523 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____1538 = (FStar_TypeChecker_Env.lookup_qname env lid)
in (FStar_Util.bind_opt uu____1538 mapper))))


let is_univ : FStar_TypeChecker_NBETerm.t  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_TypeChecker_NBETerm.Univ (uu____1585) -> begin
true
end
| uu____1587 -> begin
false
end))


let un_univ : FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.universe = (fun tm -> (match (tm) with
| FStar_TypeChecker_NBETerm.Univ (u) -> begin
u
end
| t -> begin
(

let uu____1597 = (

let uu____1599 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (Prims.op_Hat "Not a universe: " uu____1599))
in (failwith uu____1597))
end))


let is_constr_fv : FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun fvar1 -> (Prims.op_Equality fvar1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))


let is_constr : FStar_TypeChecker_Env.qninfo  ->  Prims.bool = (fun q -> (match (q) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____1621, uu____1622, uu____1623, uu____1624, uu____1625, uu____1626); FStar_Syntax_Syntax.sigrng = uu____1627; FStar_Syntax_Syntax.sigquals = uu____1628; FStar_Syntax_Syntax.sigmeta = uu____1629; FStar_Syntax_Syntax.sigattrs = uu____1630}, uu____1631), uu____1632) -> begin
true
end
| uu____1690 -> begin
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
| uu____1718 -> begin
(failwith "Universe index out of bounds")
end)
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1722 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1722))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1726 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1726))
end
| FStar_Syntax_Syntax.U_unknown -> begin
u2
end
| FStar_Syntax_Syntax.U_name (uu____1729) -> begin
u2
end
| FStar_Syntax_Syntax.U_unif (uu____1730) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end)))
in (aux u)))


let find_let : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option = (fun lbs fvar1 -> (FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1761) -> begin
(failwith "find_let : impossible")
end
| FStar_Util.Inr (name) -> begin
(

let uu____1766 = (FStar_Syntax_Syntax.fv_eq name fvar1)
in (match (uu____1766) with
| true -> begin
FStar_Pervasives_Native.Some (lb)
end
| uu____1771 -> begin
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

let uu____2113 = (FStar_List.splitAt m targs)
in (match (uu____2113) with
| (uu____2149, targs') -> begin
(

let targs'1 = (FStar_List.map (fun targ l -> (

let uu____2240 = (

let uu____2243 = (map_append FStar_Pervasives_Native.fst args l)
in (FStar_List.rev uu____2243))
in (targ uu____2240))) targs')
in FStar_TypeChecker_NBETerm.Lam ((((fun l -> (

let uu____2277 = (map_append FStar_Pervasives_Native.fst args l)
in (f1 uu____2277)))), (targs'1), ((n1 - m)), (res))))
end))
end
| uu____2284 -> begin
(match ((Prims.op_Equality m n1)) with
| true -> begin
(

let uu____2288 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (f1 uu____2288))
end
| uu____2295 -> begin
(

let uu____2297 = (FStar_List.splitAt n1 args)
in (match (uu____2297) with
| (args1, args') -> begin
(

let uu____2344 = (

let uu____2345 = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (f1 uu____2345))
in (iapp cfg uu____2344 args'))
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
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2464))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2508 = (aux args us ts)
in (match (uu____2508) with
| (us', ts') -> begin
FStar_TypeChecker_NBETerm.Construct (((i), (us'), (ts')))
end)))
end
| FStar_TypeChecker_NBETerm.FV (i, us, ts) -> begin
(

let rec aux = (fun args1 us1 ts1 -> (match (args1) with
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2635))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2679 = (aux args us ts)
in (match (uu____2679) with
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
| uu____2801 -> begin
(match ((Prims.op_Equality ar (Prims.parse_int "0"))) with
| true -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), ((FStar_List.append acc args)), (ar), (ar_lst), (tr_lb)))
end
| uu____2832 -> begin
(

let full_args = (FStar_List.append acc args)
in (

let uu____2845 = (test_args full_args ar_lst)
in (match (uu____2845) with
| (can_unfold, args1, res) -> begin
(match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta))) with
| true -> begin
((debug cfg (fun uu____2862 -> (

let uu____2863 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Zeta is not set; will not unfold %s\n" uu____2863))));
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)));
)
end
| uu____2889 -> begin
(match (can_unfold) with
| true -> begin
((debug cfg (fun uu____2895 -> (

let uu____2896 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Beta reducing recursive function %s\n" uu____2896))));
(match (res) with
| [] -> begin
(

let uu____2903 = (

let uu____2904 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2904 lb))
in (iapp cfg uu____2903 args1))
end
| (uu____2907)::uu____2908 -> begin
(

let t = (

let uu____2924 = (

let uu____2925 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2925 lb))
in (iapp cfg uu____2924 args1))
in (iapp cfg t res))
end);
)
end
| uu____2928 -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)))
end)
end)
end)))
end)
end))
end
| FStar_TypeChecker_NBETerm.Quote (uu____2953) -> begin
(

let uu____2958 = (

let uu____2960 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2960))
in (failwith uu____2958))
end
| FStar_TypeChecker_NBETerm.Reflect (uu____2963) -> begin
(

let uu____2964 = (

let uu____2966 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2966))
in (failwith uu____2964))
end
| FStar_TypeChecker_NBETerm.Lazy (uu____2969) -> begin
(

let uu____2984 = (

let uu____2986 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2986))
in (failwith uu____2984))
end
| FStar_TypeChecker_NBETerm.Constant (uu____2989) -> begin
(

let uu____2990 = (

let uu____2992 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2992))
in (failwith uu____2990))
end
| FStar_TypeChecker_NBETerm.Univ (uu____2995) -> begin
(

let uu____2996 = (

let uu____2998 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2998))
in (failwith uu____2996))
end
| FStar_TypeChecker_NBETerm.Type_t (uu____3001) -> begin
(

let uu____3002 = (

let uu____3004 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3004))
in (failwith uu____3002))
end
| FStar_TypeChecker_NBETerm.Unknown -> begin
(

let uu____3007 = (

let uu____3009 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3009))
in (failwith uu____3007))
end
| FStar_TypeChecker_NBETerm.Refinement (uu____3012) -> begin
(

let uu____3027 = (

let uu____3029 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3029))
in (failwith uu____3027))
end
| FStar_TypeChecker_NBETerm.Arrow (uu____3032) -> begin
(

let uu____3053 = (

let uu____3055 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3055))
in (failwith uu____3053))
end))
and translate_fv : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs fvar1 -> (

let debug1 = (debug cfg)
in (

let qninfo = (

let uu____3072 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in (

let uu____3073 = (FStar_Syntax_Syntax.lid_of_fv fvar1)
in (FStar_TypeChecker_Env.lookup_qname uu____3072 uu____3073)))
in (

let uu____3074 = ((is_constr qninfo) || (is_constr_fv fvar1))
in (match (uu____3074) with
| true -> begin
(FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] [])
end
| uu____3081 -> begin
(

let uu____3083 = (FStar_TypeChecker_Normalize.should_unfold cfg (fun uu____3085 -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1 qninfo)
in (match (uu____3083) with
| FStar_TypeChecker_Normalize.Should_unfold_fully -> begin
(failwith "Not yet handled")
end
| FStar_TypeChecker_Normalize.Should_unfold_no -> begin
((debug1 (fun uu____3092 -> (

let uu____3093 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(1) Decided to not unfold %s\n" uu____3093))));
(

let uu____3096 = (FStar_TypeChecker_Cfg.find_prim_step cfg fvar1)
in (match (uu____3096) with
| FStar_Pervasives_Native.Some (prim_step) when prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok -> begin
(

let arity = (prim_step.FStar_TypeChecker_Cfg.arity + prim_step.FStar_TypeChecker_Cfg.univ_arity)
in ((debug1 (fun uu____3107 -> (

let uu____3108 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Found a primop %s\n" uu____3108))));
(

let uu____3111 = (

let uu____3142 = (

let f = (fun uu____3170 uu____3171 -> ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))
in (FStar_Common.tabulate arity f))
in (((fun args -> (

let args' = (FStar_List.map FStar_TypeChecker_NBETerm.as_arg args)
in (

let callbacks = {FStar_TypeChecker_NBETerm.iapp = (iapp cfg); FStar_TypeChecker_NBETerm.translate = (translate cfg bs)}
in (

let uu____3231 = (prim_step.FStar_TypeChecker_Cfg.interpretation_nbe callbacks args')
in (match (uu____3231) with
| FStar_Pervasives_Native.Some (x) -> begin
((debug1 (fun uu____3242 -> (

let uu____3243 = (FStar_Syntax_Print.fv_to_string fvar1)
in (

let uu____3245 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print2 "Primitive operator %s returned %s\n" uu____3243 uu____3245)))));
x;
)
end
| FStar_Pervasives_Native.None -> begin
((debug1 (fun uu____3253 -> (

let uu____3254 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Primitive operator %s failed\n" uu____3254))));
(

let uu____3257 = (FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
in (iapp cfg uu____3257 args'));
)
end)))))), (uu____3142), (arity), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____3111));
))
end
| FStar_Pervasives_Native.Some (uu____3265) -> begin
((debug1 (fun uu____3271 -> (

let uu____3272 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(2) Decided to not unfold %s\n" uu____3272))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end
| uu____3279 -> begin
((debug1 (fun uu____3287 -> (

let uu____3288 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(3) Decided to not unfold %s\n" uu____3288))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end));
)
end
| FStar_TypeChecker_Normalize.Should_unfold_reify -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3298; FStar_Syntax_Syntax.sigquals = uu____3299; FStar_Syntax_Syntax.sigmeta = uu____3300; FStar_Syntax_Syntax.sigattrs = uu____3301}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3369 -> begin
((debug1 (fun uu____3374 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3384 -> (

let uu____3385 = (

let uu____3387 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3387))
in (

let uu____3388 = (

let uu____3390 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3390))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3385 uu____3388)))));
(debug1 (fun uu____3399 -> (

let uu____3400 = (

let uu____3402 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3402))
in (

let uu____3403 = (

let uu____3405 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3405))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3400 uu____3403)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3408 -> begin
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
end)
end
| FStar_TypeChecker_Normalize.Should_unfold_yes -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3416; FStar_Syntax_Syntax.sigquals = uu____3417; FStar_Syntax_Syntax.sigmeta = uu____3418; FStar_Syntax_Syntax.sigattrs = uu____3419}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3487 -> begin
((debug1 (fun uu____3492 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3502 -> (

let uu____3503 = (

let uu____3505 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3505))
in (

let uu____3506 = (

let uu____3508 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3508))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3503 uu____3506)))));
(debug1 (fun uu____3517 -> (

let uu____3518 = (

let uu____3520 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3520))
in (

let uu____3521 = (

let uu____3523 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3523))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3518 uu____3521)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3526 -> begin
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
| uu____3571 -> begin
(

let uu____3574 = (

let uu____3605 = (FStar_List.map (fun uu____3630 _ts -> (FStar_All.pipe_left id1 ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))) us)
in (((fun us1 -> (translate cfg (FStar_List.rev_append us1 bs) lb.FStar_Syntax_Syntax.lbdef))), (uu____3605), ((FStar_List.length us)), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____3574))
end)))))
and mkRec' : (FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_TypeChecker_NBETerm.t)  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun callback b bs env -> (

let uu____3691 = (FStar_Syntax_Util.let_rec_arity b)
in (match (uu____3691) with
| (ar, maybe_lst) -> begin
(

let uu____3716 = (match (maybe_lst) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3736 = (FStar_Common.tabulate ar (fun uu____3742 -> true))
in ((ar), (uu____3736)))
end
| FStar_Pervasives_Native.Some (lst) -> begin
(

let l = (trim lst)
in (((FStar_List.length l)), (l)))
end)
in (match (uu____3716) with
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

let uu____3869 = (

let uu____3872 = (mkRec' callback lb lbs0 bs0)
in (uu____3872)::bs1)
in (aux lbs' lbs0 uu____3869 bs0))
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

let uu____3889 = (FStar_BigInt.big_int_of_string s)
in FStar_TypeChecker_NBETerm.Int (uu____3889))
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
| uu____3898 -> begin
(

let uu____3899 = (

let uu____3901 = (

let uu____3903 = (FStar_Syntax_Print.const_to_string c)
in (Prims.op_Hat uu____3903 ": Not yet implemented"))
in (Prims.op_Hat "Tm_constant " uu____3901))
in (failwith uu____3899))
end))
and translate : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs e -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____3927 -> (

let uu____3928 = (

let uu____3930 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____3930))
in (

let uu____3931 = (

let uu____3933 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.term_to_string uu____3933))
in (FStar_Util.print2 "Term: %s - %s\n" uu____3928 uu____3931)))));
(debug1 (fun uu____3940 -> (

let uu____3941 = (

let uu____3943 = (FStar_List.map (fun x -> (FStar_TypeChecker_NBETerm.t_to_string x)) bs)
in (FStar_String.concat ";; " uu____3943))
in (FStar_Util.print1 "BS list: %s\n" uu____3941))));
(

let uu____3952 = (

let uu____3953 = (FStar_Syntax_Subst.compress e)
in uu____3953.FStar_Syntax_Syntax.n)
in (match (uu____3952) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3956, uu____3957) -> begin
(failwith "Tm_delayed: Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_TypeChecker_NBETerm.Unknown
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____3996 = (translate_constant c)
in FStar_TypeChecker_NBETerm.Constant (uu____3996))
end
| FStar_Syntax_Syntax.Tm_bvar (db) -> begin
(match ((db.FStar_Syntax_Syntax.index < (FStar_List.length bs))) with
| true -> begin
(FStar_List.nth bs db.FStar_Syntax_Syntax.index)
end
| uu____3999 -> begin
(failwith "de Bruijn index out of bounds")
end)
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
((debug1 (fun uu____4015 -> (

let uu____4016 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____4018 = (

let uu____4020 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_All.pipe_right uu____4020 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n" uu____4016 uu____4018)))));
(

let uu____4031 = (translate cfg bs t)
in (

let uu____4032 = (FStar_List.map (fun x -> (

let uu____4036 = (

let uu____4037 = (translate_univ bs x)
in FStar_TypeChecker_NBETerm.Univ (uu____4037))
in (FStar_TypeChecker_NBETerm.as_arg uu____4036))) us)
in (iapp cfg uu____4031 uu____4032)));
)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____4039 = (translate_univ bs u)
in FStar_TypeChecker_NBETerm.Type_t (uu____4039))
end
| FStar_Syntax_Syntax.Tm_arrow (xs, c) -> begin
(

let uu____4062 = (

let uu____4083 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____4153 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____4153), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (((fun ys -> (translate_comp cfg (FStar_List.rev_append ys bs) c))), (uu____4083)))
in FStar_TypeChecker_NBETerm.Arrow (uu____4062))
end
| FStar_Syntax_Syntax.Tm_refine (bv, tm) -> begin
FStar_TypeChecker_NBETerm.Refinement ((((fun y -> (translate cfg ((y)::bs) tm))), ((fun uu____4222 -> (

let uu____4223 = (translate cfg bs bv.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_NBETerm.as_arg uu____4223))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____4225, uu____4226) -> begin
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
| FStar_Syntax_Syntax.Tm_abs ([], uu____4288, uu____4289) -> begin
(failwith "Impossible: abstraction with no binders")
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, resc) -> begin
(

let uu____4340 = (

let uu____4371 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____4441 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____4441), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (

let uu____4470 = (FStar_Util.map_opt resc (fun c uu____4482 -> (translate_residual_comp cfg bs c)))
in (((fun ys -> (translate cfg (FStar_List.rev_append ys bs) body))), (uu____4371), ((FStar_List.length xs)), (uu____4470))))
in FStar_TypeChecker_NBETerm.Lam (uu____4340))
end
| FStar_Syntax_Syntax.Tm_fvar (fvar1) -> begin
(translate_fv cfg bs fvar1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4516; FStar_Syntax_Syntax.vars = uu____4517}, (arg)::(more)::args) -> begin
(

let uu____4577 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4577) with
| (head1, uu____4595) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4639 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4639)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4648)); FStar_Syntax_Syntax.pos = uu____4649; FStar_Syntax_Syntax.vars = uu____4650}, (arg)::(more)::args) -> begin
(

let uu____4710 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4710) with
| (head1, uu____4728) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4772 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4772)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4781)); FStar_Syntax_Syntax.pos = uu____4782; FStar_Syntax_Syntax.vars = uu____4783}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.reifying -> begin
(

let cfg1 = (

let uu___649_4824 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___649_4824.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___649_4824.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___649_4824.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___649_4824.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___649_4824.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___649_4824.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___649_4824.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___649_4824.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4830)); FStar_Syntax_Syntax.pos = uu____4831; FStar_Syntax_Syntax.vars = uu____4832}, (arg)::[]) -> begin
(

let uu____4872 = (translate cfg bs (FStar_Pervasives_Native.fst arg))
in FStar_TypeChecker_NBETerm.Reflect (uu____4872))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4877; FStar_Syntax_Syntax.vars = uu____4878}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.reify_ -> begin
(

let cfg1 = (

let uu___672_4920 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___672_4920.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___672_4920.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___672_4920.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___672_4920.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___672_4920.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___672_4920.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___672_4920.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___672_4920.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = true})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug1 (fun uu____4959 -> (

let uu____4960 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____4962 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Application: %s @ %s\n" uu____4960 uu____4962)))));
(

let uu____4965 = (translate cfg bs head1)
in (

let uu____4966 = (FStar_List.map (fun x -> (

let uu____4988 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____4988), ((FStar_Pervasives_Native.snd x))))) args)
in (iapp cfg uu____4965 uu____4966)));
)
end
| FStar_Syntax_Syntax.Tm_match (scrut, branches) -> begin
(

let make_branches = (fun readback1 -> (

let cfg1 = (

let uu___688_5049 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___690_5052 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___690_5052.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___690_5052.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = false; FStar_TypeChecker_Cfg.weak = uu___690_5052.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___690_5052.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___690_5052.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___690_5052.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___690_5052.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___690_5052.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___690_5052.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___690_5052.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___690_5052.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___690_5052.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___690_5052.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___690_5052.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___690_5052.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___690_5052.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___690_5052.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___690_5052.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___690_5052.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___690_5052.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___690_5052.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___690_5052.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___690_5052.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___690_5052.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___690_5052.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___688_5049.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___688_5049.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___688_5049.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___688_5049.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___688_5049.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___688_5049.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___688_5049.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___688_5049.FStar_TypeChecker_Cfg.reifying})
in (

let rec process_pattern = (fun bs1 p -> (

let uu____5081 = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
((bs1), (FStar_Syntax_Syntax.Pat_constant (c)))
end
| FStar_Syntax_Syntax.Pat_cons (fvar1, args) -> begin
(

let uu____5117 = (FStar_List.fold_left (fun uu____5158 uu____5159 -> (match (((uu____5158), (uu____5159))) with
| ((bs2, args1), (arg, b)) -> begin
(

let uu____5251 = (process_pattern bs2 arg)
in (match (uu____5251) with
| (bs', arg') -> begin
((bs'), ((((arg'), (b)))::args1))
end))
end)) ((bs1), ([])) args)
in (match (uu____5117) with
| (bs', args') -> begin
((bs'), (FStar_Syntax_Syntax.Pat_cons (((fvar1), ((FStar_List.rev args'))))))
end))
end
| FStar_Syntax_Syntax.Pat_var (bvar) -> begin
(

let x = (

let uu____5350 = (

let uu____5351 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5351))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5350))
in (

let uu____5352 = (

let uu____5355 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____5355)::bs1)
in ((uu____5352), (FStar_Syntax_Syntax.Pat_var (x)))))
end
| FStar_Syntax_Syntax.Pat_wild (bvar) -> begin
(

let x = (

let uu____5360 = (

let uu____5361 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5361))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5360))
in (

let uu____5362 = (

let uu____5365 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____5365)::bs1)
in ((uu____5362), (FStar_Syntax_Syntax.Pat_wild (x)))))
end
| FStar_Syntax_Syntax.Pat_dot_term (bvar, tm) -> begin
(

let x = (

let uu____5375 = (

let uu____5376 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5376))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5375))
in (

let uu____5377 = (

let uu____5378 = (

let uu____5385 = (

let uu____5388 = (translate cfg1 bs1 tm)
in (readback1 uu____5388))
in ((x), (uu____5385)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____5378))
in ((bs1), (uu____5377))))
end)
in (match (uu____5081) with
| (bs2, p_new) -> begin
((bs2), ((

let uu___728_5408 = p
in {FStar_Syntax_Syntax.v = p_new; FStar_Syntax_Syntax.p = uu___728_5408.FStar_Syntax_Syntax.p})))
end)))
in (FStar_List.map (fun uu____5427 -> (match (uu____5427) with
| (pat, when_clause, e1) -> begin
(

let uu____5449 = (process_pattern bs pat)
in (match (uu____5449) with
| (bs', pat') -> begin
(

let uu____5462 = (

let uu____5463 = (

let uu____5466 = (translate cfg1 bs' e1)
in (readback1 uu____5466))
in ((pat'), (when_clause), (uu____5463)))
in (FStar_Syntax_Util.branch uu____5462))
end))
end)) branches))))
in (

let rec case = (fun scrut1 -> ((debug1 (fun uu____5488 -> (

let uu____5489 = (

let uu____5491 = (readback cfg scrut1)
in (FStar_Syntax_Print.term_to_string uu____5491))
in (

let uu____5492 = (FStar_TypeChecker_NBETerm.t_to_string scrut1)
in (FStar_Util.print2 "Match case: (%s) -- (%s)\n" uu____5489 uu____5492)))));
(

let scrut2 = (unlazy scrut1)
in (match (scrut2) with
| FStar_TypeChecker_NBETerm.Construct (c, us, args) -> begin
((debug1 (fun uu____5520 -> (

let uu____5521 = (

let uu____5523 = (FStar_All.pipe_right args (FStar_List.map (fun uu____5549 -> (match (uu____5549) with
| (x, q) -> begin
(

let uu____5563 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (Prims.op_Hat (match ((FStar_Util.is_some q)) with
| true -> begin
"#"
end
| uu____5568 -> begin
""
end) uu____5563))
end))))
in (FStar_All.pipe_right uu____5523 (FStar_String.concat "; ")))
in (FStar_Util.print1 "Match args: %s\n" uu____5521))));
(

let uu____5577 = (pickBranch cfg scrut2 branches)
in (match (uu____5577) with
| FStar_Pervasives_Native.Some (branch1, args1) -> begin
(

let uu____5598 = (FStar_List.fold_left (fun bs1 x -> (x)::bs1) bs args1)
in (translate cfg uu____5598 branch1))
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
)
end
| FStar_TypeChecker_NBETerm.Constant (c) -> begin
((debug1 (fun uu____5621 -> (

let uu____5622 = (FStar_TypeChecker_NBETerm.t_to_string scrut2)
in (FStar_Util.print1 "Match constant : %s\n" uu____5622))));
(

let uu____5625 = (pickBranch cfg scrut2 branches)
in (match (uu____5625) with
| FStar_Pervasives_Native.Some (branch1, []) -> begin
(translate cfg bs branch1)
end
| FStar_Pervasives_Native.Some (branch1, (arg)::[]) -> begin
(translate cfg ((arg)::bs) branch1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end
| FStar_Pervasives_Native.Some (uu____5659, (hd1)::tl1) -> begin
(failwith "Impossible: Matching on constants cannot bind more than one variable")
end));
)
end
| uu____5673 -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
))
in (

let uu____5674 = (translate cfg bs scrut)
in (case uu____5674))))
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

let uu____5753 = (make_rec_env (translate_letbinding cfg) lbs bs)
in (translate cfg uu____5753 body))
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____5757) -> begin
(translate cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let close1 = (fun t -> (

let bvs = (FStar_List.map (fun uu____5778 -> (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)) bs)
in (

let s1 = (FStar_List.mapi (fun i bv -> FStar_Syntax_Syntax.DB (((i), (bv)))) bvs)
in (

let s2 = (

let uu____5791 = (FStar_List.zip bvs bs)
in (FStar_List.map (fun uu____5806 -> (match (uu____5806) with
| (bv, t1) -> begin
(

let uu____5813 = (

let uu____5820 = (readback cfg t1)
in ((bv), (uu____5820)))
in FStar_Syntax_Syntax.NT (uu____5813))
end)) uu____5791))
in (

let uu____5825 = (FStar_Syntax_Subst.subst s1 t)
in (FStar_Syntax_Subst.subst s2 uu____5825))))))
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

let f = (fun uu____5834 -> (

let t = (FStar_Syntax_Util.unfold_lazy li)
in ((debug1 (fun uu____5841 -> (

let uu____5842 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n" uu____5842))));
(translate cfg bs t);
)))
in (

let uu____5845 = (

let uu____5860 = (FStar_Common.mk_thunk f)
in ((FStar_Util.Inl (li)), (uu____5860)))
in FStar_TypeChecker_NBETerm.Lazy (uu____5845)))
end));
)))
and translate_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_NBETerm.comp = (fun cfg bs c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (typ, u) -> begin
(

let uu____5892 = (

let uu____5899 = (translate cfg bs typ)
in (

let uu____5900 = (fmap_opt (translate_univ bs) u)
in ((uu____5899), (uu____5900))))
in FStar_TypeChecker_NBETerm.Tot (uu____5892))
end
| FStar_Syntax_Syntax.GTotal (typ, u) -> begin
(

let uu____5915 = (

let uu____5922 = (translate cfg bs typ)
in (

let uu____5923 = (fmap_opt (translate_univ bs) u)
in ((uu____5922), (uu____5923))))
in FStar_TypeChecker_NBETerm.GTot (uu____5915))
end
| FStar_Syntax_Syntax.Comp (ctyp) -> begin
(

let uu____5929 = (translate_comp_typ cfg bs ctyp)
in FStar_TypeChecker_NBETerm.Comp (uu____5929))
end))
and readback_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg c -> (

let c' = (match (c) with
| FStar_TypeChecker_NBETerm.Tot (typ, u) -> begin
(

let uu____5939 = (

let uu____5948 = (readback cfg typ)
in ((uu____5948), (u)))
in FStar_Syntax_Syntax.Total (uu____5939))
end
| FStar_TypeChecker_NBETerm.GTot (typ, u) -> begin
(

let uu____5961 = (

let uu____5970 = (readback cfg typ)
in ((uu____5970), (u)))
in FStar_Syntax_Syntax.GTotal (uu____5961))
end
| FStar_TypeChecker_NBETerm.Comp (ctyp) -> begin
(

let uu____5978 = (readback_comp_typ cfg ctyp)
in FStar_Syntax_Syntax.Comp (uu____5978))
end)
in (FStar_Syntax_Syntax.mk c' FStar_Pervasives_Native.None FStar_Range.dummyRange)))
and translate_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_TypeChecker_NBETerm.comp_typ = (fun cfg bs c -> (

let uu____5984 = c
in (match (uu____5984) with
| {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags} -> begin
(

let uu____6004 = (FStar_List.map (translate_univ bs) comp_univs)
in (

let uu____6005 = (translate cfg bs result_typ)
in (

let uu____6006 = (FStar_List.map (fun x -> (

let uu____6034 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____6034), ((FStar_Pervasives_Native.snd x))))) effect_args)
in (

let uu____6041 = (FStar_List.map (translate_flag cfg bs) flags)
in {FStar_TypeChecker_NBETerm.comp_univs = uu____6004; FStar_TypeChecker_NBETerm.effect_name = effect_name; FStar_TypeChecker_NBETerm.result_typ = uu____6005; FStar_TypeChecker_NBETerm.effect_args = uu____6006; FStar_TypeChecker_NBETerm.flags = uu____6041}))))
end)))
and readback_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun cfg c -> (

let uu____6046 = (readback cfg c.FStar_TypeChecker_NBETerm.result_typ)
in (

let uu____6049 = (FStar_List.map (fun x -> (

let uu____6075 = (readback cfg (FStar_Pervasives_Native.fst x))
in ((uu____6075), ((FStar_Pervasives_Native.snd x))))) c.FStar_TypeChecker_NBETerm.effect_args)
in (

let uu____6076 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags)
in {FStar_Syntax_Syntax.comp_univs = c.FStar_TypeChecker_NBETerm.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_TypeChecker_NBETerm.effect_name; FStar_Syntax_Syntax.result_typ = uu____6046; FStar_Syntax_Syntax.effect_args = uu____6049; FStar_Syntax_Syntax.flags = uu____6076}))))
and translate_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.residual_comp  ->  FStar_TypeChecker_NBETerm.residual_comp = (fun cfg bs c -> (

let uu____6084 = c
in (match (uu____6084) with
| {FStar_Syntax_Syntax.residual_effect = residual_effect; FStar_Syntax_Syntax.residual_typ = residual_typ; FStar_Syntax_Syntax.residual_flags = residual_flags} -> begin
(

let uu____6094 = (FStar_Util.map_opt residual_typ (translate cfg bs))
in (

let uu____6099 = (FStar_List.map (translate_flag cfg bs) residual_flags)
in {FStar_TypeChecker_NBETerm.residual_effect = residual_effect; FStar_TypeChecker_NBETerm.residual_typ = uu____6094; FStar_TypeChecker_NBETerm.residual_flags = uu____6099}))
end)))
and readback_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.residual_comp  ->  FStar_Syntax_Syntax.residual_comp = (fun cfg c -> (

let uu____6104 = (FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ (readback cfg))
in (

let uu____6111 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = c.FStar_TypeChecker_NBETerm.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6104; FStar_Syntax_Syntax.residual_flags = uu____6111})))
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

let uu____6122 = (translate cfg bs tm)
in FStar_TypeChecker_NBETerm.DECREASES (uu____6122))
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

let uu____6126 = (readback cfg t)
in FStar_Syntax_Syntax.DECREASES (uu____6126))
end))
and translate_monadic : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____6129 cfg bs e -> (match (uu____6129) with
| (m, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let uu____6167 = (

let uu____6176 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv m)
in (FStar_TypeChecker_Env.effect_decl_opt cfg.FStar_TypeChecker_Cfg.tcenv uu____6176))
in (match (uu____6167) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6183 = (

let uu____6185 = (FStar_Ident.string_of_lid m)
in (FStar_Util.format1 "Effect declaration not found: %s" uu____6185))
in (failwith uu____6183))
end
| FStar_Pervasives_Native.Some (ed, q) -> begin
(

let cfg' = (

let uu___936_6201 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___936_6201.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___936_6201.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___936_6201.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___936_6201.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___936_6201.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___936_6201.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___936_6201.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___936_6201.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let body_lam = (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (ty); FStar_Syntax_Syntax.residual_flags = []}
in (

let uu____6209 = (

let uu____6216 = (

let uu____6217 = (

let uu____6236 = (

let uu____6245 = (

let uu____6252 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____6252), (FStar_Pervasives_Native.None)))
in (uu____6245)::[])
in ((uu____6236), (body), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____6217))
in (FStar_Syntax_Syntax.mk uu____6216))
in (uu____6209 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos)))
in (

let maybe_range_arg = (

let uu____6286 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____6286) with
| true -> begin
(

let uu____6295 = (

let uu____6300 = (

let uu____6301 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (translate cfg [] uu____6301))
in ((uu____6300), (FStar_Pervasives_Native.None)))
in (

let uu____6302 = (

let uu____6309 = (

let uu____6314 = (

let uu____6315 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range body.FStar_Syntax_Syntax.pos body.FStar_Syntax_Syntax.pos)
in (translate cfg [] uu____6315))
in ((uu____6314), (FStar_Pervasives_Native.None)))
in (uu____6309)::[])
in (uu____6295)::uu____6302))
end
| uu____6328 -> begin
[]
end))
in (

let t = (

let uu____6335 = (

let uu____6336 = (

let uu____6337 = (FStar_Syntax_Util.un_uinst (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (translate cfg' [] uu____6337))
in (iapp cfg uu____6336 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::(((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____6354 = (

let uu____6355 = (

let uu____6362 = (

let uu____6367 = (translate cfg' bs lb.FStar_Syntax_Syntax.lbtyp)
in ((uu____6367), (FStar_Pervasives_Native.None)))
in (

let uu____6368 = (

let uu____6375 = (

let uu____6380 = (translate cfg' bs ty)
in ((uu____6380), (FStar_Pervasives_Native.None)))
in (uu____6375)::[])
in (uu____6362)::uu____6368))
in (

let uu____6393 = (

let uu____6400 = (

let uu____6407 = (

let uu____6414 = (

let uu____6419 = (translate cfg bs lb.FStar_Syntax_Syntax.lbdef)
in ((uu____6419), (FStar_Pervasives_Native.None)))
in (

let uu____6420 = (

let uu____6427 = (

let uu____6434 = (

let uu____6439 = (translate cfg bs body_lam)
in ((uu____6439), (FStar_Pervasives_Native.None)))
in (uu____6434)::[])
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6427)
in (uu____6414)::uu____6420))
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6407)
in (FStar_List.append maybe_range_arg uu____6400))
in (FStar_List.append uu____6355 uu____6393)))
in (iapp cfg uu____6335 uu____6354)))
in ((debug cfg (fun uu____6471 -> (

let uu____6472 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic: %s\n" uu____6472))));
t;
)))))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6475)); FStar_Syntax_Syntax.pos = uu____6476; FStar_Syntax_Syntax.vars = uu____6477}, ((e2, uu____6479))::[]) -> begin
(translate (

let uu___958_6520 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___958_6520.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___958_6520.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___958_6520.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___958_6520.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___958_6520.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___958_6520.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___958_6520.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___958_6520.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug cfg (fun uu____6552 -> (

let uu____6553 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____6555 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "translate_monadic app (%s) @ (%s)\n" uu____6553 uu____6555)))));
(

let fallback1 = (fun uu____6563 -> (translate cfg bs e1))
in (

let fallback2 = (fun uu____6569 -> (

let uu____6570 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_monadic (((m), (ty))))))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___970_6577 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___970_6577.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___970_6577.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___970_6577.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___970_6577.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___970_6577.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___970_6577.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___970_6577.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___970_6577.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs uu____6570)))
in (

let uu____6579 = (

let uu____6580 = (FStar_Syntax_Util.un_uinst head1)
in uu____6580.FStar_Syntax_Syntax.n)
in (match (uu____6579) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____6586 = (

let uu____6588 = (FStar_TypeChecker_Env.is_action cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (not (uu____6588)))
in (match (uu____6586) with
| true -> begin
(fallback1 ())
end
| uu____6591 -> begin
(

let uu____6593 = (

let uu____6595 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (FStar_Option.isNone uu____6595))
in (match (uu____6593) with
| true -> begin
(fallback2 ())
end
| uu____6607 -> begin
(

let e2 = (

let uu____6612 = (

let uu____6617 = (FStar_Syntax_Util.mk_reify head1)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6617 args))
in (uu____6612 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (translate (

let uu___979_6620 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___979_6620.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___979_6620.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___979_6620.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___979_6620.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___979_6620.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___979_6620.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___979_6620.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___979_6620.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2))
end))
end))))
end
| uu____6622 -> begin
(fallback1 ())
end))));
)
end
| FStar_Syntax_Syntax.Tm_match (sc, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____6743 -> (match (uu____6743) with
| (pat, wopt, tm) -> begin
(

let uu____6791 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____6791)))
end))))
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), (branches1)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___992_6825 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___992_6825.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___992_6825.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___992_6825.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___992_6825.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___992_6825.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___992_6825.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___992_6825.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___992_6825.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs tm)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____6828)) -> begin
(translate_monadic ((m), (ty)) cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty')) -> begin
(translate_monadic_lift ((msrc), (mtgt), (ty')) cfg bs e1)
end
| uu____6855 -> begin
(

let uu____6856 = (

let uu____6858 = (FStar_Syntax_Print.tag_of_term e1)
in (FStar_Util.format1 "Unexpected case in translate_monadic: %s" uu____6858))
in (failwith uu____6856))
end))
end))
and translate_monadic_lift : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____6861 cfg bs e -> (match (uu____6861) with
| (msrc, mtgt, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (

let uu____6885 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____6885) with
| true -> begin
(

let ed = (

let uu____6889 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl cfg.FStar_TypeChecker_Cfg.tcenv uu____6889))
in (

let ret1 = (

let uu____6891 = (

let uu____6892 = (FStar_Syntax_Subst.compress (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in uu____6892.FStar_Syntax_Syntax.n)
in (match (uu____6891) with
| FStar_Syntax_Syntax.Tm_uinst (ret1, (uu____6900)::[]) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((ret1), ((FStar_Syntax_Syntax.U_unknown)::[])))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
end
| uu____6907 -> begin
(failwith "NYI: Reification of indexed effect (NBE)")
end))
in (

let cfg' = (

let uu___1025_6910 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1025_6910.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1025_6910.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1025_6910.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1025_6910.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1025_6910.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1025_6910.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1025_6910.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1025_6910.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____6913 = (

let uu____6914 = (translate cfg' [] ret1)
in (iapp cfg' uu____6914 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____6923 = (

let uu____6924 = (

let uu____6929 = (translate cfg' bs ty)
in ((uu____6929), (FStar_Pervasives_Native.None)))
in (

let uu____6930 = (

let uu____6937 = (

let uu____6942 = (translate cfg' bs e1)
in ((uu____6942), (FStar_Pervasives_Native.None)))
in (uu____6937)::[])
in (uu____6924)::uu____6930))
in (iapp cfg' uu____6913 uu____6923)))
in ((debug cfg (fun uu____6958 -> (

let uu____6959 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(1): %s\n" uu____6959))));
t;
)))))
end
| uu____6962 -> begin
(

let uu____6964 = (FStar_TypeChecker_Env.monad_leq cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt)
in (match (uu____6964) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6967 = (

let uu____6969 = (FStar_Ident.text_of_lid msrc)
in (

let uu____6971 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____6969 uu____6971)))
in (failwith uu____6967))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____6974; FStar_TypeChecker_Env.mtarget = uu____6975; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____6976; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____6998 = (

let uu____7000 = (FStar_Ident.text_of_lid msrc)
in (

let uu____7002 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____7000 uu____7002)))
in (failwith uu____6998))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____7005; FStar_TypeChecker_Env.mtarget = uu____7006; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____7007; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let lift_lam = (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let uu____7046 = (

let uu____7049 = (FStar_Syntax_Syntax.bv_to_name x)
in (lift FStar_Syntax_Syntax.U_unknown ty FStar_Syntax_Syntax.tun uu____7049))
in (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) uu____7046 FStar_Pervasives_Native.None)))
in (

let cfg' = (

let uu___1049_7065 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1049_7065.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1049_7065.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1049_7065.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1049_7065.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1049_7065.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1049_7065.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1049_7065.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1049_7065.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____7068 = (translate cfg' [] lift_lam)
in (

let uu____7069 = (

let uu____7070 = (

let uu____7075 = (translate cfg bs e1)
in ((uu____7075), (FStar_Pervasives_Native.None)))
in (uu____7070)::[])
in (iapp cfg uu____7068 uu____7069)))
in ((debug cfg (fun uu____7087 -> (

let uu____7088 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(2): %s\n" uu____7088))));
t;
))))
end))
end)))
end))
and readback : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.term = (fun cfg x -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____7106 -> (

let uu____7107 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print1 "Readback: %s\n" uu____7107))));
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

let uu____7115 = (FStar_BigInt.string_of_big_int i)
in (FStar_All.pipe_right uu____7115 FStar_Syntax_Util.exp_int))
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

let uu____7175 = (FStar_List.fold_left (fun uu____7218 tf -> (match (uu____7218) with
| (args_rev, accus_rev) -> begin
(

let uu____7270 = (tf accus_rev)
in (match (uu____7270) with
| (xt, q) -> begin
(

let x1 = (

let uu____7290 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7290))
in (

let uu____7291 = (

let uu____7294 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____7294)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____7291))))
end))
end)) (([]), ([])) targs)
in (match (uu____7175) with
| (args_rev, accus_rev) -> begin
(

let body = (

let uu____7338 = (f (FStar_List.rev accus_rev))
in (readback cfg uu____7338))
in (

let uu____7339 = (FStar_Util.map_opt resc (fun thunk1 -> (

let uu____7350 = (thunk1 ())
in (readback_residual_comp cfg uu____7350))))
in (FStar_Syntax_Util.abs (FStar_List.rev args_rev) body uu____7339)))
end))
end
| FStar_TypeChecker_NBETerm.Refinement (f, targ) -> begin
(

let x1 = (

let uu____7378 = (

let uu____7379 = (

let uu____7380 = (targ ())
in (FStar_Pervasives_Native.fst uu____7380))
in (readback cfg uu____7379))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7378))
in (

let body = (

let uu____7386 = (

let uu____7387 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (f uu____7387))
in (readback cfg uu____7386))
in (FStar_Syntax_Util.refine x1 body)))
end
| FStar_TypeChecker_NBETerm.Reflect (t) -> begin
(

let tm = (readback cfg t)
in (FStar_Syntax_Util.mk_reflect tm))
end
| FStar_TypeChecker_NBETerm.Arrow (f, targs) -> begin
(

let uu____7424 = (FStar_List.fold_left (fun uu____7467 tf -> (match (uu____7467) with
| (args_rev, accus_rev) -> begin
(

let uu____7519 = (tf accus_rev)
in (match (uu____7519) with
| (xt, q) -> begin
(

let x1 = (

let uu____7539 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7539))
in (

let uu____7540 = (

let uu____7543 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____7543)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____7540))))
end))
end)) (([]), ([])) targs)
in (match (uu____7424) with
| (args_rev, accus_rev) -> begin
(

let cmp = (

let uu____7587 = (f (FStar_List.rev accus_rev))
in (readback_comp cfg uu____7587))
in (FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp))
end))
end
| FStar_TypeChecker_NBETerm.Construct (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7630 -> (match (uu____7630) with
| (x1, q) -> begin
(

let uu____7641 = (readback cfg x1)
in ((uu____7641), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7660 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7667)::uu____7668 -> begin
(

let uu____7671 = (

let uu____7674 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7674 (FStar_List.rev us)))
in (apply1 uu____7671))
end
| [] -> begin
(

let uu____7675 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7675))
end)))
end
| FStar_TypeChecker_NBETerm.FV (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7716 -> (match (uu____7716) with
| (x1, q) -> begin
(

let uu____7727 = (readback cfg x1)
in ((uu____7727), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7746 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7753)::uu____7754 -> begin
(

let uu____7757 = (

let uu____7760 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7760 (FStar_List.rev us)))
in (apply1 uu____7757))
end
| [] -> begin
(

let uu____7761 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7761))
end)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), []) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), ts) -> begin
(

let args = (map_rev (fun uu____7808 -> (match (uu____7808) with
| (x1, q) -> begin
(

let uu____7819 = (readback cfg x1)
in ((uu____7819), (q)))
end)) ts)
in (

let uu____7820 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Util.mk_app uu____7820 args)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Match (scrut, cases, make_branches), ts) -> begin
(

let args = (map_rev (fun uu____7880 -> (match (uu____7880) with
| (x1, q) -> begin
(

let uu____7891 = (readback cfg x1)
in ((uu____7891), (q)))
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
| uu____7921 -> begin
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

let args1 = (map_rev (fun uu____8008 -> (match (uu____8008) with
| (x1, q) -> begin
(

let uu____8019 = (readback cfg x1)
in ((uu____8019), (q)))
end)) args)
in (match (args1) with
| [] -> begin
head1
end
| uu____8024 -> begin
(FStar_Syntax_Util.mk_app head1 args1)
end)))
end
| FStar_TypeChecker_NBETerm.Quote (qt, qi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl (li), uu____8036) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (li)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (uu____8053, thunk1) -> begin
(

let uu____8075 = (FStar_Common.force_thunk thunk1)
in (readback cfg uu____8075))
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
| uu____8104 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____8116 -> begin
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
| uu____8137 -> begin
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
| uu____8164 -> begin
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
| uu____8188 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____8199 -> begin
false
end))


let step_as_normalizer_step : step  ->  FStar_TypeChecker_Env.step = (fun uu___1_8206 -> (match (uu___1_8206) with
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

let uu___1247_8245 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1249_8248 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1249_8248.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1249_8248.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1249_8248.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1249_8248.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1249_8248.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1249_8248.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1249_8248.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1249_8248.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1249_8248.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1249_8248.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1249_8248.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1249_8248.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1249_8248.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1249_8248.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1249_8248.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1249_8248.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___1249_8248.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1249_8248.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1249_8248.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1249_8248.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1249_8248.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1249_8248.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1249_8248.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1249_8248.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1249_8248.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1247_8245.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1247_8245.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1247_8245.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1247_8245.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1247_8245.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1247_8245.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1247_8245.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1247_8245.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____8253 -> (

let uu____8254 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8254))));
(

let r = (

let uu____8258 = (translate cfg1 [] e)
in (readback cfg1 uu____8258))
in ((debug cfg1 (fun uu____8262 -> (

let uu____8263 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8263))));
r;
));
))))


let normalize_for_unit_test : FStar_TypeChecker_Env.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun steps env e -> (

let cfg = (FStar_TypeChecker_Cfg.config steps env)
in (

let cfg1 = (

let uu___1264_8288 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1266_8291 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1266_8291.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1266_8291.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1266_8291.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1266_8291.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1266_8291.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1266_8291.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1266_8291.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1266_8291.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1266_8291.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1266_8291.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1266_8291.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1266_8291.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1266_8291.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1266_8291.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1266_8291.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1266_8291.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___1266_8291.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1266_8291.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1266_8291.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1266_8291.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1266_8291.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1266_8291.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1266_8291.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1266_8291.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1266_8291.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1264_8288.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1264_8288.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1264_8288.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1264_8288.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1264_8288.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1264_8288.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1264_8288.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1264_8288.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____8296 -> (

let uu____8297 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8297))));
(

let r = (

let uu____8301 = (translate cfg1 [] e)
in (readback cfg1 uu____8301))
in ((debug cfg1 (fun uu____8305 -> (

let uu____8306 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8306))));
r;
));
))))




