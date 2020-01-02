
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
(FStar_Thunk.force t1)
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
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____1621, uu____1622, uu____1623, uu____1624, uu____1625, uu____1626); FStar_Syntax_Syntax.sigrng = uu____1627; FStar_Syntax_Syntax.sigquals = uu____1628; FStar_Syntax_Syntax.sigmeta = uu____1629; FStar_Syntax_Syntax.sigattrs = uu____1630; FStar_Syntax_Syntax.sigopts = uu____1631}, uu____1632), uu____1633) -> begin
true
end
| uu____1693 -> begin
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
| uu____1721 -> begin
(failwith "Universe index out of bounds")
end)
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1725 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1725))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1729 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1729))
end
| FStar_Syntax_Syntax.U_unknown -> begin
u2
end
| FStar_Syntax_Syntax.U_name (uu____1732) -> begin
u2
end
| FStar_Syntax_Syntax.U_unif (uu____1733) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end)))
in (aux u)))


let find_let : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option = (fun lbs fvar1 -> (FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1764) -> begin
(failwith "find_let : impossible")
end
| FStar_Util.Inr (name) -> begin
(

let uu____1769 = (FStar_Syntax_Syntax.fv_eq name fvar1)
in (match (uu____1769) with
| true -> begin
FStar_Pervasives_Native.Some (lb)
end
| uu____1774 -> begin
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

let uu____2116 = (FStar_List.splitAt m targs)
in (match (uu____2116) with
| (uu____2152, targs') -> begin
(

let targs'1 = (FStar_List.map (fun targ l -> (

let uu____2243 = (

let uu____2246 = (map_append FStar_Pervasives_Native.fst args l)
in (FStar_List.rev uu____2246))
in (targ uu____2243))) targs')
in FStar_TypeChecker_NBETerm.Lam ((((fun l -> (

let uu____2280 = (map_append FStar_Pervasives_Native.fst args l)
in (f1 uu____2280)))), (targs'1), ((n1 - m)), (res))))
end))
end
| uu____2287 -> begin
(match ((Prims.op_Equality m n1)) with
| true -> begin
(

let uu____2291 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (f1 uu____2291))
end
| uu____2298 -> begin
(

let uu____2300 = (FStar_List.splitAt n1 args)
in (match (uu____2300) with
| (args1, args') -> begin
(

let uu____2347 = (

let uu____2348 = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (f1 uu____2348))
in (iapp cfg uu____2347 args'))
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
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2467))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2511 = (aux args us ts)
in (match (uu____2511) with
| (us', ts') -> begin
FStar_TypeChecker_NBETerm.Construct (((i), (us'), (ts')))
end)))
end
| FStar_TypeChecker_NBETerm.FV (i, us, ts) -> begin
(

let rec aux = (fun args1 us1 ts1 -> (match (args1) with
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2638))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2682 = (aux args us ts)
in (match (uu____2682) with
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
| uu____2804 -> begin
(match ((Prims.op_Equality ar (Prims.parse_int "0"))) with
| true -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), ((FStar_List.append acc args)), (ar), (ar_lst), (tr_lb)))
end
| uu____2835 -> begin
(

let full_args = (FStar_List.append acc args)
in (

let uu____2848 = (test_args full_args ar_lst)
in (match (uu____2848) with
| (can_unfold, args1, res) -> begin
(match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta))) with
| true -> begin
((debug cfg (fun uu____2865 -> (

let uu____2866 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Zeta is not set; will not unfold %s\n" uu____2866))));
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)));
)
end
| uu____2892 -> begin
(match (can_unfold) with
| true -> begin
((debug cfg (fun uu____2898 -> (

let uu____2899 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Beta reducing recursive function %s\n" uu____2899))));
(match (res) with
| [] -> begin
(

let uu____2906 = (

let uu____2907 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2907 lb))
in (iapp cfg uu____2906 args1))
end
| (uu____2910)::uu____2911 -> begin
(

let t = (

let uu____2927 = (

let uu____2928 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2928 lb))
in (iapp cfg uu____2927 args1))
in (iapp cfg t res))
end);
)
end
| uu____2931 -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)))
end)
end)
end)))
end)
end))
end
| FStar_TypeChecker_NBETerm.Quote (uu____2956) -> begin
(

let uu____2961 = (

let uu____2963 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2963))
in (failwith uu____2961))
end
| FStar_TypeChecker_NBETerm.Reflect (uu____2966) -> begin
(

let uu____2967 = (

let uu____2969 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2969))
in (failwith uu____2967))
end
| FStar_TypeChecker_NBETerm.Lazy (uu____2972) -> begin
(

let uu____2987 = (

let uu____2989 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2989))
in (failwith uu____2987))
end
| FStar_TypeChecker_NBETerm.Constant (uu____2992) -> begin
(

let uu____2993 = (

let uu____2995 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____2995))
in (failwith uu____2993))
end
| FStar_TypeChecker_NBETerm.Univ (uu____2998) -> begin
(

let uu____2999 = (

let uu____3001 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3001))
in (failwith uu____2999))
end
| FStar_TypeChecker_NBETerm.Type_t (uu____3004) -> begin
(

let uu____3005 = (

let uu____3007 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3007))
in (failwith uu____3005))
end
| FStar_TypeChecker_NBETerm.Unknown -> begin
(

let uu____3010 = (

let uu____3012 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3012))
in (failwith uu____3010))
end
| FStar_TypeChecker_NBETerm.Refinement (uu____3015) -> begin
(

let uu____3030 = (

let uu____3032 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3032))
in (failwith uu____3030))
end
| FStar_TypeChecker_NBETerm.Arrow (uu____3035) -> begin
(

let uu____3056 = (

let uu____3058 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.op_Hat "NBE ill-typed application: " uu____3058))
in (failwith uu____3056))
end))
and translate_fv : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs fvar1 -> (

let debug1 = (debug cfg)
in (

let qninfo = (

let uu____3075 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in (

let uu____3076 = (FStar_Syntax_Syntax.lid_of_fv fvar1)
in (FStar_TypeChecker_Env.lookup_qname uu____3075 uu____3076)))
in (

let uu____3077 = ((is_constr qninfo) || (is_constr_fv fvar1))
in (match (uu____3077) with
| true -> begin
(FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] [])
end
| uu____3084 -> begin
(

let uu____3086 = (FStar_TypeChecker_Normalize.should_unfold cfg (fun uu____3088 -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1 qninfo)
in (match (uu____3086) with
| FStar_TypeChecker_Normalize.Should_unfold_fully -> begin
(failwith "Not yet handled")
end
| FStar_TypeChecker_Normalize.Should_unfold_no -> begin
((debug1 (fun uu____3095 -> (

let uu____3096 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(1) Decided to not unfold %s\n" uu____3096))));
(

let uu____3099 = (FStar_TypeChecker_Cfg.find_prim_step cfg fvar1)
in (match (uu____3099) with
| FStar_Pervasives_Native.Some (prim_step) when prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok -> begin
(

let arity = (prim_step.FStar_TypeChecker_Cfg.arity + prim_step.FStar_TypeChecker_Cfg.univ_arity)
in ((debug1 (fun uu____3110 -> (

let uu____3111 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Found a primop %s\n" uu____3111))));
(

let uu____3114 = (

let uu____3145 = (

let f = (fun uu____3173 uu____3174 -> ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))
in (FStar_Common.tabulate arity f))
in (((fun args -> (

let args' = (FStar_List.map FStar_TypeChecker_NBETerm.as_arg args)
in (

let callbacks = {FStar_TypeChecker_NBETerm.iapp = (iapp cfg); FStar_TypeChecker_NBETerm.translate = (translate cfg bs)}
in (

let uu____3234 = (prim_step.FStar_TypeChecker_Cfg.interpretation_nbe callbacks args')
in (match (uu____3234) with
| FStar_Pervasives_Native.Some (x) -> begin
((debug1 (fun uu____3245 -> (

let uu____3246 = (FStar_Syntax_Print.fv_to_string fvar1)
in (

let uu____3248 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print2 "Primitive operator %s returned %s\n" uu____3246 uu____3248)))));
x;
)
end
| FStar_Pervasives_Native.None -> begin
((debug1 (fun uu____3256 -> (

let uu____3257 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Primitive operator %s failed\n" uu____3257))));
(

let uu____3260 = (FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
in (iapp cfg uu____3260 args'));
)
end)))))), (uu____3145), (arity), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____3114));
))
end
| FStar_Pervasives_Native.Some (uu____3268) -> begin
((debug1 (fun uu____3274 -> (

let uu____3275 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(2) Decided to not unfold %s\n" uu____3275))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end
| uu____3282 -> begin
((debug1 (fun uu____3290 -> (

let uu____3291 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(3) Decided to not unfold %s\n" uu____3291))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end));
)
end
| FStar_TypeChecker_Normalize.Should_unfold_reify -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3301; FStar_Syntax_Syntax.sigquals = uu____3302; FStar_Syntax_Syntax.sigmeta = uu____3303; FStar_Syntax_Syntax.sigattrs = uu____3304; FStar_Syntax_Syntax.sigopts = uu____3305}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3375 -> begin
((debug1 (fun uu____3380 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3390 -> (

let uu____3391 = (

let uu____3393 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3393))
in (

let uu____3394 = (

let uu____3396 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3396))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3391 uu____3394)))));
(debug1 (fun uu____3405 -> (

let uu____3406 = (

let uu____3408 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3408))
in (

let uu____3409 = (

let uu____3411 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3411))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3406 uu____3409)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3414 -> begin
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
end)
end
| FStar_TypeChecker_Normalize.Should_unfold_yes -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3422; FStar_Syntax_Syntax.sigquals = uu____3423; FStar_Syntax_Syntax.sigmeta = uu____3424; FStar_Syntax_Syntax.sigattrs = uu____3425; FStar_Syntax_Syntax.sigopts = uu____3426}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3496 -> begin
((debug1 (fun uu____3501 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3511 -> (

let uu____3512 = (

let uu____3514 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3514))
in (

let uu____3515 = (

let uu____3517 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3517))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3512 uu____3515)))));
(debug1 (fun uu____3526 -> (

let uu____3527 = (

let uu____3529 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3529))
in (

let uu____3530 = (

let uu____3532 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3532))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3527 uu____3530)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3535 -> begin
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
| uu____3580 -> begin
(

let uu____3583 = (

let uu____3614 = (FStar_List.map (fun uu____3639 _ts -> (FStar_All.pipe_left id1 ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))) us)
in (((fun us1 -> (translate cfg (FStar_List.rev_append us1 bs) lb.FStar_Syntax_Syntax.lbdef))), (uu____3614), ((FStar_List.length us)), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____3583))
end)))))
and mkRec' : (FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_TypeChecker_NBETerm.t)  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun callback b bs env -> (

let uu____3700 = (FStar_Syntax_Util.let_rec_arity b)
in (match (uu____3700) with
| (ar, maybe_lst) -> begin
(

let uu____3725 = (match (maybe_lst) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3745 = (FStar_Common.tabulate ar (fun uu____3751 -> true))
in ((ar), (uu____3745)))
end
| FStar_Pervasives_Native.Some (lst) -> begin
(

let l = (trim lst)
in (((FStar_List.length l)), (l)))
end)
in (match (uu____3725) with
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

let uu____3878 = (

let uu____3881 = (mkRec' callback lb lbs0 bs0)
in (uu____3881)::bs1)
in (aux lbs' lbs0 uu____3878 bs0))
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

let uu____3898 = (FStar_BigInt.big_int_of_string s)
in FStar_TypeChecker_NBETerm.Int (uu____3898))
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
| uu____3907 -> begin
(

let uu____3908 = (

let uu____3910 = (

let uu____3912 = (FStar_Syntax_Print.const_to_string c)
in (Prims.op_Hat uu____3912 ": Not yet implemented"))
in (Prims.op_Hat "Tm_constant " uu____3910))
in (failwith uu____3908))
end))
and translate : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs e -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____3936 -> (

let uu____3937 = (

let uu____3939 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____3939))
in (

let uu____3940 = (

let uu____3942 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.term_to_string uu____3942))
in (FStar_Util.print2 "Term: %s - %s\n" uu____3937 uu____3940)))));
(debug1 (fun uu____3949 -> (

let uu____3950 = (

let uu____3952 = (FStar_List.map (fun x -> (FStar_TypeChecker_NBETerm.t_to_string x)) bs)
in (FStar_String.concat ";; " uu____3952))
in (FStar_Util.print1 "BS list: %s\n" uu____3950))));
(

let uu____3961 = (

let uu____3962 = (FStar_Syntax_Subst.compress e)
in uu____3962.FStar_Syntax_Syntax.n)
in (match (uu____3961) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3965, uu____3966) -> begin
(failwith "Tm_delayed: Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_TypeChecker_NBETerm.Unknown
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____4005 = (translate_constant c)
in FStar_TypeChecker_NBETerm.Constant (uu____4005))
end
| FStar_Syntax_Syntax.Tm_bvar (db) -> begin
(match ((db.FStar_Syntax_Syntax.index < (FStar_List.length bs))) with
| true -> begin
(FStar_List.nth bs db.FStar_Syntax_Syntax.index)
end
| uu____4008 -> begin
(failwith "de Bruijn index out of bounds")
end)
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
((debug1 (fun uu____4024 -> (

let uu____4025 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____4027 = (

let uu____4029 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_All.pipe_right uu____4029 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n" uu____4025 uu____4027)))));
(

let uu____4040 = (translate cfg bs t)
in (

let uu____4041 = (FStar_List.map (fun x -> (

let uu____4045 = (

let uu____4046 = (translate_univ bs x)
in FStar_TypeChecker_NBETerm.Univ (uu____4046))
in (FStar_TypeChecker_NBETerm.as_arg uu____4045))) us)
in (iapp cfg uu____4040 uu____4041)));
)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____4048 = (translate_univ bs u)
in FStar_TypeChecker_NBETerm.Type_t (uu____4048))
end
| FStar_Syntax_Syntax.Tm_arrow (xs, c) -> begin
(

let uu____4071 = (

let uu____4092 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____4162 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____4162), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (((fun ys -> (translate_comp cfg (FStar_List.rev_append ys bs) c))), (uu____4092)))
in FStar_TypeChecker_NBETerm.Arrow (uu____4071))
end
| FStar_Syntax_Syntax.Tm_refine (bv, tm) -> begin
FStar_TypeChecker_NBETerm.Refinement ((((fun y -> (translate cfg ((y)::bs) tm))), ((fun uu____4231 -> (

let uu____4232 = (translate cfg bs bv.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_NBETerm.as_arg uu____4232))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____4234, uu____4235) -> begin
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
| FStar_Syntax_Syntax.Tm_abs ([], uu____4297, uu____4298) -> begin
(failwith "Impossible: abstraction with no binders")
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, resc) -> begin
(

let uu____4349 = (

let uu____4380 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____4450 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____4450), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (

let uu____4479 = (FStar_Util.map_opt resc (fun c uu____4491 -> (translate_residual_comp cfg bs c)))
in (((fun ys -> (translate cfg (FStar_List.rev_append ys bs) body))), (uu____4380), ((FStar_List.length xs)), (uu____4479))))
in FStar_TypeChecker_NBETerm.Lam (uu____4349))
end
| FStar_Syntax_Syntax.Tm_fvar (fvar1) -> begin
(translate_fv cfg bs fvar1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4525; FStar_Syntax_Syntax.vars = uu____4526}, (arg)::(more)::args) -> begin
(

let uu____4586 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4586) with
| (head1, uu____4604) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4648 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4648)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4657)); FStar_Syntax_Syntax.pos = uu____4658; FStar_Syntax_Syntax.vars = uu____4659}, (arg)::(more)::args) -> begin
(

let uu____4719 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4719) with
| (head1, uu____4737) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4781 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4781)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4790)); FStar_Syntax_Syntax.pos = uu____4791; FStar_Syntax_Syntax.vars = uu____4792}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.reifying -> begin
(

let cfg1 = (

let uu___651_4833 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___651_4833.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___651_4833.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___651_4833.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___651_4833.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___651_4833.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___651_4833.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___651_4833.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___651_4833.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4839)); FStar_Syntax_Syntax.pos = uu____4840; FStar_Syntax_Syntax.vars = uu____4841}, (arg)::[]) -> begin
(

let uu____4881 = (translate cfg bs (FStar_Pervasives_Native.fst arg))
in FStar_TypeChecker_NBETerm.Reflect (uu____4881))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4886; FStar_Syntax_Syntax.vars = uu____4887}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.reify_ -> begin
(

let cfg1 = (

let uu___674_4929 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___674_4929.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___674_4929.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___674_4929.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___674_4929.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___674_4929.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___674_4929.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___674_4929.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___674_4929.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = true})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug1 (fun uu____4968 -> (

let uu____4969 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____4971 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Application: %s @ %s\n" uu____4969 uu____4971)))));
(

let uu____4974 = (translate cfg bs head1)
in (

let uu____4975 = (FStar_List.map (fun x -> (

let uu____4997 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____4997), ((FStar_Pervasives_Native.snd x))))) args)
in (iapp cfg uu____4974 uu____4975)));
)
end
| FStar_Syntax_Syntax.Tm_match (scrut, branches) -> begin
(

let make_branches = (fun readback1 -> (

let cfg1 = (

let uu___690_5058 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___692_5061 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___692_5061.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___692_5061.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = false; FStar_TypeChecker_Cfg.weak = uu___692_5061.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___692_5061.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___692_5061.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___692_5061.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___692_5061.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___692_5061.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___692_5061.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___692_5061.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___692_5061.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___692_5061.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___692_5061.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___692_5061.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___692_5061.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___692_5061.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___692_5061.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___692_5061.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___692_5061.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___692_5061.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___692_5061.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___692_5061.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___692_5061.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___692_5061.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___692_5061.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___690_5058.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___690_5058.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___690_5058.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___690_5058.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___690_5058.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___690_5058.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___690_5058.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___690_5058.FStar_TypeChecker_Cfg.reifying})
in (

let rec process_pattern = (fun bs1 p -> (

let uu____5090 = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
((bs1), (FStar_Syntax_Syntax.Pat_constant (c)))
end
| FStar_Syntax_Syntax.Pat_cons (fvar1, args) -> begin
(

let uu____5126 = (FStar_List.fold_left (fun uu____5167 uu____5168 -> (match (((uu____5167), (uu____5168))) with
| ((bs2, args1), (arg, b)) -> begin
(

let uu____5260 = (process_pattern bs2 arg)
in (match (uu____5260) with
| (bs', arg') -> begin
((bs'), ((((arg'), (b)))::args1))
end))
end)) ((bs1), ([])) args)
in (match (uu____5126) with
| (bs', args') -> begin
((bs'), (FStar_Syntax_Syntax.Pat_cons (((fvar1), ((FStar_List.rev args'))))))
end))
end
| FStar_Syntax_Syntax.Pat_var (bvar) -> begin
(

let x = (

let uu____5359 = (

let uu____5360 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5360))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5359))
in (

let uu____5361 = (

let uu____5364 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____5364)::bs1)
in ((uu____5361), (FStar_Syntax_Syntax.Pat_var (x)))))
end
| FStar_Syntax_Syntax.Pat_wild (bvar) -> begin
(

let x = (

let uu____5369 = (

let uu____5370 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5370))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5369))
in (

let uu____5371 = (

let uu____5374 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____5374)::bs1)
in ((uu____5371), (FStar_Syntax_Syntax.Pat_wild (x)))))
end
| FStar_Syntax_Syntax.Pat_dot_term (bvar, tm) -> begin
(

let x = (

let uu____5384 = (

let uu____5385 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5385))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5384))
in (

let uu____5386 = (

let uu____5387 = (

let uu____5394 = (

let uu____5397 = (translate cfg1 bs1 tm)
in (readback1 uu____5397))
in ((x), (uu____5394)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____5387))
in ((bs1), (uu____5386))))
end)
in (match (uu____5090) with
| (bs2, p_new) -> begin
((bs2), ((

let uu___730_5417 = p
in {FStar_Syntax_Syntax.v = p_new; FStar_Syntax_Syntax.p = uu___730_5417.FStar_Syntax_Syntax.p})))
end)))
in (FStar_List.map (fun uu____5436 -> (match (uu____5436) with
| (pat, when_clause, e1) -> begin
(

let uu____5458 = (process_pattern bs pat)
in (match (uu____5458) with
| (bs', pat') -> begin
(

let uu____5471 = (

let uu____5472 = (

let uu____5475 = (translate cfg1 bs' e1)
in (readback1 uu____5475))
in ((pat'), (when_clause), (uu____5472)))
in (FStar_Syntax_Util.branch uu____5471))
end))
end)) branches))))
in (

let rec case = (fun scrut1 -> ((debug1 (fun uu____5497 -> (

let uu____5498 = (

let uu____5500 = (readback cfg scrut1)
in (FStar_Syntax_Print.term_to_string uu____5500))
in (

let uu____5501 = (FStar_TypeChecker_NBETerm.t_to_string scrut1)
in (FStar_Util.print2 "Match case: (%s) -- (%s)\n" uu____5498 uu____5501)))));
(

let scrut2 = (unlazy scrut1)
in (match (scrut2) with
| FStar_TypeChecker_NBETerm.Construct (c, us, args) -> begin
((debug1 (fun uu____5529 -> (

let uu____5530 = (

let uu____5532 = (FStar_All.pipe_right args (FStar_List.map (fun uu____5558 -> (match (uu____5558) with
| (x, q) -> begin
(

let uu____5572 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (Prims.op_Hat (match ((FStar_Util.is_some q)) with
| true -> begin
"#"
end
| uu____5577 -> begin
""
end) uu____5572))
end))))
in (FStar_All.pipe_right uu____5532 (FStar_String.concat "; ")))
in (FStar_Util.print1 "Match args: %s\n" uu____5530))));
(

let uu____5586 = (pickBranch cfg scrut2 branches)
in (match (uu____5586) with
| FStar_Pervasives_Native.Some (branch1, args1) -> begin
(

let uu____5607 = (FStar_List.fold_left (fun bs1 x -> (x)::bs1) bs args1)
in (translate cfg uu____5607 branch1))
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
)
end
| FStar_TypeChecker_NBETerm.Constant (c) -> begin
((debug1 (fun uu____5630 -> (

let uu____5631 = (FStar_TypeChecker_NBETerm.t_to_string scrut2)
in (FStar_Util.print1 "Match constant : %s\n" uu____5631))));
(

let uu____5634 = (pickBranch cfg scrut2 branches)
in (match (uu____5634) with
| FStar_Pervasives_Native.Some (branch1, []) -> begin
(translate cfg bs branch1)
end
| FStar_Pervasives_Native.Some (branch1, (arg)::[]) -> begin
(translate cfg ((arg)::bs) branch1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end
| FStar_Pervasives_Native.Some (uu____5668, (hd1)::tl1) -> begin
(failwith "Impossible: Matching on constants cannot bind more than one variable")
end));
)
end
| uu____5682 -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
))
in (

let uu____5683 = (translate cfg bs scrut)
in (case uu____5683))))
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

let uu____5762 = (make_rec_env (translate_letbinding cfg) lbs bs)
in (translate cfg uu____5762 body))
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____5766) -> begin
(translate cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let close1 = (fun t -> (

let bvs = (FStar_List.map (fun uu____5787 -> (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)) bs)
in (

let s1 = (FStar_List.mapi (fun i bv -> FStar_Syntax_Syntax.DB (((i), (bv)))) bvs)
in (

let s2 = (

let uu____5800 = (FStar_List.zip bvs bs)
in (FStar_List.map (fun uu____5815 -> (match (uu____5815) with
| (bv, t1) -> begin
(

let uu____5822 = (

let uu____5829 = (readback cfg t1)
in ((bv), (uu____5829)))
in FStar_Syntax_Syntax.NT (uu____5822))
end)) uu____5800))
in (

let uu____5834 = (FStar_Syntax_Subst.subst s1 t)
in (FStar_Syntax_Subst.subst s2 uu____5834))))))
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

let f = (fun uu____5843 -> (

let t = (FStar_Syntax_Util.unfold_lazy li)
in ((debug1 (fun uu____5850 -> (

let uu____5851 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n" uu____5851))));
(translate cfg bs t);
)))
in (

let uu____5854 = (

let uu____5869 = (FStar_Thunk.mk f)
in ((FStar_Util.Inl (li)), (uu____5869)))
in FStar_TypeChecker_NBETerm.Lazy (uu____5854)))
end));
)))
and translate_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_NBETerm.comp = (fun cfg bs c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (typ, u) -> begin
(

let uu____5901 = (

let uu____5908 = (translate cfg bs typ)
in (

let uu____5909 = (fmap_opt (translate_univ bs) u)
in ((uu____5908), (uu____5909))))
in FStar_TypeChecker_NBETerm.Tot (uu____5901))
end
| FStar_Syntax_Syntax.GTotal (typ, u) -> begin
(

let uu____5924 = (

let uu____5931 = (translate cfg bs typ)
in (

let uu____5932 = (fmap_opt (translate_univ bs) u)
in ((uu____5931), (uu____5932))))
in FStar_TypeChecker_NBETerm.GTot (uu____5924))
end
| FStar_Syntax_Syntax.Comp (ctyp) -> begin
(

let uu____5938 = (translate_comp_typ cfg bs ctyp)
in FStar_TypeChecker_NBETerm.Comp (uu____5938))
end))
and readback_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg c -> (

let c' = (match (c) with
| FStar_TypeChecker_NBETerm.Tot (typ, u) -> begin
(

let uu____5948 = (

let uu____5957 = (readback cfg typ)
in ((uu____5957), (u)))
in FStar_Syntax_Syntax.Total (uu____5948))
end
| FStar_TypeChecker_NBETerm.GTot (typ, u) -> begin
(

let uu____5970 = (

let uu____5979 = (readback cfg typ)
in ((uu____5979), (u)))
in FStar_Syntax_Syntax.GTotal (uu____5970))
end
| FStar_TypeChecker_NBETerm.Comp (ctyp) -> begin
(

let uu____5987 = (readback_comp_typ cfg ctyp)
in FStar_Syntax_Syntax.Comp (uu____5987))
end)
in (FStar_Syntax_Syntax.mk c' FStar_Pervasives_Native.None FStar_Range.dummyRange)))
and translate_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_TypeChecker_NBETerm.comp_typ = (fun cfg bs c -> (

let uu____5993 = c
in (match (uu____5993) with
| {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags} -> begin
(

let uu____6013 = (FStar_List.map (translate_univ bs) comp_univs)
in (

let uu____6014 = (translate cfg bs result_typ)
in (

let uu____6015 = (FStar_List.map (fun x -> (

let uu____6043 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____6043), ((FStar_Pervasives_Native.snd x))))) effect_args)
in (

let uu____6050 = (FStar_List.map (translate_flag cfg bs) flags)
in {FStar_TypeChecker_NBETerm.comp_univs = uu____6013; FStar_TypeChecker_NBETerm.effect_name = effect_name; FStar_TypeChecker_NBETerm.result_typ = uu____6014; FStar_TypeChecker_NBETerm.effect_args = uu____6015; FStar_TypeChecker_NBETerm.flags = uu____6050}))))
end)))
and readback_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun cfg c -> (

let uu____6055 = (readback cfg c.FStar_TypeChecker_NBETerm.result_typ)
in (

let uu____6058 = (FStar_List.map (fun x -> (

let uu____6084 = (readback cfg (FStar_Pervasives_Native.fst x))
in ((uu____6084), ((FStar_Pervasives_Native.snd x))))) c.FStar_TypeChecker_NBETerm.effect_args)
in (

let uu____6085 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags)
in {FStar_Syntax_Syntax.comp_univs = c.FStar_TypeChecker_NBETerm.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_TypeChecker_NBETerm.effect_name; FStar_Syntax_Syntax.result_typ = uu____6055; FStar_Syntax_Syntax.effect_args = uu____6058; FStar_Syntax_Syntax.flags = uu____6085}))))
and translate_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.residual_comp  ->  FStar_TypeChecker_NBETerm.residual_comp = (fun cfg bs c -> (

let uu____6093 = c
in (match (uu____6093) with
| {FStar_Syntax_Syntax.residual_effect = residual_effect; FStar_Syntax_Syntax.residual_typ = residual_typ; FStar_Syntax_Syntax.residual_flags = residual_flags} -> begin
(

let uu____6103 = (FStar_Util.map_opt residual_typ (translate cfg bs))
in (

let uu____6108 = (FStar_List.map (translate_flag cfg bs) residual_flags)
in {FStar_TypeChecker_NBETerm.residual_effect = residual_effect; FStar_TypeChecker_NBETerm.residual_typ = uu____6103; FStar_TypeChecker_NBETerm.residual_flags = uu____6108}))
end)))
and readback_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.residual_comp  ->  FStar_Syntax_Syntax.residual_comp = (fun cfg c -> (

let uu____6113 = (FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ (readback cfg))
in (

let uu____6120 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = c.FStar_TypeChecker_NBETerm.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6113; FStar_Syntax_Syntax.residual_flags = uu____6120})))
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

let uu____6131 = (translate cfg bs tm)
in FStar_TypeChecker_NBETerm.DECREASES (uu____6131))
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

let uu____6135 = (readback cfg t)
in FStar_Syntax_Syntax.DECREASES (uu____6135))
end))
and translate_monadic : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____6138 cfg bs e -> (match (uu____6138) with
| (m, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let uu____6176 = (

let uu____6185 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv m)
in (FStar_TypeChecker_Env.effect_decl_opt cfg.FStar_TypeChecker_Cfg.tcenv uu____6185))
in (match (uu____6176) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6192 = (

let uu____6194 = (FStar_Ident.string_of_lid m)
in (FStar_Util.format1 "Effect declaration not found: %s" uu____6194))
in (failwith uu____6192))
end
| FStar_Pervasives_Native.Some (ed, q) -> begin
(

let cfg' = (

let uu___938_6210 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___938_6210.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___938_6210.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___938_6210.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___938_6210.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___938_6210.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___938_6210.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___938_6210.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___938_6210.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let body_lam = (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (ty); FStar_Syntax_Syntax.residual_flags = []}
in (

let uu____6218 = (

let uu____6225 = (

let uu____6226 = (

let uu____6245 = (

let uu____6254 = (

let uu____6261 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____6261), (FStar_Pervasives_Native.None)))
in (uu____6254)::[])
in ((uu____6245), (body), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____6226))
in (FStar_Syntax_Syntax.mk uu____6225))
in (uu____6218 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos)))
in (

let maybe_range_arg = (

let uu____6295 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____6295) with
| true -> begin
(

let uu____6304 = (

let uu____6309 = (

let uu____6310 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (translate cfg [] uu____6310))
in ((uu____6309), (FStar_Pervasives_Native.None)))
in (

let uu____6311 = (

let uu____6318 = (

let uu____6323 = (

let uu____6324 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range body.FStar_Syntax_Syntax.pos body.FStar_Syntax_Syntax.pos)
in (translate cfg [] uu____6324))
in ((uu____6323), (FStar_Pervasives_Native.None)))
in (uu____6318)::[])
in (uu____6304)::uu____6311))
end
| uu____6337 -> begin
[]
end))
in (

let t = (

let uu____6344 = (

let uu____6345 = (

let uu____6346 = (

let uu____6347 = (

let uu____6348 = (

let uu____6355 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr)
in (FStar_All.pipe_right uu____6355 FStar_Util.must))
in (FStar_All.pipe_right uu____6348 FStar_Pervasives_Native.snd))
in (FStar_Syntax_Util.un_uinst uu____6347))
in (translate cfg' [] uu____6346))
in (iapp cfg uu____6345 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::(((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____6388 = (

let uu____6389 = (

let uu____6396 = (

let uu____6401 = (translate cfg' bs lb.FStar_Syntax_Syntax.lbtyp)
in ((uu____6401), (FStar_Pervasives_Native.None)))
in (

let uu____6402 = (

let uu____6409 = (

let uu____6414 = (translate cfg' bs ty)
in ((uu____6414), (FStar_Pervasives_Native.None)))
in (uu____6409)::[])
in (uu____6396)::uu____6402))
in (

let uu____6427 = (

let uu____6434 = (

let uu____6441 = (

let uu____6448 = (

let uu____6453 = (translate cfg bs lb.FStar_Syntax_Syntax.lbdef)
in ((uu____6453), (FStar_Pervasives_Native.None)))
in (

let uu____6454 = (

let uu____6461 = (

let uu____6468 = (

let uu____6473 = (translate cfg bs body_lam)
in ((uu____6473), (FStar_Pervasives_Native.None)))
in (uu____6468)::[])
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6461)
in (uu____6448)::uu____6454))
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6441)
in (FStar_List.append maybe_range_arg uu____6434))
in (FStar_List.append uu____6389 uu____6427)))
in (iapp cfg uu____6344 uu____6388)))
in ((debug cfg (fun uu____6505 -> (

let uu____6506 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic: %s\n" uu____6506))));
t;
)))))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6509)); FStar_Syntax_Syntax.pos = uu____6510; FStar_Syntax_Syntax.vars = uu____6511}, ((e2, uu____6513))::[]) -> begin
(translate (

let uu___960_6554 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___960_6554.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___960_6554.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___960_6554.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___960_6554.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___960_6554.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___960_6554.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___960_6554.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___960_6554.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug cfg (fun uu____6586 -> (

let uu____6587 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____6589 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "translate_monadic app (%s) @ (%s)\n" uu____6587 uu____6589)))));
(

let fallback1 = (fun uu____6597 -> (translate cfg bs e1))
in (

let fallback2 = (fun uu____6603 -> (

let uu____6604 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_monadic (((m), (ty))))))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___972_6611 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___972_6611.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___972_6611.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___972_6611.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___972_6611.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___972_6611.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___972_6611.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___972_6611.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___972_6611.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs uu____6604)))
in (

let uu____6613 = (

let uu____6614 = (FStar_Syntax_Util.un_uinst head1)
in uu____6614.FStar_Syntax_Syntax.n)
in (match (uu____6613) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____6620 = (

let uu____6622 = (FStar_TypeChecker_Env.is_action cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (not (uu____6622)))
in (match (uu____6620) with
| true -> begin
(fallback1 ())
end
| uu____6625 -> begin
(

let uu____6627 = (

let uu____6629 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (FStar_Option.isNone uu____6629))
in (match (uu____6627) with
| true -> begin
(fallback2 ())
end
| uu____6641 -> begin
(

let e2 = (

let uu____6646 = (

let uu____6651 = (FStar_Syntax_Util.mk_reify head1)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6651 args))
in (uu____6646 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (translate (

let uu___981_6654 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___981_6654.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___981_6654.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___981_6654.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___981_6654.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___981_6654.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___981_6654.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___981_6654.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___981_6654.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2))
end))
end))))
end
| uu____6656 -> begin
(fallback1 ())
end))));
)
end
| FStar_Syntax_Syntax.Tm_match (sc, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____6777 -> (match (uu____6777) with
| (pat, wopt, tm) -> begin
(

let uu____6825 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____6825)))
end))))
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), (branches1)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___994_6859 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___994_6859.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___994_6859.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___994_6859.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___994_6859.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___994_6859.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___994_6859.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___994_6859.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___994_6859.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs tm)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____6862)) -> begin
(translate_monadic ((m), (ty)) cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty')) -> begin
(translate_monadic_lift ((msrc), (mtgt), (ty')) cfg bs e1)
end
| uu____6889 -> begin
(

let uu____6890 = (

let uu____6892 = (FStar_Syntax_Print.tag_of_term e1)
in (FStar_Util.format1 "Unexpected case in translate_monadic: %s" uu____6892))
in (failwith uu____6890))
end))
end))
and translate_monadic_lift : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____6895 cfg bs e -> (match (uu____6895) with
| (msrc, mtgt, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (

let uu____6919 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____6919) with
| true -> begin
(

let ed = (

let uu____6923 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl cfg.FStar_TypeChecker_Cfg.tcenv uu____6923))
in (

let ret1 = (

let uu____6925 = (

let uu____6926 = (

let uu____6929 = (

let uu____6930 = (

let uu____6937 = (FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr)
in (FStar_All.pipe_right uu____6937 FStar_Util.must))
in (FStar_All.pipe_right uu____6930 FStar_Pervasives_Native.snd))
in (FStar_Syntax_Subst.compress uu____6929))
in uu____6926.FStar_Syntax_Syntax.n)
in (match (uu____6925) with
| FStar_Syntax_Syntax.Tm_uinst (ret1, (uu____6983)::[]) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((ret1), ((FStar_Syntax_Syntax.U_unknown)::[])))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
end
| uu____6990 -> begin
(failwith "NYI: Reification of indexed effect (NBE)")
end))
in (

let cfg' = (

let uu___1027_6993 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1027_6993.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1027_6993.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1027_6993.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1027_6993.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1027_6993.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1027_6993.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1027_6993.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1027_6993.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____6996 = (

let uu____6997 = (translate cfg' [] ret1)
in (iapp cfg' uu____6997 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____7006 = (

let uu____7007 = (

let uu____7012 = (translate cfg' bs ty)
in ((uu____7012), (FStar_Pervasives_Native.None)))
in (

let uu____7013 = (

let uu____7020 = (

let uu____7025 = (translate cfg' bs e1)
in ((uu____7025), (FStar_Pervasives_Native.None)))
in (uu____7020)::[])
in (uu____7007)::uu____7013))
in (iapp cfg' uu____6996 uu____7006)))
in ((debug cfg (fun uu____7041 -> (

let uu____7042 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(1): %s\n" uu____7042))));
t;
)))))
end
| uu____7045 -> begin
(

let uu____7047 = (FStar_TypeChecker_Env.monad_leq cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt)
in (match (uu____7047) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7050 = (

let uu____7052 = (FStar_Ident.text_of_lid msrc)
in (

let uu____7054 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____7052 uu____7054)))
in (failwith uu____7050))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____7057; FStar_TypeChecker_Env.mtarget = uu____7058; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____7059; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____7079 = (

let uu____7081 = (FStar_Ident.text_of_lid msrc)
in (

let uu____7083 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____7081 uu____7083)))
in (failwith uu____7079))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____7086; FStar_TypeChecker_Env.mtarget = uu____7087; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____7088; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let lift_lam = (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let uu____7122 = (

let uu____7125 = (FStar_Syntax_Syntax.bv_to_name x)
in (lift FStar_Syntax_Syntax.U_unknown ty uu____7125))
in (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) uu____7122 FStar_Pervasives_Native.None)))
in (

let cfg' = (

let uu___1051_7141 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___1051_7141.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___1051_7141.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1051_7141.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1051_7141.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1051_7141.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1051_7141.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1051_7141.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1051_7141.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____7144 = (translate cfg' [] lift_lam)
in (

let uu____7145 = (

let uu____7146 = (

let uu____7151 = (translate cfg bs e1)
in ((uu____7151), (FStar_Pervasives_Native.None)))
in (uu____7146)::[])
in (iapp cfg uu____7144 uu____7145)))
in ((debug cfg (fun uu____7163 -> (

let uu____7164 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(2): %s\n" uu____7164))));
t;
))))
end))
end)))
end))
and readback : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.term = (fun cfg x -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____7182 -> (

let uu____7183 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print1 "Readback: %s\n" uu____7183))));
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

let uu____7191 = (FStar_BigInt.string_of_big_int i)
in (FStar_All.pipe_right uu____7191 FStar_Syntax_Util.exp_int))
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

let uu____7251 = (FStar_List.fold_left (fun uu____7294 tf -> (match (uu____7294) with
| (args_rev, accus_rev) -> begin
(

let uu____7346 = (tf accus_rev)
in (match (uu____7346) with
| (xt, q) -> begin
(

let x1 = (

let uu____7366 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7366))
in (

let uu____7367 = (

let uu____7370 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____7370)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____7367))))
end))
end)) (([]), ([])) targs)
in (match (uu____7251) with
| (args_rev, accus_rev) -> begin
(

let body = (

let uu____7414 = (f (FStar_List.rev accus_rev))
in (readback cfg uu____7414))
in (

let uu____7415 = (FStar_Util.map_opt resc (fun thunk1 -> (

let uu____7426 = (thunk1 ())
in (readback_residual_comp cfg uu____7426))))
in (FStar_Syntax_Util.abs (FStar_List.rev args_rev) body uu____7415)))
end))
end
| FStar_TypeChecker_NBETerm.Refinement (f, targ) -> begin
(

let x1 = (

let uu____7454 = (

let uu____7455 = (

let uu____7456 = (targ ())
in (FStar_Pervasives_Native.fst uu____7456))
in (readback cfg uu____7455))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7454))
in (

let body = (

let uu____7462 = (

let uu____7463 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (f uu____7463))
in (readback cfg uu____7462))
in (FStar_Syntax_Util.refine x1 body)))
end
| FStar_TypeChecker_NBETerm.Reflect (t) -> begin
(

let tm = (readback cfg t)
in (FStar_Syntax_Util.mk_reflect tm))
end
| FStar_TypeChecker_NBETerm.Arrow (f, targs) -> begin
(

let uu____7500 = (FStar_List.fold_left (fun uu____7543 tf -> (match (uu____7543) with
| (args_rev, accus_rev) -> begin
(

let uu____7595 = (tf accus_rev)
in (match (uu____7595) with
| (xt, q) -> begin
(

let x1 = (

let uu____7615 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7615))
in (

let uu____7616 = (

let uu____7619 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____7619)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____7616))))
end))
end)) (([]), ([])) targs)
in (match (uu____7500) with
| (args_rev, accus_rev) -> begin
(

let cmp = (

let uu____7663 = (f (FStar_List.rev accus_rev))
in (readback_comp cfg uu____7663))
in (FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp))
end))
end
| FStar_TypeChecker_NBETerm.Construct (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7706 -> (match (uu____7706) with
| (x1, q) -> begin
(

let uu____7717 = (readback cfg x1)
in ((uu____7717), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7736 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7743)::uu____7744 -> begin
(

let uu____7747 = (

let uu____7750 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7750 (FStar_List.rev us)))
in (apply1 uu____7747))
end
| [] -> begin
(

let uu____7751 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7751))
end)))
end
| FStar_TypeChecker_NBETerm.FV (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7792 -> (match (uu____7792) with
| (x1, q) -> begin
(

let uu____7803 = (readback cfg x1)
in ((uu____7803), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7822 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7829)::uu____7830 -> begin
(

let uu____7833 = (

let uu____7836 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7836 (FStar_List.rev us)))
in (apply1 uu____7833))
end
| [] -> begin
(

let uu____7837 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7837))
end)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), []) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), ts) -> begin
(

let args = (map_rev (fun uu____7884 -> (match (uu____7884) with
| (x1, q) -> begin
(

let uu____7895 = (readback cfg x1)
in ((uu____7895), (q)))
end)) ts)
in (

let uu____7896 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Util.mk_app uu____7896 args)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Match (scrut, cases, make_branches), ts) -> begin
(

let args = (map_rev (fun uu____7956 -> (match (uu____7956) with
| (x1, q) -> begin
(

let uu____7967 = (readback cfg x1)
in ((uu____7967), (q)))
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
| uu____7997 -> begin
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

let args1 = (map_rev (fun uu____8084 -> (match (uu____8084) with
| (x1, q) -> begin
(

let uu____8095 = (readback cfg x1)
in ((uu____8095), (q)))
end)) args)
in (match (args1) with
| [] -> begin
head1
end
| uu____8100 -> begin
(FStar_Syntax_Util.mk_app head1 args1)
end)))
end
| FStar_TypeChecker_NBETerm.Quote (qt, qi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl (li), uu____8112) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (li)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (uu____8129, thunk1) -> begin
(

let uu____8151 = (FStar_Thunk.force thunk1)
in (readback cfg uu____8151))
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
| uu____8180 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____8192 -> begin
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
| uu____8213 -> begin
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
| uu____8240 -> begin
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
| uu____8264 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____8275 -> begin
false
end))


let step_as_normalizer_step : step  ->  FStar_TypeChecker_Env.step = (fun uu___1_8282 -> (match (uu___1_8282) with
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

let uu___1249_8321 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1251_8324 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1251_8324.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1251_8324.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1251_8324.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1251_8324.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1251_8324.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1251_8324.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1251_8324.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1251_8324.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1251_8324.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1251_8324.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1251_8324.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1251_8324.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1251_8324.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1251_8324.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1251_8324.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1251_8324.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___1251_8324.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1251_8324.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1251_8324.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1251_8324.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1251_8324.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1251_8324.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1251_8324.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1251_8324.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1251_8324.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1249_8321.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1249_8321.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1249_8321.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1249_8321.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1249_8321.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1249_8321.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1249_8321.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1249_8321.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____8329 -> (

let uu____8330 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8330))));
(

let r = (

let uu____8334 = (translate cfg1 [] e)
in (readback cfg1 uu____8334))
in ((debug cfg1 (fun uu____8338 -> (

let uu____8339 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8339))));
r;
));
))))


let normalize_for_unit_test : FStar_TypeChecker_Env.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun steps env e -> (

let cfg = (FStar_TypeChecker_Cfg.config steps env)
in (

let cfg1 = (

let uu___1266_8364 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___1268_8367 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___1268_8367.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___1268_8367.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___1268_8367.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___1268_8367.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___1268_8367.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___1268_8367.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___1268_8367.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___1268_8367.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___1268_8367.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___1268_8367.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___1268_8367.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___1268_8367.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___1268_8367.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___1268_8367.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___1268_8367.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___1268_8367.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___1268_8367.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___1268_8367.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___1268_8367.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___1268_8367.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___1268_8367.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___1268_8367.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___1268_8367.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___1268_8367.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___1268_8367.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___1266_8364.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___1266_8364.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___1266_8364.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___1266_8364.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___1266_8364.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___1266_8364.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___1266_8364.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___1266_8364.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____8372 -> (

let uu____8373 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8373))));
(

let r = (

let uu____8377 = (translate cfg1 [] e)
in (readback cfg1 uu____8377))
in ((debug cfg1 (fun uu____8381 -> (

let uu____8382 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8382))));
r;
));
))))




