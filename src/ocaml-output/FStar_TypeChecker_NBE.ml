
open Prims
open FStar_Pervasives

let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun a b -> (match ((a > b)) with
| true -> begin
a
end
| uu____18 -> begin
b
end))


let map_rev : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list = (fun f l -> (

let rec aux = (fun l1 acc -> (match (l1) with
| [] -> begin
acc
end
| (x)::xs -> begin
(

let uu____79 = (

let uu____82 = (f x)
in (uu____82)::acc)
in (aux xs uu____79))
end))
in (aux l [])))


let map_rev_append : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list  ->  'b Prims.list = (fun f l1 l2 -> (

let rec aux = (fun l acc -> (match (l) with
| [] -> begin
l2
end
| (x)::xs -> begin
(

let uu____153 = (

let uu____156 = (f x)
in (uu____156)::acc)
in (aux xs uu____153))
end))
in (aux l1 l2)))


let rec map_append : 'a 'b . ('a  ->  'b)  ->  'a Prims.list  ->  'b Prims.list  ->  'b Prims.list = (fun f l1 l2 -> (match (l1) with
| [] -> begin
l2
end
| (x)::xs -> begin
(

let uu____206 = (f x)
in (

let uu____207 = (map_append f xs l2)
in (uu____206)::uu____207))
end))


let rec drop : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list = (fun p l -> (match (l) with
| [] -> begin
[]
end
| (x)::xs -> begin
(

let uu____246 = (p x)
in (match (uu____246) with
| true -> begin
(x)::xs
end
| uu____251 -> begin
(drop p xs)
end))
end))


let fmap_opt : 'a 'b . ('a  ->  'b)  ->  'a FStar_Pervasives_Native.option  ->  'b FStar_Pervasives_Native.option = (fun f x -> (FStar_Util.bind_opt x (fun x1 -> (

let uu____288 = (f x1)
in FStar_Pervasives_Native.Some (uu____288)))))


let drop_until : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list = (fun f l -> (

let rec aux = (fun l1 -> (match (l1) with
| [] -> begin
[]
end
| (x)::xs -> begin
(

let uu____338 = (f x)
in (match (uu____338) with
| true -> begin
l1
end
| uu____343 -> begin
(aux xs)
end))
end))
in (aux l)))


let trim : Prims.bool Prims.list  ->  Prims.bool Prims.list = (fun l -> (

let uu____363 = (drop_until FStar_Pervasives.id (FStar_List.rev l))
in (FStar_List.rev uu____363)))


let implies : Prims.bool  ->  Prims.bool  ->  Prims.bool = (fun b1 b2 -> (match (((b1), (b2))) with
| (false, uu____390) -> begin
true
end
| (true, b21) -> begin
b21
end))


let debug : FStar_TypeChecker_Cfg.cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (

let uu____417 = (

let uu____419 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in (FStar_TypeChecker_Env.debug uu____419 (FStar_Options.Other ("NBE"))))
in (match (uu____417) with
| true -> begin
(f ())
end
| uu____422 -> begin
()
end)))


let debug_term : FStar_Syntax_Syntax.term  ->  unit = (fun t -> (

let uu____430 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "%s\n" uu____430)))


let debug_sigmap : FStar_Syntax_Syntax.sigelt FStar_Util.smap  ->  unit = (fun m -> (FStar_Util.smap_fold m (fun k v1 u -> (

let uu____451 = (FStar_Syntax_Print.sigelt_to_string_short v1)
in (FStar_Util.print2 "%s -> %%s\n" k uu____451))) ()))


let unlazy : FStar_TypeChecker_NBETerm.t  ->  FStar_TypeChecker_NBETerm.t = (fun t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (uu____460, t1) -> begin
(FStar_Common.force_thunk t1)
end
| t1 -> begin
t1
end))


let pickBranch : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_NBETerm.t Prims.list) FStar_Pervasives_Native.option = (fun cfg scrut branches -> (

let rec pickBranch_aux = (fun scrut1 branches1 branches0 -> (

let rec matches_pat = (fun scrutinee0 p -> ((debug cfg (fun uu____628 -> (

let uu____629 = (FStar_TypeChecker_NBETerm.t_to_string scrutinee0)
in (

let uu____631 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "matches_pat (%s, %s)\n" uu____629 uu____631)))));
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____658) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let matches_const = (fun c s1 -> ((debug cfg (fun uu____685 -> (

let uu____686 = (FStar_TypeChecker_NBETerm.t_to_string c)
in (

let uu____688 = (FStar_Syntax_Print.const_to_string s1)
in (FStar_Util.print2 "Testing term %s against pattern %s\n" uu____686 uu____688)))));
(match (c) with
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit) -> begin
(Prims.op_Equality s1 FStar_Const.Const_unit)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Bool (b)) -> begin
(match (s1) with
| FStar_Const.Const_bool (p1) -> begin
(Prims.op_Equality b p1)
end
| uu____698 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i)) -> begin
(match (s1) with
| FStar_Const.Const_int (p1, FStar_Pervasives_Native.None) -> begin
(

let uu____715 = (FStar_BigInt.big_int_of_string p1)
in (Prims.op_Equality i uu____715))
end
| uu____716 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.String (st, uu____719)) -> begin
(match (s1) with
| FStar_Const.Const_string (p1, uu____724) -> begin
(Prims.op_Equality st p1)
end
| uu____728 -> begin
false
end)
end
| FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Char (c1)) -> begin
(match (s1) with
| FStar_Const.Const_char (p1) -> begin
(Prims.op_Equality c1 p1)
end
| uu____736 -> begin
false
end)
end
| uu____738 -> begin
false
end);
))
in (

let uu____740 = (matches_const scrutinee s)
in (match (uu____740) with
| true -> begin
FStar_Util.Inl ([])
end
| uu____753 -> begin
FStar_Util.Inr (false)
end)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let rec matches_args = (fun out a p1 -> (match (((a), (p1))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, uu____878))::rest_a, ((p2, uu____881))::rest_p) -> begin
(

let uu____920 = (matches_pat t p2)
in (match (uu____920) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____949 -> begin
FStar_Util.Inr (false)
end))
in (match (scrutinee) with
| FStar_TypeChecker_NBETerm.Construct (fv', _us, args_rev) -> begin
(

let uu____997 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (match (uu____997) with
| true -> begin
(matches_args [] (FStar_List.rev args_rev) arg_pats)
end
| uu____1011 -> begin
FStar_Util.Inr (false)
end))
end
| uu____1017 -> begin
FStar_Util.Inr (true)
end))
end)
in (

let res_to_string = (fun uu___262_1035 -> (match (uu___262_1035) with
| FStar_Util.Inr (b) -> begin
(

let uu____1049 = (FStar_Util.string_of_bool b)
in (Prims.strcat "Inr " uu____1049))
end
| FStar_Util.Inl (bs) -> begin
(

let uu____1058 = (FStar_Util.string_of_int (FStar_List.length bs))
in (Prims.strcat "Inl " uu____1058))
end))
in ((debug cfg (fun uu____1066 -> (

let uu____1067 = (FStar_TypeChecker_NBETerm.t_to_string scrutinee)
in (

let uu____1069 = (FStar_Syntax_Print.pat_to_string p)
in (

let uu____1071 = (res_to_string r)
in (FStar_Util.print3 "matches_pat (%s, %s) = %s\n" uu____1067 uu____1069 uu____1071))))));
r;
))));
))
in (match (branches1) with
| [] -> begin
(failwith "Branch not found")
end
| ((p, _wopt, e))::branches2 -> begin
(

let uu____1113 = (matches_pat scrut1 p)
in (match (uu____1113) with
| FStar_Util.Inl (matches) -> begin
((debug cfg (fun uu____1138 -> (

let uu____1139 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print1 "Pattern %s matches\n" uu____1139))));
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
| (uu____1307, []) -> begin
((true), ((FStar_List.rev acc)), (ts1))
end
| ([], (uu____1342)::uu____1343) -> begin
((false), ((FStar_List.rev acc)), ([]))
end
| ((t)::ts2, (b)::bs) -> begin
(

let uu____1416 = (res && (

let uu____1419 = (

let uu____1421 = (FStar_TypeChecker_NBETerm.isAccu (FStar_Pervasives_Native.fst t))
in (not (uu____1421)))
in (implies b uu____1419)))
in (aux ts2 bs ((t)::acc) uu____1416))
end))
in (aux ts ar_list [] true)))


let find_sigelt_in_gamma : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun cfg env lid -> (

let mapper = (fun uu____1477 -> (match (uu____1477) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inr (elt, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some (elt)
end
| FStar_Util.Inr (elt, FStar_Pervasives_Native.Some (us)) -> begin
((debug cfg (fun uu____1560 -> (

let uu____1561 = (FStar_Syntax_Print.univs_to_string us)
in (FStar_Util.print1 "Universes in local declaration: %s\n" uu____1561))));
FStar_Pervasives_Native.Some (elt);
)
end
| uu____1564 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let uu____1579 = (FStar_TypeChecker_Env.lookup_qname env lid)
in (FStar_Util.bind_opt uu____1579 mapper))))


let is_univ : FStar_TypeChecker_NBETerm.t  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_TypeChecker_NBETerm.Univ (uu____1626) -> begin
true
end
| uu____1628 -> begin
false
end))


let un_univ : FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.universe = (fun tm -> (match (tm) with
| FStar_TypeChecker_NBETerm.Univ (u) -> begin
u
end
| t -> begin
(

let uu____1638 = (

let uu____1640 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (Prims.strcat "Not a universe: " uu____1640))
in (failwith uu____1638))
end))


let is_constr_fv : FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun fvar1 -> (Prims.op_Equality fvar1.FStar_Syntax_Syntax.fv_qual (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))


let is_constr : FStar_TypeChecker_Env.qninfo  ->  Prims.bool = (fun q -> (match (q) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____1662, uu____1663, uu____1664, uu____1665, uu____1666, uu____1667); FStar_Syntax_Syntax.sigrng = uu____1668; FStar_Syntax_Syntax.sigquals = uu____1669; FStar_Syntax_Syntax.sigmeta = uu____1670; FStar_Syntax_Syntax.sigattrs = uu____1671}, uu____1672), uu____1673) -> begin
true
end
| uu____1731 -> begin
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
| uu____1759 -> begin
(failwith "Universe index out of bounds")
end)
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____1763 = (aux u3)
in FStar_Syntax_Syntax.U_succ (uu____1763))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1767 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (uu____1767))
end
| FStar_Syntax_Syntax.U_unknown -> begin
u2
end
| FStar_Syntax_Syntax.U_name (uu____1770) -> begin
u2
end
| FStar_Syntax_Syntax.U_unif (uu____1771) -> begin
u2
end
| FStar_Syntax_Syntax.U_zero -> begin
u2
end)))
in (aux u)))


let find_let : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.letbinding FStar_Pervasives_Native.option = (fun lbs fvar1 -> (FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1802) -> begin
(failwith "find_let : impossible")
end
| FStar_Util.Inr (name) -> begin
(

let uu____1807 = (FStar_Syntax_Syntax.fv_eq name fvar1)
in (match (uu____1807) with
| true -> begin
FStar_Pervasives_Native.Some (lb)
end
| uu____1812 -> begin
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

let uu____2160 = (FStar_List.splitAt m targs)
in (match (uu____2160) with
| (uu____2200, targs') -> begin
(

let targs'1 = (FStar_List.map (fun targ l -> (

let uu____2291 = (

let uu____2294 = (map_append FStar_Pervasives_Native.fst args l)
in (FStar_List.rev uu____2294))
in (targ uu____2291))) targs')
in FStar_TypeChecker_NBETerm.Lam ((((fun l -> (

let uu____2328 = (map_append FStar_Pervasives_Native.fst args l)
in (f1 uu____2328)))), (targs'1), ((n1 - m)), (res))))
end))
end
| uu____2339 -> begin
(match ((Prims.op_Equality m n1)) with
| true -> begin
(

let uu____2347 = (FStar_List.map FStar_Pervasives_Native.fst args)
in (f1 uu____2347))
end
| uu____2354 -> begin
(

let uu____2356 = (FStar_List.splitAt n1 args)
in (match (uu____2356) with
| (args1, args') -> begin
(

let uu____2403 = (

let uu____2404 = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (f1 uu____2404))
in (iapp cfg uu____2403 args'))
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
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2523))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2567 = (aux args us ts)
in (match (uu____2567) with
| (us', ts') -> begin
FStar_TypeChecker_NBETerm.Construct (((i), (us'), (ts')))
end)))
end
| FStar_TypeChecker_NBETerm.FV (i, us, ts) -> begin
(

let rec aux = (fun args1 us1 ts1 -> (match (args1) with
| ((FStar_TypeChecker_NBETerm.Univ (u), uu____2694))::args2 -> begin
(aux args2 ((u)::us1) ts1)
end
| (a)::args2 -> begin
(aux args2 us1 ((a)::ts1))
end
| [] -> begin
((us1), (ts1))
end))
in (

let uu____2738 = (aux args us ts)
in (match (uu____2738) with
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
| uu____2868 -> begin
(match ((Prims.op_Equality ar (Prims.parse_int "0"))) with
| true -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), ((FStar_List.append acc args)), (ar), (ar_lst), (tr_lb)))
end
| uu____2899 -> begin
(

let full_args = (FStar_List.append acc args)
in (

let uu____2912 = (test_args full_args ar_lst)
in (match (uu____2912) with
| (can_unfold, args1, res) -> begin
(match ((not (cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.zeta))) with
| true -> begin
((debug cfg (fun uu____2929 -> (

let uu____2930 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Zeta is not set; will not unfold %s\n" uu____2930))));
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)));
)
end
| uu____2956 -> begin
(match (can_unfold) with
| true -> begin
((debug cfg (fun uu____2962 -> (

let uu____2963 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1 "Beta reducing recursive function %s\n" uu____2963))));
(match (res) with
| [] -> begin
(

let uu____2970 = (

let uu____2971 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2971 lb))
in (iapp cfg uu____2970 args1))
end
| (uu____2974)::uu____2975 -> begin
(

let t = (

let uu____2991 = (

let uu____2992 = (make_rec_env tr_lb lbs bs)
in (tr_lb uu____2992 lb))
in (iapp cfg uu____2991 args1))
in (iapp cfg t res))
end);
)
end
| uu____2995 -> begin
FStar_TypeChecker_NBETerm.Rec (((lb), (lbs), (bs), (full_args), ((Prims.parse_int "0")), (ar_lst), (tr_lb)))
end)
end)
end)))
end)
end))
end
| FStar_TypeChecker_NBETerm.Quote (uu____3020) -> begin
(

let uu____3025 = (

let uu____3027 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3027))
in (failwith uu____3025))
end
| FStar_TypeChecker_NBETerm.Reflect (uu____3030) -> begin
(

let uu____3031 = (

let uu____3033 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3033))
in (failwith uu____3031))
end
| FStar_TypeChecker_NBETerm.Lazy (uu____3036) -> begin
(

let uu____3051 = (

let uu____3053 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3053))
in (failwith uu____3051))
end
| FStar_TypeChecker_NBETerm.Constant (uu____3056) -> begin
(

let uu____3057 = (

let uu____3059 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3059))
in (failwith uu____3057))
end
| FStar_TypeChecker_NBETerm.Univ (uu____3062) -> begin
(

let uu____3063 = (

let uu____3065 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3065))
in (failwith uu____3063))
end
| FStar_TypeChecker_NBETerm.Type_t (uu____3068) -> begin
(

let uu____3069 = (

let uu____3071 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3071))
in (failwith uu____3069))
end
| FStar_TypeChecker_NBETerm.Unknown -> begin
(

let uu____3074 = (

let uu____3076 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3076))
in (failwith uu____3074))
end
| FStar_TypeChecker_NBETerm.Refinement (uu____3079) -> begin
(

let uu____3094 = (

let uu____3096 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3096))
in (failwith uu____3094))
end
| FStar_TypeChecker_NBETerm.Arrow (uu____3099) -> begin
(

let uu____3120 = (

let uu____3122 = (FStar_TypeChecker_NBETerm.t_to_string f)
in (Prims.strcat "NBE ill-typed application: " uu____3122))
in (failwith uu____3120))
end))
and translate_fv : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.fv  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs fvar1 -> (

let debug1 = (debug cfg)
in (

let qninfo = (

let uu____3139 = (FStar_TypeChecker_Cfg.cfg_env cfg)
in (

let uu____3140 = (FStar_Syntax_Syntax.lid_of_fv fvar1)
in (FStar_TypeChecker_Env.lookup_qname uu____3139 uu____3140)))
in (

let uu____3141 = ((is_constr qninfo) || (is_constr_fv fvar1))
in (match (uu____3141) with
| true -> begin
(FStar_TypeChecker_NBETerm.mkConstruct fvar1 [] [])
end
| uu____3148 -> begin
(

let uu____3150 = (FStar_TypeChecker_Normalize.should_unfold cfg (fun uu____3152 -> cfg.FStar_TypeChecker_Cfg.reifying) fvar1 qninfo)
in (match (uu____3150) with
| FStar_TypeChecker_Normalize.Should_unfold_fully -> begin
(failwith "Not yet handled")
end
| FStar_TypeChecker_Normalize.Should_unfold_no -> begin
((debug1 (fun uu____3159 -> (

let uu____3160 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(1) Decided to not unfold %s\n" uu____3160))));
(

let uu____3163 = (FStar_TypeChecker_Cfg.find_prim_step cfg fvar1)
in (match (uu____3163) with
| FStar_Pervasives_Native.Some (prim_step) when prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok -> begin
(

let arity = (prim_step.FStar_TypeChecker_Cfg.arity + prim_step.FStar_TypeChecker_Cfg.univ_arity)
in ((debug1 (fun uu____3174 -> (

let uu____3175 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Found a primop %s\n" uu____3175))));
(

let uu____3178 = (

let uu____3209 = (

let f = (fun uu____3237 uu____3238 -> ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))
in (FStar_Common.tabulate arity f))
in (((fun args -> (

let args' = (FStar_List.map FStar_TypeChecker_NBETerm.as_arg args)
in (

let callbacks = {FStar_TypeChecker_NBETerm.iapp = (iapp cfg); FStar_TypeChecker_NBETerm.translate = (translate cfg bs)}
in (

let uu____3298 = (prim_step.FStar_TypeChecker_Cfg.interpretation_nbe callbacks args')
in (match (uu____3298) with
| FStar_Pervasives_Native.Some (x) -> begin
((debug1 (fun uu____3309 -> (

let uu____3310 = (FStar_Syntax_Print.fv_to_string fvar1)
in (

let uu____3312 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print2 "Primitive operator %s returned %s\n" uu____3310 uu____3312)))));
x;
)
end
| FStar_Pervasives_Native.None -> begin
((debug1 (fun uu____3320 -> (

let uu____3321 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "Primitive operator %s failed\n" uu____3321))));
(

let uu____3324 = (FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
in (iapp cfg uu____3324 args'));
)
end)))))), (uu____3209), (arity), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____3178));
))
end
| FStar_Pervasives_Native.Some (uu____3332) -> begin
((debug1 (fun uu____3338 -> (

let uu____3339 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(2) Decided to not unfold %s\n" uu____3339))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end
| uu____3346 -> begin
((debug1 (fun uu____3354 -> (

let uu____3355 = (FStar_Syntax_Print.fv_to_string fvar1)
in (FStar_Util.print1 "(3) Decided to not unfold %s\n" uu____3355))));
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] []);
)
end));
)
end
| FStar_TypeChecker_Normalize.Should_unfold_reify -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3365; FStar_Syntax_Syntax.sigquals = uu____3366; FStar_Syntax_Syntax.sigmeta = uu____3367; FStar_Syntax_Syntax.sigattrs = uu____3368}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3436 -> begin
((debug1 (fun uu____3441 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3451 -> (

let uu____3452 = (

let uu____3454 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3454))
in (

let uu____3455 = (

let uu____3457 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3457))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3452 uu____3455)))));
(debug1 (fun uu____3466 -> (

let uu____3467 = (

let uu____3469 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3469))
in (

let uu____3470 = (

let uu____3472 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3472))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3467 uu____3470)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3475 -> begin
(FStar_TypeChecker_NBETerm.mkFV fvar1 [] [])
end)
end
| FStar_TypeChecker_Normalize.Should_unfold_yes -> begin
(match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, lbs), names1); FStar_Syntax_Syntax.sigrng = uu____3483; FStar_Syntax_Syntax.sigquals = uu____3484; FStar_Syntax_Syntax.sigmeta = uu____3485; FStar_Syntax_Syntax.sigattrs = uu____3486}, _us_opt), _rng) -> begin
(

let lbm = (find_let lbs fvar1)
in (match (lbm) with
| FStar_Pervasives_Native.Some (lb) -> begin
(match (is_rec) with
| true -> begin
(mkRec cfg lb [] [])
end
| uu____3554 -> begin
((debug1 (fun uu____3559 -> (FStar_Util.print "Translate fv: it\'s a Sig_let\n" [])));
(debug1 (fun uu____3569 -> (

let uu____3570 = (

let uu____3572 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.tag_of_term uu____3572))
in (

let uu____3573 = (

let uu____3575 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Syntax_Print.term_to_string uu____3575))
in (FStar_Util.print2 "Type of lbdef: %s - %s\n" uu____3570 uu____3573)))));
(debug1 (fun uu____3584 -> (

let uu____3585 = (

let uu____3587 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.tag_of_term uu____3587))
in (

let uu____3588 = (

let uu____3590 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Print.term_to_string uu____3590))
in (FStar_Util.print2 "Body of lbdef: %s - %s\n" uu____3585 uu____3588)))));
(translate_letbinding cfg bs lb);
)
end)
end
| FStar_Pervasives_Native.None -> begin
(failwith "Could not find let binding")
end))
end
| uu____3593 -> begin
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
| uu____3638 -> begin
(

let uu____3641 = (

let uu____3672 = (FStar_List.map (fun uu____3697 _ts -> (FStar_All.pipe_left id1 ((FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Unit)), (FStar_Pervasives_Native.None)))) us)
in (((fun us1 -> (translate cfg (FStar_List.rev_append us1 bs) lb.FStar_Syntax_Syntax.lbdef))), (uu____3672), ((FStar_List.length us)), (FStar_Pervasives_Native.None)))
in FStar_TypeChecker_NBETerm.Lam (uu____3641))
end)))))
and mkRec' : (FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_TypeChecker_NBETerm.t)  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun callback b bs env -> (

let uu____3758 = (FStar_Syntax_Util.let_rec_arity b)
in (match (uu____3758) with
| (ar, maybe_lst) -> begin
(

let uu____3783 = (match (maybe_lst) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3803 = (FStar_Common.tabulate ar (fun uu____3809 -> true))
in ((ar), (uu____3803)))
end
| FStar_Pervasives_Native.Some (lst) -> begin
(

let l = (trim lst)
in (((FStar_List.length l)), (l)))
end)
in (match (uu____3783) with
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

let uu____3936 = (

let uu____3939 = (mkRec' callback lb lbs0 bs0)
in (uu____3939)::bs1)
in (aux lbs' lbs0 uu____3936 bs0))
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

let uu____3956 = (FStar_BigInt.big_int_of_string s)
in FStar_TypeChecker_NBETerm.Int (uu____3956))
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
| uu____3965 -> begin
(

let uu____3966 = (

let uu____3968 = (

let uu____3970 = (FStar_Syntax_Print.const_to_string c)
in (Prims.strcat uu____3970 ": Not yet implemented"))
in (Prims.strcat "Tm_constant " uu____3968))
in (failwith uu____3966))
end))
and translate : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_NBETerm.t = (fun cfg bs e -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____3994 -> (

let uu____3995 = (

let uu____3997 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.tag_of_term uu____3997))
in (

let uu____3998 = (

let uu____4000 = (FStar_Syntax_Subst.compress e)
in (FStar_Syntax_Print.term_to_string uu____4000))
in (FStar_Util.print2 "Term: %s - %s\n" uu____3995 uu____3998)))));
(debug1 (fun uu____4007 -> (

let uu____4008 = (

let uu____4010 = (FStar_List.map (fun x -> (FStar_TypeChecker_NBETerm.t_to_string x)) bs)
in (FStar_String.concat ";; " uu____4010))
in (FStar_Util.print1 "BS list: %s\n" uu____4008))));
(

let uu____4019 = (

let uu____4020 = (FStar_Syntax_Subst.compress e)
in uu____4020.FStar_Syntax_Syntax.n)
in (match (uu____4019) with
| FStar_Syntax_Syntax.Tm_delayed (uu____4023, uu____4024) -> begin
(failwith "Tm_delayed: Impossible")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_TypeChecker_NBETerm.Unknown
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____4063 = (translate_constant c)
in FStar_TypeChecker_NBETerm.Constant (uu____4063))
end
| FStar_Syntax_Syntax.Tm_bvar (db) -> begin
(match ((db.FStar_Syntax_Syntax.index < (FStar_List.length bs))) with
| true -> begin
(FStar_List.nth bs db.FStar_Syntax_Syntax.index)
end
| uu____4066 -> begin
(failwith "de Bruijn index out of bounds")
end)
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
((debug1 (fun uu____4082 -> (

let uu____4083 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____4085 = (

let uu____4087 = (FStar_List.map FStar_Syntax_Print.univ_to_string us)
in (FStar_All.pipe_right uu____4087 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Uinst term : %s\nUnivs : %s\n" uu____4083 uu____4085)))));
(

let uu____4098 = (translate cfg bs t)
in (

let uu____4099 = (FStar_List.map (fun x -> (

let uu____4103 = (

let uu____4104 = (translate_univ bs x)
in FStar_TypeChecker_NBETerm.Univ (uu____4104))
in (FStar_TypeChecker_NBETerm.as_arg uu____4103))) us)
in (iapp cfg uu____4098 uu____4099)));
)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____4106 = (translate_univ bs u)
in FStar_TypeChecker_NBETerm.Type_t (uu____4106))
end
| FStar_Syntax_Syntax.Tm_arrow (xs, c) -> begin
(

let uu____4129 = (

let uu____4150 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____4220 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____4220), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (((fun ys -> (translate_comp cfg (FStar_List.rev_append ys bs) c))), (uu____4150)))
in FStar_TypeChecker_NBETerm.Arrow (uu____4129))
end
| FStar_Syntax_Syntax.Tm_refine (bv, tm) -> begin
FStar_TypeChecker_NBETerm.Refinement ((((fun y -> (translate cfg ((y)::bs) tm))), ((fun uu____4289 -> (

let uu____4290 = (translate cfg bs bv.FStar_Syntax_Syntax.sort)
in (FStar_TypeChecker_NBETerm.as_arg uu____4290))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____4292, uu____4293) -> begin
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
| FStar_Syntax_Syntax.Tm_abs ([], uu____4355, uu____4356) -> begin
(failwith "Impossible: abstraction with no binders")
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, resc) -> begin
(

let uu____4407 = (

let uu____4438 = (FStar_List.fold_right (fun x formals -> (

let next_formal = (fun prefix_of_xs_rev -> (

let uu____4508 = (translate cfg (FStar_List.append prefix_of_xs_rev bs) (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in ((uu____4508), ((FStar_Pervasives_Native.snd x)))))
in (next_formal)::formals)) xs [])
in (

let uu____4537 = (FStar_Util.map_opt resc (fun c uu____4549 -> (translate_residual_comp cfg bs c)))
in (((fun ys -> (translate cfg (FStar_List.rev_append ys bs) body))), (uu____4438), ((FStar_List.length xs)), (uu____4537))))
in FStar_TypeChecker_NBETerm.Lam (uu____4407))
end
| FStar_Syntax_Syntax.Tm_fvar (fvar1) -> begin
(translate_fv cfg bs fvar1)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4583; FStar_Syntax_Syntax.vars = uu____4584}, (arg)::(more)::args) -> begin
(

let uu____4644 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4644) with
| (head1, uu____4662) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4706 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4706)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4715)); FStar_Syntax_Syntax.pos = uu____4716; FStar_Syntax_Syntax.vars = uu____4717}, (arg)::(more)::args) -> begin
(

let uu____4777 = (FStar_Syntax_Util.head_and_args e)
in (match (uu____4777) with
| (head1, uu____4795) -> begin
(

let head2 = (FStar_Syntax_Syntax.mk_Tm_app head1 ((arg)::[]) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (

let uu____4839 = (FStar_Syntax_Syntax.mk_Tm_app head2 ((more)::args) FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (translate cfg bs uu____4839)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4848)); FStar_Syntax_Syntax.pos = uu____4849; FStar_Syntax_Syntax.vars = uu____4850}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.reifying -> begin
(

let cfg1 = (

let uu___264_4891 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___264_4891.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___264_4891.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___264_4891.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___264_4891.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___264_4891.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___264_4891.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___264_4891.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___264_4891.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4897)); FStar_Syntax_Syntax.pos = uu____4898; FStar_Syntax_Syntax.vars = uu____4899}, (arg)::[]) -> begin
(

let uu____4939 = (translate cfg bs (FStar_Pervasives_Native.fst arg))
in FStar_TypeChecker_NBETerm.Reflect (uu____4939))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____4944; FStar_Syntax_Syntax.vars = uu____4945}, (arg)::[]) when cfg.FStar_TypeChecker_Cfg.steps.FStar_TypeChecker_Cfg.reify_ -> begin
(

let cfg1 = (

let uu___265_4987 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___265_4987.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___265_4987.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___265_4987.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___265_4987.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___265_4987.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___265_4987.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___265_4987.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___265_4987.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = true})
in (translate cfg1 bs (FStar_Pervasives_Native.fst arg)))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug1 (fun uu____5026 -> (

let uu____5027 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____5029 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "Application: %s @ %s\n" uu____5027 uu____5029)))));
(

let uu____5032 = (translate cfg bs head1)
in (

let uu____5033 = (FStar_List.map (fun x -> (

let uu____5055 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____5055), ((FStar_Pervasives_Native.snd x))))) args)
in (iapp cfg uu____5032 uu____5033)));
)
end
| FStar_Syntax_Syntax.Tm_match (scrut, branches) -> begin
(

let make_branches = (fun readback1 -> (

let cfg1 = (

let uu___266_5116 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___267_5119 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___267_5119.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___267_5119.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = false; FStar_TypeChecker_Cfg.weak = uu___267_5119.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___267_5119.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___267_5119.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___267_5119.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___267_5119.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___267_5119.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___267_5119.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___267_5119.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___267_5119.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___267_5119.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___267_5119.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___267_5119.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___267_5119.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = uu___267_5119.FStar_TypeChecker_Cfg.reify_; FStar_TypeChecker_Cfg.compress_uvars = uu___267_5119.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___267_5119.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___267_5119.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___267_5119.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___267_5119.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___267_5119.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___267_5119.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___267_5119.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___267_5119.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___266_5116.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___266_5116.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___266_5116.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___266_5116.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___266_5116.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___266_5116.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___266_5116.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___266_5116.FStar_TypeChecker_Cfg.reifying})
in (

let rec process_pattern = (fun bs1 p -> (

let uu____5148 = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
((bs1), (FStar_Syntax_Syntax.Pat_constant (c)))
end
| FStar_Syntax_Syntax.Pat_cons (fvar1, args) -> begin
(

let uu____5184 = (FStar_List.fold_left (fun uu____5225 uu____5226 -> (match (((uu____5225), (uu____5226))) with
| ((bs2, args1), (arg, b)) -> begin
(

let uu____5318 = (process_pattern bs2 arg)
in (match (uu____5318) with
| (bs', arg') -> begin
((bs'), ((((arg'), (b)))::args1))
end))
end)) ((bs1), ([])) args)
in (match (uu____5184) with
| (bs', args') -> begin
((bs'), (FStar_Syntax_Syntax.Pat_cons (((fvar1), ((FStar_List.rev args'))))))
end))
end
| FStar_Syntax_Syntax.Pat_var (bvar) -> begin
(

let x = (

let uu____5417 = (

let uu____5418 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5418))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5417))
in (

let uu____5419 = (

let uu____5422 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____5422)::bs1)
in ((uu____5419), (FStar_Syntax_Syntax.Pat_var (x)))))
end
| FStar_Syntax_Syntax.Pat_wild (bvar) -> begin
(

let x = (

let uu____5427 = (

let uu____5428 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5428))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5427))
in (

let uu____5429 = (

let uu____5432 = (FStar_TypeChecker_NBETerm.mkAccuVar x)
in (uu____5432)::bs1)
in ((uu____5429), (FStar_Syntax_Syntax.Pat_wild (x)))))
end
| FStar_Syntax_Syntax.Pat_dot_term (bvar, tm) -> begin
(

let x = (

let uu____5442 = (

let uu____5443 = (translate cfg1 bs1 bvar.FStar_Syntax_Syntax.sort)
in (readback1 uu____5443))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____5442))
in (

let uu____5444 = (

let uu____5445 = (

let uu____5452 = (

let uu____5455 = (translate cfg1 bs1 tm)
in (readback1 uu____5455))
in ((x), (uu____5452)))
in FStar_Syntax_Syntax.Pat_dot_term (uu____5445))
in ((bs1), (uu____5444))))
end)
in (match (uu____5148) with
| (bs2, p_new) -> begin
((bs2), ((

let uu___268_5475 = p
in {FStar_Syntax_Syntax.v = p_new; FStar_Syntax_Syntax.p = uu___268_5475.FStar_Syntax_Syntax.p})))
end)))
in (FStar_List.map (fun uu____5494 -> (match (uu____5494) with
| (pat, when_clause, e1) -> begin
(

let uu____5516 = (process_pattern bs pat)
in (match (uu____5516) with
| (bs', pat') -> begin
(

let uu____5529 = (

let uu____5530 = (

let uu____5533 = (translate cfg1 bs' e1)
in (readback1 uu____5533))
in ((pat'), (when_clause), (uu____5530)))
in (FStar_Syntax_Util.branch uu____5529))
end))
end)) branches))))
in (

let rec case = (fun scrut1 -> ((debug1 (fun uu____5555 -> (

let uu____5556 = (

let uu____5558 = (readback cfg scrut1)
in (FStar_Syntax_Print.term_to_string uu____5558))
in (

let uu____5559 = (FStar_TypeChecker_NBETerm.t_to_string scrut1)
in (FStar_Util.print2 "Match case: (%s) -- (%s)\n" uu____5556 uu____5559)))));
(

let scrut2 = (unlazy scrut1)
in (match (scrut2) with
| FStar_TypeChecker_NBETerm.Construct (c, us, args) -> begin
((debug1 (fun uu____5587 -> (

let uu____5588 = (

let uu____5590 = (FStar_All.pipe_right args (FStar_List.map (fun uu____5616 -> (match (uu____5616) with
| (x, q) -> begin
(

let uu____5630 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (Prims.strcat (match ((FStar_Util.is_some q)) with
| true -> begin
"#"
end
| uu____5635 -> begin
""
end) uu____5630))
end))))
in (FStar_All.pipe_right uu____5590 (FStar_String.concat "; ")))
in (FStar_Util.print1 "Match args: %s\n" uu____5588))));
(

let uu____5644 = (pickBranch cfg scrut2 branches)
in (match (uu____5644) with
| FStar_Pervasives_Native.Some (branch1, args1) -> begin
(

let uu____5665 = (FStar_List.fold_left (fun bs1 x -> (x)::bs1) bs args1)
in (translate cfg uu____5665 branch1))
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
)
end
| FStar_TypeChecker_NBETerm.Constant (c) -> begin
((debug1 (fun uu____5688 -> (

let uu____5689 = (FStar_TypeChecker_NBETerm.t_to_string scrut2)
in (FStar_Util.print1 "Match constant : %s\n" uu____5689))));
(

let uu____5692 = (pickBranch cfg scrut2 branches)
in (match (uu____5692) with
| FStar_Pervasives_Native.Some (branch1, []) -> begin
(translate cfg bs branch1)
end
| FStar_Pervasives_Native.Some (branch1, (arg)::[]) -> begin
(translate cfg ((arg)::bs) branch1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end
| FStar_Pervasives_Native.Some (uu____5726, (hd1)::tl1) -> begin
(failwith "Impossible: Matching on constants cannot bind more than one variable")
end));
)
end
| uu____5740 -> begin
(FStar_TypeChecker_NBETerm.mkAccuMatch scrut2 case make_branches)
end));
))
in (

let uu____5741 = (translate cfg bs scrut)
in (case uu____5741))))
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

let uu____5820 = (make_rec_env (translate_letbinding cfg) lbs bs)
in (translate cfg uu____5820 body))
end
| FStar_Syntax_Syntax.Tm_meta (e1, uu____5824) -> begin
(translate cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_quoted (qt, qi) -> begin
(

let close1 = (fun t -> (

let bvs = (FStar_List.map (fun uu____5845 -> (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)) bs)
in (

let s1 = (FStar_List.mapi (fun i bv -> FStar_Syntax_Syntax.DB (((i), (bv)))) bvs)
in (

let s2 = (

let uu____5858 = (FStar_List.zip bvs bs)
in (FStar_List.map (fun uu____5873 -> (match (uu____5873) with
| (bv, t1) -> begin
(

let uu____5880 = (

let uu____5887 = (readback cfg t1)
in ((bv), (uu____5887)))
in FStar_Syntax_Syntax.NT (uu____5880))
end)) uu____5858))
in (

let uu____5892 = (FStar_Syntax_Subst.subst s1 t)
in (FStar_Syntax_Subst.subst s2 uu____5892))))))
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

let f = (fun uu____5901 -> (

let t = (FStar_Syntax_Util.unfold_lazy li)
in ((debug1 (fun uu____5908 -> (

let uu____5909 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 ">> Unfolding Tm_lazy to %s\n" uu____5909))));
(translate cfg bs t);
)))
in (

let uu____5912 = (

let uu____5927 = (FStar_Common.mk_thunk f)
in ((FStar_Util.Inl (li)), (uu____5927)))
in FStar_TypeChecker_NBETerm.Lazy (uu____5912)))
end));
)))
and translate_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_NBETerm.comp = (fun cfg bs c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (typ, u) -> begin
(

let uu____5999 = (

let uu____6006 = (translate cfg bs typ)
in (

let uu____6007 = (fmap_opt (translate_univ bs) u)
in ((uu____6006), (uu____6007))))
in FStar_TypeChecker_NBETerm.Tot (uu____5999))
end
| FStar_Syntax_Syntax.GTotal (typ, u) -> begin
(

let uu____6022 = (

let uu____6029 = (translate cfg bs typ)
in (

let uu____6030 = (fmap_opt (translate_univ bs) u)
in ((uu____6029), (uu____6030))))
in FStar_TypeChecker_NBETerm.GTot (uu____6022))
end
| FStar_Syntax_Syntax.Comp (ctyp) -> begin
(

let uu____6036 = (translate_comp_typ cfg bs ctyp)
in FStar_TypeChecker_NBETerm.Comp (uu____6036))
end))
and readback_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg c -> (

let c' = (match (c) with
| FStar_TypeChecker_NBETerm.Tot (typ, u) -> begin
(

let uu____6046 = (

let uu____6055 = (readback cfg typ)
in ((uu____6055), (u)))
in FStar_Syntax_Syntax.Total (uu____6046))
end
| FStar_TypeChecker_NBETerm.GTot (typ, u) -> begin
(

let uu____6068 = (

let uu____6077 = (readback cfg typ)
in ((uu____6077), (u)))
in FStar_Syntax_Syntax.GTotal (uu____6068))
end
| FStar_TypeChecker_NBETerm.Comp (ctyp) -> begin
(

let uu____6085 = (readback_comp_typ cfg ctyp)
in FStar_Syntax_Syntax.Comp (uu____6085))
end)
in (FStar_Syntax_Syntax.mk c' FStar_Pervasives_Native.None FStar_Range.dummyRange)))
and translate_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_TypeChecker_NBETerm.comp_typ = (fun cfg bs c -> (

let uu____6091 = c
in (match (uu____6091) with
| {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags1} -> begin
(

let uu____6111 = (FStar_List.map (translate_univ bs) comp_univs)
in (

let uu____6112 = (translate cfg bs result_typ)
in (

let uu____6113 = (FStar_List.map (fun x -> (

let uu____6141 = (translate cfg bs (FStar_Pervasives_Native.fst x))
in ((uu____6141), ((FStar_Pervasives_Native.snd x))))) effect_args)
in (

let uu____6148 = (FStar_List.map (translate_flag cfg bs) flags1)
in {FStar_TypeChecker_NBETerm.comp_univs = uu____6111; FStar_TypeChecker_NBETerm.effect_name = effect_name; FStar_TypeChecker_NBETerm.result_typ = uu____6112; FStar_TypeChecker_NBETerm.effect_args = uu____6113; FStar_TypeChecker_NBETerm.flags = uu____6148}))))
end)))
and readback_comp_typ : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun cfg c -> (

let uu____6153 = (readback cfg c.FStar_TypeChecker_NBETerm.result_typ)
in (

let uu____6156 = (FStar_List.map (fun x -> (

let uu____6182 = (readback cfg (FStar_Pervasives_Native.fst x))
in ((uu____6182), ((FStar_Pervasives_Native.snd x))))) c.FStar_TypeChecker_NBETerm.effect_args)
in (

let uu____6183 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.flags)
in {FStar_Syntax_Syntax.comp_univs = c.FStar_TypeChecker_NBETerm.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_TypeChecker_NBETerm.effect_name; FStar_Syntax_Syntax.result_typ = uu____6153; FStar_Syntax_Syntax.effect_args = uu____6156; FStar_Syntax_Syntax.flags = uu____6183}))))
and translate_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.residual_comp  ->  FStar_TypeChecker_NBETerm.residual_comp = (fun cfg bs c -> (

let uu____6191 = c
in (match (uu____6191) with
| {FStar_Syntax_Syntax.residual_effect = residual_effect; FStar_Syntax_Syntax.residual_typ = residual_typ; FStar_Syntax_Syntax.residual_flags = residual_flags} -> begin
(

let uu____6201 = (FStar_Util.map_opt residual_typ (translate cfg bs))
in (

let uu____6206 = (FStar_List.map (translate_flag cfg bs) residual_flags)
in {FStar_TypeChecker_NBETerm.residual_effect = residual_effect; FStar_TypeChecker_NBETerm.residual_typ = uu____6201; FStar_TypeChecker_NBETerm.residual_flags = uu____6206}))
end)))
and readback_residual_comp : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.residual_comp  ->  FStar_Syntax_Syntax.residual_comp = (fun cfg c -> (

let uu____6211 = (FStar_Util.map_opt c.FStar_TypeChecker_NBETerm.residual_typ (readback cfg))
in (

let uu____6218 = (FStar_List.map (readback_flag cfg) c.FStar_TypeChecker_NBETerm.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = c.FStar_TypeChecker_NBETerm.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6211; FStar_Syntax_Syntax.residual_flags = uu____6218})))
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

let uu____6229 = (translate cfg bs tm)
in FStar_TypeChecker_NBETerm.DECREASES (uu____6229))
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

let uu____6233 = (readback cfg t)
in FStar_Syntax_Syntax.DECREASES (uu____6233))
end))
and translate_monadic : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____6236 cfg bs e -> (match (uu____6236) with
| (m, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let uu____6274 = (

let uu____6283 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv m)
in (FStar_TypeChecker_Env.effect_decl_opt cfg.FStar_TypeChecker_Cfg.tcenv uu____6283))
in (match (uu____6274) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6290 = (

let uu____6292 = (FStar_Ident.string_of_lid m)
in (FStar_Util.format1 "Effect declaration not found: %s" uu____6292))
in (failwith uu____6290))
end
| FStar_Pervasives_Native.Some (ed, q) -> begin
(

let cfg' = (

let uu___269_6308 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___269_6308.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___269_6308.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___269_6308.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___269_6308.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___269_6308.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___269_6308.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___269_6308.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___269_6308.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let body_lam = (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (ty); FStar_Syntax_Syntax.residual_flags = []}
in (

let uu____6316 = (

let uu____6323 = (

let uu____6324 = (

let uu____6343 = (

let uu____6352 = (

let uu____6359 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((uu____6359), (FStar_Pervasives_Native.None)))
in (uu____6352)::[])
in ((uu____6343), (body), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____6324))
in (FStar_Syntax_Syntax.mk uu____6323))
in (uu____6316 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos)))
in (

let maybe_range_arg = (

let uu____6396 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____6396) with
| true -> begin
(

let uu____6405 = (

let uu____6410 = (

let uu____6411 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (translate cfg [] uu____6411))
in ((uu____6410), (FStar_Pervasives_Native.None)))
in (

let uu____6412 = (

let uu____6419 = (

let uu____6424 = (

let uu____6425 = (FStar_TypeChecker_Cfg.embed_simple FStar_Syntax_Embeddings.e_range body.FStar_Syntax_Syntax.pos body.FStar_Syntax_Syntax.pos)
in (translate cfg [] uu____6425))
in ((uu____6424), (FStar_Pervasives_Native.None)))
in (uu____6419)::[])
in (uu____6405)::uu____6412))
end
| uu____6438 -> begin
[]
end))
in (

let t = (

let uu____6445 = (

let uu____6446 = (

let uu____6447 = (FStar_Syntax_Util.un_uinst (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr))
in (translate cfg' [] uu____6447))
in (iapp cfg uu____6446 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::(((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____6464 = (

let uu____6465 = (

let uu____6472 = (

let uu____6477 = (translate cfg' bs lb.FStar_Syntax_Syntax.lbtyp)
in ((uu____6477), (FStar_Pervasives_Native.None)))
in (

let uu____6478 = (

let uu____6485 = (

let uu____6490 = (translate cfg' bs ty)
in ((uu____6490), (FStar_Pervasives_Native.None)))
in (uu____6485)::[])
in (uu____6472)::uu____6478))
in (

let uu____6503 = (

let uu____6510 = (

let uu____6517 = (

let uu____6524 = (

let uu____6529 = (translate cfg bs lb.FStar_Syntax_Syntax.lbdef)
in ((uu____6529), (FStar_Pervasives_Native.None)))
in (

let uu____6530 = (

let uu____6537 = (

let uu____6544 = (

let uu____6549 = (translate cfg bs body_lam)
in ((uu____6549), (FStar_Pervasives_Native.None)))
in (uu____6544)::[])
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6537)
in (uu____6524)::uu____6530))
in (((FStar_TypeChecker_NBETerm.Unknown), (FStar_Pervasives_Native.None)))::uu____6517)
in (FStar_List.append maybe_range_arg uu____6510))
in (FStar_List.append uu____6465 uu____6503)))
in (iapp cfg uu____6445 uu____6464)))
in ((debug cfg (fun uu____6581 -> (

let uu____6582 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic: %s\n" uu____6582))));
t;
)))))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____6585)); FStar_Syntax_Syntax.pos = uu____6586; FStar_Syntax_Syntax.vars = uu____6587}, ((e2, uu____6589))::[]) -> begin
(translate (

let uu___270_6630 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___270_6630.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___270_6630.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___270_6630.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___270_6630.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___270_6630.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___270_6630.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___270_6630.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___270_6630.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
((debug cfg (fun uu____6662 -> (

let uu____6663 = (FStar_Syntax_Print.term_to_string head1)
in (

let uu____6665 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.print2 "translate_monadic app (%s) @ (%s)\n" uu____6663 uu____6665)))));
(

let fallback1 = (fun uu____6673 -> (translate cfg bs e1))
in (

let fallback2 = (fun uu____6679 -> (

let uu____6680 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_monadic (((m), (ty))))))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___271_6687 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___271_6687.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___271_6687.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___271_6687.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___271_6687.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___271_6687.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___271_6687.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___271_6687.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___271_6687.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs uu____6680)))
in (

let uu____6689 = (

let uu____6690 = (FStar_Syntax_Util.un_uinst head1)
in uu____6690.FStar_Syntax_Syntax.n)
in (match (uu____6689) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let qninfo = (FStar_TypeChecker_Env.lookup_qname cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (

let uu____6696 = (

let uu____6698 = (FStar_TypeChecker_Env.is_action cfg.FStar_TypeChecker_Cfg.tcenv lid)
in (not (uu____6698)))
in (match (uu____6696) with
| true -> begin
(fallback1 ())
end
| uu____6701 -> begin
(

let uu____6703 = (

let uu____6705 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.FStar_TypeChecker_Cfg.delta_level fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (FStar_Option.isNone uu____6705))
in (match (uu____6703) with
| true -> begin
(fallback2 ())
end
| uu____6717 -> begin
(

let e2 = (

let uu____6722 = (

let uu____6727 = (FStar_Syntax_Util.mk_reify head1)
in (FStar_Syntax_Syntax.mk_Tm_app uu____6727 args))
in (uu____6722 FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos))
in (translate (

let uu___272_6732 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___272_6732.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___272_6732.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___272_6732.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___272_6732.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___272_6732.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___272_6732.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___272_6732.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___272_6732.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs e2))
end))
end))))
end
| uu____6734 -> begin
(fallback1 ())
end))));
)
end
| FStar_Syntax_Syntax.Tm_match (sc, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____6855 -> (match (uu____6855) with
| (pat, wopt, tm) -> begin
(

let uu____6903 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____6903)))
end))))
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), (branches1)))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
in (translate (

let uu___273_6937 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___273_6937.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___273_6937.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___273_6937.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___273_6937.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___273_6937.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___273_6937.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___273_6937.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___273_6937.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false}) bs tm)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____6940)) -> begin
(translate_monadic ((m), (ty)) cfg bs e1)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty')) -> begin
(translate_monadic_lift ((msrc), (mtgt), (ty')) cfg bs e1)
end
| uu____6967 -> begin
(

let uu____6968 = (

let uu____6970 = (FStar_Syntax_Print.tag_of_term e1)
in (FStar_Util.format1 "Unexpected case in translate_monadic: %s" uu____6970))
in (failwith uu____6968))
end))
end))
and translate_monadic_lift : (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_NBETerm.t = (fun uu____6973 cfg bs e -> (match (uu____6973) with
| (msrc, mtgt, ty) -> begin
(

let e1 = (FStar_Syntax_Util.unascribe e)
in (

let uu____6997 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____6997) with
| true -> begin
(

let ed = (

let uu____7001 = (FStar_TypeChecker_Env.norm_eff_name cfg.FStar_TypeChecker_Cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl cfg.FStar_TypeChecker_Cfg.tcenv uu____7001))
in (

let ret1 = (

let uu____7003 = (

let uu____7004 = (FStar_Syntax_Subst.compress (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr))
in uu____7004.FStar_Syntax_Syntax.n)
in (match (uu____7003) with
| FStar_Syntax_Syntax.Tm_uinst (ret1, (uu____7012)::[]) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((ret1), ((FStar_Syntax_Syntax.U_unknown)::[])))) FStar_Pervasives_Native.None e1.FStar_Syntax_Syntax.pos)
end
| uu____7019 -> begin
(failwith "NYI: Reification of indexed effect (NBE)")
end))
in (

let cfg' = (

let uu___274_7022 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___274_7022.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___274_7022.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___274_7022.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___274_7022.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___274_7022.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___274_7022.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___274_7022.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___274_7022.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____7025 = (

let uu____7026 = (translate cfg' [] ret1)
in (iapp cfg' uu____7026 ((((FStar_TypeChecker_NBETerm.Univ (FStar_Syntax_Syntax.U_unknown)), (FStar_Pervasives_Native.None)))::[])))
in (

let uu____7035 = (

let uu____7036 = (

let uu____7041 = (translate cfg' bs ty)
in ((uu____7041), (FStar_Pervasives_Native.None)))
in (

let uu____7042 = (

let uu____7049 = (

let uu____7054 = (translate cfg' bs e1)
in ((uu____7054), (FStar_Pervasives_Native.None)))
in (uu____7049)::[])
in (uu____7036)::uu____7042))
in (iapp cfg' uu____7025 uu____7035)))
in ((debug cfg (fun uu____7070 -> (

let uu____7071 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(1): %s\n" uu____7071))));
t;
)))))
end
| uu____7074 -> begin
(

let uu____7076 = (FStar_TypeChecker_Env.monad_leq cfg.FStar_TypeChecker_Cfg.tcenv msrc mtgt)
in (match (uu____7076) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7079 = (

let uu____7081 = (FStar_Ident.text_of_lid msrc)
in (

let uu____7083 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____7081 uu____7083)))
in (failwith uu____7079))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____7086; FStar_TypeChecker_Env.mtarget = uu____7087; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____7088; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____7110 = (

let uu____7112 = (FStar_Ident.text_of_lid msrc)
in (

let uu____7114 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____7112 uu____7114)))
in (failwith uu____7110))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____7117; FStar_TypeChecker_Env.mtarget = uu____7118; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____7119; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let lift_lam = (

let x = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (

let uu____7158 = (

let uu____7161 = (FStar_Syntax_Syntax.bv_to_name x)
in (lift FStar_Syntax_Syntax.U_unknown ty FStar_Syntax_Syntax.tun uu____7161))
in (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) uu____7158 FStar_Pervasives_Native.None)))
in (

let cfg' = (

let uu___275_7177 = cfg
in {FStar_TypeChecker_Cfg.steps = uu___275_7177.FStar_TypeChecker_Cfg.steps; FStar_TypeChecker_Cfg.tcenv = uu___275_7177.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___275_7177.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___275_7177.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___275_7177.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___275_7177.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___275_7177.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___275_7177.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = false})
in (

let t = (

let uu____7180 = (translate cfg' [] lift_lam)
in (

let uu____7181 = (

let uu____7182 = (

let uu____7187 = (translate cfg bs e1)
in ((uu____7187), (FStar_Pervasives_Native.None)))
in (uu____7182)::[])
in (iapp cfg uu____7180 uu____7181)))
in ((debug cfg (fun uu____7199 -> (

let uu____7200 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.print1 "translate_monadic_lift(2): %s\n" uu____7200))));
t;
))))
end))
end)))
end))
and readback : FStar_TypeChecker_Cfg.cfg  ->  FStar_TypeChecker_NBETerm.t  ->  FStar_Syntax_Syntax.term = (fun cfg x -> (

let debug1 = (debug cfg)
in ((debug1 (fun uu____7218 -> (

let uu____7219 = (FStar_TypeChecker_NBETerm.t_to_string x)
in (FStar_Util.print1 "Readback: %s\n" uu____7219))));
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

let uu____7227 = (FStar_BigInt.string_of_big_int i)
in (FStar_All.pipe_right uu____7227 FStar_Syntax_Util.exp_int))
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

let uu____7287 = (FStar_List.fold_left (fun uu____7330 tf -> (match (uu____7330) with
| (args_rev, accus_rev) -> begin
(

let uu____7382 = (tf accus_rev)
in (match (uu____7382) with
| (xt, q) -> begin
(

let x1 = (

let uu____7402 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7402))
in (

let uu____7403 = (

let uu____7406 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____7406)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____7403))))
end))
end)) (([]), ([])) targs)
in (match (uu____7287) with
| (args_rev, accus_rev) -> begin
(

let body = (

let uu____7450 = (f (FStar_List.rev accus_rev))
in (readback cfg uu____7450))
in (

let uu____7451 = (FStar_Util.map_opt resc (fun thunk1 -> (

let uu____7462 = (thunk1 ())
in (readback_residual_comp cfg uu____7462))))
in (FStar_Syntax_Util.abs (FStar_List.rev args_rev) body uu____7451)))
end))
end
| FStar_TypeChecker_NBETerm.Refinement (f, targ) -> begin
(

let x1 = (

let uu____7490 = (

let uu____7491 = (

let uu____7492 = (targ ())
in (FStar_Pervasives_Native.fst uu____7492))
in (readback cfg uu____7491))
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7490))
in (

let body = (

let uu____7498 = (

let uu____7499 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (f uu____7499))
in (readback cfg uu____7498))
in (FStar_Syntax_Util.refine x1 body)))
end
| FStar_TypeChecker_NBETerm.Reflect (t) -> begin
(

let tm = (readback cfg t)
in (FStar_Syntax_Util.mk_reflect tm))
end
| FStar_TypeChecker_NBETerm.Arrow (f, targs) -> begin
(

let uu____7536 = (FStar_List.fold_left (fun uu____7579 tf -> (match (uu____7579) with
| (args_rev, accus_rev) -> begin
(

let uu____7631 = (tf accus_rev)
in (match (uu____7631) with
| (xt, q) -> begin
(

let x1 = (

let uu____7651 = (readback cfg xt)
in (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None uu____7651))
in (

let uu____7652 = (

let uu____7655 = (FStar_TypeChecker_NBETerm.mkAccuVar x1)
in (uu____7655)::accus_rev)
in (((((x1), (q)))::args_rev), (uu____7652))))
end))
end)) (([]), ([])) targs)
in (match (uu____7536) with
| (args_rev, accus_rev) -> begin
(

let cmp = (

let uu____7699 = (f (FStar_List.rev accus_rev))
in (readback_comp cfg uu____7699))
in (FStar_Syntax_Util.arrow (FStar_List.rev args_rev) cmp))
end))
end
| FStar_TypeChecker_NBETerm.Construct (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7742 -> (match (uu____7742) with
| (x1, q) -> begin
(

let uu____7753 = (readback cfg x1)
in ((uu____7753), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7772 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7779)::uu____7780 -> begin
(

let uu____7783 = (

let uu____7786 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7786 (FStar_List.rev us)))
in (apply1 uu____7783))
end
| [] -> begin
(

let uu____7787 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7787))
end)))
end
| FStar_TypeChecker_NBETerm.FV (fv, us, args) -> begin
(

let args1 = (map_rev (fun uu____7828 -> (match (uu____7828) with
| (x1, q) -> begin
(

let uu____7839 = (readback cfg x1)
in ((uu____7839), (q)))
end)) args)
in (

let apply1 = (fun tm -> (match (args1) with
| [] -> begin
tm
end
| uu____7858 -> begin
(FStar_Syntax_Util.mk_app tm args1)
end))
in (match (us) with
| (uu____7865)::uu____7866 -> begin
(

let uu____7869 = (

let uu____7872 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____7872 (FStar_List.rev us)))
in (apply1 uu____7869))
end
| [] -> begin
(

let uu____7873 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (apply1 uu____7873))
end)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), []) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Var (bv), ts) -> begin
(

let args = (map_rev (fun uu____7920 -> (match (uu____7920) with
| (x1, q) -> begin
(

let uu____7931 = (readback cfg x1)
in ((uu____7931), (q)))
end)) ts)
in (

let uu____7932 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Util.mk_app uu____7932 args)))
end
| FStar_TypeChecker_NBETerm.Accu (FStar_TypeChecker_NBETerm.Match (scrut, cases, make_branches), ts) -> begin
(

let args = (map_rev (fun uu____7992 -> (match (uu____7992) with
| (x1, q) -> begin
(

let uu____8003 = (readback cfg x1)
in ((uu____8003), (q)))
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
| uu____8033 -> begin
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

let args1 = (map_rev (fun uu____8120 -> (match (uu____8120) with
| (x1, q) -> begin
(

let uu____8131 = (readback cfg x1)
in ((uu____8131), (q)))
end)) args)
in (match (args1) with
| [] -> begin
head1
end
| uu____8136 -> begin
(FStar_Syntax_Util.mk_app head1 args1)
end)))
end
| FStar_TypeChecker_NBETerm.Quote (qt, qi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((qt), (qi)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl (li), uu____8148) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy (li)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_TypeChecker_NBETerm.Lazy (uu____8165, thunk1) -> begin
(

let uu____8187 = (FStar_Common.force_thunk thunk1)
in (readback cfg uu____8187))
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
| uu____8256 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____8268 -> begin
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
| uu____8290 -> begin
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
| uu____8318 -> begin
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
| uu____8343 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____8354 -> begin
false
end))


let step_as_normalizer_step : step  ->  FStar_TypeChecker_Env.step = (fun uu___263_8361 -> (match (uu___263_8361) with
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

let uu___276_8400 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___277_8403 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___277_8403.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___277_8403.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___277_8403.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___277_8403.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___277_8403.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___277_8403.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___277_8403.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___277_8403.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___277_8403.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___277_8403.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___277_8403.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___277_8403.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___277_8403.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___277_8403.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___277_8403.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___277_8403.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___277_8403.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___277_8403.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___277_8403.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___277_8403.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___277_8403.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___277_8403.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___277_8403.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___277_8403.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___277_8403.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___276_8400.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___276_8400.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___276_8400.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___276_8400.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___276_8400.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___276_8400.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___276_8400.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___276_8400.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____8408 -> (

let uu____8409 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8409))));
(

let r = (

let uu____8413 = (translate cfg1 [] e)
in (readback cfg1 uu____8413))
in ((debug cfg1 (fun uu____8417 -> (

let uu____8418 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8418))));
r;
));
))))


let normalize_for_unit_test : FStar_TypeChecker_Env.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun steps env e -> (

let cfg = (FStar_TypeChecker_Cfg.config steps env)
in (

let cfg1 = (

let uu___278_8443 = cfg
in {FStar_TypeChecker_Cfg.steps = (

let uu___279_8446 = cfg.FStar_TypeChecker_Cfg.steps
in {FStar_TypeChecker_Cfg.beta = uu___279_8446.FStar_TypeChecker_Cfg.beta; FStar_TypeChecker_Cfg.iota = uu___279_8446.FStar_TypeChecker_Cfg.iota; FStar_TypeChecker_Cfg.zeta = uu___279_8446.FStar_TypeChecker_Cfg.zeta; FStar_TypeChecker_Cfg.weak = uu___279_8446.FStar_TypeChecker_Cfg.weak; FStar_TypeChecker_Cfg.hnf = uu___279_8446.FStar_TypeChecker_Cfg.hnf; FStar_TypeChecker_Cfg.primops = uu___279_8446.FStar_TypeChecker_Cfg.primops; FStar_TypeChecker_Cfg.do_not_unfold_pure_lets = uu___279_8446.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets; FStar_TypeChecker_Cfg.unfold_until = uu___279_8446.FStar_TypeChecker_Cfg.unfold_until; FStar_TypeChecker_Cfg.unfold_only = uu___279_8446.FStar_TypeChecker_Cfg.unfold_only; FStar_TypeChecker_Cfg.unfold_fully = uu___279_8446.FStar_TypeChecker_Cfg.unfold_fully; FStar_TypeChecker_Cfg.unfold_attr = uu___279_8446.FStar_TypeChecker_Cfg.unfold_attr; FStar_TypeChecker_Cfg.unfold_tac = uu___279_8446.FStar_TypeChecker_Cfg.unfold_tac; FStar_TypeChecker_Cfg.pure_subterms_within_computations = uu___279_8446.FStar_TypeChecker_Cfg.pure_subterms_within_computations; FStar_TypeChecker_Cfg.simplify = uu___279_8446.FStar_TypeChecker_Cfg.simplify; FStar_TypeChecker_Cfg.erase_universes = uu___279_8446.FStar_TypeChecker_Cfg.erase_universes; FStar_TypeChecker_Cfg.allow_unbound_universes = uu___279_8446.FStar_TypeChecker_Cfg.allow_unbound_universes; FStar_TypeChecker_Cfg.reify_ = true; FStar_TypeChecker_Cfg.compress_uvars = uu___279_8446.FStar_TypeChecker_Cfg.compress_uvars; FStar_TypeChecker_Cfg.no_full_norm = uu___279_8446.FStar_TypeChecker_Cfg.no_full_norm; FStar_TypeChecker_Cfg.check_no_uvars = uu___279_8446.FStar_TypeChecker_Cfg.check_no_uvars; FStar_TypeChecker_Cfg.unmeta = uu___279_8446.FStar_TypeChecker_Cfg.unmeta; FStar_TypeChecker_Cfg.unascribe = uu___279_8446.FStar_TypeChecker_Cfg.unascribe; FStar_TypeChecker_Cfg.in_full_norm_request = uu___279_8446.FStar_TypeChecker_Cfg.in_full_norm_request; FStar_TypeChecker_Cfg.weakly_reduce_scrutinee = uu___279_8446.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee; FStar_TypeChecker_Cfg.nbe_step = uu___279_8446.FStar_TypeChecker_Cfg.nbe_step; FStar_TypeChecker_Cfg.for_extraction = uu___279_8446.FStar_TypeChecker_Cfg.for_extraction}); FStar_TypeChecker_Cfg.tcenv = uu___278_8443.FStar_TypeChecker_Cfg.tcenv; FStar_TypeChecker_Cfg.debug = uu___278_8443.FStar_TypeChecker_Cfg.debug; FStar_TypeChecker_Cfg.delta_level = uu___278_8443.FStar_TypeChecker_Cfg.delta_level; FStar_TypeChecker_Cfg.primitive_steps = uu___278_8443.FStar_TypeChecker_Cfg.primitive_steps; FStar_TypeChecker_Cfg.strong = uu___278_8443.FStar_TypeChecker_Cfg.strong; FStar_TypeChecker_Cfg.memoize_lazy = uu___278_8443.FStar_TypeChecker_Cfg.memoize_lazy; FStar_TypeChecker_Cfg.normalize_pure_lets = uu___278_8443.FStar_TypeChecker_Cfg.normalize_pure_lets; FStar_TypeChecker_Cfg.reifying = uu___278_8443.FStar_TypeChecker_Cfg.reifying})
in ((debug cfg1 (fun uu____8451 -> (

let uu____8452 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Calling NBE with (%s) {\n" uu____8452))));
(

let r = (

let uu____8456 = (translate cfg1 [] e)
in (readback cfg1 uu____8456))
in ((debug cfg1 (fun uu____8460 -> (

let uu____8461 = (FStar_Syntax_Print.term_to_string r)
in (FStar_Util.print1 "}\nNBE returned (%s)\n" uu____8461))));
r;
));
))))




