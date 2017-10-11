module FStar.Reflection.Syntax

open FStar.Reflection.Types
open FStar.Reflection.Basic
open FStar.Reflection.Data
open FStar.Order

val flatten_name : name -> Tot string
let rec flatten_name ns =
    match ns with
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ "." ^ flatten_name ns


// TODO: these are awful names
let imp_qn       = ["Prims"; "l_imp"]
let and_qn       = ["Prims"; "l_and"]
let or_qn        = ["Prims"; "l_or"]
let not_qn       = ["Prims"; "l_not"]
let iff_qn       = ["Prims"; "l_iff"]
let eq2_qn       = ["Prims"; "eq2"]
let eq1_qn       = ["Prims"; "eq"]
let true_qn      = ["Prims"; "l_True"]
let false_qn     = ["Prims"; "l_False"]
let b2t_qn       = ["Prims"; "b2t"]
let forall_qn    = ["Prims"; "l_Forall"]
let exists_qn    = ["Prims"; "l_Exists"]
let squash_qn    = ["Prims"; "squash"]

let bool_true_qn  = ["Prims"; "true"]
let bool_false_qn = ["Prims"; "false"]

let int_lid      = ["Prims"; "int"]
let bool_lid     = ["Prims"; "bool"]
let unit_lid     = ["Prims"; "unit"]

let add_qn       = ["Prims"; "op_Addition"]
let neg_qn       = ["Prims"; "op_Minus"]
let minus_qn     = ["Prims"; "op_Subtraction"]
let mult_qn      = ["Prims"; "op_Multiply"]
let mult'_qn     = ["FStar"; "Mul"; "op_Star"]
let div_qn       = ["Prims"; "op_Division"]
let lt_qn        = ["Prims"; "op_LessThan"]
let lte_qn       = ["Prims"; "op_LessThanOrEqual"]
let gt_qn        = ["Prims"; "op_GreaterThan"]
let gte_qn       = ["Prims"; "op_GreaterThanOrEqual"]
let mod_qn       = ["Prims"; "op_Modulus"]

let nil_qn       = ["Prims"; "Nil"]
let cons_qn      = ["Prims"; "Cons"]

let mktuple2_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple2"]
let mktuple3_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple3"]
let mktuple4_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple4"]
let mktuple5_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple5"]
let mktuple6_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple6"]
let mktuple7_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple7"]
let mktuple8_qn  = ["FStar"; "Pervasives"; "Native"; "Mktuple8"]

let land_qn    = ["FStar" ; "UInt" ; "logand"]
let lxor_qn    = ["FStar" ; "UInt" ; "logxor"]
let lor_qn     = ["FStar" ; "UInt" ; "logor"]
let shiftl_qn  = ["FStar" ; "UInt" ; "shift_left"]
let shiftr_qn  = ["FStar" ; "UInt" ; "shift_right"]
let udiv_qn    = ["FStar" ; "UInt" ; "udiv"]
let umod_qn    = ["FStar" ; "UInt" ; "mod"]
let mul_mod_qn = ["FStar" ; "UInt" ; "mul_mod"]
let nat_bv_qn  = ["FStar" ; "BV"   ; "int2bv"]

(* Helpers for dealing with nested applications and arrows *)
let rec collect_app' (args : list argv) (t : term) : Tot (term * list argv) (decreases t) =
    match inspect t with
    | Tv_App l r ->
        collect_app' (r::args) l
    | _ -> (t, args)

val collect_app : term -> term * list argv
let collect_app = collect_app' []

let rec mk_app (t : term) (args : list argv) : Tot term (decreases args) =
    match args with
    | [] -> t
    | (x::xs) -> mk_app (pack (Tv_App t x)) xs

// Helper for when all arguments are explicit
let mk_e_app (t : term) (args : list term) : Tot term =
    let e t = (t, Q_Explicit) in
    mk_app t (List.Tot.map e args)

let rec collect_arr' (typs : list typ) (c : comp) : Tot (list typ * comp) (decreases c) =
    begin match inspect_comp c with
    | C_Total t ->
        begin match inspect t with
        | Tv_Arrow b c ->
            let t = type_of_binder b in
            collect_arr' (t::typs) c
        | _ ->
            (typs, c)
        end
    | _ -> (typs, c)
    end

val collect_arr : typ -> list typ * comp
let collect_arr t =
    let (ts, c) = collect_arr' [] (pack_comp (C_Total t)) in
    (List.Tot.rev ts, c)

let rec collect_abs' (bs : list binder) (t : term) : Tot (list binder * term) (decreases t) =
    match inspect t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

val collect_abs : term -> list binder * term
let collect_abs t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.rev bs, t')

let fv_to_string (fv:fv) : string = String.concat "." (inspect_fv fv)

let binder_to_string b =
  "(" ^ inspect_bv b ^ ":" ^ term_to_string (type_of_binder b) ^ ")"

let compare_fv (f1 f2 : fv) : order =
    compare_list (fun s1 s2 -> order_from_int (String.compare s1 s2)) (inspect_fv f1) (inspect_fv f2)

let rec compare_const (c1 c2 : vconst) : order =
    match c1, c2 with
    | C_Unit, C_Unit -> Eq
    | C_Int i, C_Int j -> order_from_int (i - j)
    | C_True, C_True -> Eq
    | C_False, C_False -> Eq
    | C_String s1, C_String s2 -> order_from_int (String.compare s1 s2)
    | C_Unit,  _ -> Lt    | _, C_Unit  -> Gt
    | C_Int _, _ -> Lt    | _, C_Int _ -> Gt
    | C_True,  _ -> Lt    | _, C_True  -> Gt
    | C_False, _ -> Lt    | _, C_False -> Gt
    | C_String _, _ -> Lt | _, C_String _ -> Gt

let rec compare_term (s t : term) : order =
    match inspect s, inspect t with
    | Tv_Var sv, Tv_Var tv ->
        compare_binder sv tv

    | Tv_FVar sv, Tv_FVar tv ->
        compare_fv sv tv

    | Tv_App h1 a1, Tv_App h2 a2 ->
        lex (compare_term h1 h2) (fun () -> compare_argv a1 a2)

    | Tv_Abs b1 e1, Tv_Abs b2 e2
    | Tv_Refine b1 e1, Tv_Refine b2 e2 ->
        lex (compare_binder b1 b2) (fun () -> compare_term e1 e2)

    | Tv_Arrow b1 e1, Tv_Arrow b2 e2 ->
        lex (compare_binder b1 b2) (fun () -> compare_comp e1 e2)

    | Tv_Type (), Tv_Type () ->
        Eq

    | Tv_Const c1, Tv_Const c2 ->
        compare_const c1 c2

    | Tv_Uvar u1 _, Tv_Uvar u2 _->
        compare_int u1 u2

    | Tv_Let b1 t1 t1', Tv_Let b2 t2 t2' ->
        lex (compare_binder b1 b2) (fun () ->
        lex (compare_term t1 t2) (fun () ->
             compare_term t1' t2'))

    | Tv_Match _ _, Tv_Match _ _ ->
        Eq // TODO

    | Tv_Unknown, Tv_Unknown ->
        Eq

    // From here onwards, they must have different constructors. Order them arbitrarilly as in the definition.
    | Tv_Var _, _      -> Lt   | _, Tv_Var _      -> Gt
    | Tv_FVar _, _     -> Lt   | _, Tv_FVar _     -> Gt
    | Tv_App _ _, _    -> Lt   | _, Tv_App _ _    -> Gt
    | Tv_Abs _ _, _    -> Lt   | _, Tv_Abs _ _    -> Gt
    | Tv_Arrow _ _, _  -> Lt   | _, Tv_Arrow _ _  -> Gt
    | Tv_Type (), _    -> Lt   | _, Tv_Type ()    -> Gt
    | Tv_Refine _ _, _ -> Lt   | _, Tv_Refine _ _ -> Gt
    | Tv_Const _, _    -> Lt   | _, Tv_Const _    -> Gt
    | Tv_Uvar _ _, _   -> Lt   | _, Tv_Uvar _ _   -> Gt
    | Tv_Match _ _, _  -> Lt   | _, Tv_Match _ _  -> Gt
    | Tv_Unknown, _    -> Lt   | _, Tv_Unknown    -> Gt
and compare_argv (a1 a2 : argv) : order =
    let a1, q1 = a1 in
    let a2, q2 = a2 in
    match q1, q2 with
    | Q_Implicit, Q_Explicit -> Lt
    | Q_Explicit, Q_Implicit -> Gt
    | _, _ -> compare_term a1 a2
and compare_comp (c1 c2 : comp) : order =
    let cv1 = inspect_comp c1 in
    let cv2 = inspect_comp c2 in
    match cv1, cv2 with
    | C_Total t1, C_Total t2 -> compare_term t1 t2
    | C_Lemma p1 q1, C_Lemma p2 q2 -> lex (compare_term p1 p2) (fun () -> compare_term q1 q2)

    | C_Unknown, C_Unknown -> Eq
    | C_Total _,   _  -> Lt | _, C_Total _   -> Gt
    | C_Lemma _ _, _  -> Lt | _, C_Lemma _ _ -> Gt
    | C_Unknown,   _  -> Lt | _, C_Unknown   -> Gt

let mk_stringlit (s : string) : term =
    pack (Tv_Const (C_String s))

let mk_strcat (t1 t2 : term) : term =
    mk_e_app (pack (Tv_FVar (pack_fv ["Prims"; "strcat"]))) [t1; t2]

let mk_cons (h t : term) : term =
   mk_e_app (pack (Tv_FVar (pack_fv cons_qn))) [h; t]

let mk_cons_t (ty h t : term) : term =
   mk_app (pack (Tv_FVar (pack_fv cons_qn))) [(ty, Q_Implicit); (h, Q_Explicit); (t, Q_Explicit)]

let rec mk_list (ts : list term) : term =
    match ts with
    | [] -> pack (Tv_FVar (pack_fv nil_qn))
    | t::ts -> mk_cons t (mk_list ts)

let mktuple_n (ts : list term) : term =
    assume (List.length ts <= 8);
    match List.length ts with
    | 0 -> pack (Tv_Const C_Unit)
    | 1 -> let [x] = ts in x
    | n -> begin
           let qn = match n with
                    | 2 -> mktuple2_qn
                    | 3 -> mktuple3_qn
                    | 4 -> mktuple4_qn
                    | 5 -> mktuple5_qn
                    | 6 -> mktuple6_qn
                    | 7 -> mktuple7_qn
                    | 8 -> mktuple8_qn
           in mk_e_app (pack (Tv_FVar (pack_fv qn))) ts
           end

let mkpair (t1 t2 : term) : term =
    mktuple_n [t1;t2]
