module FStar.Reflection.Derived

open FStar.Reflection.Types
open FStar.Reflection.Basic
open FStar.Reflection.Data
open FStar.Reflection.Const
open FStar.Order

let name_of_bv (bv : bv) : string =
    (inspect_bv bv).bv_ppname

let type_of_bv (bv : bv) : typ =
    (inspect_bv bv).bv_sort

let bv_to_string (bv : bv) : string =
    let bvv = inspect_bv bv in
    "(" ^ bvv.bv_ppname ^ ":" ^ term_to_string bvv.bv_sort ^ ")"

let bv_of_binder (b : binder) : bv =
    let bv, _ = inspect_binder b in
    bv

let mk_binder (bv : bv) : binder =
    pack_binder bv Q_Explicit

let name_of_binder (b : binder) : string =
    name_of_bv (bv_of_binder b)

let type_of_binder (b : binder) : typ =
    type_of_bv (bv_of_binder b)

let binder_to_string (b : binder) : string =
    bv_to_string (bv_of_binder b) //TODO: print aqual

val flatten_name : name -> Tot string
let rec flatten_name ns =
    match ns with
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ "." ^ flatten_name ns

(* Helpers for dealing with nested applications and arrows *)
let rec collect_app' (args : list argv) (t : term) : Tot (term * list argv) (decreases t) =
    match inspect_ln t with
    | Tv_App l r ->
        collect_app' (r::args) l
    | _ -> (t, args)

val collect_app : term -> term * list argv
let collect_app = collect_app' []

let rec mk_app (t : term) (args : list argv) : Tot term (decreases args) =
    match args with
    | [] -> t
    | (x::xs) -> mk_app (pack_ln (Tv_App t x)) xs

// Helper for when all arguments are explicit
let mk_e_app (t : term) (args : list term) : Tot term =
    let e t = (t, Q_Explicit) in
    mk_app t (List.Tot.map e args)

let rec mk_tot_arr (bs: list binder) (cod : term) : Tot term (decreases bs) =
    match bs with
    | [] -> cod
    | (b::bs) -> pack_ln (Tv_Arrow b (pack_comp (C_Total (mk_tot_arr bs cod) None)))

let rec collect_arr' (bs : list binder) (c : comp) : Tot (list binder * comp) (decreases c) =
    begin match inspect_comp c with
    | C_Total t _ ->
        begin match inspect_ln t with
        | Tv_Arrow b c ->
            collect_arr' (b::bs) c
        | _ ->
            (bs, c)
        end
    | _ -> (bs, c)
    end

val collect_arr_bs : typ -> list binder * comp
let collect_arr_bs t =
    let (bs, c) = collect_arr' [] (pack_comp (C_Total t None)) in
    (List.Tot.rev bs, c)

val collect_arr : typ -> list typ * comp
let collect_arr t =
    let (bs, c) = collect_arr' [] (pack_comp (C_Total t None)) in
    let ts = List.Tot.map type_of_binder bs in
    (List.Tot.rev ts, c)

let rec collect_abs' (bs : list binder) (t : term) : Tot (list binder * term) (decreases t) =
    match inspect_ln t with
    | Tv_Abs b t' ->
        collect_abs' (b::bs) t'
    | _ -> (bs, t)

val collect_abs : term -> list binder * term
let collect_abs t =
    let (bs, t') = collect_abs' [] t in
    (List.Tot.rev bs, t')

let fv_to_string (fv:fv) : string = String.concat "." (inspect_fv fv)

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

let compare_binder (b1 b2 : binder) : order =
    let bv1, _ = inspect_binder b1 in
    let bv2, _ = inspect_binder b2 in
    compare_bv bv1 bv2
  
let rec compare_term (s t : term) : order =
    match inspect_ln s, inspect_ln t with
    | Tv_Var sv, Tv_Var tv ->
        compare_bv sv tv

    | Tv_BVar sv, Tv_BVar tv ->
        compare_bv sv tv

    | Tv_FVar sv, Tv_FVar tv ->
        compare_fv sv tv

    | Tv_App h1 a1, Tv_App h2 a2 ->
        lex (compare_term h1 h2) (fun () -> compare_argv a1 a2)

    | Tv_Abs b1 e1, Tv_Abs b2 e2 ->
        lex (compare_binder b1 b2) (fun () -> compare_term e1 e2)

    | Tv_Refine bv1 e1, Tv_Refine bv2 e2 ->
        lex (compare_bv bv1 bv2) (fun () -> compare_term e1 e2)

    | Tv_Arrow b1 e1, Tv_Arrow b2 e2 ->
        lex (compare_binder b1 b2) (fun () -> compare_comp e1 e2)

    | Tv_Type (), Tv_Type () ->
        Eq

    | Tv_Const c1, Tv_Const c2 ->
        compare_const c1 c2

    | Tv_Uvar u1 _, Tv_Uvar u2 _->
        compare_int u1 u2

    | Tv_Let r1 bv1 t1 t1', Tv_Let r2 bv2 t2 t2' ->
        lex (compare_bv bv1 bv2) (fun () ->
        lex (compare_term t1 t2) (fun () ->
             compare_term t1' t2'))

    | Tv_Match _ _, Tv_Match _ _ ->
        Eq // TODO

    | Tv_AscribedT e1 t1 tac1, Tv_AscribedT e2 t2 tac2 ->
        lex (compare_term e1 e2) (fun () ->
        lex (compare_term t1 t2) (fun () ->
        match tac1, tac2 with
        | None, None -> Eq
        | None, _  -> Lt
        | _, None -> Gt
        | Some e1, Some e2 -> compare_term e1 e2))

    | Tv_AscribedC e1 c1 tac1, Tv_AscribedC e2 c2 tac2 ->
        lex (compare_term e1 e2) (fun () ->
        lex (compare_comp c1 c2) (fun () ->
        match tac1, tac2 with
        | None, None -> Eq
        | None, _  -> Lt
        | _, None -> Gt
        | Some e1, Some e2 -> compare_term e1 e2))

    | Tv_Unknown, Tv_Unknown ->
        Eq

    // From here onwards, they must have different constructors. Order them arbitrarilly as in the definition.
    | Tv_Var _, _      -> Lt   | _, Tv_Var _      -> Gt
    | Tv_BVar _, _     -> Lt   | _, Tv_BVar _     -> Gt
    | Tv_FVar _, _     -> Lt   | _, Tv_FVar _     -> Gt
    | Tv_App _ _, _    -> Lt   | _, Tv_App _ _    -> Gt
    | Tv_Abs _ _, _    -> Lt   | _, Tv_Abs _ _    -> Gt
    | Tv_Arrow _ _, _  -> Lt   | _, Tv_Arrow _ _  -> Gt
    | Tv_Type (), _    -> Lt   | _, Tv_Type ()    -> Gt
    | Tv_Refine _ _, _ -> Lt   | _, Tv_Refine _ _ -> Gt
    | Tv_Const _, _    -> Lt   | _, Tv_Const _    -> Gt
    | Tv_Uvar _ _, _   -> Lt   | _, Tv_Uvar _ _   -> Gt
    | Tv_Match _ _, _  -> Lt   | _, Tv_Match _ _  -> Gt
    | Tv_AscribedT _ _ _, _  -> Lt | _, Tv_AscribedT _ _ _  -> Gt
    | Tv_AscribedC _ _ _, _  -> Lt | _, Tv_AscribedC _ _ _  -> Gt    
    | Tv_Unknown, _    -> Lt   | _, Tv_Unknown    -> Gt
and compare_argv (a1 a2 : argv) : order =
    let a1, q1 = a1 in
    let a2, q2 = a2 in
    match q1, q2 with
    (* We should never see Q_Meta here *)
    | Q_Implicit, Q_Explicit -> Lt
    | Q_Explicit, Q_Implicit -> Gt
    | _, _ -> compare_term a1 a2
and compare_comp (c1 c2 : comp) : order =
    let cv1 = inspect_comp c1 in
    let cv2 = inspect_comp c2 in
    match cv1, cv2 with
    | C_Total t1 md1, C_Total t2 md2 -> lex (compare_term t1 t2)
                                        (fun () -> match md1, md2 with
                                                   | None, None -> Eq
                                                   | None, Some _ -> Lt
                                                   | Some _, None -> Gt
                                                   | Some x, Some y -> compare_term x y)

    | C_Lemma p1 q1, C_Lemma p2 q2 -> lex (compare_term p1 p2) (fun () -> compare_term q1 q2)

    | C_Unknown, C_Unknown -> Eq
    | C_Total _ _, _  -> Lt | _, C_Total _ _ -> Gt
    | C_Lemma _ _, _  -> Lt | _, C_Lemma _ _ -> Gt
    | C_Unknown,   _  -> Lt | _, C_Unknown   -> Gt

let mk_stringlit (s : string) : term =
    pack_ln (Tv_Const (C_String s))

let mk_strcat (t1 t2 : term) : term =
    mk_e_app (pack_ln (Tv_FVar (pack_fv ["Prims"; "strcat"]))) [t1; t2]

let mk_cons (h t : term) : term =
   mk_e_app (pack_ln (Tv_FVar (pack_fv cons_qn))) [h; t]

let mk_cons_t (ty h t : term) : term =
   mk_app (pack_ln (Tv_FVar (pack_fv cons_qn))) [(ty, Q_Implicit); (h, Q_Explicit); (t, Q_Explicit)]

let rec mk_list (ts : list term) : term =
    match ts with
    | [] -> pack_ln (Tv_FVar (pack_fv nil_qn))
    | t::ts -> mk_cons t (mk_list ts)

let mktuple_n (ts : list term) : term =
    assume (List.Tot.length ts <= 8);
    match List.Tot.length ts with
    | 0 -> pack_ln (Tv_Const C_Unit)
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
           in mk_e_app (pack_ln (Tv_FVar (pack_fv qn))) ts
           end

let destruct_tuple (t : term) : option (list term) =
    let head, args = collect_app t in
    match inspect_ln head with
    | Tv_FVar fv ->
        if List.Tot.contains (inspect_fv fv) [mktuple2_qn; mktuple3_qn; mktuple4_qn; mktuple5_qn;
                                              mktuple6_qn; mktuple7_qn; mktuple8_qn]
        then Some (List.Tot.concatMap (fun (t, q) ->
                                      match q with
                                      | Q_Implicit -> []
                                      | Q_Explicit -> [t]) args)
        else None
    | _ -> None

let mkpair (t1 t2 : term) : term =
    mktuple_n [t1;t2]

let rec head (t : term) : term =
    match inspect_ln t with
    | Tv_Match t _
    | Tv_Let _ _ t _
    | Tv_Abs _ t
    | Tv_Refine _ t
    | Tv_App t _
    | Tv_AscribedT t _ _ 
    | Tv_AscribedC t _ _ -> head t

    | Tv_Unknown
    | Tv_Uvar _ _
    | Tv_Const _
    | Tv_Type _
    | Tv_Var _
    | Tv_BVar _
    | Tv_FVar _
    | Tv_Arrow _ _ -> t

let nameof (t : term) : string =
    match inspect_ln t with
    | Tv_FVar fv -> String.concat "." (inspect_fv fv)
    | _ -> "?"

let is_uvar (t : term) : bool =
    match inspect_ln (head t) with
    | Tv_Uvar _ _ -> true
    | _ -> false
