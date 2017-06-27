module Printers

open FStar.Tactics

let mk_lit (s : string) : term =
    pack (Tv_Const (C_String s))

let mk_strcat (t1 t2 : term) : term =
    mk_app (pack (Tv_FVar (pack_fv ["FStar";"String"; "strcat"]))) [t1; t2]

let rec mk_concat (ts : list term) : term =
    match ts with
    | [] ->
        mk_lit ""
    | t::ts ->
        mk_strcat t (mk_concat ts)

let paren (e : term) : term =
    mk_strcat (mk_lit "(") (mk_strcat e (mk_lit ")"))

let printer : tactic unit =
    x <-- intro;
    e <-- cur_env;
    let xt = type_of_binder x in
    xt_ns <-- (match inspect xt with
               | Tv_FVar fv -> return (inspect_fv fv)
               | _ -> fail "not a qname type?");
    match lookup_typ e xt_ns with
    | Unk -> fail "type not found?"
    | Sg_Inductive _ bs t ctors ->
        let br1 ctor = match ctor with | Ctor name t ->
            let pn = String.concat "." name in
            let _, t_args = collect_arr t in
            let bs = List.Tot.map (fun ti -> Pat_Wild (fresh_binder ti)) t_args in
            let bod = pack (Tv_Const (C_String pn)) in
            let bod = match bs with | [] -> bod | _ -> paren bod in
            (Pat_Cons (pack_fv name) bs, bod)
        in
        let branches = List.Tot.map br1 ctors in
        let m = pack (Tv_Match (pack (Tv_Var x)) branches) in
        exact (return m)

type t1 =
    | A of int
    | B of string
    | C

let t1_print : t1 -> string = synth_by_tactic printer

let _ = assert_norm (t1_print (A 8) = "(Printers.A)")
let _ = assert_norm (t1_print (B "thing") = "(Printers.B)")
let _ = assert_norm (t1_print C = "Printers.C")
