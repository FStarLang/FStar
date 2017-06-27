module Printers

open FStar.Tactics

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
            (Pat_Cons (pack_fv name) [], pack (Tv_Const (C_String pn)))
        in
        let branches = List.Tot.map br1 ctors in
        let m = pack (Tv_Match (pack (Tv_Var x)) branches) in
        exact (return m)

type t1 =
    | A
    | B
    | C

let t1_print : t1 -> string = synth_by_tactic printer

let _ = assert (t1_print A = "Printers.A")
let _ = assert (t1_print B = "Printers.B")
let _ = assert (t1_print C = "Printers.C")
