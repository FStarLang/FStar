module BinderAttributes

module T = FStar.Tactics
open FStar.List.Tot

let default_to (def : 'a) (x : option 'a) : Tot 'a =
    match x with
    | None -> def
    | Some a -> a

type description (d : string) = ()

type inductive_example =
    | CaseExplicit : [@@@ description "x"] x:int -> [@@@ description "y"] y:string -> inductive_example
    | CaseImplicit : #[@@@ description "x_imp"] x_imp:int -> #[@@@ description "y_imp"] y_imp:string -> inductive_example
    | CaseMixed : #[@@@ description "x_imp"] x_imp:int -> [@@@ description "y"] y:string -> inductive_example

let f (#[@@@ description "x_imp"] x_imp:int) ([@@@ description "y"] y:string) : Tot unit =
    ()

let f2 (#[@@@ description "x_imp"]x_imp [@@@ description "y"]y : int) : Tot unit =
    ()

type binder =
    {
        qual : string;
        desc : option string;
        name : string
    }
type binders = list binder

// We assume there's always just one attribute 'description' for simplicity
let get_description (t : T.term) : T.Tac string =
    match T.inspect t with
    | T.Tv_App _ (v, _) -> begin
        match T.inspect v with
        | T.Tv_Const c -> begin
            match c with
            | T.C_String desc -> desc
            | _ -> T.fail "Expected string description"
            end
        | _ -> T.fail "Expected constant as a value of description attribute"
        end
    | _ -> T.fail "Expected description attribute"

let binder_to_string (b : binder) : Tot string =
    let desc = default_to "no description" b.desc in
    "(" ^ b.name ^ ", " ^ b.qual ^ ", " ^ desc ^ ")"

let rec binders_to_string (b : binders) : Tot string =
    match b with
    | [] -> "[]"
    | ba :: bs ->
        let desc = default_to "no description" ba.desc in
        (binder_to_string ba) ^ " :: " ^ (binders_to_string bs)

let binder_from_term (b : T.binder) : T.Tac binder =
    let (bv, (qual, attrs)) = T.inspect_binder b in
    let desc_opt = match attrs with | [] -> None | a :: as -> Some (get_description a) in
    let q = match qual with | T.Q_Implicit -> "Implicit" | T.Q_Explicit -> "Explicit" | T.Q_Meta _ -> "Meta" in
    let bvv = T.inspect_bv bv in
    let open FStar.Tactics in
    { name = bvv.bv_ppname; qual = q; desc = desc_opt }

let rec binders_from_arrow (ty : T.term) : T.Tac binders =
    match T.inspect_ln ty with
    | T.Tv_Arrow b comp -> begin
        let ba = binder_from_term b in
        match T.inspect_comp comp with
        | T.C_Total ty2 _ -> ba :: binders_from_arrow ty2
        | _ -> T.fail "Unsupported computation type"
        end
    | T.Tv_FVar fv -> [] //last part
    | _ -> T.fail "Expected an arrow type"

let binders_from_term (env : T.env) (qname : list string) : T.Tac (list binders) =
    let b =
        match T.lookup_typ env qname with
        | Some s -> begin
            match T.inspect_sigelt s with
            | T.Sg_Let _ lbs -> begin
                let lbv = T.lookup_lb_view lbs qname in
                [ binders_from_arrow T.(lbv.lb_typ) ] // single binder in letbinding
                end
            | T.Sg_Inductive _ _ _ _ cts -> begin
                T.map (fun ctr -> binders_from_arrow (snd ctr)) cts
                end
            | _ -> T.fail "Expected let binding or inductive"
            end
        | None -> T.fail "Could not find definition"
    in
    b

let compare_binders (expected : binder) (actual : binder) : Tot bool =
    expected.name = actual.name && expected.desc = actual.desc && expected.qual = actual.qual

let rec validate (expected : binders) (actual : binders) : T.Tac unit =
    match expected, actual with
    | [], [] -> () // pass
    | x :: xs, y :: ys ->
        if compare_binders x y
            then validate xs ys
            else
                begin
                T.print ("Expected " ^ (binder_to_string x) ^ " got " ^ (binder_to_string y));
                T.fail "Test failed. Different results"
                end
    | _, _ -> T.fail "Test failed. Expected different number of binders"

let rec iter2 (f : 'a -> 'b -> T.Tac unit) (l1 : list 'a) (l2 : list 'b) : T.Tac unit =
    match l1, l2 with
    | [], [] -> ()
    | x :: xs, y :: ys -> begin
        f x y;
        iter2 f xs ys
        end
    | _, _ -> T.fail "Lists have different sizes"

let _ =
    assert True by begin
        let b = binders_from_term (T.top_env()) (T.explode_qn (`%inductive_example)) in
        let bss = T.map (fun b -> binders_to_string b) b in
        let expected =
            [
                [{ name = "x"; qual = "Explicit"; desc = Some "x"; }; { name = "y"; qual = "Explicit"; desc = Some "y"; }];
                [{ name = "x_imp"; qual = "Implicit"; desc = Some "x_imp"; }; { name = "y_imp"; qual = "Implicit"; desc = Some "y_imp"; }];
                [{ name = "x_imp"; qual = "Implicit"; desc = Some "x_imp"; }; { name = "y"; qual = "Explicit"; desc = Some "y"; }];
            ] in
        iter2 (fun ex bs -> validate ex bs) expected b
    end

let _ =
    assert True by begin
        let b = binders_from_term (T.top_env()) (T.explode_qn (`%f)) in
        let bss = T.map (fun b -> binders_to_string b) b in
        let expected = [[{ name = "x_imp"; qual = "Implicit"; desc = Some "x_imp"; }; { name = "y"; qual = "Explicit"; desc = Some "y"; }]] in
        iter2 (fun ex bs -> validate ex bs) expected b
    end

let _ =
    assert True by begin
        let b = binders_from_term (T.top_env()) (T.explode_qn (`%f2)) in
        let bss = T.map (fun b -> binders_to_string b) b in
        let expected = [[{ name = "x_imp"; qual = "Implicit"; desc = Some "x_imp"; }; { name = "y"; qual = "Explicit"; desc = Some "y"; }]] in
        iter2 (fun ex bs -> validate ex bs) expected b
    end
