module MultipleAttributesBinder

module T = FStar.Tactics
open FStar.List.Tot

type attr_value =
    | String : v:string -> attr_value
    | Int : v:int -> attr_value

type attr1 (v : string) = ()
type attr2 (v : int) = ()
type attr3 (v : attr_value) = ()

let f (#[@@@ attr1 "imp"; attr2 1; attr3 (String "x")] x_imp:int) ([@@@ attr1 "exp"; attr2 2; attr3 (String "y")] y:string) : Tot unit =
    ()

noeq type binder =
    {
        qual : string;
        attrs : list T.term;
        name : string
    }
type binders = list binder

let binder_from_term (b : T.binder) : T.Tac binder =
    let (bv, (qual, a)) = T.inspect_binder b in
    let q = match qual with | T.Q_Implicit -> "Implicit" | T.Q_Explicit -> "Explicit" | T.Q_Meta _ -> "Meta" in
    let bvv = T.inspect_bv bv in
    let open FStar.Tactics in
    { name = bvv.bv_ppname; qual = q; attrs = a }

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
        let bs =
            match (binders_from_term (T.top_env()) (T.explode_qn (`%f))) with
            | bs::_ -> bs
            | _ -> T.fail "Failed to collect binders from 'f'"
        in

        let expected_bs =
            [
                { name = "x_imp"; qual = "Implicit"; attrs = [ `(attr1 "imp"); `(attr2 1); `(attr3 (String "x")) ]; };
                { name = "y";     qual = "Explicit"; attrs = [ `(attr1 "exp"); `(attr2 2); `(attr3 (String "y")) ]; }
            ]
        in
        iter2 (fun e_b b ->
            if not (e_b.name = b.name) then T.fail "Binder names are different";
            if not (e_b.qual = b.qual) then T.fail "Binder quals are different";
            iter2 (fun e_a a ->
                if not (T.term_to_ast_string e_a = T.term_to_ast_string a)
                    then T.fail ("Expected " ^ (T.term_to_ast_string e_a) ^ " got " ^ (T.term_to_ast_string a))
            ) e_b.attrs b.attrs
        ) expected_bs bs
    end
