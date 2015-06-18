#light "off"
 
module Microsoft.FStar.ToSMT.SplitQueryCases

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.ToSMT.Term

let rec is_ite_all_the_way (t:term) :bool = match t.tm with
    | App (ITE, _::_::eb::_) ->
      (
        match eb.tm with
            | FreeV _ -> true
            | _       -> is_ite_all_the_way eb
      )
    | _ -> false

let rec parse_query_for_split_cases (t:term) (f:term -> term) :bool * (term * (term -> term)) = match t.tm with
    | Quant (Forall, l, opt, l', t) ->
      parse_query_for_split_cases t (fun x -> f ((mkForall'' (l, opt, l', x))))

    | App (Imp, t1::t2::_) ->
      let r =
        match t2.tm with
            | Quant (Forall, _, _, _, _) ->
              parse_query_for_split_cases t2 (fun x -> f (mkImp (t1, x)))

            | App (ITE, _) when is_ite_all_the_way t2 ->
              true, (t2, (fun x -> f (mkImp (t1, x))))

            | _ -> false, (mkFalse, (fun _ -> mkFalse))
      in
      r

    | App (ITE, _) when is_ite_all_the_way t ->
      true, (t, f)

    | _ -> false, (mkFalse, (fun _ -> mkFalse))

let strip_not (t:term) :term = match t.tm with
    | App (Not, hd::_) -> hd
    | _                -> t

(* return t1 = ite term for n cases, t2 = conj of neg of all guards, t3 = rest of the input term *)
let rec get_next_n_cases (n:int) (t:term) :term * term * term =
    if n <= 0 then mkTrue, mkTrue, t
    else
        match t.tm with
            | App (ITE, guard::tb::eb::l') ->
              let t', gs, rest = get_next_n_cases (n - 1) eb in
              mkApp' (ITE, guard::tb::t'::l'), mkAnd ((mkNot guard), gs), rest

            | FreeV fv -> mkTrue, mkTrue, t

            | _ -> raise Impos

let rec check_split_cases (f:term -> term) (q:term) (neg_guards:term) (check:decl -> unit) :term =
    match q.tm with
        | App (ITE, _) ->
          let t, gs, rest = get_next_n_cases (!Options.split_cases) q in
          let t' = f (mkImp (neg_guards, t)) in
          let _ = check (Assume (mkNot t', None)) in
          check_split_cases f rest (mkAnd (neg_guards, gs)) check

        | FreeV fv -> mkAnd (neg_guards, mkNot q)

        | _ -> raise Impos

let check_exhaustiveness (f:term -> term) (neg_guards:term) (check:decl -> unit) :unit =
    check (Assume (mkNot (f (mkNot neg_guards)), None))

let can_handle_query (q:decl) :bool * (term * (term -> term)) =
    match q with
        | Assume(q', _) -> parse_query_for_split_cases (strip_not q') (fun x -> x)
        | _ -> false, (mkFalse, (fun x -> x))

let r = ref 0

let handle_query ((t, f):(term * (term -> term))) (n:int) (check:decl -> unit) :unit =
    let l = check_split_cases f t mkTrue check in
    check_exhaustiveness f l check
