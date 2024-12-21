module FStar.Tactics.TypeRepr

//#set-options "--print_implicits --print_full_names --print_universes"

open FStar.Tactics.V2.Bare

let add_suffix (s:string) (nm:name) : name =
  explode_qn (implode_qn nm ^ s)

let unitv_                 : term = `()
let unitt_                 : term = `(unit)
let empty_                 : term = `(empty)
let either_ (a b : term)   : term = `(either (`#a) (`#b))
let tuple2_ (a b : term)   : term = `(tuple2 (`#a) (`#b))
let mktuple2_ (a b : term) : term = `(Mktuple2 (`#a) (`#b))

let get_inductive_typ (nm:string) : Tac (se:sigelt_view{Sg_Inductive? se}) =
  let e = top_env () in
  let se = lookup_typ e (explode_qn nm) in
  match se with
  | None -> fail "ctors_of_typ: type not found"
  | Some se ->
    let sev = inspect_sigelt se in
    if Sg_Inductive? sev then
      sev
    else
      fail "ctors_of_typ: not an inductive type"

let alg_ctor (ty : typ) : Tac typ =
  let tys, c = collect_arr ty in
  Tactics.Util.fold_right (fun ty acc -> tuple2_ ty acc) tys unitt_

[@@plugin]
let generate_repr_typ (params : binders) (ctors : list ctor)  : Tac typ =
  let ctor_typs = Util.map (fun (_, ty) -> alg_ctor ty) ctors in
  let alternative_typ =
    Util.fold_right (fun ty acc -> either_ ty acc) ctor_typs empty_ in
  alternative_typ

(* Expects a goal of type [t -> t_repr] *)
[@@plugin]
let generate_down () : Tac unit =
  let b = intro () in
  let cases = t_destruct b in
  cases |> Util.iteri #(fv & nat) (fun i (c, n) ->
    let bs = repeatn n (fun _ -> intro ()) in
    let _b_eq = intro () in
    let sol = Util.fold_right (fun (b:binding) acc -> mktuple2_ b acc) bs unitv_ in
    let _ = repeatn i (fun _ -> apply (`Inr)) in
    apply (`Inl);
    exact sol
  )

let rec get_apply_tuple (b:binding) : Tac (list binding) =
  let hd, args = collect_app b.sort in
  match inspect hd, args with
  | Tv_UInst fv _, [b1; b2]
  | Tv_FVar fv, [b1; b2] ->
    if inspect_fv fv = explode_qn (`%tuple2) then
      let cases = t_destruct b in
      guard (List.Tot.length cases = 1 && inspect_fv (fst (List.Tot.hd cases)) = explode_qn (`%Mktuple2) && snd (List.Tot.hd cases) = 2);
      let b1 = intro () in
      let b2 = intro () in
      let _eq = intro () in
      b1 :: get_apply_tuple b2
    else
      fail ("unexpected term in apply_tuple: " ^ term_to_string b.sort)
  | Tv_FVar fv, [] ->
    if inspect_fv fv = explode_qn (`%unit) then
      []
    else
      fail ("unexpected term in apply_tuple: " ^ term_to_string b.sort)
  | _ ->
    fail ("unexpected term in apply_tuple: " ^ term_to_string b.sort)

(* Expects a goal of type [t_repr -> t] *)

let rec generate_up_aux (ctors : list ctor) (b:binding) : Tac unit =
  match ctors with
  | [] ->
    (* b must have type empty, it's the finisher for the cases *)
    apply (`empty_elim);
    exact b
  | c::cs ->
    let cases = t_destruct b in
    if List.Tot.length cases <> 2 then
      fail "generate_up_aux: expected Inl/Inr???";
    focus (fun () ->
      let b' = intro () in
      let _eq = intro () in
      let c_name = fst c in
      let args = get_apply_tuple b' in
      apply (pack (Tv_FVar (pack_fv c_name)));
      Util.iter (fun (b:binding) -> exact b) args;
      qed()
    );
    let b = intro () in
    let _eq = intro () in
    generate_up_aux cs b

(* Expects a goal of type [t_repr -> t] *)
[@@plugin]
let generate_up (nm:string) () : Tac unit =
  let Sg_Inductive {ctors} = get_inductive_typ nm in
  let b = intro () in
  generate_up_aux ctors b

let make_implicits (bs : binders) : binders =
  bs |> List.Tot.map (fun b ->
    match b.qual with
    | Q_Explicit -> { b with qual = Q_Implicit }
    | _ -> b
  )

let binder_to_argv (b:binder) : argv =
  (binder_to_term b, b.qual)

let generate_all (nm:name) (params:binders) (ctors : list ctor) : Tac decls =
  let params_i = make_implicits params in
  let t =      mk_app (pack (Tv_FVar (pack_fv nm))) (List.Tot.map binder_to_argv params) in
  let t_repr = generate_repr_typ params ctors in
  let se_repr = pack_sigelt <| Sg_Let {
    isrec = false;
    lbs = [{
      lb_fv = pack_fv (add_suffix "_repr" nm);
      lb_us = [];
      lb_typ = mk_arr params <| C_Total (`Type);
      lb_def = mk_abs params t_repr;
    }]
  }
  in
  
  let down_def =
    `(_ by (generate_down ()))
  in
  let down_def = mk_abs params_i down_def in
  let se_down =
    let b = fresh_binder t in
    pack_sigelt <| Sg_Let {
      isrec = false;
      lbs = [{
        lb_fv = pack_fv (add_suffix "_down" nm);
        lb_us = [];
        lb_typ = mk_tot_arr params_i <| Tv_Arrow b (C_Total t_repr);
        lb_def = down_def;
      }]
  }
  in
  let up_def =
    `(_ by (generate_up (`#(pack (Tv_Const (C_String (implode_qn nm))))) ()))
  in
  let up_def = mk_abs params_i up_def in
  let se_up =
    let b = fresh_binder t_repr in
    pack_sigelt <| Sg_Let {
      isrec = false;
      lbs = [{
        lb_fv = pack_fv (add_suffix "_up" nm);
        lb_us = [];
        lb_typ = mk_tot_arr params_i <| Tv_Arrow b (C_Total t);
        lb_def = up_def;
      }]
  }
  in
  [se_repr; se_down; se_up]

[@@plugin]
let entry (nm : string) : Tac decls =
  let Sg_Inductive {params; nm; ctors} = get_inductive_typ nm in
  generate_all nm params ctors
