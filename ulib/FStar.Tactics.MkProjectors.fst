module FStar.Tactics.MkProjectors

open FStar.List.Tot
open FStar.Class.Embeddable
open FStar.Tactics.V2
open FStar.Class.Printable

exception NotFound

[@@plugin]
let mk_one_projector (unf:list string) (np:nat) (i:nat) : Tac unit =
  let _ = ignore (repeatn (np+1) intro) in
  let r = t_destruct (nth_var (-1)) in
  match r with
  | [(cons, arity)] -> begin
    if (i >= arity) then
      fail "proj: bad index in mk_one_projector";
    let bs = repeatn (arity+1) (fun () -> intro ()) in
    rewrite (nth_var (-1));
    norm [iota; delta_only unf; zeta_full];
    (* NB: ^ zeta_full above so we reduce under matches too. Since
    we are not unfolding anything but the projectors, which are
    not, recursive, this should not bring about any divergence. An
    alternative is to use NBE. *)
    let t = List.Tot.index bs i in
    exact t
  end
  | _ -> fail "proj: more than one case?"

let subst_map (ss : list (namedv * fv)) (r:term) (t : term) : Tac term =
  let subst = List.Tot.map (fun (x, fv) -> NT (Reflection.V2.pack_namedv x) (mk_e_app (Tv_FVar fv) [r])) ss in
  subst_term subst t

let binder_set_qual (q:aqualv) (b:binder) : binder =
  { b with qual = q }

let binder_to_term (b:binder) : Tot term =
  pack (Tv_Var (binder_to_namedv b))

let rec list_last #a (xs : list a) : Tac a =
  match xs with
  | [] -> fail "list_last: empty"
  | [x] -> x
  | _::xs -> list_last xs

let mk_proj_decl (is_method:bool)
                 (tyqn:name) ctorname univs indices (params:list binder) (idx:nat) (fieldnm : ppname_t) (fieldty : typ)
                 (unfold_names : list string)
                 (smap : list (namedv & fv))
: Tac (list sigelt & fv)
=
  let np = length params in
  let ni = length indices in
  let tyfv = pack_fv tyqn in
  let fv = pack_fv (cur_module () @ ["__proj__" ^ list_last ctorname ^ "__item__" ^ unseal fieldnm]) in
  let rty : binder = fresh_binder (mk_e_app (pack (Tv_FVar tyfv))
                                   (List.Tot.map binder_to_term (params @ indices)))
  in
  let s : typ = (rty <: binder).sort in
  //print ("rty " ^ term_to_string s);
  let projty = mk_tot_arr (List.Tot.map (binder_set_qual Q_Implicit) params
                           @ List.Tot.map (binder_set_qual Q_Implicit) indices
                           @ [rty])
                          (subst_map smap (binder_to_term rty) fieldty)
  in
  let se_proj = pack_sigelt <|
    Sg_Let {
      isrec = false;
      lbs = [{
              lb_fv  = fv;
              lb_us  = univs;
              lb_typ = projty;
              lb_def =
                 (* NB: the definition of the projector is again a tactic
                 invocation, so this whole thing has two phases. *)
                 (`(_ by (mk_one_projector
                            (`#(embed unfold_names))
                            (`#(embed (np+ni)))
                            (`#(embed #int idx)))))
    }]}
  in
  let maybe_se_method : list sigelt =
    if not is_method then [] else
    let meth_fv = pack_fv (cur_module () @ [unseal fieldnm]) in
    let s : typ = (rty <: binder).sort in
    let rty = { rty with qual = Q_Meta (`Typeclasses.tcresolve) } in
    let projty = mk_tot_arr (List.Tot.map (binder_set_qual Q_Implicit) params
                             @ List.Tot.map (binder_set_qual Q_Implicit) indices
                             @ [rty])
                            (subst_map smap (binder_to_term rty) fieldty)
    in
    [pack_sigelt <| Sg_Let {
      isrec = false;
      lbs = [{
              lb_fv  = meth_fv;
              lb_us  = univs;
              lb_typ = projty;
              lb_def =
                 (* NB: the definition of the projector is again a tactic
                 invocation, so this whole thing has two phases. *)
                 (`(_ by (mk_one_projector
                            (`#(embed unfold_names))
                            (`#(embed (np+ni)))
                            (`#(embed #int idx)))))
    }]}]

  in
  (se_proj :: maybe_se_method , fv)

[@@plugin]
let mk_projs (is_class:bool) (tyname:string) : Tac decls =
  let tyqn = explode_qn tyname in
  match lookup_typ (top_env ()) tyqn with
  | None ->
    raise NotFound
  | Some se ->
    match inspect_sigelt se with
    | Sg_Inductive {nm; univs; params; typ; ctors} ->
      if (length ctors <> 1) then
        fail "Expected an inductive with one constructor";
      let indices = fst (collect_arr_bs typ) in
      let [(ctorname, ctor_t)] = ctors in
      let (fields, _) = collect_arr_bs ctor_t in
      let (decls, _, _, _) =
        fold_left (fun (decls, smap, unfold_names, idx) (field : binder) ->
                     let (ds, fv) = mk_proj_decl is_class tyqn ctorname univs indices params idx field.ppname field.sort unfold_names smap in
                     (decls @ ds,
                      (binder_to_namedv field,fv)::smap,
                      (implode_qn (inspect_fv fv))::unfold_names,
                      idx+1))
                  ([], [], [], 0)
                  fields
      in
      decls
    | _ ->
      fail "not an inductive"
