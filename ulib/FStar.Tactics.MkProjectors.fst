module FStar.Tactics.MkProjectors

(* NB: We cannot use typeclasses here, or any module that depends on
them, since they use the tactics defined here. So we must be careful
with our includes. *)
open FStar.List.Tot
open FStar.Reflection.V2
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Syntax.Syntax
open FStar.Tactics.V2.SyntaxCoercions
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Tactics.V2.Derived
open FStar.Tactics.Util
open FStar.Tactics.NamedView

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

let binder_mk_implicit (b:binder) : binder =
  let q =
    match b.qual with
    | Q_Explicit -> Q_Implicit
    | q -> q (* keep Q_Meta as it is *)
  in
  { b with qual = q }

let binder_to_term (b:binder) : Tot term =
  pack (Tv_Var (binder_to_namedv b))

let binder_argv (b:binder) : Tot argv =
  let q =
    match b.qual with
    | Q_Meta _ -> Q_Implicit
    | q -> q
  in
  (binder_to_term b, q)

let rec list_last #a (xs : list a) : Tac a =
  match xs with
  | [] -> fail "list_last: empty"
  | [x] -> x
  | _::xs -> list_last xs

let embed_int (i:int) : term =
  let open FStar.Reflection.V2 in
  pack_ln (Tv_Const (C_Int i))

let rec embed_string_list (xs : list string) : term =
  let open FStar.Reflection.V2 in
  match xs with
  | [] -> `Nil
  | x::xs ->
    let t = pack_ln (Tv_Const (C_String x)) in
    `(Cons #string (`#t) (`#(embed_string_list xs)))

let mk_proj_decl (is_method:bool)
                 (tyqn:name) ctorname (univs : list univ_name) indices (params:list binder)
                 (idx:nat)
                 (field : binder)
                 (unfold_names : list string)
                 (smap : list (namedv & fv))
: Tac (list sigelt & fv)
=
  let np = length params in
  let ni = length indices in
  let tyfv = pack_fv tyqn in
  let fv = pack_fv (cur_module () @ ["__proj__" ^ list_last ctorname ^ "__item__" ^ unseal field.ppname]) in
  let rty : term =
    let hd = pack (Tv_UInst tyfv (List.Tot.map (fun un -> pack_universe (Uv_Name un)) univs)) in
    mk_app hd (List.Tot.map binder_argv (params @ indices))
  in
  let rb : binder = fresh_binder rty in
  let projty = mk_tot_arr (List.Tot.map binder_mk_implicit (params @ indices)
                           @ [rb])
                          (subst_map smap (binder_to_term rb) field.sort)
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
                            (`#(embed_string_list unfold_names))
                            (`#(embed_int (np+ni)))
                            (`#(embed_int idx)))))
    }]}
  in
  let maybe_se_method : list sigelt =
    if not is_method then [] else
    if List.existsb (Reflection.V2.TermEq.term_eq (`Typeclasses.no_method)) field.attrs then [] else
    let meth_fv = pack_fv (cur_module () @ [unseal field.ppname]) in
    let rb = { rb with qual = Q_Meta (`Typeclasses.tcresolve) } in
    let projty = mk_tot_arr (List.Tot.map binder_mk_implicit (params @ indices)
                             @ [rb])
                            (subst_map smap (binder_to_term rb) field.sort)
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
                            (`#(embed_string_list unfold_names))
                            (`#(embed_int (np+ni)))
                            (`#(embed_int idx)))))
    }]}]
  in
  (* Propagate binder attributes, i.e. attributes in the field
  decl, to the method itself. *)
  let se_proj = set_sigelt_attrs (field.attrs @ sigelt_attrs se_proj) se_proj in

  (* Do we need to set the sigelt's Projector qual? If so,
  here is how to do it, but F* currently rejects tactics
  trying to generate "internal" qualifiers like Projector. However,
  it does not seem to make a difference. *)
  // let se_proj = set_sigelt_quals (
  //                 Projector (tyqn, pack_ident (unseal field.ppname, range_0)) ::
  //                 sigelt_quals se_proj) se_proj
  // in
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
                     let (ds, fv) = mk_proj_decl is_class tyqn ctorname univs indices params idx field unfold_names smap in
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
