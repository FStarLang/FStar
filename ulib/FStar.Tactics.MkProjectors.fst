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

let meta_projectors = ()

(* Thunked version of debug *)
let debug (f : unit -> Tac string) : Tac unit =
  if debugging () then
    print (f ())

[@@plugin]
let mk_one_projector (unf:list string) (np:nat) (i:nat) : Tac unit =
  debug (fun () -> dump "ENTRY mk_one_projector"; "");
  let _params = Stubs.Tactics.V2.Builtins.intros np in
  let thing : binding = intro () in
  let r = t_destruct thing in
  match r with
  | [(cons, arity)] -> begin
    if (i >= arity) then
      fail "proj: bad index in mk_one_projector";
    let _      = Stubs.Tactics.V2.Builtins.intros i in
    let the_b  = intro () in
    let _      = Stubs.Tactics.V2.Builtins.intros (arity-i-1) in
    let eq_b   : binding = intro () in
    rewrite eq_b;
    norm [iota; delta_only unf; zeta_full];
    (* NB: ^ zeta_full above so we reduce under matches too. Since
    we are not unfolding anything but the projectors, which are
    not, recursive, this should not bring about any divergence. An
    alternative is to use NBE. *)
    exact the_b
  end
  | _ -> fail "proj: more than one case?"

[@@plugin]
let mk_one_method (proj:string) (np:nat) : Tac unit =
  debug (fun () -> dump "ENTRY mk_one_method"; "");
  let nm = explode_qn proj in
  let params = repeatn np (fun () -> let b : binding = intro () in
                                     (binding_to_term b, Q_Implicit)) in
  let thing : binding = intro () in
  let proj = pack (Tv_FVar (pack_fv nm)) in
  exact (mk_app proj (params @ [(binding_to_term thing, Q_Explicit)]))

let subst_map (ss : list (namedv & fv)) (r:term) (t : term) : Tac term =
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

let embed_string (s:string) : term =
  let open FStar.Reflection.V2 in
  pack_ln (Tv_Const (C_String s))

(* For compatibility: the typechecker sets this attribute for all
projectors. Karamel relies on it to do inlining. *)
let substitute_attr : term =
  `Pervasives.Substitute

let mk_proj_decl (is_method:bool)
                 (tyqn:name) ctorname
                 (univs : list univ_name)
                 (params : list binder)
                 (idx:nat)
                 (field : binder)
                 (unfold_names_tm : term)
                 (smap : list (namedv & fv))
: Tac (list sigelt & fv)
=
  debug (fun () -> "Processing field " ^ unseal field.ppname);
  debug (fun () -> "Field typ = " ^ term_to_string field.sort);
  let np = length params in
  let tyfv = pack_fv tyqn in
  let nm : name = cur_module () @ ["__proj__" ^ list_last ctorname ^ "__item__" ^ unseal field.ppname] in
  let fv = pack_fv nm in
  let rty : term =
    let hd = pack (Tv_UInst tyfv (List.Tot.map (fun un -> pack_universe (Uv_Name un)) univs)) in
    mk_app hd (List.Tot.map binder_argv params)
  in
  let rb : binder = fresh_binder rty in
  let projty = mk_tot_arr (List.Tot.map binder_mk_implicit params
                           @ [rb])
                          (subst_map smap (binder_to_term rb) field.sort)
  in
  debug (fun () -> "Proj typ = " ^ term_to_string projty);
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
                            (`#unfold_names_tm)
                            (`#(embed_int np))
                            (`#(embed_int idx)))))
    }]}
  in
  let maybe_se_method : list sigelt =
    if not is_method then [] else
    if List.existsb (Reflection.TermEq.Simple.term_eq (`Typeclasses.no_method)) field.attrs then [] else
    let meth_fv = pack_fv (cur_module () @ [unseal field.ppname]) in
    let rb = { rb with qual = Q_Meta (`Typeclasses.tcresolve) } in
    let projty = mk_tot_arr (List.Tot.map binder_mk_implicit params
                             @ [rb])
                            (subst_map smap (binder_to_term rb) field.sort)
    in
    (* The method is just defined based on the projector. *)
    let lb_def =
      if true
      then
        (* This generates a method defined to be equal to the projector
             i.e.  method {| c |} = c.method *)
        (`(_ by (mk_one_method
                   (`#(embed_string (implode_qn nm)))
                   (`#(embed_int np)))))
      else
        (* This defines the method in the same way as the projector
             i.e.  method {| c |} = match c with | Mk ... method ... -> method *)
        (`(_ by (mk_one_projector
                   (`#unfold_names_tm)
                   (`#(embed_int np))
                   (`#(embed_int idx)))))
    in
    (* dump ("returning se with name " ^ unseal field.ppname); *)
    (* dump ("def = " ^ term_to_string lb_def); *)
    let se = pack_sigelt <| Sg_Let {
      isrec = false;
      lbs = [{
              lb_fv  = meth_fv;
              lb_us  = univs;
              lb_typ = projty;
              lb_def = lb_def;
      }]}
    in
    [se]
  in
  (* Propagate binder attributes, i.e. attributes in the field
  decl, to the method itself. *)
  let se_proj = set_sigelt_attrs (substitute_attr :: field.attrs @ sigelt_attrs se_proj) se_proj in

  (* Do we need to set the sigelt's Projector qual? If so,
  here is how to do it, but F* currently rejects tactics
  trying to generate "internal" qualifiers like Projector. However,
  it does not seem to make a difference. *)
  (* In fact, it seems to trip the encoding as soon as a field
  has more binders, since the encoding has some primitive treatment
  for projectors/discriminators. *)
  //let se_proj = set_sigelt_quals (
  //                Projector (ctorname, pack_ident (unseal field.ppname, range_0)) ::
  //                sigelt_quals se_proj) se_proj
  //in
  (se_proj :: maybe_se_method , fv)

[@@plugin]
let mk_projs (is_class:bool) (tyname:string) : Tac decls =
  debug (fun () -> "!! mk_projs tactic called on: " ^ tyname);
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
      if Cons? indices then
        fail "Inductive indices nonempty?";
      let [(ctorname, ctor_t)] = ctors in
      (* dump ("ityp = " ^ term_to_string typ); *)
      (* dump ("ctor_t = " ^ term_to_string ctor_t); *)
      let (fields, _) = collect_arr_bs ctor_t in
      let unfold_names_tm = `(Nil u#0 #string) in
      let (decls, _, _, _) =
        fold_left (fun (decls, smap, unfold_names_tm, idx) (field : binder) ->
          let (ds, fv) = mk_proj_decl is_class tyqn ctorname univs params idx field unfold_names_tm smap in
          (decls @ ds,
           (binder_to_namedv field, fv)::smap,
           (`(Cons u#0 #string (`#(embed_string (implode_qn (inspect_fv fv)))) (`#unfold_names_tm))),
           idx+1))
        ([], [], unfold_names_tm, 0)
        fields
      in
      decls
    | _ ->
      fail "not an inductive"
