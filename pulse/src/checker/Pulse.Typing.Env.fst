(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Typing.Env

open Pulse.Syntax

module G = FStar.Ghost
module L = FStar.List.Tot

module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
open FStar.List.Tot

noeq
type env = {
  f : RT.fstar_top_env;
  bs : list binding;
  f_bs : (f_bs : R.env { f_bs == bindings_extend_env f bs });
  ctxt: Pulse.RuntimeUtils.context;

  anf_ctr : Sealed.sealed nat;
  (* ^ Used to generate more stable ANF binders. *)
}

let fstar_env g = RU.env_set_context g.f g.ctxt

let bindings g = g.bs

let equal_elim g1 g2 =
  Sealed.sealed_singl g1.anf_ctr g2.anf_ctr

let elab_env g = g.f_bs

let fresh_anf (g:env) =
  let id = T.unseal g.anf_ctr in
  let g = { g with anf_ctr = Sealed.seal (id + 1) } in
  g, id

let default_context : Pulse.RuntimeUtils.context = FStar.Sealed.seal []

let mk_env (f:RT.fstar_top_env) : env =
  { f; bs = []; f_bs=f; ctxt = default_context; anf_ctr = Sealed.seal 0 }

let mk_env_dom f : Lemma (dom (mk_env f) == Set.empty) =
  assert (dom (mk_env f) `Set.equal` Set.empty)

let push g b =
  { g with bs = b :: g.bs; f_bs = binding_extend_env g.f_bs b }

let push_univ_vars g us =
  { g with f = RU.push_univ_vars g.f us; f_bs = RU.push_univ_vars g.f_bs us }

let rec lookup_bindings (g: env_bindings) (x: var) : option typ =
  match g with
  | [] -> None
  | BindingVar {n; x=y; ty} :: g -> if x = y then Some ty else lookup_bindings g x
  | BindingGotoLabel .. :: g | BindingPost .. :: g -> lookup_bindings g x

let rec lookup_bindings_fresh (g: env_bindings) (x: var { ~(x `Set.mem` bindings_dom g) }) :
    Lemma (lookup_bindings g x == None) =
  match g with
  | [] -> ()
  | b :: g -> lookup_bindings_fresh g x

let lookup g x = lookup_bindings (bindings g) x
let lookup_fresh g x = lookup_bindings_fresh (bindings g) x
let lookup_push g x b = () 

let rec lookup_goto_bindings (g: env_bindings) (x: var) : option (ppname & comp_st) =
  match g with
  | [] -> None
  | BindingVar .. :: g -> lookup_goto_bindings g x
  | BindingGotoLabel { n; x=y; post } :: g ->
    if x = y then Some (n, post) else lookup_goto_bindings g x
  | BindingPost { post } :: g ->
    match lookup_goto_bindings g x with
    | None -> None
    | Some (n, post0) -> Some (n, comp_add_pre post0 post)

let lookup_goto g x = lookup_goto_bindings (bindings g) x
let lookup_goto_push g x b = ()

let fresh g =
  let v = RU.next_id () in
  assume ~(v `Set.mem` dom g);
  v

let push_env g1 g2 =
  assume (bindings_extend_env (bindings_extend_env g1.f g1.bs) g2.bs == bindings_extend_env g1.f (g2.bs @ g1.bs));
  {
    f = g1.f;
    bs = g2.bs @ g1.bs;
    f_bs = bindings_extend_env g1.f_bs g2.bs;
    ctxt = g1.ctxt ;
    anf_ctr = g1.anf_ctr;
  }

let push_env_dom g1 g2 = admit ()

let push_env_assoc g1 g2 g3 =
  L.append_assoc g3.bs g2.bs g1.bs;
  assert (equal (push_env g1 (push_env g2 g3)) (push_env (push_env g1 g2) g3))

let intro_env_extends (g1 g2 g3:env)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures g1 `env_extends` g2) = ()

let elim_env_extends (g1:env) (g2:env { g1 `env_extends` g2 })
  : GTot (g3:env { extends_with g1 g2 g3 }) =
  FStar.IndefiniteDescription.indefinite_description_ghost
    env (fun g3 -> extends_with g1 g2 g3)

let elim_env_extends_tot (g1:env) (g2:env { g1 `env_extends` g2 })
  : g3:G.erased env { extends_with g1 g2 (Ghost.reveal g3)  }
  = G.hide (elim_env_extends g1 g2)

let rec diff_witness (#a:Type) (l1 l2:list a) (l3:G.erased (list a))
  : Pure (list a)
         (requires l1 == l2 @ G.reveal l3)
         (ensures fun w -> w == G.reveal l3) =
  match l1, l2 with
  | [], _ -> []
  | _, [] -> l1
  | hd1::tl1, hd2::tl2 ->
    diff_witness tl1 tl2 l3

let diff_witness' (#a:Type) (l1 l2:list a) (l3:G.erased (list a))
  : Pure (list a)
         (requires l1 == G.reveal l3 @ l2)
         (ensures fun w -> w == G.reveal l3) =
  L.rev_append l3 l2;
  let rev_l3 = diff_witness (L.rev l1) (L.rev l2) (L.rev l3) in
  L.rev_involutive l3;
  L.rev rev_l3

let diff g1 g2 =
  let g3 = elim_env_extends_tot g1 g2 in
  let bs3 = diff_witness' g1.bs g2.bs g3.bs in
  let g3 = {
    f = g1.f;
    bs = bs3;
    f_bs = bindings_extend_env g2.f bs3;
    ctxt = g1.ctxt;
    anf_ctr = g1.anf_ctr;
  } in
  assert (equal g1 (push_env g2 g3));
  g3

let env_extends_refl (g:env) : Lemma (g `env_extends` g) =
  assert (equal g (push_env g (mk_env g.f)));
  intro_env_extends g g (mk_env g.f)

let env_extends_trans (g1 g2 g3:env)
  : Lemma (requires g1 `env_extends` g2 /\ g2 `env_extends` g3)
          (ensures g1 `env_extends` g3) =
  let g12 = elim_env_extends g1 g2 in
  let g23 = elim_env_extends g2 g3 in
  L.append_assoc g12.bs g23.bs g3.bs;
  assert (equal g1 (push_env g3 (push_env g23 g12)));
  intro_env_extends g1 g3 (push_env g23 g12)

let env_extends_push (g:env) (b: binding { dom g `Set.disjoint` binding_dom b })
  : Lemma (push g b `env_extends` g) =
  assert (equal (push g b) (push_env g (push (mk_env g.f) b)));
  intro_env_extends (push g b) g (push (mk_env g.f) b)

let extends_with_push (g1 g2 g3:env)
  (x:var { ~ (Set.mem x (dom g1)) }) n (t:typ)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures extends_with (push_binding g1 x n t) g2 (push_binding g3 x n t)) =
  assert (equal (push_binding g1 x n t)
                (push_env g2 (push_binding g3 x n t)))

let push_context g ctx r = { g with ctxt = Pulse.RuntimeUtils.extend_context ctx (Some r) g.ctxt }
let push_context_no_range g ctx = { g with ctxt = Pulse.RuntimeUtils.extend_context ctx None g.ctxt }
let reset_context g g' = { g with ctxt = g'.ctxt }
let get_context g = g.ctxt

let range_of_env (g:env) = 
    let ctx = T.unseal g.ctxt in
    match 
      T.tryPick
        (fun (_, r) ->
          match r with
          | None -> None
          | Some r -> 
            if not (RU.is_range_zero r) then Some r else None) ctx with
    | Some r -> r
    | _ -> FStar.Range.range_0
  
let ctxt_elt_to_string (c : (string & option range)) : T.Tac string = 
  match snd c with
  | None -> fst c
  | Some r -> Printf.sprintf ("%s @ %s") (fst c) (T.range_to_string r)

let ctx_to_string (c:list (string & option range)) : T.Tac string =
    match c with
    | [] -> ""
    | _ -> 
      Printf.sprintf "\n\tContext:\n\t%s" (String.concat "\n\t" (T.map ctxt_elt_to_string c))

let ctxt_to_list (g:env) : T.Tac (list string) =
  let ctx = T.unseal g.ctxt in
  T.map ctxt_elt_to_string ctx

let print_context (g:env) : T.Tac string = 
  let ctx = T.unseal g.ctxt in
  match ctx with
  | [] -> ""
  | _ -> 
    Printf.sprintf "\n\tContext:\n\t%s" (String.concat "\n\t" (ctxt_to_list g))

let binding_to_string : binding -> T.Tac string = function
  | BindingVar { n; x; ty } ->
    Printf.sprintf "%s#%d : %s" (T.unseal n.name) x (Pulse.Syntax.Printer.term_to_string ty)
  | BindingGotoLabel { n; x; post } ->
    Printf.sprintf "%s#%d : %s" (T.unseal n.name) x (Pulse.Syntax.Printer.comp_to_string post)
  | BindingPost { post } ->
    Printf.sprintf "extra post: %s" (Pulse.Syntax.Printer.term_to_string post)

let env_to_string (e:env) : T.Tac string =
  String.concat "\n  " (T.map binding_to_string (bindings e))

open FStar.Pprint

// Cannot use Pprint.separate_map, it takes a pure func
// FIXME: duplicate in Pulse.PP
private
let rec separate_map (sep: document) (f : 'a -> T.Tac document) (l : list 'a) : T.Tac document =
  match l with
  | [] -> empty
  | [x] -> f x
  | x::xs -> f x ^^ sep ^/^ separate_map sep f xs

let env_to_doc' (simplify:bool) (e:env) : T.Tac document =
  let pp1 : var_binding -> T.Tac document =
    fun { n; ty; x } ->
      infix 2 1 colon
        (doc_of_string (T.unseal n.name ^ "#" ^ string_of_int x))
        (align (Pulse.Syntax.Printer.term_to_doc ty))
  in
  let maybe_filter (vtns: list var_binding) =
    if simplify then
      vtns |> T.filter (fun {n; ty; x} ->
        let is_unit = FStar.Reflection.TermEq.term_eq ty (`unit) in
        let is_wild = T.unseal n.name = "__" in
        not (is_unit && is_wild)
      )
    else
      vtns
  in
  let rec var_bindings = function
    | [] -> []
    | BindingVar b :: bs -> b :: var_bindings bs
    | _ :: bs -> var_bindings bs
  in
  var_bindings (bindings e) |> maybe_filter |> separate_map comma pp1

let env_to_doc = env_to_doc' true

let get_range (g:env) (r:option range) : T.Tac range =
    match r with
    | None -> range_of_env g
    | Some r -> 
      if RU.is_range_zero r
      then range_of_env g
      else r

let fail_doc_env (#a:Type) (with_env:bool) (g:env) (r:option range) (msg:list Pprint.document) =
  let r = get_range g r in
  let msg =
    let indent d = nest 2 (hardline ^^ align d) in
    let with_env =
      if with_env then true
      else Pulse.Config.debug_flag "env_on_err"
    in
    if with_env
    then msg @ [doc_of_string "In typing environment:" ^^ indent (env_to_doc g)]
    else msg
  in
  T.fail_doc_at msg (Some r)

let warn_doc (g:env) (r:option range) (msg:list Pprint.document) : T.Tac unit =
  let r = get_range g r in
  let issue = FStar.Issue.mk_issue_doc "Warning" msg (Some r) None (ctxt_to_list g) in
  T.log_issues [issue]

let info_doc (g:env) (r:option range) (msg:list Pprint.document) =
  let r = get_range g r in
  let issue = FStar.Issue.mk_issue_doc "Info" msg (Some r) None (ctxt_to_list g) in
  T.log_issues [issue]

let info_doc_env (g:env) (r:option range) (msg:list Pprint.document) =
  let indent d = nest 2 (hardline ^^ align d) in
  info_doc g r (msg @
    [doc_of_string "In typing environment:" ^^ indent (env_to_doc g)]
  )

let fail (#a:Type) (g:env) (r:option range) (msg:string) =
  fail_doc g r [Pprint.arbitrary_string msg]

let warn (g:env) (r:option range) (msg:string) : T.Tac unit =
  warn_doc g r [Pprint.arbitrary_string msg]

let info (g:env) (r:option range) (msg:string) =
  info_doc g r [Pprint.arbitrary_string msg]

let fail_doc_with_subissues #a (g:env) (ro : option range)
  (sub : list Issue.issue)
  (msg : list document)
=
  (* If for whatever reason `sub` is empty, F* will handle it well
  and a generic error message will be displayed *)
  if Nil? sub then (
    let issue =
      FStar.Issue.mk_issue_doc
        "Error"
        (msg @ [doc_of_string "F* did not provide any extra information on why this failed."])
        None
        None
        []
    in
    T.log_issues [issue];
    T.raise T.Stop
  )
  ;
  let issues = sub |> T.map (fun is ->
    FStar.Issue.mk_issue_doc
      (Issue.level_of_issue is)
      (msg @ Issue.message_of_issue is)
      (Issue.range_of_issue is)
      (Issue.number_of_issue is)
      (Issue.context_of_issue is)
    )
  in
  T.log_issues issues;
  T.raise T.Stop

let info_doc_with_subissues (g:env) (r:option range)
  (sub : list Issue.issue)
  (msg : list Pprint.document)
=
  let msg = msg @ [
    doc_of_string "Issues:" ^^ hardline ^^
        (List.Tot.map Issue.issue_to_doc sub |>
         concat) ]
  in
  info_doc g r msg
