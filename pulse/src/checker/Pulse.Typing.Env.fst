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

module R = FStar.Reflection
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
open FStar.List.Tot

type bmap = m:Map.t var typ {
  forall (x:var). (~ (Map.contains m x)) ==> (Map.sel m x == tm_unknown)
}

let related (bs:list (var & typ)) (m:Map.t var typ) =
  (forall (b:var & typ).
          L.memP b bs ==> (Map.contains m (fst b) /\
                           Map.sel m (fst b) == snd b)) /\
  
  (forall (x:var). Map.contains m x ==> (List.Tot.memP (x, Map.sel m x) bs))

noeq
type env = {
  f : RT.fstar_top_env;
  bs : list (var & typ);
  names : list ppname;
  m : m:bmap { related bs m /\ L.length names == L.length bs };
  ctxt: Pulse.RuntimeUtils.context
}

let fstar_env g = RU.env_set_context g.f g.ctxt

let bindings g = g.bs

let rec bindings_with_ppname_aux (bs:list (var & typ)) (names:list ppname)
  : T.Tac (list (ppname & var & typ)) =

  match bs, names with
  | [], [] -> []
  | (x, t)::bs, n::names -> (n, x, t)::(bindings_with_ppname_aux bs names)
  | _ -> T.fail "impossible! env bs and names have different lengths"
let bindings_with_ppname g = bindings_with_ppname_aux g.bs g.names  

let as_map g = g.m

let bindings_as_map _ = ()

let empty_bmap : bmap = Map.const_on Set.empty tm_unknown

let rec equal_names (l1 l2:list ppname)
  : Lemma 
    (requires L.length l1 == L.length l2)
    (ensures l1 == l2) =
  match l1, l2 with
  | [], [] -> ()
  | n1::l1, n2::l2 ->
    equal_names l1 l2

let equal_elim g1 g2 =
  equal_names g1.names g2.names;
  assert (Map.equal g1.m g2.m)

let default_context : Pulse.RuntimeUtils.context = FStar.Sealed.seal []

let mk_env (f:RT.fstar_top_env) : env =
  { f; bs = []; names=[]; m = empty_bmap; ctxt = default_context }

let mk_env_bs _ = ()

let mk_env_dom _ = assert (Set.equal (Map.domain empty_bmap) Set.empty)

let push_binding g x p t =
  { g with bs = (x, t)::g.bs;
           names = p::g.names;
           m = Map.upd g.m x t }

let push_binding_bs _ _ _ _ = ()

let push_binding_as_map _ _ _ _ = ()

let fresh g =
  let v = RU.next_id () in
  assume ~(v `Set.mem` dom g);
  v

//
// TODO: Move to ulib
//
let rec append_memP (#a:Type) (l1 l2:list a) (x:a)
  : Lemma (L.memP x (l1 @ l2) <==> (L.memP x l1 \/ L.memP x l2))
          [SMTPat (L.memP x (l1 @ l2))] =
  match l1 with
  | [] -> ()
  | _::tl -> append_memP tl l2 x

let push_env (g1:env) (g2:env { disjoint g1 g2 }) : env =
  { f = g1.f; bs = g2.bs @ g1.bs; names= g2.names @ g1.names;
    m = Map.concat g2.m g1.m; ctxt = g1.ctxt }

let push_env_fstar_env _ _ = ()

let push_env_bindings _ _ = ()

let push_env_as_map _ _ = ()

let push_env_assoc g1 g2 g3 =
  L.append_assoc g3.bs g2.bs g1.bs;
  assert (equal (push_env g1 (push_env g2 g3)) (push_env (push_env g1 g2) g3))

let check_disjoint g s =
  admit ();
  not (L.existsb (fun (x, _) -> Set.mem x s) g.bs)

let rec remove_binding_aux (g:env)
  (prefix:list (var & typ))
  (prefix_names:list ppname { List.length prefix == List.length prefix_names})
  (suffix:list (var & typ) { Cons? suffix })
  (suffix_names:list ppname { List.length suffix == List.length suffix_names })
  : Pure (var & typ & env)
         (requires bindings g == prefix @ suffix /\
                   g.names == prefix_names @ suffix_names)
         (ensures fun r ->
            let x, t, g' = r in
            fstar_env g' == fstar_env g /\
            (~ (x `Set.mem` dom g')) /\
            g == push_env (push_binding (mk_env (fstar_env g)) x ppname_default t) g')
         (decreases List.Tot.length suffix) =
  match suffix, suffix_names with
  | [x, t], _ ->
    let m = Map.restrict (Set.complement (Set.singleton x)) (Map.upd g.m x tm_unknown) in
    // we need uniqueness invariant in the representation
    assume (forall (b:var & typ). List.Tot.memP b prefix <==> (List.Tot.memP b g.bs /\
                                                               fst b =!= x));
    let g' = {g with bs = prefix; names=prefix_names; m} in
    assert (equal g (push_env (push_binding (mk_env (fstar_env g)) x ppname_default t) g'));
    x, t, g'
  | (x, t)::suffix_rest, n::suffix_names_rest ->
    assume (prefix @ suffix == (prefix @ [x,t]) @ suffix_rest);
    assume (prefix_names @ suffix_names == (prefix_names @ [n]) @ suffix_names_rest);
    remove_binding_aux g (prefix @ [x, t]) (prefix_names @ [n]) suffix_rest suffix_names_rest

let remove_binding g =
  remove_binding_aux g [] [] g.bs g.names

let remove_latest_binding g =
  match g.bs with
  | (x, t)::rest ->
    let m = Map.restrict (Set.complement (Set.singleton x)) (Map.upd g.m x tm_unknown) in
    // we need uniqueness invariant in the representation
    assume (forall (b:var & typ). List.Tot.memP b rest <==> (List.Tot.memP b g.bs /\
                                                             fst b =!= x));
    let g' = {g with bs = rest; names=L.tl g.names; m} in
    assert (equal g (push_binding g' x ppname_default t));
    x, t, g'    

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

let rec create_m (bs:list (var & typ)) : m:bmap { related bs m } =
  match bs with
  | [] -> empty_bmap
  | (x, t)::tl ->
    // TODO: need to encode uniqueness in the repr
    assume (forall (b:var & typ). List.Tot.memP b tl ==> fst b =!= x);
    Map.upd (create_m tl) x t

let rec diff_names (#a:Type) (l1 l2:list a)
  : Pure (list a)
         (requires L.length l1 >= L.length l2)
         (ensures fun l -> L.length l == L.length l1 - L.length l2) =
  match l1, l2 with
  | [], _ -> []
  | _, [] -> l1
  | _::tl1, _::tl2 -> diff_names tl1 tl2


#push-options "--z3rlimit_factor 12"
let diff g1 g2 =
  let g3 = elim_env_extends_tot g1 g2 in
  assert (g1.bs == g3.bs @ g2.bs);

  let g1_bs_rev = L.rev g1.bs in
  let g2_bs_rev = L.rev g2.bs in
  let g3_bs_rev : G.erased _ = G.elift1 L.rev g3.bs in

  L.rev_append g3.bs g2.bs;
  assert (g1_bs_rev == g2_bs_rev @ g3_bs_rev);

  let rev_bs3 = diff_witness g1_bs_rev g2_bs_rev g3_bs_rev in
  assert (g1_bs_rev == g2_bs_rev @ rev_bs3);

  L.rev_append g2_bs_rev rev_bs3;
  L.rev_involutive g1.bs;
  L.rev_involutive g2.bs;

  let bs3 = L.rev rev_bs3 in
  assert (g1.bs == bs3 @ g2.bs);

  L.append_length bs3 g2.bs;
  assume (forall (a:Type) (l:list a). L.length (L.rev l) == L.length l);

  let names3 = L.rev (diff_names (L.rev g1.names) (L.rev g2.names)) in
  let m3 = create_m bs3 in

  let g3 = {
    f = g1.f;
    bs = bs3;
    names = names3;
    m = m3;
    ctxt = g1.ctxt;
  } in
  assume (disjoint g2 g3);  // needs distinct entries in g
  assert (equal g1 (push_env g2 g3));
  g3
#pop-options

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

let env_extends_push (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (push_binding g x n t `env_extends` g) =
  assert (equal (push_binding g x n t) (push_env g (push_binding (mk_env g.f) x n t)));
  intro_env_extends (push_binding g x n t) g (push_binding (mk_env g.f) x n t)

let extends_with_push (g1 g2 g3:env)
  (x:var { ~ (Set.mem x (dom g1)) }) n (t:typ)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures extends_with (push_binding g1 x n t) g2 (push_binding g3 x n t)) =
  assert (equal (push_binding g1 x n t)
                (push_env g2 (push_binding g3 x n t)))

#push-options "--admit_smt_queries true"
let rec subst_env (en:env) (ss:subst)
  : en':env { fstar_env en == fstar_env en' /\
              dom en == dom en' } =
  match bindings en with
  | [] -> en
  | _ ->
    let x, t, en = remove_latest_binding en in
    push_binding (subst_env en ss) x ppname_default (subst_term t ss) 
#pop-options

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

let print_issue (g:env) (i:FStar.Issue.issue) : T.Tac string = 
    let open FStar.Issue in
    let range_opt_to_string = function
      | None -> "Unknown range"
      | Some r -> T.range_to_string r
    in
    Printf.sprintf "%s (%s): %s%s"
       (range_opt_to_string (range_of_issue i))
       (level_of_issue i)
       (render_issue i)
       (ctx_to_string (T.unseal (get_context g) @ (T.map (fun i -> (i, None)) (context_of_issue i))))

let print_issues (g:env)
                 (i:list FStar.Issue.issue)
   = String.concat "\n" (T.map (print_issue g) i)

let env_to_string (e:env) : T.Tac string =
  let bs = T.map #((var & typ) & ppname) #_
    (fun ((n, t), x) -> Printf.sprintf "%s#%d : %s" (T.unseal x.name) n (Pulse.Syntax.Printer.term_to_string t))
    (T.zip e.bs e.names) in
  String.concat "\n  " bs

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
  let pp1 : ((var & typ) & ppname) -> T.Tac document =
    fun ((n, t), x) ->
      infix 2 1 colon
        (doc_of_string (T.unseal x.name ^ "#" ^ string_of_int n))
        (align (Pulse.Syntax.Printer.term_to_doc t))
  in
  let maybe_filter vtns =
    if simplify then
      vtns |> T.filter (fun ((n, t), x) ->
        let is_unit = FStar.Reflection.TermEq.term_eq t (`unit) in
        let x : ppname = x in
        let is_wild = T.unseal x.name = "_" in
        not (is_unit && is_wild)
      )
    else
      vtns
  in
  T.zip e.bs e.names |> maybe_filter |> separate_map comma pp1

let env_to_doc = env_to_doc' false

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
  : T.TacH a (requires fun _ -> True) (ensures fun _ r -> FStar.Tactics.Result.Failed? r)
=
  (* If for whatever reason `sub` is empty, F* will handle it well
  and a generic error message will be displayed *)
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
