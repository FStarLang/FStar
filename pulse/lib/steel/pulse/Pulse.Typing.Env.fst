module Pulse.Typing.Env

open Pulse.Syntax

module L = FStar.List.Tot

module R = FStar.Reflection
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
open FStar.List.Tot

type bmap = m:Map.t var typ {
  forall (x:var). (~ (Map.contains m x)) ==> (Map.sel m x == Tm_Unknown)
}

let remove_binding ((x, _):var & typ) (m:bmap) : bmap =
  Map.restrict (Set.complement (Set.singleton x)) (Map.upd m x Tm_Unknown)

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

let fstar_env g = g.f

let bindings g = g.bs

let as_map g = g.m

let bindings_as_map _ = ()

let empty_bmap : bmap = Map.const_on Set.empty Tm_Unknown

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

let push_binding g x p t =
  { g with bs = (x, t)::g.bs;
           names = p::g.names;
          m = Map.upd g.m x t }

let push_binding_bs _ _ _ _ = ()

let push_binding_as_map _ _ _ _ = ()

let rec max (bs:list (var & typ)) (current:var)
  : v:var { current <= v /\ (forall (b:var & typ). List.Tot.memP b bs ==> fst b <= v) } =
  match bs with
  | [] -> current
  | (x, t)::rest ->
    let current = if x < current then current else x in
    max rest current

let fresh g =
  match g.bs with
  | [] -> 1
  | (x, _)::bs_rest ->
    let max = max bs_rest x in
    max + 1

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

let intro_env_extends (g1 g2 g3:env)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures g1 `env_extends` g2) = ()

let elim_env_extends (g1:env) (g2:env { g1 `env_extends` g2 })
  : GTot (g3:env { extends_with g1 g2 g3 }) =
  FStar.IndefiniteDescription.indefinite_description_ghost
    env (fun g3 -> extends_with g1 g2 g3)

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

let push_context g ctx r = { g with ctxt = Pulse.RuntimeUtils.extend_context ctx (Some r) g.ctxt }
let push_context_no_range g ctx = { g with ctxt = Pulse.RuntimeUtils.extend_context ctx None g.ctxt }

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
       (message_of_issue i)
       (ctx_to_string (T.unseal (get_context g) @ (T.map (fun i -> (i, None)) (context_of_issue i))))

let print_issues (g:env)
                 (i:list FStar.Issue.issue)
   = String.concat "\n" (T.map (print_issue g) i)

let env_to_string (e:env) : T.Tac string =
  let bs = T.map
    (fun ((_, t), x) -> Printf.sprintf "%s : %s" (T.unseal x.name) (Pulse.Syntax.Printer.term_to_string t))
    (T.zip e.bs e.names) in
  Printf.sprintf "Env:\n\t%s\n" (String.concat "\n\t" bs)

let fail (#a:Type) (g:env) (r:option range) (msg:string) =
  let r = 
    match r with
    | None -> range_of_env g
    | Some r -> 
      if RU.is_range_zero r
      then range_of_env g
      else r
  in
  let ctx = Printf.sprintf "Environment: %s\n"  (env_to_string g) in
  let issue = FStar.Issue.mk_issue "Error" msg (Some r) None (ctx::ctxt_to_list g) in
  FStar.Tactics.log_issues [issue];
  T.fail "Pulse checker failed"