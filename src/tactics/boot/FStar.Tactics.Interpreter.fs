#light "off"
module FStar.Tactics.Interpreter
open FStar
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Syntax.Syntax
open FStar.Util
open FStar.Range

module Err = FStar.Errors
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module PC = FStar.Parser.Const
open FStar.TypeChecker.Env
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module U = FStar.Syntax.Util
module TcRel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module TcTerm = FStar.TypeChecker.TcTerm
module N = FStar.TypeChecker.Normalize
open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Basic
module E = FStar.Tactics.Embedding
module Core = FStar.Tactics.Basic
open FStar.Syntax.Embeddings
open FStar.Reflection.Basic
open FStar.Reflection.Interpreter
module RD = FStar.Reflection.Data
module RE = FStar.Reflection.Embeddings
open FStar.Tactics.Native

let tacdbg = BU.mk_ref false

let mk_tactic_interpretation_0 (reflect:bool)
                               (t:tac<'r>) (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
 (*  We have: t () embedded_state
     The idea is to:
        1. unembed the state
        2. run the `t` tactic
        3. embed the result and final state and return it to the normalizer
  *)
  match args with
  | [(embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, args are: %s\n"
            (Ident.string_of_lid nm)
            (Print.args_to_string args));
    let res = E.embed_result embed_r t_r (N.psc_range psc) (run t ps) in
    Some res)
  | _ ->
    failwith ("Unexpected application of tactic primitive")

let mk_tactic_interpretation_1 (reflect:bool)
                               (t:'a -> tac<'r>) (unembed_a:unembedder<'a>)
                               (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    let res = run (t a) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res)))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_1_env
                               (reflect:bool)
                               (t:N.psc -> 'a -> tac<'r>) (unembed_a:unembedder<'a>)
                               (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    let res = run (t psc a) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res)))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_2 (reflect:bool)
                               (t:'a -> 'b -> tac<'r>)
                               (unembed_a:unembedder<'a>) (unembed_b:unembedder<'b>)
                               (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    let res = run (t a b) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_3 (reflect:bool)
                               (t:'a -> 'b -> 'c -> tac<'r>)
                               (unembed_a:unembedder<'a>)
                               (unembed_b:unembedder<'b>)
                               (unembed_c:unembedder<'c>)
                               (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    BU.bind_opt (unembed_c c) (fun c ->
    let res = run (t a b c) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res)))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_4 (reflect:bool)
                               (t:'a -> 'b -> 'c -> 'd -> tac<'r>)
                               (unembed_a:unembedder<'a>)
                               (unembed_b:unembedder<'b>)
                               (unembed_c:unembedder<'c>)
                               (unembed_d:unembedder<'d>)
                               (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    BU.bind_opt (unembed_c c) (fun c ->
    BU.bind_opt (unembed_d d) (fun d ->
    let res = run (t a b c d) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_5 (reflect:bool)
                               (t:'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
                               (unembed_a:unembedder<'a>)
                               (unembed_b:unembedder<'b>)
                               (unembed_c:unembedder<'c>)
                               (unembed_d:unembedder<'d>)
                               (unembed_e:unembedder<'e>)
                               (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (e, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    BU.bind_opt (unembed_c c) (fun c ->
    BU.bind_opt (unembed_d d) (fun d ->
    BU.bind_opt (unembed_e e) (fun e ->
    let res = run (t a b c d e) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res)))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_6 (reflect:bool)
                               (t:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> tac<'r>)
                               (unembed_a:unembedder<'a>)
                               (unembed_b:unembedder<'b>)
                               (unembed_c:unembedder<'c>)
                               (unembed_d:unembedder<'d>)
                               (unembed_e:unembedder<'e>)
                               (unembed_f:unembedder<'f>)
                               (embed_r:embedder<'r>) (t_r:typ)
                               (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed_a a) (fun a ->
    BU.bind_opt (unembed_b b) (fun b ->
    BU.bind_opt (unembed_c c) (fun c ->
    BU.bind_opt (unembed_d d) (fun d ->
    BU.bind_opt (unembed_e e) (fun e ->
    BU.bind_opt (unembed_f f) (fun f ->
    let res = run (t a b c d e f) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res))))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_13 (reflect:bool)
                                (t:'t1 -> 't2 -> 't3 -> 't4 -> 't5 -> 't6 -> 't7 -> 't8 -> 't9 -> 't10 -> 't11 -> 't12 -> 't13 -> tac<'r>)
                                (unembed_t1: unembedder<'t1>)
                                (unembed_t2: unembedder<'t2>)
                                (unembed_t3: unembedder<'t3>)
                                (unembed_t4: unembedder<'t4>)
                                (unembed_t5: unembedder<'t5>)
                                (unembed_t6: unembedder<'t6>)
                                (unembed_t7: unembedder<'t7>)
                                (unembed_t8: unembedder<'t8>)
                                (unembed_t9: unembedder<'t9>)
                                (unembed_t10: unembedder<'t10>)
                                (unembed_t11: unembedder<'t11>)
                                (unembed_t12: unembedder<'t12>)
                                (unembed_t13: unembedder<'t13>)
                                (embed_r:embedder<'r>) (t_r:typ)
                                (nm:Ident.lid) (psc:N.psc) (args:args) : option<term> =
  match args with
  | [(a1, _); (a2, _); (a3, _); (a4, _); (a5, _); (a6, _); (a7, _); (a8, _); (a9, _); (a10, _); (a11, _); (a12, _); (a13, _); (embedded_state, _)] ->
    BU.bind_opt (E.unembed_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));

    BU.bind_opt (unembed_t1 a1) (fun  a1 ->
    BU.bind_opt (unembed_t2 a2) (fun  a2 ->
    BU.bind_opt (unembed_t3 a3) (fun  a3 ->
    BU.bind_opt (unembed_t4 a4) (fun  a4 ->
    BU.bind_opt (unembed_t5 a5) (fun  a5 ->
    BU.bind_opt (unembed_t6 a6) (fun  a6 ->
    BU.bind_opt (unembed_t7 a7) (fun  a7 ->
    BU.bind_opt (unembed_t8 a8) (fun  a8 ->
    BU.bind_opt (unembed_t9 a9) (fun  a9 ->
    BU.bind_opt (unembed_t10 a10) (fun a10 ->
    BU.bind_opt (unembed_t11 a11) (fun a11 ->
    BU.bind_opt (unembed_t12 a12) (fun a12 ->
    BU.bind_opt (unembed_t13 a13) (fun a13 ->
    let res = run (t a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) ps in
    Some (E.embed_result embed_r t_r (N.psc_range psc) res)))))))))))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))


let step_from_native_step (s: native_primitive_step): N.primitive_step =
    { N.name=s.name;
      N.arity=s.arity;
      N.auto_reflect=Some (s.arity - 1);
      N.strong_reduction_ok=s.strong_reduction_ok;
      N.requires_binder_substitution = false; // GM: really?
      N.interpretation=(fun psc args -> s.tactic psc args) }

let rec primitive_steps () : list<N.primitive_step> =
    let mk nm arity interpretation =
      let nm = E.fstar_tactics_lid' ["Builtins";nm] in {
      N.name=nm;
      N.arity=arity;
      N.auto_reflect=Some (arity - 1);
      N.strong_reduction_ok=false;
      N.requires_binder_substitution = true;
      N.interpretation=(fun psc args -> interpretation nm psc args);
    } in
    let native_tactics = list_all () in
    let native_tactics_steps = List.map step_from_native_step native_tactics in
    // mktac0 cannot exist due to having a top-level effect
    let mktac1 (name : string) (f : 'a -> tac<'r>)
               (u_a : unembedder<'a>)
               (e_r : embedder<'r>) (tr : typ) : N.primitive_step =
        mk name 2 (mk_tactic_interpretation_1 false f u_a e_r tr)
    in
    let mktac2 (name : string) (f : 'a -> 'b -> tac<'r>)
               (u_a : unembedder<'a>) (u_b : unembedder<'b>)
               (e_r : embedder<'r>) (tr : typ) : N.primitive_step =
        mk name 3 (mk_tactic_interpretation_2 false f u_a u_b e_r tr)
    in
    let mktac3 (name : string) (f : 'a -> 'b -> 'c -> tac<'r>)
               (u_a : unembedder<'a>) (u_b : unembedder<'b>) (u_c : unembedder<'c>)
               (e_r : embedder<'r>) (tr : typ) : N.primitive_step =
        mk name 4 (mk_tactic_interpretation_3 false f u_a u_b u_c e_r tr)
    in
    let mktac5 (name : string) (f : 'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
               (u_a : unembedder<'a>) (u_b : unembedder<'b>) (u_c : unembedder<'c>)
               (u_d : unembedder<'d>) (u_e : unembedder<'e>)
               (e_r : embedder<'r>) (tr : typ) : N.primitive_step =
        mk name 6 (mk_tactic_interpretation_5 false f u_a u_b u_c u_d u_e e_r tr)
    in
    let decr_depth_interp psc (args : args) =
        match args with
        | [(ps, _)] ->
            bind_opt (E.unembed_proofstate ps) (fun ps ->
            let ps = set_ps_psc psc ps in
            Some (E.embed_proofstate (N.psc_range psc) (decr_depth ps)))

        | _ -> failwith "Unexpected application of decr_depth"
    in
    let decr_depth_step : N.primitive_step =
        {N.name = Ident.lid_of_str "FStar.Tactics.Types.decr_depth";
         N.arity = 1;
         N.auto_reflect=None;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = false;
         N.interpretation = decr_depth_interp
         }
    in
    let incr_depth_interp psc (args : args) =
        match args with
        | [(ps, _)] ->
            bind_opt (E.unembed_proofstate ps) (fun ps ->
            let ps = set_ps_psc psc ps in
            Some (E.embed_proofstate (N.psc_range psc) (incr_depth ps)))
        | _ -> failwith "Unexpected application of incr_depth"
    in
    let incr_depth_step : N.primitive_step =
        {N.name = Ident.lid_of_str "FStar.Tactics.Types.incr_depth";
         N.arity = 1;
         N.auto_reflect=None;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = false;
         N.interpretation = incr_depth_interp
         }
    in
    let tracepoint_interp psc (args : args) =
        match args with
        | [(ps, _)] ->
            bind_opt (E.unembed_proofstate ps) (fun ps ->
            let ps = set_ps_psc psc ps in
            tracepoint ps;
            Some U.exp_unit)
        | _ -> failwith "Unexpected application of tracepoint"
    in
    let set_proofstate_range_interp psc (args : args) =
        match args with
        | [(ps, _); (r, _)] ->
            bind_opt (E.unembed_proofstate ps) (fun ps ->
            bind_opt (unembed_range r) (fun r ->
            let ps' = set_proofstate_range ps r in
            Some (E.embed_proofstate (N.psc_range psc) ps')))
        | _ -> failwith "Unexpected application of set_proofstate_range"
    in
    let push_binder_interp psc (args:args) =
        match args with
        | [(env_t, _); (b, _)] ->
            bind_opt (RE.unembed_env env_t) (fun env ->
            bind_opt (RE.unembed_binder b) (fun b ->
            let env = Env.push_binders env [b] in
            Some (RE.embed_env env_t.pos env)))
        | _ -> failwith "Unexpected application of push_binder"
    in
    let set_proofstate_range_step : N.primitive_step =
        let nm = Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range" in
        {N.name = nm;
         N.arity = 2;
         N.auto_reflect=None;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = false;
         N.interpretation = set_proofstate_range_interp
        }
    in
    let tracepoint_step : N.primitive_step =
        let nm = Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
        {N.name = nm;
         N.arity = 1;
         N.auto_reflect=None;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = true;
         N.interpretation = tracepoint_interp
        }
    in
    let push_binder_step : N.primitive_step =
       let nm = E.fstar_tactics_lid' ["Builtins";"push_binder"] in
        {N.name = nm;
         N.arity = 2;
         N.auto_reflect=None;
         N.strong_reduction_ok = false;
         N.requires_binder_substitution = true;
         N.interpretation = push_binder_interp
        }
    in
    // When we want an identity embedding/unembedding, we use put/get
    // This is useful when, say, unembedding types for polymorphic tactics, due to our
    // parametricity argument.

    // Note that when embedding, we use bogus types. This is wrong, and we should
    // really keep the unembed types and use them.
    let put : embedder<term> = fun rng t -> { t with pos = rng } in
    let get : unembedder<term> = fun t -> Some t in
    [
      mktac2 "fail"          (fun _ -> fail) get unembed_string put t_unit; //nb: the put embedding is never used
      mktac1 "trivial"       trivial unembed_unit embed_unit t_unit;
      mktac2 "__trytac"        (fun _ -> trytac) get (unembed_tactic_0' get) (embed_option put t_unit) t_unit;
      mktac1 "intro"         intro unembed_unit RE.embed_binder RD.fstar_refl_binder;
      mktac1 "intro_rec"     intro_rec unembed_unit (embed_tuple2
                                              RE.embed_binder RD.fstar_refl_binder
                                              RE.embed_binder RD.fstar_refl_binder)
                                         (E.pair_typ RD.fstar_refl_binder RD.fstar_refl_binder);
      mktac1 "norm"          norm (unembed_list unembed_norm_step) embed_unit t_unit;
      mktac3 "norm_term_env" norm_term_env RE.unembed_env (unembed_list unembed_norm_step) RE.unembed_term RE.embed_term S.t_term;
      mktac2 "norm_binder_type"
                               norm_binder_type (unembed_list unembed_norm_step) RE.unembed_binder embed_unit t_unit;
      mktac2 "rename_to"     rename_to RE.unembed_binder unembed_string embed_unit t_unit;
      mktac1 "binder_retype" binder_retype RE.unembed_binder embed_unit t_unit;
      mktac1 "revert"        revert unembed_unit embed_unit t_unit;
      mktac1 "clear_top"     clear_top unembed_unit embed_unit t_unit;
      mktac1 "clear"         clear RE.unembed_binder embed_unit t_unit;
      mktac1 "rewrite"       rewrite RE.unembed_binder embed_unit t_unit;
      mktac1 "smt"           smt unembed_unit embed_unit t_unit;
      mktac1 "refine_intro"  refine_intro unembed_unit embed_unit t_unit;
      mktac2 "t_exact"       t_exact unembed_bool RE.unembed_term embed_unit t_unit;
      mktac1 "apply"         (apply  true) RE.unembed_term embed_unit t_unit;
      mktac1 "apply_raw"     (apply false) RE.unembed_term embed_unit t_unit;
      mktac1 "apply_lemma"   apply_lemma RE.unembed_term embed_unit t_unit;
      // A tac 5... oh my...
      mktac5 "__divide"        (fun _ _ -> divide) get get unembed_int (unembed_tactic_0' get) (unembed_tactic_0' get)
                                                            (embed_tuple2 put t_unit put t_unit) t_unit;
      mktac2 "__seq"           seq (unembed_tactic_0' unembed_unit) (unembed_tactic_0' unembed_unit) embed_unit t_unit;

      mktac1 "set_options"   set_options unembed_string embed_unit t_unit;

      mktac1 "tc"            tc RE.unembed_term RE.embed_term S.t_term;
      mktac1 "unshelve"      unshelve RE.unembed_term embed_unit t_unit;
      mktac2 "unquote"       unquote get RE.unembed_term put t_unit;

      mktac1 "prune"         prune unembed_string embed_unit t_unit;
      mktac1 "addns"         addns unembed_string embed_unit t_unit;

      mktac1 "print"         print unembed_string embed_unit t_unit;
      mktac1 "dump"          print_proof_state unembed_string embed_unit t_unit;
      mktac1 "dump1"         print_proof_state1 unembed_string embed_unit t_unit;

      mktac2 "__pointwise"     pointwise E.unembed_direction (unembed_tactic_0' unembed_unit) embed_unit t_unit;
      mktac2 "__topdown_rewrite" topdown_rewrite
                                 (unembed_tactic_1 RE.embed_term (unembed_tuple2 unembed_bool unembed_int))
                                 (unembed_tactic_0' unembed_unit)
                                 embed_unit t_unit;

      mktac1 "trefl"         trefl   unembed_unit embed_unit t_unit;
      mktac1 "later"         later   unembed_unit embed_unit t_unit;
      mktac1 "dup"           dup     unembed_unit embed_unit t_unit;
      mktac1 "flip"          flip    unembed_unit embed_unit t_unit;
      mktac1 "qed"           qed     unembed_unit embed_unit t_unit;
      mktac1 "dismiss"       dismiss unembed_unit embed_unit t_unit;
      mktac1 "tadmit"        tadmit  unembed_unit embed_unit t_unit;

      mktac1 "cases"         cases RE.unembed_term (embed_tuple2
                                                      RE.embed_term S.t_term
                                                      RE.embed_term S.t_term)
                                                  (E.pair_typ S.t_term S.t_term);

      mktac1 "top_env"       top_env     unembed_unit RE.embed_env RD.fstar_refl_env;
      mktac1 "cur_env"       cur_env     unembed_unit RE.embed_env RD.fstar_refl_env;
      mktac1 "cur_goal"      cur_goal'   unembed_unit RE.embed_term S.t_term;
      mktac1 "cur_witness"   cur_witness unembed_unit RE.embed_term S.t_term;

      mktac1 "inspect"       inspect RE.unembed_term      RE.embed_term_view RD.fstar_refl_term_view;
      mktac1 "pack"          pack    RE.unembed_term_view RE.embed_term      S.t_term;

      mktac1 "fresh"         fresh       unembed_unit embed_int S.t_int;
      mktac1 "ngoals"        ngoals      unembed_unit embed_int S.t_int;
      mktac1 "ngoals_smt"    ngoals_smt  unembed_unit embed_int S.t_int;
      mktac1 "is_guard"      is_guard    unembed_unit embed_bool t_bool;

      mktac2 "uvar_env"      uvar_env RE.unembed_env (unembed_option RE.unembed_term) RE.embed_term S.t_term;
      mktac2 "unify"         unify RE.unembed_term RE.unembed_term embed_bool t_bool;
      mktac3 "launch_process" launch_process unembed_string unembed_string unembed_string embed_string t_string;

      mktac2 "fresh_bv_named"  fresh_bv_named unembed_string RE.unembed_term RE.embed_bv S.t_bv;
      mktac1 "change"          change RE.unembed_term embed_unit t_unit;

      mktac1 "get_guard_policy" get_guard_policy unembed_unit E.embed_guard_policy E.t_guard_policy;
      mktac1 "set_guard_policy" set_guard_policy E.unembed_guard_policy embed_unit t_unit;

      decr_depth_step;
      incr_depth_step;
      tracepoint_step;
      set_proofstate_range_step;
      push_binder_step
    ]@reflection_primops @native_tactics_steps

// Please note, these markers are for some makefile magic that tweaks this function in the OCaml output

//IN F*: and unembed_tactic_1 (#a:Type) (#b:Type) (arg:embedder a) (res:unembedder b) (f:term) : option (a -> tac b) =
and unembed_tactic_1<'a,'b> (arg:embedder<'a>) (res:unembedder<'b>) (f:term) : option<('a -> tac<'b>)> = //JUST FSHARP
    Some (fun x ->
      let rng = FStar.Range.dummyRange  in
      let x_tm = arg rng x in
      let app = S.mk_Tm_app f [as_arg x_tm] None rng in
      unembed_tactic_0 res app)

//IN F*: and unembed_tactic_0 (#b:Type) (unembed_b:unembedder b) (embedded_tac_b:term) : tac b =
and unembed_tactic_0<'b> (unembed_b:unembedder<'b>) (embedded_tac_b:term) : tac<'b> = //JUST FSHARP
    bind get (fun proof_state ->
    let rng = embedded_tac_b.pos in
    let tm = S.mk_Tm_app embedded_tac_b
                         [S.as_arg (E.embed_proofstate rng proof_state)]
                          None
                          rng in

    // Why not HNF? While we don't care about strong reduction we need more than head
    // normal form due to primitive steps. Consider `norm (steps 2)`: we need to normalize
    // `steps 2` before caling norm, or it will fail to unembed the set of steps. Further,
    // at this moment at least, the normalizer will not call into any step of arity > 1.
    let steps = [N.Weak; N.Reify; N.UnfoldUntil Delta_constant; N.UnfoldTac; N.Primops; N.Unascribe] in
    if Env.debug proof_state.main_context (Options.Other "TacVerbose") then
        BU.print1 "Starting normalizer with %s\n" (Print.term_to_string tm);
    let result = N.normalize_with_primitive_steps (primitive_steps ()) steps proof_state.main_context tm in
    if Env.debug proof_state.main_context (Options.Other "TacVerbose") then
        BU.print1 "Reduced tactic: got %s\n" (Print.term_to_string result);

    // F* requires more annotations.
    // IN F*: let res : option<either<(b * proofstate), (string * proofstate)>> = E.unembed_result result unembed_b in
    let res = E.unembed_result result unembed_b in //JUST FSHARP

    match res with
    | Some (Inl (b, ps)) ->
        bind (set ps) (fun _ -> ret b)

    | Some (Inr (msg, ps)) ->
        bind (set ps) (fun _ -> fail msg)

    | None ->
        Errors.raise_error (Errors.Fatal_TacticGotStuck, (BU.format1 "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s" (Print.term_to_string result))) proof_state.main_context.range
    )
//IN F*: and unembed_tactic_0' (#b:Type) (unembed_b:unembedder b) (embedded_tac_b:term) : option (tac b) =
and unembed_tactic_0'<'b> (unembed_b:unembedder<'b>) (embedded_tac_b:term) : option<(tac<'b>)> = //JUST FSHARP
    Some <| unembed_tactic_0 unembed_b embedded_tac_b

//IN F*: let unembed_tactic_1_alt (#a:Type) (#b:Type) (arg:embedder a) (res:unembedder b) (f:term) : option (a -> tac b) =
let unembed_tactic_1_alt<'a,'b> (arg:embedder<'a>) (res:unembedder<'b>) (f:term) : option<('a -> tac<'b>)> = //JUST FSHARP
    Some (fun x ->
      let rng = FStar.Range.dummyRange  in
      let x_tm = arg rng x in
      let app = S.mk_Tm_app f [as_arg x_tm] None rng in
      let app = U.mk_reify app in
      unembed_tactic_0 res app)


let report_implicits ps (is : Env.implicits) : unit =
    let errs = List.map (fun (r, _, uv, _, ty, rng) ->
                (Errors.Fatal_UninstantiatedUnificationVarInTactic, BU.format3 ("Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")")
                             (Print.uvar_to_string uv) (Print.term_to_string ty) r,
                 rng)) is in
    match errs with
    | [] -> ()
    | (e, msg, r)::tl -> begin
        dump_proofstate ps "failing due to uninstantiated implicits";
        // A trick to print each error exactly once.
        Err.add_errors tl;
        Err.raise_error (e, msg) r
    end

let run_tactic_on_typ (tactic:term) (env:env) (typ:typ) : list<goal> // remaining goals
                                                        * term // witness
                                                        =
    // This bit is really important: a typechecked tactic can contain many uvar redexes
    // that make normalization SUPER slow (probably exponential). Doing this first pass
    // gets rid of those redexes and leaves a much smaller term, which performs a lot better.
    if !tacdbg then
        BU.print1 "About to reduce uvars on: %s\n" (Print.term_to_string tactic);
    let tactic = N.reduce_uvar_solutions env tactic in
    if !tacdbg then
        BU.print1 "About to check tactic term: %s\n" (Print.term_to_string tactic);

    (* Do NOT use the returned tactic, the typechecker is not idempotent and
     * will mess up the monadic lifts . c.f #1307 *)
    let _, _, g = TcTerm.tc_reified_tactic env tactic in
    TcRel.force_trivial_guard env g;
    Err.stop_if_err ();
    let tau = unembed_tactic_0 unembed_unit tactic in
    let env, _ = Env.clear_expected_typ env in
    let env = { env with Env.instantiate_imp = false } in
    (* TODO: We do not faithfully expose universes to metaprograms *)
    let env = { env with Env.lax_universes = true } in
    let ps, w = proofstate_of_goal_ty env typ in
    if !tacdbg then
        BU.print1 "Running tactic with goal = %s\n" (Print.term_to_string typ);
    let res, ms = BU.record_time (fun () -> run tau ps) in
    if !tacdbg then
        BU.print3 "Tactic %s ran in %s ms (%s)\n" (Print.term_to_string tactic) (string_of_int ms) (Print.lid_to_string env.curmodule);
    match res with
    | Success (_, ps) ->
        if !tacdbg then
            BU.print1 "Tactic generated proofterm %s\n" (Print.term_to_string w); //FIXME: Is this right?
        List.iter (fun g -> if is_irrelevant g
                            then if TcRel.teq_nosmt g.context g.witness U.exp_unit
                                 then ()
                                 else failwith (BU.format1 "Irrelevant tactic witness does not unify with (): %s" (Print.term_to_string g.witness))
                            else ())
                  (ps.goals @ ps.smt_goals);

        // Check that all implicits are instantiated. This will also typecheck
        // the implicits, so make it do a lax check because we certainly
        // do not want to repeat all of the reasoning that took place in tactics.
        // It would also most likely fail.
        let g = {TcRel.trivial_guard with Env.implicits=ps.all_implicits} in
        let g = TcRel.solve_deferred_constraints env g |> TcRel.resolve_implicits_tac in
        report_implicits ps g.implicits;
        (ps.goals@ps.smt_goals, w)

    | Failed (s, ps) ->
        dump_proofstate (subst_proof_state (N.psc_subst ps.psc) ps) "at the time of failure";
        Errors.raise_error (Errors.Fatal_ArgumentLengthMismatch, (BU.format1 "user tactic failed: %s" s)) typ.pos

// Polarity
type pol =
    | Pos
    | Neg
    | Both // traversing both polarities at once

// Result of traversal
type tres_m<'a> =
    | Unchanged of 'a
    | Simplified of 'a * list<goal>
    | Dual of 'a * 'a * list<goal>

type tres = tres_m<term>

let tpure x = Unchanged x

let flip p = match p with
    | Pos -> Neg
    | Neg -> Pos
    | Both -> Both

let by_tactic_interp (pol:pol) (e:Env.env) (t:term) : tres =
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with

    // by_tactic marker
    | Tm_fvar fv, [(rett, Some (Implicit _)); (tactic, None); (assertion, None)]
            when S.fv_eq_lid fv PC.by_tactic_lid ->
        begin match pol with
        | Pos ->
            let gs, _ = run_tactic_on_typ tactic e assertion in
            Simplified (FStar.Syntax.Util.t_true, gs)

        | Both ->
            let gs, _ = run_tactic_on_typ tactic e assertion in
            Dual (assertion, FStar.Syntax.Util.t_true, gs)

        | Neg ->
            // Peel away tactics in negative positions, they're assumptions!
            Simplified (assertion, [])
        end

    // spinoff marker: simply spin off a query independently.
    // So, equivalent to `by_tactic idtac` without importing the (somewhat heavy) tactics module
    | Tm_fvar fv, [(assertion, None)]
            when S.fv_eq_lid fv PC.spinoff_lid ->
        begin  match pol with
        | Pos ->
            Simplified (FStar.Syntax.Util.t_true, [fst <| goal_of_goal_ty e assertion])

        | Both ->
            Dual (assertion, FStar.Syntax.Util.t_true, [fst <| goal_of_goal_ty e assertion])

        | Neg ->
            Simplified (assertion, [])
        end

    | _ ->
        Unchanged t

let explode (t : tres_m<'a>) : 'a * 'a * list<goal> =
    match t with
    | Unchanged t -> (t, t, [])
    | Simplified (t, gs) -> (t, t, gs)
    | Dual (tn, tp, gs) -> (tn, tp, gs)

let comb1 (f : 'a -> 'b) : tres_m<'a> -> tres_m<'b> = function
    | Unchanged t -> Unchanged (f t)
    | Simplified (t, gs) -> Simplified (f t, gs)
    | Dual (tn, tp, gs) -> Dual (f tn, f tp, gs)

let comb2 (f : 'a -> 'b -> 'c ) (x : tres_m<'a>) (y : tres_m<'b>) : tres_m<'c> =
    match x, y with
    | Unchanged t1, Unchanged t2 ->
        Unchanged (f t1 t2)

    | Unchanged t1, Simplified (t2, gs)
    | Simplified (t1, gs), Unchanged t2 ->
        Simplified (f t1 t2, gs)

    | Simplified (t1, gs1), Simplified (t2, gs2) ->
        Simplified (f t1 t2, gs1@gs2)

    | _ ->
        let (n1, p1, gs1) = explode x in
        let (n2, p2, gs2) = explode y in
        Dual (f n1 n2, f p1 p2, gs1@gs2)

let comb_list (rs : list<tres_m<'a>>) : tres_m<list<'a>> =
    let rec aux rs acc =
        match rs with
        | [] -> acc
        | hd::tl -> aux tl (comb2 (fun l r -> l::r) hd acc)
    in
    aux (List.rev rs) (tpure [])

let emit (gs : list<goal>) (m : tres_m<'a>) : tres_m<'a> =
    comb2 (fun () x -> x) (Simplified ((), gs)) m

let rec traverse (f: pol -> Env.env -> term -> tres) (pol:pol) (e:Env.env) (t:term) : tres =
    let r =
        match (SS.compress t).n with
        | Tm_uinst (t,us) -> let tr = traverse f pol e t in
                             comb1 (fun t' -> Tm_uinst (t', us)) tr

        | Tm_meta (t, m) -> let tr = traverse f pol e t in
                            comb1 (fun t' -> Tm_meta (t', m)) tr

        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv PC.imp_lid ->
               // ==> is specialized to U_zero
               let x = S.new_bv None (U.mk_squash U_zero p) in
               let r1 = traverse f (flip pol)  e                p in
               let r2 = traverse f       pol  (Env.push_bv e x) q in
               comb2 (fun l r -> (U.mk_imp l r).n) r1 r2

        (* p <==> q is special, each side is bipolar *)
        (* So we traverse its arguments with pol = Both, and negative and positive versions *)
        (* of p and q *)
        (* then we return (in general) (p- ==> q+) /\ (q- ==> p+) *)
        (* But if neither side ran tactics, we just keep p <==> q *)
        | Tm_app ({ n = Tm_fvar fv }, [(p,_); (q,_)]) when S.fv_eq_lid fv PC.iff_lid ->
               // <==> is specialized to U_zero
               let xp = S.new_bv None (U.mk_squash U_zero p) in
               let xq = S.new_bv None (U.mk_squash U_zero q) in
               let r1 = traverse f Both (Env.push_bv e xq) p in
               let r2 = traverse f Both (Env.push_bv e xp) q in
               // Should be flipping the tres, I think
               begin match r1, r2 with
               | Unchanged _, Unchanged _ ->
                  comb2 (fun l r -> (U.mk_iff l r).n) r1 r2
               | _ ->
                  let (pn, pp, gs1) = explode r1 in
                  let (qn, qp, gs2) = explode r2 in
                  let t = U.mk_conj (U.mk_imp pn qp) (U.mk_imp qn pp) in
                  Simplified (t.n, gs1@gs2)
               end

        | Tm_app (hd, args) ->
                let r0 = traverse f pol e hd in
                let r1 = List.fold_right (fun (a, q) r ->
                                              let r' = traverse f pol e a in
                                              comb2 (fun a args -> (a, q)::args) r' r)
                                                 args (tpure []) in
                comb2 (fun hd args -> Tm_app (hd, args)) r0 r1

        | Tm_abs (bs, t, k) ->
                // TODO: traverse k?
                let bs, topen = SS.open_term bs t in
                let e' = Env.push_binders e bs in
                let r0 = List.map (fun (bv, aq) ->
                                     let r = traverse f (flip pol) e bv.sort in
                                     comb1 (fun s' -> ({ bv with sort = s' }, aq)) r
                                  ) bs
                in
                let rbs = comb_list r0 in
                let rt = traverse f pol e' topen in
                comb2 (fun bs t -> (U.abs bs t k).n) rbs rt

        | Tm_ascribed (t, asc, ef) ->
            // TODO: traverse the types?
            comb1 (fun t -> Tm_ascribed (t, asc, ef)) (traverse f pol e t)

        | x ->
            tpure x in
    match r with
    | Unchanged tn' ->
        f pol e ({ t with n = tn' })

    | Simplified (tn', gs) ->
        emit gs (f pol e ({ t with n = tn' }))

    | Dual (tn, tp, gs) ->
        let rp = f pol e ({ t with n = tp }) in
        let (_, p', gs') = explode rp in
        Dual ({t with n = tn}, p', gs@gs')

let getprop (e:env) (t:term) : option<term> =
    let tn = N.normalize [N.Weak; N.HNF; N.UnfoldUntil Delta_constant] e t in
    U.un_squash tn

let preprocess (env:Env.env) (goal:term) : list<(Env.env * term * FStar.Options.optionstate)> =
    tacdbg := Env.debug env (Options.Other "Tac");
    if !tacdbg then
        BU.print2 "About to preprocess %s |= %s\n"
                        (Env.all_binders env |> Print.binders_to_string ",")
                        (Print.term_to_string goal);
    let initial = (1, []) in
    // This match should never fail
    let (t', gs) =
        match traverse by_tactic_interp Pos env goal with
        | Unchanged t' -> (t', [])
        | Simplified (t', gs) -> (t', gs)
        | _ -> failwith "no"
    in
    if !tacdbg then
        BU.print2 "Main goal simplified to: %s |- %s\n"
                (Env.all_binders env |> Print.binders_to_string ", ")
                (Print.term_to_string t');
    let s = initial in
    let s = List.fold_left (fun (n,gs) g ->
                 let phi = match getprop g.context g.goal_ty with
                           | None ->
                                Err.raise_error (Err.Fatal_TacticProofRelevantGoal,
                                    (BU.format1 "Tactic returned proof-relevant goal: %s" (Print.term_to_string g.goal_ty))) env.range
                           | Some phi -> phi
                 in
                 if !tacdbg then
                     BU.print2 "Got goal #%s: %s\n" (string_of_int n) (goal_to_string g);
                 let gt' = TcUtil.label ("Could not prove goal #" ^ string_of_int n) goal.pos phi in
                 (n+1, (g.context, gt', g.opts)::gs)) s gs in
    let (_, gs) = s in
    // Use default opts for main goal
    (env, t', FStar.Options.peek ()) :: gs

let reify_tactic (a : term) : term =
    let r = S.mk_Tm_uinst (S.fv_to_tm (S.lid_as_fv PC.reify_tactic_lid Delta_equational None)) [U_zero] in
    mk_Tm_app r [S.iarg t_unit; S.as_arg a] None a.pos

let synthesize (env:Env.env) (typ:typ) (tau:term) : term =
    tacdbg := Env.debug env (Options.Other "Tac");
    let gs, w = run_tactic_on_typ (reify_tactic tau) env typ in
    // Check that all goals left are irrelevant. We don't need to check their
    // validity, as we will typecheck the witness independently.
    if List.existsML (fun g -> not (Option.isSome (getprop g.context g.goal_ty))) gs
    then Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, ("synthesis left open goals")) typ.pos
    else w

let splice (env:Env.env) (tau:term) : list<sigelt> =
    tacdbg := Env.debug env (Options.Other "Tac");
    let typ = S.t_decls in // running with goal type FStar.Reflection.Data.decls
    let gs, w = run_tactic_on_typ (reify_tactic tau) env typ in
    // Check that all goals left are irrelevant. We don't need to check their
    // validity, as we will typecheck the witness independently.
    if List.existsML (fun g -> not (Option.isSome (getprop g.context g.goal_ty))) gs
        then Err.raise_error (Err.Fatal_OpenGoalsInSynthesis, ("splice left open goals")) typ.pos;

    // Fully normalize the witness
    let w = N.normalize [N.Weak; N.HNF; N.UnfoldUntil Delta_constant;
                         N.Primops; N.Unascribe; N.Unmeta] env w in

    // Unembed it, this must work if things are well-typed
    BU.must <| unembed_list RE.unembed_sigelt w
