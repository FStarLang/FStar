#light "off"
module FStar.Tactics.InterpFuns

(* This module is awful, don't even look at it please. *)

open FStar
open FStar.All
open FStar.Syntax.Syntax
open FStar.Range

open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Syntax.Embeddings
open FStar.Tactics.Basic
open FStar.Tactics.Native

module S     = FStar.Syntax.Syntax
module SS    = FStar.Syntax.Subst
module PC    = FStar.Parser.Const
module BU    = FStar.Util
module Print = FStar.Syntax.Print
module Cfg   = FStar.TypeChecker.Cfg
module E     = FStar.Tactics.Embedding
module RE    = FStar.Reflection.Embeddings
module NBETerm = FStar.TypeChecker.NBETerm

let mk_tactic_interpretation_0 (reflect:bool)
                               (t:tac<'r>) (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
 (*  We have: t () embedded_state
     The idea is to:
        1. unembed the state
        2. run the `t` tactic (catching exceptions)
        3. embed the result and final state and return it to the normalizer
  *)
  match args with
  | [(embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, args are: %s\n"
            (Ident.string_of_lid nm)
            (Print.args_to_string args));
    let res = embed (E.e_result er) (Cfg.psc_range psc) (run_safe t ps) in
    Some res)
  | _ ->
    failwith ("Unexpected application of tactic primitive")

let mk_tactic_interpretation_1 (reflect:bool)
                               (t:'a -> tac<'r>) (ea:embedding<'a>)
                               (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed ea a) (fun a ->
    let res = run_safe (t a) ps in
    Some (embed (E.e_result er) (Cfg.psc_range psc) res)))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_1_env
                               (reflect:bool)
                               (t:Cfg.psc -> 'a -> tac<'r>) (ea:embedding<'a>)
                               (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed ea a) (fun a ->
    let res = run_safe (t psc a) ps in
    Some (embed (E.e_result er) (Cfg.psc_range psc) res)))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_2 (reflect:bool)
                               (t:'a -> 'b -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>)
                               (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed ea a) (fun a ->
    BU.bind_opt (unembed eb b) (fun b ->
    let res = run_safe (t a b) ps in
    Some (embed (E.e_result er) (Cfg.psc_range psc) res))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_3 (reflect:bool)
                               (t:'a -> 'b -> 'c -> tac<'r>)
                               (ea:embedding<'a>)
                               (eb:embedding<'b>)
                               (ec:embedding<'c>)
                               (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed ea a) (fun a ->
    BU.bind_opt (unembed eb b) (fun b ->
    BU.bind_opt (unembed ec c) (fun c ->
    let res = run_safe (t a b c) ps in
    Some (embed (E.e_result er) (Cfg.psc_range psc) res)))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_4 (reflect:bool)
                               (t:'a -> 'b -> 'c -> 'd -> tac<'r>)
                               (ea:embedding<'a>)
                               (eb:embedding<'b>)
                               (ec:embedding<'c>)
                               (ed:embedding<'d>)
                               (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed ea a) (fun a ->
    BU.bind_opt (unembed eb b) (fun b ->
    BU.bind_opt (unembed ec c) (fun c ->
    BU.bind_opt (unembed ed d) (fun d ->
    let res = run_safe (t a b c d) ps in
    Some (embed (E.e_result er) (Cfg.psc_range psc) res))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_5 (reflect:bool)
                               (t:'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
                               (ea:embedding<'a>)
                               (eb:embedding<'b>)
                               (ec:embedding<'c>)
                               (ed:embedding<'d>)
                               (ee:embedding<'e>)
                               (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (e, _); (embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed ea a) (fun a ->
    BU.bind_opt (unembed eb b) (fun b ->
    BU.bind_opt (unembed ec c) (fun c ->
    BU.bind_opt (unembed ed d) (fun d ->
    BU.bind_opt (unembed ee e) (fun e ->
    let res = run_safe (t a b c d e) ps in
    Some (embed (E.e_result er) (Cfg.psc_range psc) res)))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let mk_tactic_interpretation_6 (reflect:bool)
                               (t:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> tac<'r>)
                               (ea:embedding<'a>)
                               (eb:embedding<'b>)
                               (ec:embedding<'c>)
                               (ed:embedding<'d>)
                               (ee:embedding<'e>)
                               (ef:embedding<'f>)
                               (er:embedding<'r>)
                               (nm:Ident.lid) (psc:Cfg.psc) (args:args) : option<term> =
  match args with
  | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _); (embedded_state, _)] ->
    BU.bind_opt (unembed E.e_proofstate embedded_state) (fun ps ->
    let ps = set_ps_psc psc ps in
    log ps (fun () ->
    BU.print2 "Reached %s, goals are: %s\n"
            (Ident.string_of_lid nm)
            (Print.term_to_string embedded_state));
    BU.bind_opt (unembed ea a) (fun a ->
    BU.bind_opt (unembed eb b) (fun b ->
    BU.bind_opt (unembed ec c) (fun c ->
    BU.bind_opt (unembed ed d) (fun d ->
    BU.bind_opt (unembed ee e) (fun e ->
    BU.bind_opt (unembed ef f) (fun f ->
    let res = run_safe (t a b c d e f) ps in
    Some (embed (E.e_result er) (Cfg.psc_range psc) res))))))))
  | _ ->
    failwith (Util.format2 "Unexpected application of tactic primitive %s %s" (Ident.string_of_lid nm) (Print.args_to_string args))

let step_from_native_step (s: native_primitive_step): Cfg.primitive_step =
    { Cfg.name=s.name;
      Cfg.arity=s.arity;
      Cfg.univ_arity=0; // Zoe : We might need to change that
      Cfg.auto_reflect=Some (s.arity - 1);
      Cfg.strong_reduction_ok=s.strong_reduction_ok;
      Cfg.requires_binder_substitution = false; // GM: really?
      Cfg.interpretation=(fun psc args -> s.tactic psc args);
      Cfg.interpretation_nbe = NBETerm.dummy_interp s.name;
   }

let mk nm nunivs arity interpretation =
  let nm = E.fstar_tactics_lid' ["Builtins";nm] in {
  Cfg.name=nm;
  Cfg.arity=arity;
  Cfg.univ_arity=nunivs;
  Cfg.auto_reflect=Some (arity - 1);
  Cfg.strong_reduction_ok=false;
  Cfg.requires_binder_substitution = true;
  Cfg.interpretation=(fun psc args -> interpretation nm psc args);
  Cfg.interpretation_nbe = NBETerm.dummy_interp nm;
}

let native_tactics = list_all ()
let native_tactics_steps = List.map step_from_native_step native_tactics

// mktac0 cannot exist due to having a top-level effect
let mktac1 (nunivs:int) (name : string) (f : 'a -> tac<'r>)
           (ea : embedding<'a>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 2 nunivs (mk_tactic_interpretation_1 false f ea er)

let mktac2 (nunivs:int) (name : string) (f : 'a -> 'b -> tac<'r>)
           (ea : embedding<'a>) (eb : embedding<'b>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 3 nunivs (mk_tactic_interpretation_2 false f ea eb er)

let mktac3 (nunivs:int) (name : string) (f : 'a -> 'b -> 'c -> tac<'r>)
           (ea : embedding<'a>) (eb : embedding<'b>) (ec : embedding<'c>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 4 nunivs (mk_tactic_interpretation_3 false f ea eb ec er)

let mktac5 (nunivs:int) (name : string) (f : 'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
           (ea : embedding<'a>) (eb : embedding<'b>) (ec : embedding<'c>)
           (ed : embedding<'d>) (ee : embedding<'e>)
           (er : embedding<'r>) : Cfg.primitive_step =
    mk name 6 nunivs (mk_tactic_interpretation_5 false f ea eb ec ed ee er)
