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
module NBET    = FStar.TypeChecker.NBETerm

let unembed e t n = FStar.Syntax.Embeddings.unembed e t true n
let embed e rng t n = FStar.Syntax.Embeddings.embed e t rng None n

let extract_1 (ea:embedding<'a>)
              (ncb:norm_cb) (args:args) : option<'a> =
    match args with
    | [(a, _)] ->
      BU.bind_opt (unembed ea a ncb) (fun a ->
      Some a)
    | _ ->
      failwith "extract_1: wrong number of arguments"

let extract_2 (ea:embedding<'a>) (eb:embedding<'b>)
              (ncb:norm_cb) (args:args) : option<('a * 'b)> =
    match args with
    | [(a, _); (b, _)] ->
      BU.bind_opt (unembed ea a ncb) (fun a ->
      BU.bind_opt (unembed eb b ncb) (fun b ->
      Some (a, b)))
    | _ ->
      failwith "extract_2: wrong number of arguments"

let extract_3 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>)
              (ncb:norm_cb) (args:args) : option<('a * 'b * 'c)> =
    match args with
    | [(a, _); (b, _); (c, _)] ->
      BU.bind_opt (unembed ea a ncb) (fun a ->
      BU.bind_opt (unembed eb b ncb) (fun b ->
      BU.bind_opt (unembed ec c ncb) (fun c ->
      Some (a, b, c))))
    | _ ->
      failwith "extract_3: wrong number of arguments"

let extract_4 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (ncb:norm_cb) (args:args) : option<('a * 'b * 'c * 'd)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _)] ->
      BU.bind_opt (unembed ea a ncb) (fun a ->
      BU.bind_opt (unembed eb b ncb) (fun b ->
      BU.bind_opt (unembed ec c ncb) (fun c ->
      BU.bind_opt (unembed ed d ncb) (fun d ->
      Some (a, b, c, d)))))
    | _ ->
      failwith "extract_4: wrong number of arguments"

let extract_5 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (ee:embedding<'e>)
              (ncb:norm_cb) (args:args) : option<('a * 'b * 'c * 'd * 'e)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
      BU.bind_opt (unembed ea a ncb) (fun a ->
      BU.bind_opt (unembed eb b ncb) (fun b ->
      BU.bind_opt (unembed ec c ncb) (fun c ->
      BU.bind_opt (unembed ed d ncb) (fun d ->
      BU.bind_opt (unembed ee e ncb) (fun e ->
      Some (a, b, c, d, e))))))
    | _ ->
      failwith "extract_5: wrong number of arguments"

let extract_6 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (ee:embedding<'e>) (ef:embedding<'f>)
              (ncb:norm_cb) (args:args) : option<('a * 'b * 'c * 'd * 'e * 'f)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _)] ->
      BU.bind_opt (unembed ea a ncb) (fun a ->
      BU.bind_opt (unembed eb b ncb) (fun b ->
      BU.bind_opt (unembed ec c ncb) (fun c ->
      BU.bind_opt (unembed ed d ncb) (fun d ->
      BU.bind_opt (unembed ee e ncb) (fun e ->
      BU.bind_opt (unembed ef f ncb) (fun f ->
      Some (a, b, c, d, e, f)))))))
    | _ ->
      failwith "extract_6: wrong number of arguments"

let extract_7 (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
              (ee:embedding<'e>) (ef:embedding<'f>) (eg:embedding<'g>)
              (ncb:norm_cb) (args:args) : option<('a * 'b * 'c * 'd * 'e * 'f * 'g)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _); (g, _)] ->
      BU.bind_opt (unembed ea a ncb) (fun a ->
      BU.bind_opt (unembed eb b ncb) (fun b ->
      BU.bind_opt (unembed ec c ncb) (fun c ->
      BU.bind_opt (unembed ed d ncb) (fun d ->
      BU.bind_opt (unembed ee e ncb) (fun e ->
      BU.bind_opt (unembed ef f ncb) (fun f ->
      BU.bind_opt (unembed eg g ncb) (fun g ->
      Some (a, b, c, d, e, f, g))))))))
    | _ ->
      failwith "extract_7: wrong number of arguments"

let extract_1_nbe (ea:NBETerm.embedding<'a>)
              (args:NBETerm.args) : option<'a> =
    match args with
    | [(a, _)] ->
      BU.bind_opt (NBETerm.unembed ea a) (fun a ->
      Some a)
    | _ ->
      failwith "extract_1_nbe: wrong number of arguments"

let extract_2_nbe (ea:NBETerm.embedding<'a>) (eb:NBETerm.embedding<'b>)
              (args:NBETerm.args) : option<('a * 'b)> =
    match args with
    | [(a, _); (b, _)] ->
      BU.bind_opt (NBETerm.unembed ea a) (fun a ->
      BU.bind_opt (NBETerm.unembed eb b) (fun b ->
      Some (a, b)))
    | _ ->
      failwith "extract_2_nbe: wrong number of arguments"

let extract_3_nbe (ea:NBETerm.embedding<'a>) (eb:NBETerm.embedding<'b>) (ec:NBETerm.embedding<'c>)
              (args:NBETerm.args) : option<('a * 'b * 'c)> =
    match args with
    | [(a, _); (b, _); (c, _)] ->
      BU.bind_opt (NBETerm.unembed ea a) (fun a ->
      BU.bind_opt (NBETerm.unembed eb b) (fun b ->
      BU.bind_opt (NBETerm.unembed ec c) (fun c ->
      Some (a, b, c))))
    | _ ->
      failwith "extract_3_nbe: wrong number of arguments"

let extract_4_nbe (ea:NBETerm.embedding<'a>) (eb:NBETerm.embedding<'b>) (ec:NBETerm.embedding<'c>) (ed:NBETerm.embedding<'d>)
              (args:NBETerm.args) : option<('a * 'b * 'c * 'd)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _)] ->
      BU.bind_opt (NBETerm.unembed ea a) (fun a ->
      BU.bind_opt (NBETerm.unembed eb b) (fun b ->
      BU.bind_opt (NBETerm.unembed ec c) (fun c ->
      BU.bind_opt (NBETerm.unembed ed d) (fun d ->
      Some (a, b, c, d)))))
    | _ ->
      failwith "extract_4_nbe: wrong number of arguments"

let extract_5_nbe (ea:NBETerm.embedding<'a>) (eb:NBETerm.embedding<'b>) (ec:NBETerm.embedding<'c>) (ed:NBETerm.embedding<'d>)
              (ee:NBETerm.embedding<'e>)
              (args:NBETerm.args) : option<('a * 'b * 'c * 'd * 'e)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _)] ->
      BU.bind_opt (NBETerm.unembed ea a) (fun a ->
      BU.bind_opt (NBETerm.unembed eb b) (fun b ->
      BU.bind_opt (NBETerm.unembed ec c) (fun c ->
      BU.bind_opt (NBETerm.unembed ed d) (fun d ->
      BU.bind_opt (NBETerm.unembed ee e) (fun e ->
      Some (a, b, c, d, e))))))
    | _ ->
      failwith "extract_5_nbe: wrong number of arguments"

let extract_6_nbe (ea:NBETerm.embedding<'a>) (eb:NBETerm.embedding<'b>) (ec:NBETerm.embedding<'c>) (ed:NBETerm.embedding<'d>)
              (ee:NBETerm.embedding<'e>) (ef:NBETerm.embedding<'f>)
              (args:NBETerm.args) : option<('a * 'b * 'c * 'd * 'e * 'f)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _)] ->
      BU.bind_opt (NBETerm.unembed ea a) (fun a ->
      BU.bind_opt (NBETerm.unembed eb b) (fun b ->
      BU.bind_opt (NBETerm.unembed ec c) (fun c ->
      BU.bind_opt (NBETerm.unembed ed d) (fun d ->
      BU.bind_opt (NBETerm.unembed ee e) (fun e ->
      BU.bind_opt (NBETerm.unembed ef f) (fun f ->
      Some (a, b, c, d, e, f)))))))
    | _ ->
      failwith "extract_6_nbe: wrong number of arguments"

let extract_7_nbe (ea:NBETerm.embedding<'a>) (eb:NBETerm.embedding<'b>) (ec:NBETerm.embedding<'c>) (ed:NBETerm.embedding<'d>)
              (ee:NBETerm.embedding<'e>) (ef:NBETerm.embedding<'f>) (eg:NBETerm.embedding<'g>)
              (args:NBETerm.args) : option<('a * 'b * 'c * 'd * 'e * 'f * 'g)> =
    match args with
    | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _); (g, _)] ->
      BU.bind_opt (NBETerm.unembed ea a) (fun a ->
      BU.bind_opt (NBETerm.unembed eb b) (fun b ->
      BU.bind_opt (NBETerm.unembed ec c) (fun c ->
      BU.bind_opt (NBETerm.unembed ed d) (fun d ->
      BU.bind_opt (NBETerm.unembed ee e) (fun e ->
      BU.bind_opt (NBETerm.unembed ef f) (fun f ->
      BU.bind_opt (NBETerm.unembed eg g) (fun g ->
      Some (a, b, c, d, e, f, g))))))))
    | _ ->
      failwith "extract_7_nbe: wrong number of arguments"


let mk_tactic_interpretation_1 (t:'a -> tac<'r>)
                               (ea:embedding<'a>) (er:embedding<'r>)
                               (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_2 ea E.e_proofstate ncb args) (fun (a, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r ncb))

let mk_tactic_interpretation_2 (t:'a -> 'b -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (er:embedding<'r>)
                               (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_3 ea eb E.e_proofstate ncb args) (fun (a, b, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r ncb))

let mk_tactic_interpretation_3 (t:'a -> 'b -> 'c -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (er:embedding<'r>)
                               (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_4 ea eb ec E.e_proofstate ncb args) (fun (a, b, c, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r ncb))

let mk_tactic_interpretation_4 (t:'a -> 'b -> 'c -> 'd -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
                               (er:embedding<'r>)
                               (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_5 ea eb ec ed E.e_proofstate ncb args) (fun (a, b, c, d, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c d) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r ncb))

let mk_tactic_interpretation_5 (t:'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
                               (ee:embedding<'e>) (er:embedding<'r>)
                               (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_6 ea eb ec ed ee E.e_proofstate ncb args) (fun (a, b, c, d, e, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c d e) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r ncb))

let mk_tactic_interpretation_6 (t:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> tac<'r>)
                               (ea:embedding<'a>) (eb:embedding<'b>) (ec:embedding<'c>) (ed:embedding<'d>)
                               (ee:embedding<'e>) (ef:embedding<'f>) (er:embedding<'r>)
                               (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_7 ea eb ec ed ee ef E.e_proofstate ncb args) (fun (a, b, c, d, e, f, ps) ->
  let ps = set_ps_psc psc ps in
  let r = run_safe (t a b c d e f) ps in
  Some (embed (E.e_result er) (Cfg.psc_range psc) r ncb))

let mk_tactic_nbe_interpretation_1 (t:'a -> tac<'r>)
                               (ea:NBET.embedding<'a>) (er:NBET.embedding<'r>)
                               (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_2_nbe ea E.e_proofstate_nbe args) (fun (a, ps) ->
  let r = run_safe (t a) ps in
  Some (NBETerm.embed (E.e_result_nbe er) r))

let mk_tactic_nbe_interpretation_2 (t:'a -> 'b -> tac<'r>)
                               (ea:NBET.embedding<'a>) (eb:NBET.embedding<'b>) (er:NBET.embedding<'r>)
                               (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_3_nbe ea eb E.e_proofstate_nbe args) (fun (a, b, ps) ->
  let r = run_safe (t a b) ps in
  Some (NBETerm.embed (E.e_result_nbe er) r))

let mk_tactic_nbe_interpretation_3 (t:'a -> 'b -> 'c -> tac<'r>)
                               (ea:NBET.embedding<'a>) (eb:NBET.embedding<'b>) (ec:NBET.embedding<'c>) (er:NBET.embedding<'r>)
                               (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_4_nbe ea eb ec E.e_proofstate_nbe args) (fun (a, b, c, ps) ->
  let r = run_safe (t a b c) ps in
  Some (NBETerm.embed (E.e_result_nbe er) r))

let mk_tactic_nbe_interpretation_4 (t:'a -> 'b -> 'c -> 'd -> tac<'r>)
                               (ea:NBET.embedding<'a>) (eb:NBET.embedding<'b>) (ec:NBET.embedding<'c>) (ed:NBET.embedding<'d>)
                               (er:NBET.embedding<'r>)
                               (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_5_nbe ea eb ec ed E.e_proofstate_nbe args) (fun (a, b, c, d, ps) ->
  let r = run_safe (t a b c d) ps in
  Some (NBETerm.embed (E.e_result_nbe er) r))

let mk_tactic_nbe_interpretation_5 (t:'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)
                               (ea:NBET.embedding<'a>) (eb:NBET.embedding<'b>) (ec:NBET.embedding<'c>) (ed:NBET.embedding<'d>)
                               (ee:NBET.embedding<'e>) (er:NBET.embedding<'r>)
                               (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_6_nbe ea eb ec ed ee E.e_proofstate_nbe args) (fun (a, b, c, d, e, ps) ->
  let r = run_safe (t a b c d e) ps in
  Some (NBETerm.embed (E.e_result_nbe er) r))

let mk_tactic_nbe_interpretation_6 (t:'a -> 'b -> 'c -> 'd -> 'e -> 'f -> tac<'r>)
                               (ea:NBET.embedding<'a>) (eb:NBET.embedding<'b>) (ec:NBET.embedding<'c>) (ed:NBET.embedding<'d>)
                               (ee:NBET.embedding<'e>) (ef:NBET.embedding<'f>) (er:NBET.embedding<'r>)
                               (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_7_nbe ea eb ec ed ee ef E.e_proofstate_nbe args) (fun (a, b, c, d, e, f, ps) ->
  let r = run_safe (t a b c d e f) ps in
  Some (NBETerm.embed (E.e_result_nbe er) r))

let step_from_native_step (s: native_primitive_step): Cfg.primitive_step =
  { Cfg.name                         = s.name
  ; Cfg.arity                        = s.arity
  ; Cfg.univ_arity                   = 0 // Zoe : We might need to change that
  ; Cfg.auto_reflect                 = Some (s.arity - 1)
  ; Cfg.strong_reduction_ok          = s.strong_reduction_ok
  ; Cfg.requires_binder_substitution = false // GM: Don't think we care about pretty-printing on native
  ; Cfg.interpretation               = s.tactic
  ; Cfg.interpretation_nbe           = NBETerm.dummy_interp s.name
  }

let mk nm arity nunivs interp nbe_interp =
  let nm = E.fstar_tactics_lid' ["Builtins"; nm] in
  { Cfg.name                         = nm
  ; Cfg.arity                        = arity
  ; Cfg.univ_arity                   = nunivs
  ; Cfg.auto_reflect                 = Some (arity - 1)
  ; Cfg.strong_reduction_ok          = true
  ; Cfg.requires_binder_substitution = true
  ; Cfg.interpretation               = interp
  ; Cfg.interpretation_nbe           = nbe_interp
  }

let native_tactics = list_all ()
let native_tactics_steps = List.map step_from_native_step native_tactics

let rec drop n l =
    if n = 0 then l
    else
        match l with
        | [] -> failwith "drop: impossible"
        | _::xs -> drop (n-1) xs

(* These functions are suboptimal, since they need to take embeddings for both
 * the interpreter AND the NBE evaluator. Attempting to coallesce them
 * is not easy, since we have some parametric e_any embeddings of differing types
 * (S.embedding<term> vs NBETerm.embedding<NBETerm.t>). So we pass both of them.
 * We also need to pass in two versions of the underlying primitive, since they
 * will be instantiated differently (again term vs NBETerm.t). Such is life
 * without higher-order polymorphism. *)
let mktac1 (nunivs:int) (name : string)
           (f : 'a -> tac<'r>) (ea : embedding<'a>) (er : embedding<'r>)
           (nf : 'na -> tac<'nr>) (nea : NBET.embedding<'na>) (ner : NBET.embedding<'nr>)
           : Cfg.primitive_step =
    mk name 2 nunivs (mk_tactic_interpretation_1     f  ea  er)
                     (fun args -> mk_tactic_nbe_interpretation_1 nf nea ner (drop nunivs args))

let mktac2 (nunivs:int) (name : string)
           (f : 'a -> 'b -> tac<'r>)  (ea : embedding<'a>)  (eb : embedding<'b>)  (er : embedding<'r>)
           (nf : 'na -> 'nb -> tac<'nr>) (nea : NBET.embedding<'na>) (neb : NBET.embedding<'nb>) (ner : NBET.embedding<'nr>)
           : Cfg.primitive_step =
    mk name 3 nunivs (mk_tactic_interpretation_2     f  ea  eb  er)
                     (fun args -> mk_tactic_nbe_interpretation_2 nf nea neb ner (drop nunivs args))

let mktac3 (nunivs:int) (name : string)
           (f : 'a -> 'b -> 'c -> tac<'r>)  (ea : embedding<'a>)  (eb : embedding<'b>)  (ec : embedding<'c>)  (er : embedding<'r>)
           (nf : 'na -> 'nb -> 'nc -> tac<'nr>) (nea : NBET.embedding<'na>) (neb : NBET.embedding<'nb>) (nec : NBET.embedding<'nc>) (ner : NBET.embedding<'nr>)
           : Cfg.primitive_step =
    mk name 4 nunivs (mk_tactic_interpretation_3 f ea eb ec er)
                     (fun args -> mk_tactic_nbe_interpretation_3 nf nea neb nec ner (drop nunivs args))

let mktac4 (nunivs:int) (name : string)
           (f : 'a -> 'b -> 'c -> 'd -> tac<'r>)  (ea : embedding<'a>)  (eb : embedding<'b>)  (ec : embedding<'c>)  (ed : embedding<'d>)  (er : embedding<'r>)
           (nf : 'na -> 'nb -> 'nc -> 'nd -> tac<'nr>) (nea : NBET.embedding<'na>) (neb : NBET.embedding<'nb>) (nec : NBET.embedding<'nc>) (ned : NBET.embedding<'nd>) (ner : NBET.embedding<'nr>)
           : Cfg.primitive_step =
    mk name 5 nunivs (mk_tactic_interpretation_4 f ea eb ec ed er)
                     (fun args -> mk_tactic_nbe_interpretation_4 nf nea neb nec ned ner (drop nunivs args))

let mktac5 (nunivs:int) (name : string)
           (f : 'a -> 'b -> 'c -> 'd -> 'e -> tac<'r>)  (ea : embedding<'a>)  (eb : embedding<'b>)  (ec : embedding<'c>)  (ed : embedding<'d>)  (ee : embedding<'e>)  (er : embedding<'r>)
           (nf : 'na -> 'nb -> 'nc -> 'nd -> 'ne -> tac<'nr>) (nea : NBET.embedding<'na>) (neb : NBET.embedding<'nb>) (nec : NBET.embedding<'nc>) (ned : NBET.embedding<'nd>) (nee : NBET.embedding<'ne>) (ner : NBET.embedding<'nr>)
           : Cfg.primitive_step =
    mk name 6 nunivs (mk_tactic_interpretation_5 f ea eb ec ed ee er)
                     (fun args -> mk_tactic_nbe_interpretation_5 nf nea neb nec ned nee ner (drop nunivs args))

(* Total interpretations *)

let mkt nm arity nunivs interp nbe_interp =
  let nm = E.fstar_tactics_lid' ["Builtins"; nm] in
  { Cfg.name                         = nm
  ; Cfg.arity                        = arity
  ; Cfg.univ_arity                   = nunivs
  ; Cfg.auto_reflect                 = None
  ; Cfg.strong_reduction_ok          = true
  ; Cfg.requires_binder_substitution = false
  ; Cfg.interpretation               = interp
  ; Cfg.interpretation_nbe           = nbe_interp
  }

let mk_total_interpretation_1 (f:'a -> 'r)
                              (ea:embedding<'a>) (er:embedding<'r>)
                              (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_1 ea ncb args) (fun a ->
  let r = f a in
  Some (embed er (Cfg.psc_range psc) r ncb))

let mk_total_interpretation_2 (f:'a -> 'b -> 'r)
                              (ea:embedding<'a>) (eb:embedding<'b>) (er:embedding<'r>)
                              (psc:Cfg.psc) (ncb:norm_cb) (args:args) : option<term> =
  BU.bind_opt (extract_2 ea eb ncb args) (fun (a, b) ->
  let r = f a b in
  Some (embed er (Cfg.psc_range psc) r ncb))

let mk_total_nbe_interpretation_1 (f:'a -> 'r)
                              (ea:NBETerm.embedding<'a>) (er:NBETerm.embedding<'r>)
                              (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_1_nbe ea args) (fun a ->
  let r = f a in
  Some (NBETerm.embed er r))

let mk_total_nbe_interpretation_2 (f:'a -> 'b -> 'r)
                              (ea:NBETerm.embedding<'a>)
                              (eb:NBETerm.embedding<'b>)
                              (er:NBETerm.embedding<'r>)
                              (args:NBETerm.args) : option<NBETerm.t> =
  BU.bind_opt (extract_2_nbe ea eb args) (fun (a, b) ->
  let r = f a b in
  Some (NBETerm.embed er r))

let mktot1 (nunivs:int) (name : string)
           (f : 'a -> 'r)
           (ea : embedding<'a>)
           (er : embedding<'r>)
           (nf : 'na -> 'nr)
           (nea : NBETerm.embedding<'na>)
           (ner : NBETerm.embedding<'nr>)
           : Cfg.primitive_step =
    mkt name 1 nunivs (mk_total_interpretation_1     f  ea  er)
                      (fun args -> mk_total_nbe_interpretation_1 nf nea ner (drop nunivs args))

let mktot2 (nunivs:int) (name : string)
           (f : 'a -> 'b -> 'r)
           (ea : embedding<'a>) (eb:embedding<'b>)
           (er : embedding<'r>)
           (nf : 'na -> 'nb -> 'nr)
           (nea : NBETerm.embedding<'na>) (neb:NBETerm.embedding<'nb>)
           (ner : NBETerm.embedding<'nr>)
           : Cfg.primitive_step =
    mkt name 2 nunivs (mk_total_interpretation_2     f  ea  eb  er)
                      (fun args -> mk_total_nbe_interpretation_2 nf nea neb ner (drop nunivs args))
