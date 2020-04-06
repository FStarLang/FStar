#light "off"
module FStar.Tactics.InterpFuns

(* This module is awful, don't even look at it please. *)

open FStar
open FStar.All

open FStar.Syntax.Embeddings
open FStar.Tactics.Monad

module Cfg   = FStar.TypeChecker.Cfg
module NBET  = FStar.TypeChecker.NBETerm

(* These functions are suboptimal, since they need to take embeddings for both
 * the interpreter AND the NBE evaluator. Attempting to coallesce them
 * is not easy, since we have some parametric e_any embeddings of differing types
 * (Syntax.embedding<term> vs NBET.embedding<NBET.t>). So we pass both of them.
 * We also need to pass in two versions of the underlying primitive, since they
 * will be instantiated differently (again term vs NBET.t). Such is life
 * without higher-order polymorphism. *)

val mktac1 :
    int ->
    string ->
    ('a -> tac<'r>) ->
    embedding<'a> ->
    embedding<'r> ->
    ('na -> tac<'nr>) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step

val mktac2 :
    int ->
    string ->
    ('a -> 'b -> tac<'r>) ->
    embedding<'a> ->
    embedding<'b> ->
    embedding<'r> ->
    ('na -> 'nb -> tac<'nr>) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nb> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step

val mktac3 :
    int ->
    string ->
    ('a -> 'b -> 'c -> tac<'r>) ->
    embedding<'a> ->
    embedding<'b> ->
    embedding<'c> ->
    embedding<'r> ->
    ('na -> 'nb -> 'nc -> tac<'nr>) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nb> ->
    NBET.embedding<'nc> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step

val mktac4 :
    int ->
    string ->
    ('a -> 'b -> 'c -> 'd -> tac<'r>) ->
    embedding<'a> ->
    embedding<'b> ->
    embedding<'c> ->
    embedding<'d> ->
    embedding<'r> ->
    ('na -> 'nb -> 'nc -> 'nd -> tac<'nr>) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nb> ->
    NBET.embedding<'nc> ->
    NBET.embedding<'nd> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step

val mktac5 :
    int ->
    string ->
    ('a -> 'b -> 'c -> 'd -> 'e -> tac<'r>) ->
    embedding<'a> ->
    embedding<'b> ->
    embedding<'c> ->
    embedding<'d> ->
    embedding<'e> ->
    embedding<'r> ->
    ('na -> 'nb -> 'nc -> 'nd -> 'ne -> tac<'nr>) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nb> ->
    NBET.embedding<'nc> ->
    NBET.embedding<'nd> ->
    NBET.embedding<'ne> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step

val mktot1 :
    int ->
    string ->
    ('a -> 'r) ->
    embedding<'a> ->
    embedding<'r> ->
    ('na -> 'nr) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step

val mktot1_psc :
    int ->
    string ->
    (Cfg.psc -> 'a -> 'r) ->
    embedding<'a> ->
    embedding<'r> ->
    (Cfg.psc -> 'na -> 'nr) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step

val mktot2 :
    int ->
    string ->
    ('a -> 'b -> 'r) ->
    embedding<'a> ->
    embedding<'b> ->
    embedding<'r> ->
    ('na -> 'nb -> 'nr) ->
    NBET.embedding<'na> ->
    NBET.embedding<'nb> ->
    NBET.embedding<'nr> ->
    Cfg.primitive_step
