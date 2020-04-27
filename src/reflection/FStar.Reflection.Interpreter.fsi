#light "off"
module FStar.Reflection.Interpreter

open FStar.Ident
open FStar.List
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.TypeChecker.Env
open FStar.Reflection.Basic
open FStar.Reflection.Data

module Cfg   = FStar.TypeChecker.Cfg

val reflection_primops : list<Cfg.primitive_step>
