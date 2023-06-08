module Pulse.Typing.Env
open Pulse.Syntax.Base
module RT = FStar.Reflection.Typing

let eqn = term & term & term
let binding = either term eqn
let env_bindings = list (var & binding)
let context = FStar.Sealed.Inhabited.sealed #(list string) []
noeq
type env = {
  f: RT.fstar_top_env;
  g: env_bindings;
  ctxt: context
}
