module PulseSyntaxExtension.Desugar

open FStar.Compiler.Effect
module Sugar = PulseSyntaxExtension.Sugar
module SW = PulseSyntaxExtension.SyntaxWrapper
module TcEnv = FStar.TypeChecker.Env
module R = FStar.Compiler.Range

// An error can be "None", which means all relevant
// errors were already logged via the error API.
type error = option (string & R.range)

let err a = nat -> either a error & nat

let env_t : Type0 = PulseSyntaxExtension.Env.env_t

val desugar_decl (env:env_t)
                 (p:Sugar.decl)
  : err SW.decl

let name = list string

val initialize_env (env:TcEnv.env)
                   (open_namespaces: list name)
                   (module_abbrevs: list (string & name))
  : env_t
