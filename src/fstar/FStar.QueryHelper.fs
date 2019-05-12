(* FStar.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)
#light "off"

module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
