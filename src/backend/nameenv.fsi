(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.NameEnv

type env

val create : list<string> -> env

val push : env -> string -> string -> env

val resolve : env -> string -> string
