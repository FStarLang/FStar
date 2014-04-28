(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.NameEnv

// At some point, that nameenv should be responsible of printing
// the shortest path to a lident. Currently, only a map from
// internal names to external names.
type env = Env of Map<string, string>

let create (nm : list<string>) : env=
    Env Map.empty

let push (Env env : env) (x : string) (pp : string) =
    if Map.containsKey x env then
        failwith "duplicated-internal-name"
    Env (Map.add x pp env)

let resolve (Env env : env) (x : string) =
    match Map.tryFind x env with
    | None   -> failwith "unknown-internal-name"
    | Some x -> x
