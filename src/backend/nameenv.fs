(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.NameEnv

// At some point, that nameenv should be responsible of printing
// the shortest path to a lident. Currently, only a map from
// internal names to external names.
type env = {
    env_root : list<string>;
    env_map  : Map<string, string>;
}

let root (env : env) =
    env.env_root

let create (nm : list<string>) : env=
    { env_root = nm; env_map = Map.empty; }

let push (env : env) (x : string) (pp : string) =
    if Map.containsKey x env.env_map then
        failwith "duplicated-internal-name"
    { env with env_map = Map.add x pp env.env_map; }

let resolve (env : env) (x : string) =
    match Map.tryFind x env.env_map with
    | None   -> failwith "unknown-internal-name"
    | Some x -> x
