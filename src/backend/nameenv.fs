(* -------------------------------------------------------------------- *)
#light "off"

module Microsoft.FStar.Backends.NameEnv
open Microsoft.FStar.Util

// At some point, that nameenv should be responsible of printing
// the shortest path to a lident. Currently, only a map from
// internal names to external names.
type env = {
    env_root : list<string>;
    env_map  : smap<string>;
}

let root (env : env) =
    env.env_root

let create (nm : list<string>) : env=
    { env_root = nm; env_map = smap_create(0); }

let push (env : env) (x : string) (pp : string) =
(*
    if Map.containsKey x env.env_map then
        failwith "duplicated-internal-name"
    else
*)
    let m = env.env_map in
    smap_add m x pp;
    { env with env_map = m}

let resolve (env : env) (x : string) =
    match smap_try_find env.env_map x with
    | None   -> failwith "unknown-internal-name"
    | Some x -> x
