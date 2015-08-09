
type env =
{env_root : string list; env_map : string Support.Microsoft.FStar.Util.smap}

let is_Mkenv = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenv"))

let root = (fun ( env ) -> env.env_root)

let create = (fun ( nm ) -> (let _70_28466 = (Support.Microsoft.FStar.Util.smap_create 0)
in {env_root = nm; env_map = _70_28466}))

let push = (fun ( env ) ( x ) ( pp ) -> (let m = env.env_map
in (let _64_10 = (Support.Microsoft.FStar.Util.smap_add m x pp)
in (let _64_12 = env
in {env_root = _64_12.env_root; env_map = m}))))

let resolve = (fun ( env ) ( x ) -> (match ((Support.Microsoft.FStar.Util.smap_try_find env.env_map x)) with
| None -> begin
(Support.All.failwith "unknown-internal-name")
end
| Some (x) -> begin
x
end))




