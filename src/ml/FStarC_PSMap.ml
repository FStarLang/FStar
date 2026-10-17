module StringOps =
  struct
    type t = string
    let equal (x:t) (y:t) = x=y
    let compare (x:t) (y:t) = BatString.compare x y
    let hash (x:t) = BatHashtbl.hash x
  end

(* Stdlib's Map rather than BatMap: its [find_opt] does not raise and catch
   [Not_found], which is costly when backtraces are recorded. *)
module StringMap = Map.Make(StringOps)
exception Found

type 'value t = 'value StringMap.t
let empty (_: unit) : 'value t = StringMap.empty
let add (map: 'value t) (key: string) (value: 'value) = StringMap.add key value map
let find_default (map: 'value t) (key: string) (dflt: 'value) =
  match StringMap.find_opt key map with Some v -> v | None -> dflt
let of_list (l: (string * 'value) list) : 'value t =
  List.fold_left (fun acc (k,v) -> add acc k v) (empty ()) l
let try_find (map: 'value t) (key: string) =
  StringMap.find_opt key map
let fold (m:'value t) f a = StringMap.fold f m a
let find_map (m:'value t) f =
  let res = ref None in
  let upd k v =
    let r = f k v in
    if r <> None then (res := r; raise Found) in
  (try StringMap.iter upd m with Found -> ());
  !res
let modify (m: 'value t) (k: string) (upd: 'value option -> 'value) =
  StringMap.update k (fun vopt -> Some (upd vopt)) m

let merge (m1: 'value t) (m2: 'value t) : 'value t =
  fold m1 (fun k v m -> add m k v) m2

let remove (m: 'value t)  (key:string)
  : 'value t = StringMap.remove key m

let keys m = fold m (fun k _ acc -> k::acc) []
let iter (m:'value t) f = StringMap.iter f m
