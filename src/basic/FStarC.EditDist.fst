module FStarC.EditDist


let edit_distance (s1 s2 : string) : int =
  let cache : IMap.t (IMap.t int) = IMap.create 10 in
  let lookup (i : int) (j : int) : option int =
    match IMap.try_find cache i with
    | Some m -> IMap.try_find m j
    | None -> None
  in
  let set (i : int) (j : int) (d : int) : unit =
    let m = match IMap.try_find cache i with
      | Some m -> m
      | None -> IMap.create 10
    in
    IMap.add m j d;
    IMap.add cache i m
  in
  let l1 = String.length s1 in
  let l2 = String.length s2 in
  let rec go (i1 i2 : int) : int =
    if i1 = l1 then l2 - i2
    else if i2 = l2 then l1 - i1
    else match lookup i1 i2 with
    | Some d -> d
    | None ->
      let d =
        if String.get s1 i1 = String.get s2 i2 then
          go (i1 + 1) (i2 + 1)
        else
          let d1 = go (i1 + 1) i2 in
          let d2 = go i1 (i2 + 1) in
          let d3 = go (i1 + 1) (i2 + 1) in
          min (min d1 d2) d3 + 1
      in
      set i1 i2 d;
      d
  in
  go 0 0
