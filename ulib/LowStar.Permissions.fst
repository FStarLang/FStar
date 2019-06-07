module LowStar.Permissions

module F = FStar.FunctionalExtensionality

open FStar.Real 


type permission = r:real{r >=. 0.0R /\ r <=. 1.0R}

type perm_id = pos

let allows_read (p:permission) : GTot bool =  
  p >. 0.0R

let allows_write (p: permission) : GTot bool =
  p = 1.0R


noeq type perms_rec (a: Type0) = {
  current_max : perm_id;
  owner: perm_id;
  perm_map    : F.restricted_t perm_id (fun (x:perm_id) -> permission & a)
}

let get_permission_from_pid (#a: Type0) (p: perms_rec a) (pid: perm_id) : GTot permission =
  let (perm, _) = p.perm_map pid in
  perm

let is_live_pid (#a: Type0) (v_perms: perms_rec a) (pid:perm_id) : GTot bool =
  get_permission_from_pid v_perms pid >. 0.0R


type live_pid (#a: Type0) (v_perms: perms_rec a) = pid:perm_id{is_live_pid v_perms pid}

let get_snapshot_from_pid (#a: Type0) (p: perms_rec a) (pid: perm_id) : GTot a =
  let (_, snap) = p.perm_map pid in snap



let rec sum_until (#a: Type0) (f:perm_id -> permission & a) (n:nat) : GTot real =
  if n = 0 then 0.0R
  else 
    let (x, _) = f n in x +. sum_until f (n - 1)

let value_perms (a: Type0) = p:perms_rec a{
  // Permissions are null above currently split objects
  (forall (n:perm_id). n > p.current_max ==> get_permission_from_pid p n = 0.R) /\
  // The sum of permissions is the number of splits up till now
  (sum_until p.perm_map p.current_max = 1.0R) /\ 
  // All permissions have the same snapshot
  (forall (pid1 pid2: perm_id). let snap1 = get_snapshot_from_pid p pid1 in let snap2 = get_snapshot_from_pid p pid2 in
     snap1 == snap2
  )
}

let new_value_perms (#a: Type0) (init: a) : Ghost (value_perms a)
  (requires (True)) (ensures (fun v_perms -> 
    (forall (pid:perm_id).{:pattern get_snapshot_from_pid v_perms pid}
      get_snapshot_from_pid v_perms pid == init
    )
  ))
  =
  let f:F.restricted_t perm_id (fun (x:perm_id) -> permission & a) = 
     F.on_dom perm_id (fun (x:perm_id) -> if x = 1 then 
         ((1.0R <: permission), init) 
       else 
         ((0.0R <: permission), init)
     )   
  in
  { current_max = 1; perm_map = f; owner = 1 }

type permission_kind =
  | DEAD 
  | RO
  | RW
  | FULL

let get_perm_kind_from_pid (#a: Type0) (perms: value_perms a) (pid: perm_id) : GTot permission_kind = 
  let permission = get_permission_from_pid perms pid in
  if permission = 0.0R then
    DEAD
  else if permission <. 1.0R then 
    RO
  else if perms.owner <> pid then
    RW
  else 
    FULL

let rec same_prefix_same_sum_until(#a: Type0) (p1 p2:perm_id -> permission & a) (n:nat) : Lemma
  (requires forall (x:perm_id). x <= n ==> begin
    let (perm1, _) = p1 x in let (perm2, _) = p2 x in
    perm1 = perm2
  end)
  (ensures sum_until p1 n = sum_until p2 n)
  = if n = 0 then () else same_prefix_same_sum_until p1 p2 (n-1)

let rec sum_until_change 
  (#a: Type0) 
  (p1 p2:perm_id -> permission & a)
  (n:nat)
  (i:perm_id)
  (v:permission) 
  : Lemma (requires (forall (x:perm_id). 
    let (v1, _) = p1 x in let (v2, _) = p2 x in
    (x <= n /\ x <> i) ==> v1 = v2) /\
    i <= n /\
    begin let (v', _) = p2 i in v' = v end
  ) (ensures (let (v', _) = p1 i in sum_until p2 n = sum_until p1 n +. v -. v'))
  = 
    if n = i then same_prefix_same_sum_until p1 p2 (n-1)
    else sum_until_change p1 p2 (n-1) i v

let share_perms (#a: Type0) (v_perms: value_perms a) (pid: live_pid v_perms) : Ghost (value_perms a & perm_id)  
  (requires (True)) (ensures (fun (new_v_perms, new_pid) -> 
    new_pid <> pid /\
    get_permission_from_pid new_v_perms pid = get_permission_from_pid v_perms pid /. 2.0R /\
    get_permission_from_pid new_v_perms new_pid = get_permission_from_pid v_perms pid /. 2.0R /\
    (forall (pid':perm_id{pid' <> pid /\ pid' <> new_pid}).{:pattern get_permission_from_pid new_v_perms pid'} 
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    ) /\
    (forall (pid':perm_id).{:pattern get_snapshot_from_pid new_v_perms pid'}
      get_snapshot_from_pid v_perms pid' == get_snapshot_from_pid new_v_perms pid'
    )    
  ))
  =
  let current_max' = v_perms.current_max + 1 in
  let (p, _) = v_perms.perm_map pid in
  let perm_map1' = F.on_dom perm_id (fun (x:perm_id) ->
    let (old_p, old_snap) = v_perms.perm_map x in
    if x = pid then ((p /. 2.0R <: permission), old_snap) else (old_p, old_snap))
  in
  sum_until_change v_perms.perm_map perm_map1' v_perms.current_max pid (p /. 2.0R);
  let perm_map2' = F.on_dom perm_id (fun (x:perm_id) ->
    let (old_p, old_snap) = perm_map1' x in
    if x = current_max' then ((p /. 2.0R <: permission), old_snap) else (old_p, old_snap))
  in
  sum_until_change perm_map1' perm_map2' current_max' current_max' (p /. 2.0R);
  let v_perms' : perms_rec a =
    { v_perms with 
      current_max = current_max'; 
      perm_map = perm_map2'
    }
  in
  (v_perms', current_max')


let rec sum_greater_than_subterm (#a: Type0) (f:perm_id -> permission & a) (n:nat) (pid1:perm_id)
  : Lemma (ensures (
    if n < pid1 then sum_until f n >=. 0.0R else
    sum_until f n >=. (let (x, _) = f pid1 in x)
  )) =
  if n = 0 then () else sum_greater_than_subterm f (n-1) pid1

let rec sum_greater_than_subterms (#a: Type0) (f:perm_id -> permission & a) (n:nat) (pid1: perm_id)
  (pid2:perm_id{pid1 <> pid2})
  : Lemma (ensures (
    let (pid1, pid2) = if pid1 < pid2 then (pid1, pid2) else (pid2, pid1) in
    if n < pid1 then sum_until f n >=. 0.0R else
    if n < pid2 then sum_until f n >=. (let (x, _) = f pid1 in x) else
    sum_until f n >=. (let (x, _) = f pid1 in x) +. (let (x, _) = f pid2 in x)
  )) =
  if n = 0 then () else sum_greater_than_subterms f (n-1) pid1 pid2

let merge_perms
  (#a: Type0)
  (v_perms: value_perms a)
  (pid1: live_pid v_perms)
  (pid2: live_pid v_perms{pid1 <> pid2}) 
  : Ghost (value_perms a & perm_id) 
  (requires (True)) (ensures (fun (new_v_perms, new_pid) -> 
    new_pid = pid1 /\
    get_permission_from_pid new_v_perms new_pid = 
      get_permission_from_pid v_perms pid1 +. get_permission_from_pid v_perms pid2 /\
    get_permission_from_pid new_v_perms pid2 = 0.0R /\
    (forall (pid':perm_id{pid' <> pid1 /\ pid' <> pid2}).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    ) /\
    (forall (pid':(live_pid v_perms)).{:pattern get_snapshot_from_pid new_v_perms pid'}
      get_snapshot_from_pid v_perms pid' == get_snapshot_from_pid new_v_perms pid'
    )
  ))
  = 
  let (p1, snap1) = v_perms.perm_map pid1 in
  let (p2, snap2) = v_perms.perm_map pid2 in
  sum_greater_than_subterms v_perms.perm_map v_perms.current_max pid1 pid2;
  let p_sum : permission = p1 +. p2 in
  let perm_map1' = F.on_dom perm_id (fun (x:perm_id) ->
    assert(sum_until v_perms.perm_map v_perms.current_max = 1.0R);
    if x = pid1 then ((p1 +. p2 <: permission), snap1)
    else v_perms.perm_map x
  ) in
  sum_until_change v_perms.perm_map perm_map1' v_perms.current_max pid1 p_sum;
  let perm_map2' = F.on_dom perm_id (fun (x:perm_id) -> 
    if x = pid2 then ((0.0R <: permission), snap2) else perm_map1' x
  ) in
  sum_until_change perm_map1' perm_map2' v_perms.current_max pid2 0.0R;
  let v_perms': perms_rec a =
    {  v_perms with perm_map = perm_map2' } in
  (v_perms', pid1)

let change_snapshot (#a: Type0) (v_perms: value_perms a) (new_snapshot: a) 
  : Ghost (value_perms a)
  (requires (True)) (ensures (fun new_v_perms -> 
    (forall (pid:perm_id).{:pattern get_permission_from_pid new_v_perms pid}
      get_permission_from_pid new_v_perms pid = get_permission_from_pid v_perms pid
    ) /\
    (forall (pid:(live_pid v_perms)). {:pattern get_snapshot_from_pid new_v_perms pid}
      get_snapshot_from_pid new_v_perms pid == new_snapshot
    )
  ))
  =
  let out = { v_perms with 
    perm_map = F.on_dom perm_id (fun (x:perm_id) ->
      let (p, _) = v_perms.perm_map x in (p, new_snapshot)
    )
  } in
  same_prefix_same_sum_until v_perms.perm_map out.perm_map v_perms.current_max;
  out

