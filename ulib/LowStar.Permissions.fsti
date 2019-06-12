(*
   Copyright 2008-2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

///  Permissions allow Low* code to make the difference between read-only and mutable resources.
module LowStar.Permissions

module F = FStar.FunctionalExtensionality
open FStar.Real

(**** Permissions as real numbers *)

/// A permission is a real number between 0 and 1. It is not meant ot be extracted, and as such should always be handled
/// through a ``Ghost`` type.
type permission = r:real{r >=. 0.0R /\ r <=. 1.0R}


/// A permission value of 0 means that the resource is not live. It is live, and can be read, as long as the permission is
/// strictly positive.
let allows_read (p: permission) : Tot bool =
  p >. 0.0R

/// A full permission (of value 1) is required for writing to the resource.
let allows_write (p: permission) : Tot bool =
  p = 1.0R

/// The common way to share a permission is to halve its value.
let half_permission (p: permission) : Tot (permission) =
  p /. 2.0R

/// When merging resources, you have to sum the permissions.
let summable_permissions (p1: permission) (p2: permission)
  : Tot bool =
   p1 +. p2 <=. 1.0R

let sum_permissions (p1: permission) (p2: permission{p1 +. p2 <=. 1.0R})
  : Tot (permission) =
  (p1 +.  p2)

/// On top of the permission as a number, we define a view defining what you can actually do with the resource given its
/// permission and a flag signalling if you are its owner.
type permission_kind =
  | DEAD (* No access *)
  | RO (* Read access *)
  | RW (* Read-write access *)
  | FULL (* Read-write access and deallocation *)

/// Translates the permission and the ownership flag into a permission kind.
let permission_to_kind (p: permission) (is_fully_owned: bool) : permission_kind =
  if p = 0.0R then
    DEAD
  else if p <. 1.0R then
    RO
  else if not is_fully_owned then
    RW
  else
    FULL

(*** Keeping track of permissions *)

/// To keep track of permissions for the resources in program, we define a data structure storing
/// who owns which permission. We call this data structure a "permission map", which is indexed by
/// permission identifiers defined below:
val perm_id: eqtype

let disjoint_pid (pid1 pid2: Ghost.erased perm_id) : GTot bool =
  Ghost.reveal pid1 <> Ghost.reveal pid2

let same_pid (pid1 pid2: Ghost.erased perm_id) : GTot bool =
  Ghost.reveal pid1 = Ghost.reveal pid2

/// Here is the permission map. It stores three informations about each permission id ``pid``:
///  * the permission owned by the ``pid``;
///  * whether the ``pid` owns the resource or not;
///  * each ``pid``contains a snapshot of the value of the resource
val perms_rec (a: Type0) : Type0


/// Next are getter methods for each of these pieces of information

val get_permission_from_pid: #a: Type0 -> p:perms_rec a -> pid:perm_id -> GTot permission

let is_live_pid (#a: Type0) (v_perms: perms_rec a) (pid:perm_id) : GTot bool =
  get_permission_from_pid v_perms pid >. 0.0R

type live_pid (#a: Type0) (v_perms: perms_rec a) = pid:perm_id{is_live_pid v_perms pid}

val get_snapshot_from_pid: #a: Type0 -> p: perms_rec a -> pid: perm_id -> GTot a

val is_fully_owned: #a: Type0 -> p: perms_rec a -> GTot bool

let get_perm_kind_from_pid (#a: Type0) (perms: perms_rec a) (pid: perm_id) : GTot permission_kind =
  let permission = get_permission_from_pid perms pid in
  let fully_owned = is_fully_owned perms in
  permission_to_kind permission fully_owned

/// Finally, the permission map has to be "synchronized" with an external value to ensure the unicity of the
/// live value of the resource.
type value_perms (a: Type0) (v: a) = p:perms_rec a{forall (pid:live_pid p). get_snapshot_from_pid p pid == v}

(*** Interacting with permissions *)

/// Permission maps can only be created and changed through a narrow API that is compatible with
/// the meaning associated with permissions.

/// A new value perms is created with a single ``pid`` who has full permission and ownership of the resource.
/// You also have to provide the initial value for the snapshot.
val new_value_perms: #a: Type0 -> init: a -> fully_owned: bool -> Ghost (value_perms a init & perm_id)
  (requires (True)) (ensures (fun (v_perms, pid) ->
    get_permission_from_pid v_perms pid = 1.0R /\
    is_fully_owned v_perms = fully_owned
  ))

/// Sharing a particular ``pid`` halves the permission associated with it and returns a new ``perm_id``
/// containing the other half.
val share_perms: #a: Type0 -> #v: a -> v_perms: value_perms a v -> pid: live_pid v_perms -> Ghost (value_perms a v & perm_id)
  (requires (True)) (ensures (fun (new_v_perms, new_pid) ->
    new_pid <> pid /\
    get_permission_from_pid new_v_perms pid = get_permission_from_pid v_perms pid /. 2.0R /\
    get_permission_from_pid new_v_perms new_pid = get_permission_from_pid v_perms pid /. 2.0R /\
    (forall (pid':perm_id{pid' <> pid /\ pid' <> new_pid}).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    )
  ))


/// When merginin two ``pid``, the first one will receive the sum of both permissions while the second
/// ``pid`` will be deactivated with a zeroed permission.
val merge_perms:
  #a: Type0 ->
  #v: a ->
  v_perms: value_perms a v ->
  pid1: live_pid v_perms ->
  pid2: live_pid v_perms{pid1 <> pid2}
  -> Ghost (value_perms a v)
  (requires (True)) (ensures (fun new_v_perms ->
    get_permission_from_pid new_v_perms pid1 =
      get_permission_from_pid v_perms pid1 +. get_permission_from_pid v_perms pid2 /\
    get_permission_from_pid new_v_perms pid2 = 0.0R /\
    (forall (pid':perm_id{pid' <> pid1 /\ pid' <> pid2}).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    )
  ))

/// The invariants let us prove a particularly useful lemma: if you have full permission, then you are
/// the only live ``pid``.
val only_one_live_pid_with_full_permission:
  #a: Type0 ->
  #v: a ->
  v_perms: value_perms a v ->
  pid: perm_id ->
  Lemma (requires (get_permission_from_pid v_perms pid == 1.0R))
    (ensures (forall (pid':live_pid v_perms). pid == pid'))




/// Once you have full permission with a ``pid``, you can change the value of the snapshot associated with it.
/// This ensures that read-only permissions cannot change the value of the snapshot.
val change_snapshot:
  #a: Type0 ->
  #v: a ->
  v_perms: value_perms a v ->
  pid: perm_id ->
  new_snapshot: a ->
  Ghost (value_perms a new_snapshot)
  (requires (get_permission_from_pid v_perms pid == 1.0R))
  (ensures (fun new_v_perms ->
    (forall (pid:perm_id).{:pattern get_permission_from_pid new_v_perms pid}
      get_permission_from_pid new_v_perms pid = get_permission_from_pid v_perms pid
    )
  ))
