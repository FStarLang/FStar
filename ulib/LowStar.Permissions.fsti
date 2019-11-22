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

include Steel.Permissions

(*** Keeping track of permissions *)

/// To keep track of permissions for the resources in program, we define a data structure storing
/// who owns which permission. We call this data structure a "permission map", which is indexed by
/// permission identifiers defined below:
type perm_id = pos

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
  Permission?.r (get_permission_from_pid v_perms pid) >. 0.0R

type live_pid (#a: Type0) (v_perms: perms_rec a) = pid:perm_id{is_live_pid v_perms pid}

val get_snapshot_from_pid: #a: Type0 -> p: perms_rec a -> pid: perm_id -> Tot a

val get_current_max: #a:Type0 -> p:perms_rec a -> perm_id

val is_fully_owned: #a: Type0 -> p: perms_rec a -> GTot bool

let get_perm_kind_from_pid (#a: Type0) (perms: perms_rec a) (pid: perm_id) : GTot permission_kind =
  let permission = get_permission_from_pid perms pid in
  let fully_owned = is_fully_owned perms in
  permission_to_kind permission

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
    Permission?.r (get_permission_from_pid v_perms pid) = 1.0R /\
    is_fully_owned v_perms = fully_owned /\
    pid = get_current_max v_perms
  ))

/// Sharing a particular ``pid`` halves the permission associated with it and returns a new ``perm_id``
/// containing the other half.
noextract
val share_perms: #a: Type0 -> #v: a -> v_perms: value_perms a v -> pid: live_pid v_perms -> Ghost (value_perms a v & perm_id)
  (requires (True)) (ensures (fun (new_v_perms, new_pid) ->
    new_pid <> pid /\
    get_permission_from_pid new_v_perms pid ==
      half_permission (get_permission_from_pid v_perms pid) /\
    get_permission_from_pid new_v_perms new_pid ==
      half_permission (get_permission_from_pid v_perms pid) /\
    ~ (is_live_pid v_perms new_pid) /\
    (forall (pid':perm_id{pid' <> pid /\ pid' <> new_pid}).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    ) /\
    get_current_max new_v_perms > get_current_max v_perms
  ))

/// Sharing a particular ``pid`` halves the permission associated with it and returns a new
/// map containing the other half in the given ``new_pid``
noextract
val share_perms_with_pid:
  #a: Type0 ->
  #v: a ->
  v_perms: value_perms a v ->
  pid: live_pid v_perms ->
  new_pid:perm_id ->
  Ghost (value_perms a v)
  (requires
    pid <> new_pid /\
    new_pid > get_current_max v_perms)
  (ensures (fun new_v_perms ->
    get_permission_from_pid new_v_perms pid ==
      half_permission (get_permission_from_pid v_perms pid) /\
    get_permission_from_pid new_v_perms new_pid ==
      half_permission (get_permission_from_pid v_perms pid)  /\
    (forall (pid':perm_id{pid' <> pid /\ pid' <> new_pid}).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    ) /\
    get_current_max new_v_perms > get_current_max v_perms
  ))


/// Moves a particular ``pid`` zeroes the permission associated with it and returns a new
/// map containing the original permission in the given ``new_pid``
noextract
val move_perms_with_pid:
  #a: Type0 ->
  #v: a ->
  v_perms: value_perms a v ->
  pid: live_pid v_perms ->
  new_pid:perm_id ->
  Ghost (value_perms a v)
  (requires
    pid <> new_pid /\
    new_pid > get_current_max v_perms)
  (ensures (fun new_v_perms ->
    get_permission_from_pid new_v_perms pid == zero_permission /\
    get_permission_from_pid new_v_perms new_pid == get_permission_from_pid v_perms pid /\
    (forall (pid':perm_id{pid' <> pid /\ pid' <> new_pid}).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    ) /\
    get_current_max new_v_perms > get_current_max v_perms
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
  (requires (
    summable_permissions
      (get_permission_from_pid v_perms pid1)
      (get_permission_from_pid v_perms pid2)
  )) (ensures (fun new_v_perms ->
    get_permission_from_pid new_v_perms pid1 ==
      sum_permissions
	(get_permission_from_pid v_perms pid1)
	(get_permission_from_pid v_perms pid2) /\
    get_permission_from_pid new_v_perms pid2 == zero_permission /\
    (forall (pid':perm_id{pid' <> pid1 /\ pid' <> pid2}).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid v_perms pid' == get_permission_from_pid new_v_perms pid'
    ) /\
    get_current_max new_v_perms = get_current_max v_perms
  ))

/// The invariants let us prove a particularly useful lemma: if you have full permission, then you are
/// the only live ``pid``.
val only_one_live_pid_with_full_permission:
  #a: Type0 ->
  #v: a ->
  v_perms: value_perms a v ->
  pid: perm_id ->
  Lemma (requires (get_permission_from_pid v_perms pid == full_permission))
    (ensures (forall (pid':live_pid v_perms). pid == pid'))


/// If a pid is live, then it is smaller than the current max
val lemma_live_pid_smaller_max (#a:Type0) (v_perms:perms_rec a) (pid:live_pid v_perms)
  : Lemma (pid <= get_current_max v_perms)

/// If a pid is live, then it is smaller than the current max
val lemma_greater_max_not_live_pid (#a:Type0) (v_perms:perms_rec a) (pid:perm_id) : Lemma
    (requires pid > get_current_max v_perms)
    (ensures not (is_live_pid v_perms pid))

/// Once you have full permission with a ``pid``, you can change the value of the snapshot associated with it.
/// This ensures that read-only permissions cannot change the value of the snapshot.
val change_snapshot:
  #a: Type0 ->
  #v: a ->
  v_perms: value_perms a v ->
  pid: perm_id ->
  new_snapshot: a ->
  Pure (value_perms a new_snapshot)
  (requires (get_permission_from_pid v_perms pid == full_permission))
  (ensures (fun new_v_perms ->
    (forall (pid':perm_id).{:pattern get_permission_from_pid new_v_perms pid'}
      get_permission_from_pid new_v_perms pid' == get_permission_from_pid v_perms pid' /\
      (pid' <> pid ==>
        get_snapshot_from_pid new_v_perms pid' ==
        get_snapshot_from_pid v_perms pid')
    ) /\
    get_snapshot_from_pid new_v_perms pid == new_snapshot /\
    get_current_max v_perms = get_current_max new_v_perms
  ))
