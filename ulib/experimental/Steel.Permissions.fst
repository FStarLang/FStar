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

module Steel.Permissions

open FStar.Real


(**** Permissions as real numbers *)

/// A permission is a real number between 0 and 1.
[@@erasable]
noeq type permission =
  | Permission:  (r:real{r >=. zero /\ r <=. one}) -> permission

let zero_permission : permission = Permission 0.0R
let full_permission : permission = Permission 1.0R

inline_for_extraction
noeq type with_perm (a: Type) = {
  wp_v: a;
  wp_perm: permission;
}

/// A permission value of 0 means that the resource is not live. It is live, and can be read, as long as the permission is
/// strictly positive.
let allows_read (p: permission) : GTot bool =
  Permission?.r p >. 0.0R

/// A full permission (of value 1) is required for writing to the resource.
let allows_write (p: permission) : GTot bool =
  Permission?.r p = 1.0R

/// The common way to share a permission is to halve its value.
let half_permission (p: permission) : GTot (permission) =
  Permission ((Permission?.r p) /. two)

/// When merging resources, you have to sum the permissions.
let summable_permissions (p1: permission) (p2: permission)
  : GTot bool =
   Permission?.r p1 +. Permission?.r p2 <=. 1.0R

let sum_permissions (p1: permission) (p2: permission{summable_permissions p1 p2})
  : GTot (permission) =
  Permission (Permission?.r p1 +.  Permission?.r p2)

let lesser_equal_permission (p1 p2:permission) : GTot bool =
  (Permission?.r p1 <=.  Permission?.r p2)

let sub_permissions (p1: permission) (p2: permission{p2 `lesser_equal_permission` p1})
  : GTot permission =
  Permission (Permission?.r p1 -.  Permission?.r p2)

/// On top of the permission as a number, we define a view defining what you can actually do with the resource given its
/// permission and a flag signalling if you are its owner.
type permission_kind =
  | DEAD (* No access *)
  | RO (* Read access *)
  | RW (* Read-write access *)

/// Translates the permission and the ownership flag into a permission kind.
let permission_to_kind (p: permission) : GTot permission_kind =
  if Permission?.r p = 0.0R then
    DEAD
  else if Permission?.r p <. 1.0R then
    RO
  else
    RW
