(*
   Copyright 2020 Microsoft Research

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

module PulseCore.FractionalPermission

include FStar.Real

/// This module defines fractional permissions, to be used with Steel references

/// A fractional permission is a real value between 0 (excluded) and 1.
/// 1 represents full ownership, while any fraction corresponds to a shared
/// permission.
///
/// We do not in fact restrict to <= 1 here, so there are no additional constraints
/// when writing something like `p1+p2`, but every library does in fact limit
/// permissions to 1.0R.
///
/// Note: it's important to use a literal 0.0R to enable normalizer simplifications
/// to kick in. See Pulse PR #83 and F* PR #3305.
[@@ erasable]
type perm : Type0 = r:real { r >. 0.0R }
