module OvlInclude
open OvlInclAll

(* An [open] of a module that [include]s others has to contribute all the
   names it re-exports, not just the first one the include walk reaches.
   [find_in_module_with_includes] returned on that first hit, so this [open]
   offered a single candidate and overloading never got to choose: [f] was
   whatever the last [include] in OvlInclAll happened to name, regardless of
   the argument. See #4460. *)

(* 1. The report. Reached through the include, [OvlInt.f] is the candidate
   an [int] argument selects, even though [OvlBool.f] is the one plain
   scope order finds first. *)
let use_int (x:int) : int = f x

(* 2. The other direction, so this cannot be passed by always preferring the
   deeper include: a [bool] argument still selects [OvlBool.f]. *)
let use_bool (x:bool) : bool = f x

(* 3. Nothing discriminates, so the scope-order answer stands, and through an
   include that means the last one: [OvlBool.mk]. *)
let primary_kept : OvlBool.t = mk true
