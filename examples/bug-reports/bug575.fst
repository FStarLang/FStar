module Bug575
#set-options "--__temp_no_proj Bug575 --lax"

type relation = int -> Type0

(* // This works *)
(* noeq type multi0 (r:int -> Type0) : int -> Type = *)
(* | Multi_step0 : x:int -> r x -> multi0 r x *)

// Needs the --__temp_no_proj
noeq type multi (r:relation) : int -> Type0 =
| Multi_step : x:int -> r x -> multi r x

// Because the dependent pattern matching here goes wrong
//    Probably because the abbreviation isn't unfolded at the right time
#set-options "--debug Bug575 --debug_level Rel --debug_level RelCheck"
let is_Multi_step (r:relation) (x:int) (projectee : multi r x) =
  match projectee with
  | Multi_step y ry  -> true

(* Attempting 14449 *)
(* Flex-flex patterns: intersected r, x, projectee, y and r, x, projectee, y; got r, x, projectee, y *)
(* 	k1=(r:relation -> x:int -> projectee:(multi r@1 x@0) -> y:((fun r x projectee -> int) r@2 x@1 projectee@0) -> Type) *)
(* 	k2=(r:relation -> x:int -> projectee:(multi r@1 x@0) -> Tot (?20191 r@2 x@1 projectee@0)) *)
(* Unexpected error *)
(* k=(?20191 r x projectee) *)
(* xs=r, x, projectee *)
(* args=r x projectee y *)
(* Ill-formed substitutution *)
(*    at FStar.TypeChecker.Rel.subst_k@1819(syntax`2 k, FSharpList`1 xs, FSharpList`1 args) in C:\Users\nswamy\workspace\FStar\src\typechecker\FStar.TypeChecker.Rel.fs:line 1828 *)
(*    at FStar.TypeChecker.Rel.solve_both_pats@1798(env env, worklist wl, prob orig, worklist wl@1798-1, cell`1 u1, syntax`2 k1, FSharpList`1 xs, FSharpList`1 args1, cell`1 u2, syntax`2 k2, FSharpList`1 ys, FSharpList`1 args2, range r) in C:\Users\nswamy\workspace\FStar\src\typechecker\FStar.TypeChecker.Rel.fs:line 1836 *)
(*    at FStar.TypeChecker.Rel.solve_and_commit(env env, worklist probs, FSharpFunc`2 err) in C:\Users\nswamy\workspace\FStar\src\typechecker\FStar.TypeChecker.Rel.fs:line 2379 *)
(*    at FStar.TypeChecker.Rel.try_teq(env env, syntax`2 t1, syntax`2 t2) in C:\Users\nswamy\workspace\FStar\src\typechecker\FStar.TypeChecker.Rel.fs:line 2408 *)
(*    at FStar.TypeChecker.Util.check_and_ascribe(env env, syntax`2 e, syntax`2 t1, syntax`2 t2) in C:\Users\nswamy\workspace\FStar\src\typechecker\FStar.TypeChecker.Util.fs:line 1214 *)
(*    at FStar.TypeChecker.TcTerm.value_check_expected_typ$cont@126(env env, syntax`2 e, guard_t guard, lcomp lc, syntax`2 t, FSharpOption`1 matchValue, Unit unitVar) in C:\Users\nswamy\workspace\FStar\src\typechecker\FStar.TypeChecker.TcTerm.fs:line 130 *)

