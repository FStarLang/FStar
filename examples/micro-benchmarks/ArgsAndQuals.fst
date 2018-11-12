module ArgsAndQuals

(* Seems silly, but this used to complain about an inference failure instead of the
 * obviously wrong arguments. Using the right arguments fails anyway,
 * see Guido's comment on #1486 on July 30 2018,
 * https://github.com/FStarLang/FStar/issues/1486#issuecomment-408958279 *)

val test1 : #a:Type -> #wp1:pure_wp a -> $t1:(unit -> PURE a wp1) -> PURE a wp1
[@(expect_failure [91])]
let test1 #_ #_ #_ t1 = t1 ()
