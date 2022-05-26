open Prims
type 'a metatc = unit -> 'a FStar_Tactics_Result.tc_result
let return : 'a . 'a -> 'a metatc =
  fun uu___ -> (fun x -> Obj.magic (fun uu___ -> x)) uu___
let bind : 'a 'b . 'a metatc -> ('a -> 'b metatc) -> 'b metatc =
  fun f ->
    fun g ->
      fun uu___ ->
        let r = f () in
        match r with
        | FStar_Tactics_Result.Tc_success x -> let uu___1 = g x in uu___1 ()
        | FStar_Tactics_Result.Tc_failure m ->
            FStar_Tactics_Result.Tc_failure m
type ('uuuuu, 'uuuuu1) valid_prop = unit
let (check_prop_validity :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> unit metatc) =
  fun en ->
    fun t ->
      fun uu___ ->
        let errs = FStar_TypeChecker_Rel.query_formula en t in
        if (FStar_Compiler_List.length errs) = Prims.int_zero
        then FStar_Tactics_Result.Tc_success ()
        else FStar_Tactics_Result.Tc_failure ""