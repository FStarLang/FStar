open Prims
let tau1: Prims.unit FStar_Tactics.tactic =
  FStar_Tactics.bind (FStar_Tactics.prune "")
    (fun uu___82_22  ->
       FStar_Tactics.bind FStar_Tactics.split
         (fun uu___81_27  ->
            FStar_Tactics.bind (FStar_Tactics.addns "FStar.List")
              (fun uu___80_36  ->
                 FStar_Tactics.bind (FStar_Tactics.addns "Prims")
                   (fun uu___79_45  ->
                      FStar_Tactics.bind (FStar_Tactics.smt ())
                        (fun uu___78_54  ->
                           FStar_Tactics.bind (FStar_Tactics.addns "Prims")
                             (fun uu___77_63  ->
                                FStar_Tactics.bind FStar_Tactics.cur_goal
                                  (fun g  ->
                                     match g with
                                     | (uu____74,t) ->
                                         FStar_Tactics.bind
                                           (FStar_Tactics.smt ())
                                           (fun uu___76_84  ->
                                              Printf.printf "Running native tactic";
                                              FStar_Tactics.return ()))))))))

(* handwritten invocation *)
let _ = FStar_Tactics_Native.register_tactic "NativeArith.__tau1" 1
    (fun ps args ->
        FStar_Tactics_Interpreter.mk_tactic_interpretation_0
            ps
            (FStar_Tactics_Native.from_tactic_0 tau1)
            FStar_Reflection_Basic.embed_unit
            FStar_TypeChecker_Common.t_unit
            (FStar_Ident.lid_of_str "NativeArith.__tau1")
            args)