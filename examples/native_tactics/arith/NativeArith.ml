open Prims
let tau1: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.prune "")
    (fun uu___100_19  ->
       FStar_Tactics_Effect.bind FStar_Tactics_Logic.split
         (fun uu___99_28  ->
            FStar_Tactics_Effect.bind
              (FStar_Tactics_Builtins.addns "FStar.List")
              (fun uu___98_37  ->
                 FStar_Tactics_Effect.bind
                   (FStar_Tactics_Builtins.addns "Prims")
                   (fun uu___97_46  ->
                      FStar_Tactics_Effect.bind
                        (FStar_Tactics_Builtins.smt)
                        (fun uu___96_55  ->
                           FStar_Tactics_Effect.bind
                             (FStar_Tactics_Builtins.addns "Prims")
                             (fun uu___95_64  ->
                                FStar_Tactics_Effect.bind
                                  (FStar_Tactics_Builtins.smt)
                                  (fun uu___94_73  ->
                                     FStar_Tactics_Effect.return ())))))))
let _ =
  FStar_Tactics_Native.register_tactic "NativeArith.__tau1" 1
    (fun ps  ->
       fun args  ->
         FStar_Tactics_Interpreter.mk_tactic_interpretation_0 ps
           (FStar_Tactics_Native.from_tactic_0 tau1)
           FStar_Reflection_Basic.embed_unit FStar_TypeChecker_Common.t_unit
           (FStar_Ident.lid_of_str "NativeArith.__tau1") args)
