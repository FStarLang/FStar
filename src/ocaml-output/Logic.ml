open Prims
let _ = Printf.printf "start\n%!"
type phi = Prims.unit
type psi = Prims.unit
type xi = Prims.unit
let tau: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind FStar_Tactics_Logic.implies_intro
    (fun h  -> Printf.printf "Nooo\n%!";
       FStar_Tactics_Effect.bind FStar_Tactics_Logic.right
         (fun uu___80_16  -> Printf.printf "A\n%!";
            FStar_Tactics_Effect.bind
              (FStar_Tactics_Logic.and_elim
                 (FStar_Reflection_Basic.pack
                    (FStar_Reflection_Data.Tv_Var h)))
              (fun uu___79_18  ->Printf.printf "B\n%!";
                 FStar_Tactics_Effect.bind FStar_Tactics_Logic.implies_intro
                   (fun h1  ->Printf.printf "C\n%!";
                      FStar_Tactics_Effect.bind
                        FStar_Tactics_Logic.implies_intro
                        (fun uu___78_22  ->Printf.printf "D\n%!";
                           FStar_Tactics_Effect.bind
                             (FStar_Tactics_Builtins.apply
                                (fun uu____25  ->Printf.printf "E\n%!";
                                   fun s  -> Printf.printf "F\n%!";
                                     FStar_Tactics_Effect.Success
                                       ((Obj.magic ()), s)))
                             (fun uu___77_33  ->Printf.printf "G\n%!";
                                FStar_Tactics_Effect.bind
                                  (FStar_Tactics_Builtins.exact
                                     (FStar_Tactics_Effect.return
                                        (FStar_Reflection_Basic.pack
                                           (FStar_Reflection_Data.Tv_Var h1))))
                                  (fun uu___76_35  -> Printf.printf "H\n%!";
                                     FStar_Tactics_Builtins.qed)))))))
let _ =
  FStar_Tactics_Native.register_tactic "Logic.__tau" 1
    (fun ps  ->
       fun args  ->
         FStar_Tactics_Interpreter.mk_tactic_interpretation_0 ps
           (FStar_Tactics_Native.from_tactic_0 tau)
           FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit
           (FStar_Ident.lid_of_str "Logic.__tau") args)
