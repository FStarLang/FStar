open Prims
let app:
  Prims.unit FStar_Tactics_Effect.tactic ->
    Prims.unit FStar_Tactics_Effect.tactic
  = fun t  -> FStar_Tactics_Builtins.seq FStar_Tactics_Derived.idtac t
let _ =
  FStar_Tactics_Native.register_tactic "Bug1154_tactic.__app" 2
    (fun ps  ->
       fun args  ->
         FStar_Tactics_Interpreter.mk_tactic_interpretation_1 ps
           (FStar_Tactics_Native.from_tactic_1 app)
           (fun x -> fun () -> (FStar_Tactics_Builtins.from_tac_0 (FStar_Tactics_Interpreter.unembed_tactic_0
            FStar_Syntax_Embeddings.unembed_unit x)))
           FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit
           (FStar_Ident.lid_of_str "Bug1154_tactic.__app") args)