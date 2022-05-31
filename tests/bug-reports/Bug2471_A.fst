module Bug2471_A

open FStar.List.Tot
open FStar.Tactics

let id_tac (x:'a): Tac 'a = x
let implicit1 (): Tac term = Tv_FVar (pack_fv (id_tac ["a"]))
let explicit1 (): Tac term = pack (Tv_FVar (pack_fv (id_tac ["a"])))

let implicit2 (): Tac term = Tv_Const (id_tac (); C_String "a")
let explicit2 (): Tac term = pack (Tv_Const (id_tac (); C_String "a"))

let implicit3 (): Tac term = (Tv_FVar (pack_fv ["a"]))
let implicit4 (): Tac term = (Tv_Const (id (); C_String "a"))

let _ = run_tactic (fun _ -> let _ = implicit1 () in ())
let _ = run_tactic (fun _ -> let _ = implicit2 () in ())
let _ = run_tactic (fun _ -> let _ = implicit3 () in ())
let _ = run_tactic (fun _ -> let _ = implicit4 () in ())
let _ = run_tactic (fun _ -> let _ = explicit1 () in ())
let _ = run_tactic (fun _ -> let _ = explicit2 () in ())
