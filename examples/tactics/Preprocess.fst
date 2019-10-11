module Preprocess

open FStar.Tactics

let rec visit (ff : term -> Tac term) (t : term) : Tac term =
    let tv = inspect t in
    let tv' =
        match tv with
        | Tv_Var _
        | Tv_BVar _
        | Tv_FVar _ -> tv
        | Tv_FVar fv -> Tv_FVar fv
        | Tv_Type () -> Tv_Type ()
        | Tv_Const c -> Tv_Const c
        | Tv_Uvar i u -> Tv_Uvar i u
        | Tv_Unknown -> Tv_Unknown
        | Tv_App l (r, q) ->
             let l = visit ff l in
             let r = visit ff r in
             Tv_App l (r, q)
        | Tv_Abs b t ->
            let t = visit ff t in
            Tv_Abs b t
        | Tv_Refine b r ->
            let r = visit ff r in
            Tv_Refine b r
        | Tv_Let r attrs b def t ->
            let def = visit ff def in
            let t = visit ff t in
            Tv_Let r attrs b def t
        | Tv_Match sc brs ->
            let sc = visit ff sc in
            let brs = map (visit_br ff) brs in
            Tv_Match sc brs
        | Tv_AscribedT e t topt ->
            let e = visit ff e in
            let t = visit ff t in
            Tv_AscribedT e t topt
        | Tv_AscribedC e c topt ->
            let e = visit ff e in
            Tv_AscribedC e c topt
        | _ -> fail "impos"
    in
    ff (pack tv')
and visit_br (ff : term -> Tac term) (b:branch) : Tac branch = b

let incr_lits_by_1 (t:term) : Tac term =
    match t with
    | Tv_Const (C_Int x) -> Tv_Const (C_Int (x+1))
    | _ -> t

let test_add_1 (x:int) : int =
    _ by (exact (visit incr_lits_by_1 (quote (x + 1))))
    
