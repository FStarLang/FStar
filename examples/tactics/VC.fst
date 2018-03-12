module VC

open FStar.Tactics

let tau b tm : Tac term =
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    let tm = norm_term [] tm in
    tm
