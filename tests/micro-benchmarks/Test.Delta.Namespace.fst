module Test.Delta.Namespace
module L = FStar.List.Tot
open FStar.Tactics
module P = FStar.Printf
let f (x:int) = x + 1
let m (y:list int) = L.map f y

let n2 = assert (m [1;2;3] == L.map (fun x -> x + 1) [1;2;3])
             by (norm [delta_namespace["Test.Delta"];zeta;iota;primops]; //don't unfold the map, but unfold m and f
                 let g = cur_goal () in
                 let f = term_as_formula g in
                 match f with
                 | Comp (Eq _) lhs rhs ->
                   let head, args = collect_app lhs in
                   (match inspect head, args with
                    | Tv_UInst fv _, [_int1; _int2; (lam, _); _] ->
                      let is_lam = Tv_Abs? (inspect lam) in
                      if fv_to_string fv = (`%L.map)
                      && is_lam
                      then trefl()
                      else fail (P.sprintf "Unexpected reduction: head=%s, lam=%s; expected head = %s"
                                                  (fv_to_string fv)
                                                  (term_to_string lam)
                                                  (`%L.map))
                    | _ ->
                      fail ("Unexpected reduction: head= " ^ term_to_string head))
                 | _ -> 
                   fail ("Unexpected goal : " ^ formula_to_string f))
