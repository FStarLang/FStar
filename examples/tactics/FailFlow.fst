module FailFlow

open FStar.Tactics

#set-options "--debug FailFlow --debug_level SMTQuery"

(* TODO: Give this spec to the actual `fail`, but need to fix #1479, sigh *)
assume val ffail : msg:string -> TAC 'a (fun ps p -> p (FStar.Tactics.Result.Failed msg ps))
 
let f () : Tac unit =
    ffail "asd";
    assert False

let f' () : Tac unit =
    fail_act "asd";
    assert False

(* This must fail *)
[@Pervasives.fail]
let g () : Tac unit =
    print "asd";
    assert False

(* Metaprograms that succeed *)
effect TacS (a:Type) = TAC a (fun _ p -> forall x ps. p (FStar.Tactics.Result.Success x ps))

(* None of these succeed *)
[@Pervasives.fail]
let fs () : TacS unit =
    ffail "asd";
    assert False

[@Pervasives.fail]
let fs' () : TacS unit =
    fail_act "asd";
    assert False

[@Pervasives.fail]
let gs () : Tac unit =
    print "asd";
    assert False
