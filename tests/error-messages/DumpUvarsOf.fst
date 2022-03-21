module DumpUvarsOf

open FStar.Tactics

assume val p : bool -> int -> Type
assume val q : Type
assume val lem : b:bool -> i:int -> squash (p b i) -> Lemma q
assume val p5 : unit -> Lemma (p false 5)

let test () =
  assert q by begin
    apply_lemma (`lem);
    dump "1";
    dump_uvars_of (_cur_goal ()) "2";
    apply_lemma (`p5);
    ()
  end
