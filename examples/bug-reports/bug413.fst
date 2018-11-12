module Bug413

type blah = _:unit{True} -> unit

(*
/home/hritcu/Projects/fstar/pub/examples/bug-reports/bug413.fst(3,15-3,15): Syntax error
*)
