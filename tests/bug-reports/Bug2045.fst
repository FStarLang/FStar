module Bug2045

open FStar.Tactics.V2

let ff () : Dv string = ""

let _ =
    assert True by begin
      dump (ff ());
      ()
    end
