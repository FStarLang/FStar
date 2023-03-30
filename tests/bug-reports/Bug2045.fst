module Bug2045

open FStar.Tactics

let ff () : Dv string = ""

let _ =
    assert True by begin
      dump (ff ());
      ()
    end
