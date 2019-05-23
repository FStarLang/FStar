module LowStar.RST.Loops

let rec while res inv guard test body =
  if test () then begin
    body ();
    while res inv guard test body
  end
