module CharConstants

open FStar.Tactics.V2

let _ = assert True by begin
  match `('a') with
  | Tv_Const c -> (
    match c with
    | C_Char c ->
      if c = 'a' then ()
      else fail "3"
    | _ -> fail "2"
  )
  | _ -> fail "1"
end

let _ = assert True by begin
  guard (
    Tactics.Print.term_to_ast_string (`'z')
    =
    "C_Char 'z'"
  )
end
