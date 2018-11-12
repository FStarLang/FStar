module Raise

open FStar.Tactics

exception Wat
exception Wut

let _ =
  assert True by begin
    let i =
      match catch (fun () -> raise #int Wat) with
      | Inr x -> 1
      | Inl e -> begin match e with
                | Wat -> 2
                | e -> raise e
                end
    in ()
  end

[@(expect_failure [228])]
let _ =
  assert True by begin
    let i =
      match catch (fun () -> raise #int Wut) with
      | Inr x -> 1
      | Inl e -> begin match e with
                | Wat -> 2
                | e -> raise e
                end
    in ()
  end

let _ =
  assert True by begin
    let i =
      try raise Wat; 1
      with
      | e -> begin match e with
            | Wat -> 2
            | e -> raise e
            end
    in ()
  end

[@(expect_failure [228])]
let _ =
  assert True by begin
    let i =
      try raise Wut; 1
      with
      | e -> begin match e with
            | Wat -> 2
            | e -> raise e
            end
    in ()
  end
