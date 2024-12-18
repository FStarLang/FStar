open FStarC_Json

(** Hints. *)
type hint = {
    hint_name:string;
    hint_index:Z.t;
    fuel:Z.t;
    ifuel:Z.t;
    unsat_core:string list option;
    query_elapsed_time:Z.t;
    hash:string option
}

type hints = hint option list

type hints_db = {
    module_digest:string;
    hints: hints
}

type hints_read_result =
  | HintsOK of hints_db
  | MalformedJson
  | UnableToOpen

let write_hints (filename: string) (hints: hints_db): unit =
  let json = `List [
    `String hints.module_digest;
    `List (List.map (function
      | None -> `Null
      | Some { hint_name; hint_index; fuel; ifuel; unsat_core; query_elapsed_time; hash } ->
          `List [
            `String hint_name;
            `Int (Z.to_int hint_index);
            `Int (Z.to_int fuel);
            `Int (Z.to_int ifuel);
            (match unsat_core with
            | None -> `Null
            | Some strings ->
                `List (List.map (fun s -> `String s) strings));
            `Int (Z.to_int query_elapsed_time);
            `String (match hash with | Some(h) -> h | _ -> "")
          ]
    ) hints.hints)
  ] in
  let channel = open_out_bin filename in
  BatPervasives.finally
    (fun () -> close_out channel)
    (fun channel -> Yojson.Safe.pretty_to_channel channel json)
    channel

let read_hints (filename: string) : hints_read_result =
  let mk_hint nm ix fuel ifuel unsat_core time hash_opt = {
      hint_name = nm;
      hint_index = Z.of_int ix;
      fuel = Z.of_int fuel;
      ifuel = Z.of_int ifuel;
      unsat_core = begin
        match unsat_core with
        | `Null ->
           None
        | `List strings ->
           Some (List.map (function
                           | `String s -> s
                           | _ -> raise Exit)
                           strings)
        |  _ ->
           raise Exit
        end;
      query_elapsed_time = Z.of_int time;
      hash = hash_opt
  }
  in
  try
    let chan = open_in filename in
    let json = Yojson.Safe.from_channel chan in
    close_in chan;
    HintsOK (
        match json with
        | `List [
            `String module_digest;
            `List hints
          ] -> {
            module_digest;
            hints = List.map (function
                        | `Null -> None
                        | `List [ `String hint_name;
                                  `Int hint_index;
                                  `Int fuel;
                                  `Int ifuel;
                                  unsat_core;
                                  `Int query_elapsed_time ] ->
                          (* This case is for dealing with old-style hint files
                             that lack a query-hashes field. We should remove this
                             case once we definitively remove support for old hints *)
                           Some (mk_hint hint_name hint_index fuel ifuel unsat_core query_elapsed_time None)
                        | `List [ `String hint_name;
                                  `Int hint_index;
                                  `Int fuel;
                                  `Int ifuel;
                                  unsat_core;
                                  `Int query_elapsed_time;
                                  `String hash ] ->
                           let hash_opt = if hash <> "" then Some(hash) else None in
                           Some (mk_hint hint_name hint_index fuel ifuel unsat_core query_elapsed_time hash_opt)
                        | _ ->
                           raise Exit
                      ) hints
          }
        | _ ->
           raise Exit
    )
  with
   | Exit ->
      MalformedJson
   | Sys_error _ ->
      UnableToOpen

