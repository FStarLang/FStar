module DeepMatch

(* Matches nested in each other's last branch, at a position that receives a
   value.  The C printer used to emit a match's trailing branch once on trial,
   to see whether it was empty, and again for real: exponential in the depth
   here, where this test would not finish.  A branch whose value is assigned
   or returned is never empty, so the trial is now made only where the value
   is discarded. *)

open FStar.All

let f (xs : list int) : int =
  match xs with
  | [0] -> 0
  | _ ->
    match xs with
    | [1] -> 1
    | _ ->
      match xs with
      | [2] -> 2
      | _ ->
        match xs with
        | [3] -> 3
        | _ ->
          match xs with
          | [4] -> 4
          | _ ->
            match xs with
            | [5] -> 5
            | _ ->
              match xs with
              | [6] -> 6
              | _ ->
                match xs with
                | [7] -> 7
                | _ ->
                  match xs with
                  | [8] -> 8
                  | _ ->
                    match xs with
                    | [9] -> 9
                    | _ ->
                      match xs with
                      | [10] -> 10
                      | _ ->
                        match xs with
                        | [11] -> 11
                        | _ ->
                          match xs with
                          | [12] -> 12
                          | _ ->
                            match xs with
                            | [13] -> 13
                            | _ ->
                              match xs with
                              | [14] -> 14
                              | _ ->
                                match xs with
                                | [15] -> 15
                                | _ ->
                                  match xs with
                                  | [16] -> 16
                                  | _ ->
                                    match xs with
                                    | [17] -> 17
                                    | _ ->
                                      match xs with
                                      | [18] -> 18
                                      | _ ->
                                        match xs with
                                        | [19] -> 19
                                        | _ ->
                                          match xs with
                                          | [20] -> 20
                                          | _ ->
                                            match xs with
                                            | [21] -> 21
                                            | _ ->
                                              match xs with
                                              | [22] -> 22
                                              | _ ->
                                                match xs with
                                                | [23] -> 23
                                                | _ ->
                                                  match xs with
                                                  | [24] -> 24
                                                  | _ ->
                                                    match xs with
                                                    | [25] -> 25
                                                    | _ ->
                                                      match xs with
                                                      | [26] -> 26
                                                      | _ ->
                                                        match xs with
                                                        | [27] -> 27
                                                        | _ ->
                                                          28

let main () : ML unit =
  FStar.IO.print_string (string_of_int (f [3] + f [27] + f []) ^ "\n")
