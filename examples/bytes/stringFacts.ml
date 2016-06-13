module StringFacts = struct

  let string_xor len s1 s2 =
    let res = Bytes.create len in
    for i=0 to len-1 do
      Bytes.set res i (char_of_int ((int_of_char s1.[i]) lxor (int_of_char s2.[i])))
    done;
    res
      
  let string_of_int nb i =
    let rec put_bytes bb lb n =
      if lb = 0 then failwith "not enough bytes"
      else
        begin
          Bytes.set bb (lb-1) (char_of_int (n mod 256));
          if n/256 > 0 then
            put_bytes bb (lb-1) (n/256)
          else bb
        end
    in
    let b = String.make nb (char_of_int 0) in
    put_bytes b nb i

  let int_of_string c : int =
      let x = ref 0 in
      for y = 0 to String.length c - 1 do
          x := 256 * !x + (int_of_char (String.get c y))
      done;
      !x
              
  let debug_print_string (s : string) : string =
    let res = ref "" in
    for i = 0 to String.length s - 1 do
      res := !res ^ (Printf.sprintf "%x " (int_of_char s.[i]));
    done;
    !res
     
  (* Some helpers to deal with the conversation from hex literals to bytes and
   * conversely. Mostly for tests. *)

  let digit_to_int c = match c with
    | '0'..'9' -> Char.code c - Char.code '0'
    | 'a'..'f' -> 10 + Char.code c - Char.code 'a'
    | _ -> failwith "hex_to_char: invalid hex digit"

  let hex_to_char a b =
    Char.chr ((digit_to_int a) lsl 4 + digit_to_int b)

  let char_to_hex c =
    let n = Char.code c in
    let digits = "0123456789abcdef" in
    digits.[n lsr 4], digits.[n land 0x0f]

  let hex_of_string s =
    let n = String.length s in
    let buf = Buffer.create (2 * n) in
    for i = 0 to n - 1 do
      let d1,d2 = char_to_hex s.[i] in
      Buffer.add_char buf d1;
      Buffer.add_char buf d2;
    done;
    Buffer.contents buf

  let string_of_hex s =
    let n = String.length s in
    if n mod 2 <> 0 then
      failwith "string_of_hex: invalid length"
    else
      let res = Bytes.create (n/2) in
      let rec aux i =
        if i >= n then ()
        else (
          Bytes.set res (i/2) (hex_to_char s.[i] s.[i+1]);
          aux (i+2)
        )
      in
      aux 0;
      res

end
