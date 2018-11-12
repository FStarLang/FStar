module JSONParser.Spec

let char   : eqtype = Char.char
let string : eqtype = Seq.seq char

let string_of_char (c: char): Tot string = Seq.cons c Seq.empty

let double_quote   : char   = Char.char_of_int 34
let s_double_quote : string = string_of_char double_quote
let left_brace     : char   = Char.char_of_int 123
let s_left_brace   : string = string_of_char left_brace
let right_brace    : char   = Char.char_of_int 123
let s_right_brace  : string = string_of_char right_brace
let comma          : char   = Char.char_of_int 44
let s_comma        : string = string_of_char comma
let colon          : char   = Char.char_of_int 58
let s_colon        : string = string_of_char colon

(** The following works, but then [json_schema] loops at type-checking
<<
let key: eqtype = (s: string {not (Seq.mem double_quote s)})
>>

Ugly workaround for now:
*)
type key =
| Key: (s: string {not (Seq.mem double_quote s)}) -> key

type json_schema =
| String
| Object of (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)} )

let rec object_as_type (j: json_schema) (as_type: (j': json_schema {j' << j}) -> Tot Type0) (l: list (key * json_schema) {l << j}) (s: key) : Tot Type0 =
match l with
| [] -> False
| (s', j') :: q -> if s = s' then as_type j' else object_as_type j as_type q s

let rec object_as_type_append_cons
  (j: json_schema)
  (as_type: (j': json_schema {j' << j}) -> Tot Type0)
  (l: list (key * json_schema) {l << j})
  (s: key)
  (j': json_schema)
  (l' q: list (key * json_schema))
: Lemma
  (requires (List.Tot.noRepeats (List.Tot.map fst l)))
  (ensures ((l == List.Tot.append l' ((s, j') :: q)) ==> (let _ : squash (j' << l) =  List.Tot.precedes_append_cons_prod_r l l' s j' q in object_as_type j as_type l s == as_type j')))
  (decreases l')
= FStar.Classical.impl_intro_gen
    #(l == List.Tot.append l' ((s, j') :: q) /\ j' << l)
    #(fun _ -> object_as_type j as_type l s == as_type j')
    (fun _ -> match l' with
      | [] -> ()
      | (s_, j_) :: q' ->
	List.Tot.map_append fst l' ((s, j') :: q);
	List.Tot.noRepeats_append_elim (List.Tot.map fst l') (List.Tot.map fst ((s, j') :: q));
	object_as_type_append_cons j as_type (List.Tot.tl l) s j' q' q
	  )
	  
let rec as_gtype (j: json_schema) : Tot Type0 =
  match j with
  | String -> (s: string { ~ (Seq.mem double_quote s) } )
  | Object l ->
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) as_gtype l)

let as_gtype_object_eq
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
: Lemma
  (requires True)
  (ensures 
   (as_gtype (Object l) ==
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) as_gtype l)))
  [SMTPat (as_gtype (Object l))]
= assert_norm (as_gtype (Object l) ==
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) as_gtype l))

let as_gtype_string: squash (as_gtype String == (s: string { ~ (Seq.mem double_quote s ) } )) = ()

let rec as_value_type (j: json_schema) : Tot Type0 =
  match j with
  | String -> Buffer.buffer char
  | Object l ->
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type j as_value_type l)

let gprint_string (s: string { ~ (Seq.mem double_quote s) } ) : GTot string =
  Seq.cons double_quote (Seq.snoc s double_quote)

let object_rec_prereq
  (j: json_schema)
  (gprint: (j': json_schema {j' << j}) -> (data: as_gtype j') -> GTot string)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (s: key)
  (j': json_schema)
  (q: list (key * json_schema) { l' == ((s, j') :: q) } )
: Lemma
  (ensures
    ((List.Tot.strict_prefix_of (List.Tot.map fst l') (List.Tot.map fst l) \/ List.Tot.map fst l' == List.Tot.map fst l)
    /\ List.Tot.mem s (List.Tot.map fst l)
    /\ object_as_type j as_gtype l s == as_gtype j'
    /\ j' << l /\ j' << j
    /\ List.Tot.strict_prefix_of q l))
=   List.Tot.map_strict_prefix_of fst l' l;
    List.Tot.mem_strict_prefix_of (List.Tot.map fst l') s (List.Tot.map fst l);
    List.Tot.strict_prefix_of_trans q l' l;
    let (s: key {List.Tot.mem s (List.Tot.map fst l)}) = s in
    FStar.Classical.exists_elim
	(object_as_type j as_gtype l s == as_gtype j' /\ j' << l)
	#_
	#(fun l3 -> l == List.Tot.append l3 l')
	(List.Tot.strict_prefix_of_or_eq_exists_append l' l)
	(fun l3 ->
          object_as_type_append_cons j as_gtype l s j' l3 q;
	  List.Tot.precedes_append_cons_prod_r l l3 s j' q
	  )

let rec gprint_object
  (j: json_schema)
  (gprint: (j': json_schema {j' << j}) -> (data: as_gtype j') -> GTot string)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
: GTot string
= match l' with
  | [] -> Seq.empty
  | ((s, j')::q) ->
    object_rec_prereq j gprint l data l' s j' q;
    let (data' : as_gtype j') =
      DependentMap.sel data s
    in
    let objprint = gprint j' data' in
    let suff =
      if Cons? q
      then
	Seq.cons comma (gprint_object j gprint l data q)
      else
	Seq.empty
    in
    Seq.append (gprint_string (Key?.s s)) (Seq.cons colon (Seq.append objprint suff))

let rec gprint (j: json_schema) (data: as_gtype j) : GTot string =
  match j with
  | String -> gprint_string data
  | Object l ->
    as_gtype_object_eq l;
    Seq.cons
      left_brace
      (Seq.snoc
	(gprint_object j (fun (j': json_schema {j' << j}) data' -> gprint j' data') l data l)
	right_brace)

let gprint_object_eq
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (data: as_gtype (Object l))
: Lemma
  (requires True)
  (ensures (gprint (Object l) data == (
    as_gtype_object_eq l;
    Seq.cons
      left_brace
      (Seq.snoc
	(gprint_object (Object l) gprint l data l)
	right_brace))))
  [SMTPat (gprint (Object l) data)]
= assert_norm (gprint (Object l) data == (
    as_gtype_object_eq l;
    Seq.cons
      left_brace
      (Seq.snoc
	(gprint_object (Object l) gprint l data l)
	right_brace)))

let is_whitespace (c: char): Tot bool =
  match Char.int_of_char c with
    | 9 (* horizontal tab *)
    | 10 (* line feed *)
    | 13 (* carriage return *)
    | 32 (* space *)
      -> true
    | _ -> false

let double_quote_is_not_whitespace:
  squash (~ (is_whitespace double_quote))
= ()

let rec gparse_whitespace
  (s: string)
: Ghost string
  (requires True)
  (ensures (fun _ -> True))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then s
  else if is_whitespace (Seq.head s)
       then gparse_whitespace (Seq.tail s)
       else s

let gparse_whitespace_empty
: squash (gparse_whitespace Seq.empty == Seq.empty)
= ()

let rec gparse_whitespace_append
  (s_white: string { forall (i: nat { i < Seq.length s_white } ) . is_whitespace (Seq.index s_white i) } )
  (s: string)
: Lemma
  (requires True)
  (ensures (gparse_whitespace (Seq.append s_white s) == gparse_whitespace s))
  (decreases (Seq.length s_white))
= if Seq.length s_white = 0
  then begin
    Seq.lemma_eq_elim s_white Seq.empty;
    Seq.append_empty_l s
  end else begin
    let _ : squash (s_white == Seq.cons (Seq.head s_white) (Seq.tail s_white)) =
          Seq.cons_head_tail s_white
    in
    let _ : squash (Seq.append s_white s == Seq.cons (Seq.head s_white) (Seq.append (Seq.tail s_white) s)) =
	  Seq.append_cons (Seq.head s_white) (Seq.tail s_white) s
    in
    let s_white: (s_white: string {Seq.length s_white > 0 /\ ( forall (i: nat { i < Seq.length s_white } ) . is_whitespace (Seq.index s_white i)) } ) = s_white in
    let _ : squash (forall (i: nat {i < Seq.length (Seq.tail s_white) } ) . is_whitespace (Seq.index (Seq.tail s_white) i)) =
	  FStar.Classical.forall_intro (Seq.index_tail s_white)
    in
    let _ : squash (Seq.tail (Seq.append s_white s) == Seq.append (Seq.tail s_white) s) =
	  Seq.lemma_tail_append s_white s
    in
    gparse_whitespace_append (Seq.tail s_white) s
  end

let gparse_whitespace_not_whitespace
  (s: string { Seq.length s > 0 /\ ~ (is_whitespace (Seq.index s 0)) } )
: Lemma
  (ensures (gparse_whitespace s == s))
= ()

let rec not_whitespace_gparse_whitespace
  (s: string)
: Lemma
  (requires True)
  (ensures (Seq.length (gparse_whitespace s) > 0 ==> ~ (is_whitespace (Seq.index (gparse_whitespace s) 0))))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then ()
  else if is_whitespace (Seq.index s 0)
  then not_whitespace_gparse_whitespace (Seq.tail s)
  else ()

let rec gparse_whitespace_exists
  (s: string)
: Lemma
  (requires True)
  (ensures (exists s_white .
    s == Seq.append s_white (gparse_whitespace s) /\
    (forall (i: nat {i < Seq.length s_white }) . is_whitespace (Seq.index s_white i))))
  (decreases (Seq.length s))
= if Seq.length s = 0 || not (is_whitespace (Seq.index s 0))
  then begin
    Seq.append_empty_l s;
    FStar.Classical.exists_intro
      (fun s_white -> s == Seq.append s_white (gparse_whitespace s) /\
	(forall (i: nat {i < Seq.length s_white }) . is_whitespace (Seq.index s_white i)))
      Seq.empty
  end else
    FStar.Classical.exists_elim
      (exists s_white .
	s == Seq.append s_white (gparse_whitespace s) /\
	(forall (i: nat {i < Seq.length s_white }) . is_whitespace (Seq.index s_white i)))
      #_
      #(fun s_white ->
	Seq.tail s == Seq.append s_white (gparse_whitespace (Seq.tail s)) /\
	(forall (i: nat {i < Seq.length s_white }) . is_whitespace (Seq.index s_white i)))
      (gparse_whitespace_exists (Seq.tail s))
      (fun s_white ->
	Seq.append_cons (Seq.head s) s_white (gparse_whitespace (Seq.tail s));
	FStar.Classical.exists_intro
	  (fun s_white -> s == Seq.append s_white (gparse_whitespace s) /\
	    (forall (i: nat {i < Seq.length s_white }) . is_whitespace (Seq.index s_white i)))
	  (Seq.cons (Seq.head s) s_white))

let length_gparse_whitespace
  (s: string)
: Lemma
  (ensures (Seq.length (gparse_whitespace s) <= Seq.length s))
= FStar.Classical.exists_elim
    (Seq.length (gparse_whitespace s) <= Seq.length s)
    #_
    #(fun s_white ->
        s == Seq.append s_white (gparse_whitespace s) /\
	(forall (i: nat {i < Seq.length s_white }) . is_whitespace (Seq.index s_white i)))
    (gparse_whitespace_exists s)
    (fun s_white -> ())

let rec gparse_string_contents
  (accu: string)
  (s: string)
: Ghost (option (string * string))
  (requires True)
  (ensures (fun _ -> True))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then None
  else if Seq.head s = double_quote
  then Some (accu, Seq.tail s)
  else gparse_string_contents (Seq.snoc accu (Seq.head s)) (Seq.tail s)

let rec length_gparse_string_contents
  (accu: string)
  (s contents s': string)
: Lemma
  (requires (gparse_string_contents accu s == Some (contents, s')))
  (ensures (Seq.length s' < Seq.length s))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then ()
  else if Seq.head s = double_quote
  then ()
  else length_gparse_string_contents (Seq.snoc accu (Seq.head s)) (Seq.tail s) contents s'

let rec not_mem_double_quote_gparse_string_contents
  (accu: string)
  (s contents s': string)
: Lemma
  (requires ((~ (Seq.mem double_quote accu)) /\ gparse_string_contents accu s == Some (contents, s')))
  (ensures (~ (Seq.mem double_quote contents)))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then ()
  else if Seq.head s = double_quote
  then ()
  else begin
    Seq.lemma_mem_snoc accu (Seq.head s);
    not_mem_double_quote_gparse_string_contents (Seq.snoc accu (Seq.head s)) (Seq.tail s) contents s'
  end

let rec gparse_string_contents_append_cons
  (accu: string)
  (left: string {~ (Seq.mem double_quote left) } )
  (right: string)
: Lemma
  (requires True)
  (ensures (gparse_string_contents accu (Seq.append left (Seq.cons double_quote right)) == Some (Seq.append accu left, right)))
  (decreases (Seq.length left))
= if Seq.length left = 0
  then begin
      Seq.lemma_eq_elim left Seq.empty;
      Seq.append_empty_l (Seq.cons double_quote right);
      Seq.lemma_tl double_quote right;
      Seq.append_empty_r accu
  end else begin
      Seq.cons_head_tail left;
      Seq.append_cons (Seq.head left) (Seq.tail left) (Seq.cons double_quote right);
      Seq.mem_cons (Seq.head left) (Seq.tail left);
      assert (Seq.head left <> double_quote);
      let _ : squash (gparse_string_contents accu (Seq.append left (Seq.cons double_quote right)) == gparse_string_contents (Seq.snoc accu (Seq.head left)) (Seq.tail (Seq.append left (Seq.cons double_quote right)))) = () in
      Seq.lemma_tail_append left (Seq.cons double_quote right);
      let _ : squash (gparse_string_contents (Seq.snoc accu (Seq.head left)) (Seq.append (Seq.tail left) (Seq.cons double_quote right)) == Some (Seq.append (Seq.snoc accu (Seq.head left)) (Seq.tail left), right)) =
	gparse_string_contents_append_cons (Seq.snoc accu (Seq.head left)) (Seq.tail left) right
      in
      let _ : squash (Seq.append (Seq.snoc accu (Seq.head left)) (Seq.tail left) == Seq.append accu (Seq.cons (Seq.head left) (Seq.tail left))) =
	Seq.append_cons_snoc accu (Seq.head left) (Seq.tail left);
	Seq.lemma_eq_elim (Seq.append (Seq.snoc accu (Seq.head left)) (Seq.tail left)) (Seq.append accu (Seq.cons (Seq.head left) (Seq.tail left)))
      in
      ()
  end

let gparse_exact_char
  (c: char)
  (s: string)
: GTot (option string)
= let s1 = gparse_whitespace s in
  if Seq.length s1 = 0
  then None
  else if Seq.head s1 <> c
  then None
  else Some (Seq.tail s1)

let gparse_exact_char_append_cons
  (s_white: string { forall (i: nat { i < Seq.length s_white } ) . is_whitespace (Seq.index s_white i) } )
  (c: char {~ (is_whitespace c)})
  (s_tail: string)
: Lemma
  (ensures (gparse_exact_char c (Seq.append s_white (Seq.cons c s_tail)) == Some s_tail))
= gparse_whitespace_append s_white (Seq.cons c s_tail);
  gparse_whitespace_not_whitespace (Seq.cons c s_tail);
  Seq.lemma_tl c s_tail

let length_gparse_exact_char 
  (c: char)
  (s: string)
  (s_tail: string)
: Lemma
  (requires (gparse_exact_char c s = Some s_tail))
  (ensures (Seq.length s_tail < Seq.length s))
= let s1 = gparse_whitespace s in
  let _ = length_gparse_whitespace s in
  ()

let gparse_string (s: string): GTot (option (string * string)) =
  match gparse_exact_char double_quote s with
  | Some s_tail -> gparse_string_contents Seq.empty s_tail
  | _ -> None

let not_mem_double_quote_gparse_string
  (s contents s': string)
: Lemma
  (requires (gparse_string s == Some (contents, s')))
  (ensures (~ (Seq.mem double_quote contents)))
= match gparse_exact_char double_quote s with
  | Some s_tail -> begin
      not_mem_double_quote_gparse_string_contents Seq.empty s_tail contents s';
      Seq.append_empty_l contents
    end

let gparse_string_append_cons_append_cons
  (s_white: string { forall (i: nat { i < Seq.length s_white } ) . is_whitespace (Seq.index s_white i) } )
  (s_contents: string { ~ (Seq.mem double_quote s_contents) } )
  (s_tail: string)
: Lemma
  (gparse_string (Seq.append s_white (Seq.cons double_quote (Seq.append s_contents (Seq.cons double_quote s_tail))))
   == Some (s_contents, s_tail))
= let s2 = Seq.append s_contents (Seq.cons double_quote s_tail) in
  let _ = gparse_exact_char_append_cons s_white double_quote s2 in
  let _ : squash (gparse_string_contents Seq.empty s2 == Some (Seq.append Seq.empty s_contents, s_tail)) =
      gparse_string_contents_append_cons Seq.empty s_contents s_tail
  in
  Seq.append_empty_l s_contents

let gparse_string_gprint_string
  (s_white: string { forall (i: nat { i < Seq.length s_white } ) . is_whitespace (Seq.index s_white i) } )
  (s_contents: string { ~ (Seq.mem double_quote s_contents) } )
  (s_tail: string)
: Lemma
  (gparse_string (Seq.append s_white (Seq.append (gprint_string s_contents) s_tail))
   == Some (s_contents, s_tail))
= let _ : squash (Seq.append (gprint_string s_contents) s_tail == Seq.cons double_quote (Seq.append s_contents (Seq.cons double_quote s_tail))) =
    Seq.append_cons double_quote (Seq.snoc s_contents double_quote) s_tail;
    Seq.append_cons_snoc s_contents double_quote s_tail
  in
  gparse_string_append_cons_append_cons s_white s_contents s_tail

let length_gparse_string
  (s contents s': string)
: Lemma
  (requires (gparse_string s == Some (contents, s')))
  (ensures (Seq.length s' < Seq.length s))
= match gparse_exact_char double_quote s with
  | Some s_tail ->
    let _ = length_gparse_exact_char double_quote s s_tail in
    let _ = length_gparse_string_contents Seq.empty s_tail contents s' in
    Seq.append_empty_l contents

let rec gparse_exact_string_contents
  (against: string)
  (parsee: string)
: Ghost (option string)
  (requires True)
  (ensures (fun _ -> True))
  (decreases (Seq.length against))
= if Seq.length against = 0
  then Some parsee
  else if Seq.length parsee = 0
  then None
  else if Seq.head against <> Seq.head parsee
  then None
  else gparse_exact_string_contents (Seq.tail against) (Seq.tail parsee)

let rec gparse_exact_string_contents_append
  (against: string)
  (tail: string)
: Lemma
  (requires True)
  (ensures (gparse_exact_string_contents against (Seq.append against tail) == Some tail))
  (decreases (Seq.length against))
= if Seq.length against = 0
  then
    let _ = Seq.lemma_eq_elim against Seq.empty in
    Seq.append_empty_l tail
  else
    let _ = Seq.cons_head_tail against in
    let _ = Seq.append_cons (Seq.head against) (Seq.tail against) tail in
    let _ = Seq.lemma_tail_append against tail in
    gparse_exact_string_contents_append (Seq.tail against) tail

let rec length_gparse_exact_string_contents
  (against: string)
  (parsee: string)
  (tail: string)
: Lemma
  (requires (gparse_exact_string_contents against parsee = Some tail))
  (ensures (Seq.length tail <= Seq.length parsee))
  (decreases (Seq.length against))
= if Seq.length against = 0
  then ()
  else length_gparse_exact_string_contents (Seq.tail against) (Seq.tail parsee) tail

let gparse_exact_string
  (against: string { ~ (Seq.mem double_quote against) })
  (parsee: string)
: GTot (option string)
= match gparse_exact_char double_quote parsee with
  | Some s1 ->
    begin match gparse_exact_string_contents against s1 with
    | Some s2 ->
      if Seq.length s2 = 0
      then None
      else if Seq.head s2 <> double_quote
      then None
      else Some (Seq.tail s2)
    | _ -> None
    end
  | _ -> None

let length_gparse_exact_string
  (against: string { ~ (Seq.mem double_quote against) })
  (parsee: string)
  (tail: string)
: Lemma
  (requires (gparse_exact_string against parsee == Some tail))
  (ensures (Seq.length tail < Seq.length parsee))
= match gparse_exact_char double_quote parsee with
  | Some s1 ->
    let _ = length_gparse_exact_char double_quote parsee s1 in
    match gparse_exact_string_contents against s1 with
    | Some s2 ->
      length_gparse_exact_string_contents against s1 s2

let gparse_exact_string_gprint_string
  (white: string { forall (i: nat { i < Seq.length white } ) . is_whitespace (Seq.index white i) } )
  (against: string {~ (Seq.mem double_quote against) } )
  (tail: string)
: Lemma
  (ensures (gparse_exact_string against (Seq.append white (Seq.append (gprint_string against) tail)) == Some tail))
= let _ : squash (Seq.append (gprint_string against) tail == Seq.cons double_quote (Seq.append against (Seq.cons double_quote tail))) =
    Seq.append_cons double_quote (Seq.snoc against double_quote) tail;
    Seq.append_cons_snoc against double_quote tail
  in
  gparse_exact_char_append_cons white double_quote (Seq.append against (Seq.cons double_quote tail));
  gparse_exact_string_contents_append against (Seq.cons double_quote tail);
  Seq.lemma_tl double_quote tail

let rec gparse_object
  (j: json_schema)
  (gparse: (j': json_schema {j' << j}) -> (data: as_gtype j') -> (s: string) -> GTot (option (as_gtype j' * (s': string {Seq.length s' < Seq.length s}))))
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (s: string)
: Ghost (option (DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l) * (s': string {Seq.length s' <= Seq.length s} )))
  (requires True)
  (ensures (fun _ -> True))
  (decreases l')
= match l' with
  | [] -> Some (data, s)
  | ((s', j') :: q) ->
    object_rec_prereq j gprint l data l' s' j' q;
    let (data' : as_gtype j') =
      DependentMap.sel data s'
    in
    begin match gparse_exact_string (Key?.s s') s with
    | None -> None
    | Some s1 ->
      let _ = length_gparse_exact_string (Key?.s s') s s1 in
      begin match gparse_exact_char colon s1 with
      | None -> None
      | Some s2 ->
	let _ = length_gparse_exact_char colon s1 s2 in
	begin match gparse j' data' s2 with
	| None -> None
	| Some (new_data', s3) ->
	  let new_data = DependentMap.upd data s' new_data' in
	  if Cons? q
	  then begin match gparse_exact_char comma s3 with
	  | None -> None
	  | Some s4 ->
	    let _ = length_gparse_exact_char comma s3 s4 in
	    begin match gparse_object j gparse l new_data q s4 with
	    | None -> None
	    | Some (new_data_, s5) ->
	      let (s6: string {Seq.length s6 <= Seq.length s}) = s5 in
	      Some (new_data_, s6)
	    end
	  end else
	    Some (new_data, s3)
	end
      end
    end

let rec gparse
  (j: json_schema)
  (data: as_gtype j)
  (s: string)
: Ghost (option (as_gtype j * (s': string {Seq.length s' < Seq.length s})))
  (requires True)
  (ensures (fun _ -> True))
  (decreases j)
= match j with
  | String ->
    begin match gparse_string s with
    | Some (new_data, rem) ->
      let _ = length_gparse_string s new_data rem in
      not_mem_double_quote_gparse_string s new_data rem;
      length_gparse_string s new_data rem;
      Some (new_data, rem)
    | None -> None
    end
  | Object l ->
    match gparse_exact_char left_brace s with
    | None -> None
    | Some s1 ->
      let _ = length_gparse_exact_char left_brace s s1 in
      let gparse_rec (j': json_schema {j' << j}) (data: as_gtype j') (s: string) : GTot (option (as_gtype j' * (s': string {Seq.length s' < Seq.length s}))) = gparse j' data s in
      as_gtype_object_eq l;
      begin match gparse_object j gparse_rec l data l s1 with
      | None -> None
      | Some (new_data, s2) ->
	begin match gparse_exact_char right_brace s2 with
	| None -> None
	| Some s3 ->
	  let _ = length_gparse_exact_char right_brace s2 s3 in
	  Some (new_data, s3)
	end
      end

let gparse_object_eq
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (data: as_gtype (Object l))
  (s: string)
: Lemma
  (requires True)
  (ensures (gparse (Object l) data s ==
    (match gparse_exact_char left_brace s with
    | None -> None
    | Some s1 ->
      let _ = length_gparse_exact_char left_brace s s1 in
      as_gtype_object_eq l;
      let data : DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type (Object l) as_gtype l) = data in      
      begin match gparse_object (Object l) gparse l data l s1 with
      | None -> None
      | Some (new_data, s2) ->
	begin match gparse_exact_char right_brace s2 with
	| None -> None
	| Some s3 ->
	  let _ = length_gparse_exact_char right_brace s2 s3 in
	  Some (new_data, s3)
	end
      end
  )))
  [SMTPat (gparse (Object l) data s)]
= assert_norm (gparse (Object l) data s ==
    (match gparse_exact_char left_brace s with
    | None -> None
    | Some s1 ->
      let _ = length_gparse_exact_char left_brace s s1 in
      as_gtype_object_eq l;
      let data : DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type (Object l) as_gtype l) = data in      
      begin match gparse_object (Object l) gparse l data l s1 with
      | None -> None
      | Some (new_data, s2) ->
	begin match gparse_exact_char right_brace s2 with
	| None -> None
	| Some s3 ->
	  let _ = length_gparse_exact_char right_brace s2 s3 in
	  Some (new_data, s3)
	end
      end
  ))

let gparse_object_eq_some
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (data: as_gtype (Object l))
  (s: string)
  (s1: string {gparse_exact_char left_brace s == Some s1})
  (new_data: as_gtype (Object l))
  (s2: string { (
    as_gtype_object_eq l; (
    Seq.length s2 <= Seq.length s1 /\ (
    let (s2: string { Seq.length s2 <= Seq.length s1 } ) = s2 in
    gparse_object (Object l) gparse l data l s1 == Some (new_data, s2)
  ))) })
  (s3: string { gparse_exact_char right_brace s2 == Some s3 } )
: Lemma
  (requires True)
  (ensures (Seq.length s3 < Seq.length s /\ (let (s3 : string { Seq.length s3 < Seq.length s } ) = s3 in ( gparse (Object l) data s == Some (new_data, s3)))))
= gparse_object_eq l data s

let length_gprint
  (j: json_schema)
  (data: as_gtype j)
: Lemma
  (requires True)
  (ensures (Seq.length (gprint j data) > 0))
  [SMTPat (Seq.length (gprint j data))]
= match j with
  | Object l ->
    as_gtype_object_eq l
  | _ -> ()

let gparse_object_gprint_object_aux_nil
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))  
  (tail: string)
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (l_left: list (key * json_schema) {l == List.Tot.append l_left l' } )
  (hsel: (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) }) ->
    Lemma (DependentMap.sel data0 k == DependentMap.sel data k)
  )
: Lemma
  (requires (l' == []))
  (ensures (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail)))
=
    let _ : squash (l_left == l) =
      List.Tot.append_l_nil l_left
    in
    let f
      (k: key { List.Tot.mem k (List.Tot.map fst l) } )
    : Lemma (DependentMap.sel data0 k == DependentMap.sel data k)
    = let (k: key { List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) } ) = k in
      hsel k
    in
    let _
    : squash (forall (k: key { List.Tot.mem k (List.Tot.map fst l) } ) .
      DependentMap.sel data0 k == DependentMap.sel data k
    ) =
      FStar.Classical.forall_intro f
    in
    DependentMap.equal_intro data0 data;
    DependentMap.equal_elim data0 data;
    Seq.append_empty_l tail;
    assert (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail))

let gparse_object_cons_nil
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (s': key {List.Tot.mem s' (List.Tot.map fst l) } )
  (j': json_schema { object_as_type j as_gtype l s' == as_gtype j' } )
  (q: list (key * json_schema) { l' == (s', j') :: q /\ j' << j /\ List.Tot.strict_prefix_of q l /\ ~ (Cons? q) } )
  (s: string)
  (s1: string { Seq.length s1 < Seq.length s /\ gparse_exact_string (Key?.s s') s == Some s1 } )
  (s2: string { Seq.length s2 < Seq.length s1 /\ gparse_exact_char colon s1 == Some s2 } )
  (data': as_gtype j' { data' == DependentMap.sel data s' } )
  (new_data': as_gtype j')
  (s3: string { Seq.length s3 < Seq.length s2 /\ gparse j' data' s2 == Some (new_data', s3) } )
  (new_data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l) { new_data == DependentMap.upd data s' new_data' } )
: Lemma
  (ensures (gparse_object j gparse l data l' s == Some (new_data, s3)))
= ()  

let gparse_object_gprint_object_aux_cons_nil
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))  
  (tail: string)
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (l_left: list (key * json_schema) {l == List.Tot.append l_left l' } )
  (s': key { List.Tot.mem s' (List.Tot.map fst l) } )
  (j': json_schema { object_as_type j as_gtype l s' == as_gtype j' } )
  (q: list (key * json_schema) {l' == (s', j') :: q /\ List.Tot.strict_prefix_of q l})
  (s: string {s == Seq.append (gprint_object j gprint l data l') tail } )
  (s2: string { Seq.length s2 < Seq.length s /\ gparse_exact_string (Key?.s s') s == Some s2 } )
  (s3: string { Seq.length s3 < Seq.length s2 /\ gparse_exact_char colon s2 == Some s3 } )
  (data': as_gtype j' { DependentMap.sel data s' == data' } )
  (data0': as_gtype j' { DependentMap.sel data0 s' == data0' } )
  (s4: string { Seq.length s4 < Seq.length s3  /\ gparse j' data0' s3 == Some (data', s4) /\ s4 == Seq.append Seq.empty tail } )
  (new_l_left: list (key * json_schema) { l == List.Tot.append new_l_left q /\ ~ (Cons? q) } )
  (new_data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l) {new_data0 == DependentMap.upd data0 s' data' } )
  (new_hsel: (
    (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst new_l_left)}) ->
    Lemma
    (DependentMap.sel new_data0 k == DependentMap.sel data k)))
: Lemma
  (ensures (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail)))
= object_rec_prereq j gprint l data l' s' j' q;
  let _ : squash (new_data0 == data) =
    let _ : squash (new_l_left == l) =
      List.Tot.append_l_nil new_l_left
    in
    let f
      (k: key { List.Tot.mem k (List.Tot.map fst l) } )
    : Lemma (DependentMap.sel new_data0 k == DependentMap.sel data k)
    = let (k: key { List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst new_l_left) } ) = k in
      new_hsel k
    in
    let _
    : squash (forall (k: key { List.Tot.mem k (List.Tot.map fst l) } ) .
      DependentMap.sel new_data0 k == DependentMap.sel data k
    ) =
      FStar.Classical.forall_intro f
    in
    DependentMap.equal_intro new_data0 data;
    DependentMap.equal_elim new_data0 data
  in
  let _ : squash (gparse_object j gparse l data0 l' s == Some (new_data0, s4)) =
    let (j': json_schema { object_as_type j as_gtype l s' == as_gtype j' }) = j' in
    let (q: list (key * json_schema) { l' == (s', j') :: q /\ j' << j /\ List.Tot.strict_prefix_of q l /\ ~ (Cons? q) } ) = q in
    let (s2: string { Seq.length s2 < Seq.length s /\ gparse_exact_string (Key?.s s') s == Some s2 } ) = s2 in
    let (s3: string { Seq.length s3 < Seq.length s2 /\ gparse_exact_char colon s2 == Some s3 } ) = s3 in
    let (data0': as_gtype j' {data0' == DependentMap.sel data0 s' } ) = data0' in
    let (data': as_gtype j') = data' in
    let (s4: string { Seq.length s4 < Seq.length s3 /\ gparse j' data0' s3 == Some (data', s4) } ) = s4 in
    let (new_data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l) { new_data0 == DependentMap.upd data0 s' data' } ) = new_data0 in
    gparse_object_cons_nil j l data0 l' s' j' q s s2 s3 data0' data' s4 new_data0
  in
  Seq.append_empty_l tail;
  assert (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail))

let gparse_object_cons_cons
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (s': key {List.Tot.mem s' (List.Tot.map fst l) } )
  (j': json_schema { object_as_type j as_gtype l s' == as_gtype j' } )
  (q: list (key * json_schema) { l' == (s', j') :: q /\ j' << j /\ List.Tot.strict_prefix_of q l /\ (Cons? q) } )
  (s: string)
  (s1: string { Seq.length s1 < Seq.length s /\ gparse_exact_string (Key?.s s') s == Some s1 } )
  (s2: string { Seq.length s2 < Seq.length s1 /\ gparse_exact_char colon s1 == Some s2 } )
  (data': as_gtype j' { data' == DependentMap.sel data s' } )
  (new_data': as_gtype j')
  (s3: string { Seq.length s3 < Seq.length s2 /\ gparse j' data' s2 == Some (new_data', s3) } )
  (new_data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l) { new_data == DependentMap.upd data s' new_data' } )
  (s4: string { Seq.length s4 < Seq.length s3 /\ gparse_exact_char comma s3 == Some s4 } )
  (data_: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (s5: string { Seq.length s5 <= Seq.length s4 /\ gparse_object j gparse l new_data q s4 == Some (data_, s5) } )
: Lemma
  (ensures (gparse_object j gparse l data l' s == Some (data_, s5)))
= ()  


#reset-options "--z3rlimit 32"

let gparse_object_gprint_object_aux_cons_cons
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))  
  (tail: string)
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (l_left: list (key * json_schema) {l == List.Tot.append l_left l' } )
  (ihgparse_object:
    (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l)) ->
    (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l)) ->
    (tail: string) ->
    (l'': list (key * json_schema) {(List.Tot.strict_prefix_of l'' l \/ l'' == l) /\ l'' << l'}) ->
    (l_left: list (key * json_schema) {l == List.Tot.append l_left l'' } ) ->
    (hsel: (
      (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) }) ->
      Lemma (DependentMap.sel data0 k == DependentMap.sel data k)
    )) ->
    Lemma (gparse_object j gparse l data0 l'' (Seq.append (gprint_object j gprint l data l'') tail) == Some (data, tail)))
  (s': key { List.Tot.mem s' (List.Tot.map fst l) } )
  (j': json_schema { object_as_type j as_gtype l s' == as_gtype j' } )
  (q: list (key * json_schema) {l' == (s', j') :: q /\ List.Tot.strict_prefix_of q l /\ j' << j})
  (s: string {s == Seq.append (gprint_object j gprint l data l') tail} )
  (s2: string { Seq.length s2 < Seq.length s /\ gparse_exact_string (Key?.s s') s == Some s2 } )
  (s3: string { Seq.length s3 < Seq.length s2 /\ gparse_exact_char colon s2 == Some s3 } )
  (data': as_gtype j' { DependentMap.sel data s' == data' } )
  (data0': as_gtype j' { DependentMap.sel data0 s' == data0' } )
  (s4: string { Seq.length s4 < Seq.length s3  /\ gparse j' data0' s3 == Some (data', s4) /\ s4 == Seq.append (Seq.cons comma (gprint_object j gprint l data q)) tail } )
  (new_l_left: list (key * json_schema) { l == List.Tot.append new_l_left q /\ Cons? q } )
  (new_data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l) {new_data0 == DependentMap.upd data0 s' data' })
  (new_hsel: (
    (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst new_l_left)}) ->
    Lemma
    (DependentMap.sel new_data0 k == DependentMap.sel data k)))
: Lemma
  (ensures (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail)))
= object_rec_prereq j gprint l data l' s' j' q;
  let s45 = gprint_object j gprint l data q in
  let s5 = Seq.append s45 tail in
  let _ : squash (s4 == Seq.cons comma s5) =
    Seq.append_cons comma s45 tail
  in
  let _ : squash (gparse_object j gparse l new_data0 q s5 == Some (data, tail)) =
    ihgparse_object new_data0 data tail q new_l_left new_hsel;
    assert (gparse_object j gparse l new_data0 q s5 == Some (data, tail))
  in
  let _ : squash (gparse_exact_char comma s4 == Some s5) =
    Seq.append_empty_l s4;
    gparse_exact_char_append_cons Seq.empty comma s5
  in
  let _ =
    gparse_object_cons_cons
      j l data0 l'
      s' j' q
      s s2 s3
      data0'
      data'
      s4
      new_data0
      s5
      data
      tail
  in    
  assert (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail))

let gparse_object_gprint_object_aux_cons
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))  
  (tail: string)
  (ihgparse: (j': json_schema {j' << j}) -> (data0': as_gtype j') -> (data': as_gtype j') -> (tail': string) ->
    Lemma (gparse j' data0' (Seq.append (gprint j' data') tail') == Some (data', tail')))
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (l_left: list (key * json_schema) {l == List.Tot.append l_left l' } )
  (hsel: (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) }) ->
    Lemma (DependentMap.sel data0 k == DependentMap.sel data k)
  )
  (ihgparse_object:
    (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l)) ->
    (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l)) ->
    (tail: string) ->
    (l'': list (key * json_schema) {(List.Tot.strict_prefix_of l'' l \/ l'' == l) /\ l'' << l'}) ->
    (l_left: list (key * json_schema) {l == List.Tot.append l_left l'' } ) ->
    (hsel: (
      (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) }) ->
      Lemma (DependentMap.sel data0 k == DependentMap.sel data k)
    )) ->
    Lemma (gparse_object j gparse l data0 l'' (Seq.append (gprint_object j gprint l data l'') tail) == Some (data, tail)))
  (s': key)
  (j': json_schema {j' << j})
  (q: list (key * json_schema))
: Lemma
  (requires (l' == (s', j') :: q))
  (ensures (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail)))
= object_rec_prereq j gprint l data l' s' j' q;
  let (data' : as_gtype j') =
    DependentMap.sel data s'
  in
  let objprint = gprint j' data' in
  let suff =
    if Cons? q
    then
      Seq.cons comma (gprint_object j gprint l data q)
    else
      Seq.empty
  in
  let esuff = Seq.append objprint suff in
  let pkey = gprint_string (Key?.s s') in
  let s1 = Seq.cons colon esuff in
  let s0 = Seq.append pkey s1 in
  let s = Seq.append s0 tail in
  let s2 = Seq.append s1 tail in
  let _ : squash (s == Seq.append pkey s2) =
    Seq.append_assoc pkey s1 tail
  in
  assert (Seq.length s2 < Seq.length s);
  let _ : squash (gparse_exact_string (Key?.s s') s == Some s2) =
    Seq.append_empty_l s;
    gparse_exact_string_gprint_string Seq.empty (Key?.s s') s2
  in
  let s3 = Seq.append esuff tail in
  let _ : squash (s2 == Seq.cons colon s3) =
    Seq.append_cons colon esuff tail
  in
  assert (Seq.length s3 < Seq.length s2);
  let _ : squash (gparse_exact_char colon s2 == Some s3) =
    Seq.append_empty_l s2;
    gparse_exact_char_append_cons Seq.empty colon s3
  in
  let s4 = Seq.append suff tail in
  let _ : squash (s3 == Seq.append objprint s4) =
    Seq.append_assoc objprint suff tail
  in
  let _ : squash (Seq.length s4 < Seq.length s3) =
    length_gprint j' data'
  in
  let (data0' : as_gtype j') =
    DependentMap.sel data0 s'
  in
  let _ : squash (gparse j' data0' (Seq.append (gprint j' data') s4) == Some (data', s4)) =
    let (j': json_schema { j' << j } ) = j' in
    let data0' : as_gtype j' = data0' in
    let data'  : as_gtype j' = data'  in
    ihgparse j' data0' data' s4
  in
  assert (gparse j' data0' s3 == Some (data', s4));
  let new_data0 = DependentMap.upd data0 s' data' in
  let new_l_left = List.Tot.append l_left [(s', j')] in
  let _ : squash (l == List.Tot.append new_l_left q) =
    List.Tot.append_cons_l (s', j') [] q;
    List.Tot.append_assoc l_left [(s', j')] q
  in
  let new_hsel
    (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst new_l_left)})
  : Lemma
    (DependentMap.sel new_data0 k == DependentMap.sel data k)
  = let _ : squash (List.Tot.mem k (List.Tot.map fst l_left) \/ k == s') =
      List.Tot.map_append fst l_left [(s', j')];
      List.Tot.append_mem (List.Tot.map fst l_left) [s'] k
    in
    if k = s'
    then DependentMap.sel_upd_same new_data0 s' data'
    else begin
      DependentMap.sel_upd_other new_data0 s' data' k;
      let (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) } ) = k in
      hsel k
    end
  in
  if Cons? q
  then gparse_object_gprint_object_aux_cons_cons
         j l data0 data tail l' l_left
	 ihgparse_object
	 s' j' q
	 s s2 s3
	 data' data0'
	 s4
	 new_l_left new_data0 new_hsel
  else gparse_object_gprint_object_aux_cons_nil
         j l data0 data tail l' l_left
	 s' j' q
	 s s2 s3
	 data' data0'
	 s4
	 new_l_left new_data0 new_hsel

let rec gparse_object_gprint_object_aux
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))  
  (tail: string)
  (ihgparse: (j': json_schema {j' << j}) -> (data0': as_gtype j') -> (data': as_gtype j') -> (tail': string) ->
    Lemma (gparse j' data0' (Seq.append (gprint j' data') tail') == Some (data', tail')))
  (l': list (key * json_schema) {List.Tot.strict_prefix_of l' l \/ l' == l})
  (l_left: list (key * json_schema) {l == List.Tot.append l_left l' } )
  (hsel: (k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) }) ->
    Lemma (DependentMap.sel data0 k == DependentMap.sel data k)
  )
: Lemma
  (requires True)
  (ensures (gparse_object j gparse l data0 l' (Seq.append (gprint_object j gprint l data l') tail) == Some (data, tail)))
  (decreases l')  
= match l' with
  | [] ->
    gparse_object_gprint_object_aux_nil j l data0 data tail l' l_left hsel
  | ((s', j') :: q) ->
    object_rec_prereq j gprint l data l' s' j' q;
    let ihgparse_object
      (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
      (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
      (tail: string)
      (l'': list (key * json_schema) {(List.Tot.strict_prefix_of l'' l \/ l'' == l) /\ l'' << l'})
      (l_left: list (key * json_schema) {l == List.Tot.append l_left l'' } )
      (hsel: (
	(k: key {List.Tot.mem k (List.Tot.map fst l) /\ List.Tot.mem k (List.Tot.map fst l_left) }) ->
	Lemma (DependentMap.sel data0 k == DependentMap.sel data k)
      ))
    : Lemma
      (ensures (gparse_object j gparse l data0 l'' (Seq.append (gprint_object j gprint l data l'') tail) == Some (data, tail)))
    = gparse_object_gprint_object_aux j l data0 data tail ihgparse l'' l_left hsel
    in
    gparse_object_gprint_object_aux_cons j l data0 data tail ihgparse l' l_left hsel ihgparse_object s' j' q

let gparse_object_gprint_object
  (j: json_schema)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data0: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (tail: string)
  (ihgparse: (j': json_schema {j' << j}) -> (data0': as_gtype j') -> (data': as_gtype j') -> (tail': string) ->
    Lemma (gparse j' data0' (Seq.append (gprint j' data') tail') == Some (data', tail')))
: Lemma
  (ensures (gparse_object j gparse l data0 l (Seq.append (gprint_object j gprint l data l) tail) == Some (data, tail)))
= List.Tot.append_nil_l l;
  gparse_object_gprint_object_aux j l data0 data tail ihgparse l [] (fun _ -> ())

let gparse_gprint_aux
  (j: json_schema)
  (data0: as_gtype j)
  (data: as_gtype j)
  (tail: string)
  (ihgparse: (j': json_schema {j' << j}) -> (data0': as_gtype j') -> (data': as_gtype j') -> (tail': string) ->
    Lemma (gparse j' data0' (Seq.append (gprint j' data') tail') == Some (data', tail')))
: Lemma
  (requires True)
  (ensures (gparse j data0 (Seq.append (gprint j data) tail) == Some (data, tail)))
  (decreases j)
= match j with
  | String ->
    Seq.append_empty_l (Seq.append (gprint j data) tail);
    gparse_string_gprint_string Seq.empty data tail;
    assert (gparse j data0 (Seq.append (gprint j data) tail) == Some (data, tail))
  | Object l ->
    let s = Seq.append (gprint j data) tail in
    as_gtype_object_eq l;
    let data : DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l) = data in      
    let s0 = gprint_object j gprint l data l in
    let s1 = Seq.snoc s0 right_brace in
    let s2 = Seq.cons left_brace s1 in
    assert_norm (gprint j data == s2);
    let s3 = Seq.append s1 tail in
    let s4 = Seq.cons left_brace s3 in
    let _ : squash (s == s4) =
      Seq.append_cons left_brace s1 tail
    in
    let _ : squash (gparse_exact_char left_brace s == Some s3) =
      Seq.append_empty_l s4;
      gparse_exact_char_append_cons Seq.empty left_brace s3
    in
    let s5 = Seq.cons right_brace tail in
    let _ : squash (s3 == Seq.append s0 s5) =
      Seq.append_cons_snoc s0 right_brace tail
    in
    let (data0 : DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l)) = data0 in
    let (data : DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l)) = data in
    let l0 = l in
    let (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j}) = l in
    let _ : squash (gparse_object j gparse l data0 l0 s3 == Some (data, s5)) =
      gparse_object_gprint_object j l data0 data s5 ihgparse;
      assert (gparse_object j gparse l data0 l0 s3 == Some (data, s5))
    in
    let _ : squash (gparse_exact_char right_brace s5 == Some tail) =
      Seq.append_empty_l s5;
      gparse_exact_char_append_cons Seq.empty right_brace tail
    in
    assert (gparse j data0 (Seq.append (gprint j data) tail) == gparse j data0 s);
    gparse_object_eq_some l data0 s s3 data s5 tail

let rec gparse_gprint
  (j: json_schema)
  (data0: as_gtype j)
  (data: as_gtype j)
  (tail: string)
: Lemma
  (requires True)
  (ensures (gparse j data0 (Seq.append (gprint j data) tail) == Some (data, tail)))
  (decreases j)
= let ihgparse
    (j': json_schema {j' << j})
    (data0': as_gtype j')
    (data': as_gtype j')
    (tail': string)
  : Lemma
    (gparse j' data0' (Seq.append (gprint j' data') tail') == Some (data', tail'))
  = gparse_gprint j' data0' data' tail'
  in
  gparse_gprint_aux j data0 data tail ihgparse
