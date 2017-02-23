module Test

let char   : eqtype = Char.char
let string : eqtype = Seq.seq char

let string_of_char (c: char): Tot string = Seq.cons c Seq.createEmpty

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


let rec list_precedes (#a: Type) (l1 l2: list a)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases l2)
= match l2 with
  | [] -> False
  | _ :: q -> l1 == q \/ list_precedes l1 q

let rec list_precedes_nil (#a: Type) (x: a) (l: list a)
: Lemma
  (requires True)
  (ensures (list_precedes [] (x::l)))
  (decreases l)
= match l with
  | [] -> ()
  | a' :: q -> list_precedes_nil a' q

let list_precedes_or_eq_nil (#a: Type) (l: list a)
: Lemma
  (ensures (list_precedes [] l \/ l == []))
= match l with
  | [] -> ()
  | a :: q -> list_precedes_nil a q

let list_precedes_cons (#a: Type) (x: a) (l: list a) :
  Lemma
  (ensures (list_precedes l (x::l)))
= ()

let rec list_precedes_trans (#a: Type) (l1 l2 l3: list a)
: Lemma
  (requires True)
  (ensures ((list_precedes l1 l2 /\ list_precedes l2 l3) ==> list_precedes l1 l3))
  (decreases l3)
= match l3 with
  | [] -> ()
  | _ :: q -> list_precedes_trans l1 l2 q

let rec list_precedes_correct (#a) (l1 l2: list a)
: Lemma
  (requires True)
  (ensures (list_precedes l1 l2 ==> l1 << l2))
  (decreases l2)
= match l2 with
  | [] -> ()
  | _ :: q ->
    list_precedes_correct l1 q

let rec map_list_precedes (#a #b: Type) (f: a -> Tot b) (l1: list a) (l2: list a) :
 Lemma
 (requires True)
 (ensures (list_precedes l1 l2 ==> list_precedes (List.Tot.map f l1) (List.Tot.map f l2)))
 (decreases l2)
= match l2 with
  | [] -> ()
  | a::q ->
    map_list_precedes f l1 q

let rec mem_list_precedes (#a: eqtype) (l1: list a) (m: a) (l2: list a)
: Lemma
  (requires True)
  (ensures ((List.Tot.mem m l1 /\ list_precedes l1 l2) ==> List.Tot.mem m l2))
= match l2 with
  | [] -> ()
  | a :: q ->
    mem_list_precedes l1 m q

let rec list_precedes_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures (list_precedes l1 l2 ==> (exists l3 . l2 == List.Tot.append l3 l1)))
= match l2 with
  | [] -> ()
  | a :: q ->
    FStar.Classical.or_elim
      #(l1 == q)
      #(list_precedes l1 q)
      #(fun _ -> exists l3 . l2 == List.Tot.append l3 l1)
      (fun _ ->
	FStar.Classical.exists_intro (fun l3 -> l2 == List.Tot.append l3 l1) (a :: []))
      (fun _ ->
	FStar.Classical.exists_elim
	  (exists l3 . l2 == List.Tot.append l3 l1)
	  #_
	  #(fun l3 -> q == List.Tot.append l3 l1)
	  (list_precedes_exists_append l1 q)
	  (fun l3 ->
	     FStar.Classical.exists_intro (fun l3 -> l2 == List.Tot.append l3 l1) (a :: l3)
	     ))

let list_precedes_or_eq_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures ((list_precedes l1 l2 \/ l1 == l2) ==> (exists l3 . l2 == List.Tot.append l3 l1)))
= FStar.Classical.or_elim
    #(list_precedes l1 l2)
    #(l1 == l2)
    #(fun _ -> exists l3 . l2 == List.Tot.append l3 l1)
    (fun _ ->
      list_precedes_exists_append l1 l2)
    (fun _ ->
	FStar.Classical.exists_intro
	  (fun l3 -> l2 == List.Tot.append l3 l1)
	  [] )

let precedes_tl
  (#a: Type)
  (l: list a {Cons? l})
: Lemma (ensures (List.Tot.tl l << l))
= ()

let rec precedes_append_cons_r
  (#a: Type)
  (l1: list a)
  (x: a)
  (l2: list a)
: Lemma
  (requires True)
  (ensures (x << List.Tot.append l1 (x :: l2)))
  [SMTPat (x << List.Tot.append l1 (x :: l2))]
= match l1 with
  | [] -> ()
  | _ :: q -> precedes_append_cons_r q x l2


let precedes_append_cons_prod_r
  (#a #b: Type)
  (l l1: list (a * b))
  (x: a)
  (y: b)
  (l2: list (a * b))
: Lemma
  (requires (l == List.Tot.append l1 ((x, y) :: l2)))
  (ensures (x << l /\ y << l))
  [SMTPatOr [ [ SMTPatT (x << l); SMTPatT (l == List.Tot.append l1 ((x, y) :: l2))] ; [SMTPatT (y << l); SMTPatT (l == List.Tot.append l1 ((x, y) :: l2))] ] ]
= precedes_append_cons_r l1 (x, y) l2

let rec object_as_type_append_cons
  (j: json_schema)
  (as_type: (j': json_schema {j' << j}) -> Tot Type0)
  (l: list (key * json_schema) {l << j})
  (s: key)
  (j': json_schema)
  (l' q: list (key * json_schema))
: Lemma
  (requires (List.Tot.noRepeats (List.Tot.map fst l)))
  (ensures ((l == List.Tot.append l' ((s, j') :: q)) ==> (let _ : squash (j' << l) =  precedes_append_cons_prod_r l l' s j' q in object_as_type j as_type l s == as_type j')))
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

let as_gtype_object (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)}) : Lemma
  (ensures 
   (as_gtype (Object l) ==
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) as_gtype l))) =
      assert_norm (as_gtype (Object l) ==
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) as_gtype l))

let as_gtype_string: squash (as_gtype String == (s: string { ~ (Seq.mem double_quote s ) } )) = ()

let rec as_value_type (j: json_schema) : Tot Type0 =
  match j with
  | String -> Buffer.buffer char
  | Object l ->
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type j as_value_type l)

let as_struct_ptr_type (j: json_schema) : Tot Type = Struct.struct_ptr (as_value_type j)

let gprint_string (s: string { ~ (Seq.mem double_quote s) } ) : GTot string =
  Seq.cons double_quote (Seq.snoc s double_quote)

let object_rec_prereq
  (j: json_schema)
  (gprint: (j': json_schema {j' << j}) -> (data: as_gtype j') -> GTot string)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {list_precedes l' l \/ l' == l})
  (s: key)
  (j': json_schema)
  (q: list (key * json_schema) { l' == ((s, j') :: q) } )
: Lemma
  (ensures
    ((list_precedes (List.Tot.map fst l') (List.Tot.map fst l) \/ List.Tot.map fst l' == List.Tot.map fst l)
    /\ List.Tot.mem s (List.Tot.map fst l)
    /\ object_as_type j as_gtype l s == as_gtype j'
    /\ j' << l
    /\ list_precedes q l))
=   map_list_precedes fst l' l;
    mem_list_precedes (List.Tot.map fst l') s (List.Tot.map fst l);
    list_precedes_trans q l' l;
    let (s: key {List.Tot.mem s (List.Tot.map fst l)}) = s in
    FStar.Classical.exists_elim
	(object_as_type j as_gtype l s == as_gtype j' /\ j' << l)
	#_
	#(fun l3 -> l == List.Tot.append l3 l')
	(list_precedes_or_eq_exists_append l' l)
	(fun l3 ->
          object_as_type_append_cons j as_gtype l s j' l3 q;
	  precedes_append_cons_prod_r l l3 s j' q
	  )

let rec gprint_object
  (j: json_schema)
  (gprint: (j': json_schema {j' << j}) -> (data: as_gtype j') -> GTot string)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {list_precedes l' l \/ l' == l})
: GTot string
= match l' with
  | [] -> Seq.createEmpty
  | ((s, j')::q) ->
    object_rec_prereq j gprint l data l' s j' q;
    let (data' : as_gtype j') =
      DependentMap.sel data s
    in
    let suff =
      if List.Tot.length q > 0
      then
	s_comma
      else
	Seq.createEmpty
    in
    Seq.append (gprint_string (Key?.s s))
      (Seq.cons colon
	(Seq.append
	  (gprint j' data')
	  suff))

let rec gprint (j: json_schema) (data: as_gtype j) : GTot string =
  match j with
  | String -> gprint_string data
  | Object l ->
    as_gtype_object l;
    list_precedes_or_eq_nil l;
    Seq.cons
      left_brace
      (Seq.snoc
	(gprint_object j (fun (j': json_schema {j' << j}) data' -> gprint j' data') l data [])
	right_brace)

let seq_is_suffix_of
  (#a: Type)
  (s_suff s: Seq.seq a)
= exists s_pref . (s == Seq.append s_pref s_suff)

let seq_cons_head_tail
  (#a: Type)
  (s: Seq.seq a {Seq.length s > 0})
: Lemma
  (requires True)
  (ensures (s == Seq.cons (Seq.head s) (Seq.tail s)))
  [SMTPat (Seq.cons (Seq.head s) (Seq.tail s))]
= let _ : squash (Seq.slice s 0 1 == Seq.create 1 (Seq.index s 0)) =
      Seq.lemma_index_slice s 0 1 0;
      Seq.lemma_index_create 1 (Seq.index s 0) 0;
      Seq.lemma_eq_elim (Seq.slice s 0 1) (Seq.create 1 (Seq.index s 0))
  in
  Seq.lemma_split s 1

let seq_head_cons
  (#a: Type)
  (x: a)
  (s: Seq.seq a)
: Lemma
  (ensures (Seq.head (Seq.cons x s) == x))
= ()

let seq_is_suffix_of_tail
  (#a: Type)
  (s: Seq.seq a {Seq.length s > 0})
: Lemma
  (requires True)
  (ensures ((Seq.tail s) `seq_is_suffix_of` s))
  [SMTPat ((Seq.tail s) `seq_is_suffix_of` s)]
= seq_cons_head_tail s    

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
: squash (gparse_whitespace Seq.createEmpty == Seq.createEmpty)
= ()

let seq_index_cons_l
  (#a: Type)
  (c: a)
  (s: Seq.seq a)
: Lemma
  (ensures (Seq.index (Seq.cons c s) 0 == c))
= ()

let seq_index_cons_r
  (#a: Type)
  (c: a)
  (s: Seq.seq a)
  (i: nat {1 <= i /\ i <= Seq.length s})
: Lemma
  (ensures (Seq.index (Seq.cons c s) i == Seq.index s (i - 1)))
= ()

let seq_append_cons
  (#a: Type)
  (c: a)
  (s1 s2: Seq.seq a)
: Lemma
  (ensures (Seq.append (Seq.cons c s1) s2 == Seq.cons c (Seq.append s1 s2)))
= Seq.lemma_eq_elim (Seq.append (Seq.cons c s1) s2) (Seq.cons c (Seq.append s1 s2))

let seq_index_tail
  (#a: Type)
  (s: Seq.seq a {Seq.length s > 0})
  (i: nat {i < Seq.length s - 1} )
: Lemma
  (ensures (Seq.index (Seq.tail s) i == Seq.index s (i + 1)))
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
    Seq.lemma_eq_elim s_white Seq.createEmpty;
    Seq.append_empty_l s
  end else begin
    let _ : squash (s_white == Seq.cons (Seq.head s_white) (Seq.tail s_white)) =
          seq_cons_head_tail s_white
    in
    let _ : squash (Seq.append s_white s == Seq.cons (Seq.head s_white) (Seq.append (Seq.tail s_white) s)) =
	  seq_append_cons (Seq.head s_white) (Seq.tail s_white) s
    in
    let s_white: (s_white: string {Seq.length s_white > 0 /\ ( forall (i: nat { i < Seq.length s_white } ) . is_whitespace (Seq.index s_white i)) } ) = s_white in
    let _ : squash (forall (i: nat {i < Seq.length (Seq.tail s_white) } ) . is_whitespace (Seq.index (Seq.tail s_white) i)) =
	  FStar.Classical.forall_intro (seq_index_tail s_white)
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
      Seq.createEmpty
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
	seq_append_cons (Seq.head s) s_white (gparse_whitespace (Seq.tail s));
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

let seq_mem_cons
  (#a:eqtype)
  (x:a)
  (s:Seq.seq a)
: Lemma
  (ensures (forall y. Seq.mem y (Seq.cons x s) <==> Seq.mem y s \/ x=y))
= Seq.lemma_append_count (Seq.create 1 x) s

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
      Seq.lemma_eq_elim left Seq.createEmpty;
      Seq.append_empty_l (Seq.cons double_quote right);
      Seq.lemma_tl double_quote right;
      Seq.append_empty_r accu
  end else begin
      seq_cons_head_tail left;
      seq_append_cons (Seq.head left) (Seq.tail left) (Seq.cons double_quote right);
      seq_mem_cons (Seq.head left) (Seq.tail left);
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
  | Some s_tail -> gparse_string_contents Seq.createEmpty s_tail
  | _ -> None

let not_mem_double_quote_gparse_string
  (s contents s': string)
: Lemma
  (requires (gparse_string s == Some (contents, s')))
  (ensures (~ (Seq.mem double_quote contents)))
= match gparse_exact_char double_quote s with
  | Some s_tail -> begin
      not_mem_double_quote_gparse_string_contents Seq.createEmpty s_tail contents s';
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
  let _ : squash (gparse_string_contents Seq.createEmpty s2 == Some (Seq.append Seq.createEmpty s_contents, s_tail)) =
      gparse_string_contents_append_cons Seq.createEmpty s_contents s_tail
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
    seq_append_cons double_quote (Seq.snoc s_contents double_quote) s_tail;
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
    let _ = length_gparse_string_contents Seq.createEmpty s_tail contents s' in
    Seq.append_empty_l contents

let rec list_memP_precedes
  (#a: Type)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (List.Tot.memP x l ==> x << l))
  (decreases l)
= match l with
  | [] -> ()
  | y :: q ->
    FStar.Classical.or_elim
      #(x == y)
      #(List.Tot.memP x q)
      #(fun _ -> x << l)
      (fun _ -> ())
      (fun _ -> list_memP_precedes x q)

let list_assoc_precedes
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a * b))
  (y: b)
: Lemma
  (requires (List.Tot.assoc x l == Some y))
  (ensures (x << l /\ y << l))
= List.Tot.assoc_memP_some x y l;
  list_memP_precedes (x, y) l

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
    let _ = Seq.lemma_eq_elim against Seq.createEmpty in
    Seq.append_empty_l tail
  else
    let _ = seq_cons_head_tail against in
    let _ = seq_append_cons (Seq.head against) (Seq.tail against) tail in
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
    seq_append_cons double_quote (Seq.snoc against double_quote) tail;
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
  (l': list (key * json_schema) {list_precedes l' l \/ l' == l})
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
	  if List.Tot.length q > 0
	  then Some (new_data, s3)
	  else begin match gparse_exact_char comma s3 with
	  | None -> None
	  | Some s4 ->
	    let _ = length_gparse_exact_char comma s3 s4 in
	    begin match gparse_object j gparse l new_data q s4 with
	    | None -> None
	    | Some (new_data_, s5) ->
	      let (s6: string {Seq.length s6 <= Seq.length s}) = s5 in
	      Some (new_data_, s6)
	    end
	  end
	end
      end
    end

(*
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
    as_gtype_object l;
    list_precedes_or_eq_nil l;
    let s1 = gparse_whitespace s in
    let _ = length_gparse_whitespace s in
    if Seq.length s1 = 0
    then None
    else if Seq.head s1 <> left_brace
    then None
    else let s2 = Seq.tail s1 in
	 let gparse_rec
	   (j': json_schema {j' << j})
	   (data': as_gtype j')
	   (s': string)
	 : GTot (option (as_gtype j' * (s'': string {Seq.length s'' < Seq.length s'})))
	 = gparse j' data' s'
	 in
	 match gparse_object j gparse_rec l data (List.Tot.map fst l) s2 with
	 | None -> None
	 | Some (new_data, s3) ->
	   let s4 = gparse_whitespace s3 in
	   let _ = length_gparse_whitespace s3 in
	   if Seq.length s4 = 0
	   then None
	   else if Seq.head s4 <> right_brace
	   then None
	   else Some (new_data, Seq.tail s4)
*)
