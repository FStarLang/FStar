module Test

let char   : eqtype = Char.char
let string : eqtype = Seq.seq char

let string_of_char = Seq.create 1

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

let rec object_as_type_noRepeats 
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
	object_as_type_noRepeats j as_type (List.Tot.tl l) s j' q' q
	  )
	  
let rec as_gtype (j: json_schema) : Tot Type0 =
  match j with
  | String -> (s: string { ~ (Seq.mem double_quote s) } )
  | Object l ->
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) (fun (j' : json_schema {j' << Object l}) -> as_gtype j') l)

assume val as_gtype_object (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)}) : Lemma
  (ensures (as_gtype (Object l) == DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) (fun (j' : json_schema {j' << Object l}) -> as_gtype j') l))) // TODO: WHY WHY WHY does it NOT work by reflexivity?

let as_gtype_string: squash (as_gtype String == (s: string { ~ (Seq.mem double_quote s ) } )) = ()

let rec as_value_type (j: json_schema) : Tot Type0 =
  match j with
  | String -> Buffer.buffer char
  | Object l ->
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type j as_value_type l)

let as_struct_ptr_type (j: json_schema) : Tot Type = Struct.struct_ptr (as_value_type j)

let gprint_string (s: string { ~ (Seq.mem double_quote s) } ) : GTot string =
  Seq.cons double_quote (Seq.snoc s double_quote)

let rec object_gprint
  (j: json_schema)
  (gprint: (j': json_schema {j' << j}) -> (data: as_gtype j') -> GTot string)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ (list_precedes l' l \/ l' == l)})
: GTot string
= match l' with
  | [] -> Seq.createEmpty
  | ((s, j')::q) ->
    map_list_precedes fst l' l;
    mem_list_precedes (List.Tot.map fst l') s (List.Tot.map fst l);
    let (s: key {List.Tot.mem s (List.Tot.map fst l)}) = s in
    FStar.Classical.exists_elim
	(object_as_type j as_gtype l s == as_gtype j' /\ j' << l)
	#_
	#(fun l3 -> l == List.Tot.append l3 l')
	(list_precedes_or_eq_exists_append l' l)
	(fun l3 ->
          object_as_type_noRepeats j as_gtype l s j' l3 q;
	  precedes_append_cons_prod_r l l3 s j' q
	  );
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
	(object_gprint j (fun (j': json_schema {j' << j}) data' -> gprint j' data') l data [])
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

let gparse_char
  (#t: Type)
  (s: string)
  (f: (char -> GTot bool))
  (cont_true: ((c: char {f c}) -> (s': string {s == Seq.cons c s'}) -> GTot (option t)))
  (cont_false: option t)
: GTot (option t)
= if Seq.length s = 0
  then None
  else if f (Seq.head s)
  then let _ : squash (1 <= Seq.length s) = () in
       cont_true (Seq.head s) (Seq.tail s)
  else cont_false

let gparse_char_head_tail_true
  (#t: Type)
  (s: string { Seq.length s > 0 } )
  (f: (char -> GTot bool) { f (Seq.head s) } )
  (cont_true: ((c: char {f c}) -> string -> GTot (option t)))
  (cont_false: option t)
: Lemma
  (ensures (gparse_char s f cont_true cont_false == cont_true (Seq.head s) (Seq.tail s)))
= ()

let gparse_char_head_tail_false
  (#t: Type)
  (s: string { Seq.length s > 0 } )
  (f: (char -> GTot bool) { ~ (f (Seq.head s)) } )
  (cont_true: ((c: char {f c}) -> string -> GTot (option t)))
  (cont_false: (option t))
: Lemma
  (ensures (gparse_char s f cont_true cont_false == cont_false))
= ()

let gparse_char_cons_true
  (#t: Type)
  (f: (char -> GTot bool))
  (c: char {f c} )
  (s: string)
  (cont_true: ((c': char {f c' }) -> (s': string {Seq.cons c s == Seq.cons c' s'}) -> GTot (option t)))
  (cont_false: option t)
: Lemma
  (ensures (gparse_char (Seq.cons c s) f cont_true cont_false == cont_true c s))
= Seq.lemma_tl c s

let gparse_char_cons_false
  (#t: Type)
  (f: (char -> GTot bool))
  (c: char {~ (f c)} )
  (s: string)
  (cont_true: ((c': char {f c' }) -> (s': string {Seq.cons c s == Seq.cons c' s'}) -> GTot (option t)))
  (cont_false: option t)
: Lemma
  (ensures (gparse_char (Seq.cons c s) f cont_true cont_false == cont_false))
= ()

let gparse_char_is_some
  (#t: Type)
  (s: string)
  (f: (char -> GTot bool))
  (cont_true: ((c: char {f c}) -> (s': string {s == Seq.cons c s'}) -> GTot (option t)))
  (cont_false: option t)
: Lemma
  (requires ((forall c s . Some? (cont_true c s)) /\ Some? (cont_false) /\ Seq.length s > 0))
  (ensures (Some? (gparse_char s f cont_true cont_false)))
= ()

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
  else
    let cont_true (c: char {is_whitespace c}) (s': string {s == Seq.cons c s'}) = 
      Some (gparse_whitespace s')
    in
    let cont_false = Some s in
    gparse_char_is_some s is_whitespace cont_true cont_false;
    Some?.v (gparse_char s is_whitespace cont_true cont_false)

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
    let _ : squash (gparse_whitespace (Seq.append s_white s) == gparse_whitespace (Seq.append (Seq.tail s_white) s)) =
	  gparse_char_cons_true is_whitespace (Seq.head s_white) (Seq.append (Seq.tail s_white) s) (fun c' s' -> Some (gparse_whitespace s')) (Some s)
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


(*

    let (l: list (key * json_schema)
    assert (l << j);
    let (data : DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_gtype j as_gtype l)) = data in
    let rec aux (l': list (key * json_schema) {l' << l \/ l' == l}) =
      match l' with
	| [] -> s_right_brace
	| ((s, j')::q) -> let (data' : as_gtype j' ) = (DependentMap.sel data s) in Seq.append s_double_quote (Seq.append (Key?._0 s) (Seq.append s_double_quote (Seq.append s_colon (Seq.append (gprint j' data') s_right_brace))))
    in Seq.append s_left_brace (aux l)
*)
