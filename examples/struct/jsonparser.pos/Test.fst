module Test

let string : eqtype = Seq.seq Char.char

let string_of_char = Seq.create 1

let double_quote   : Char.char = Char.char_of_int 34
let s_double_quote : string    = string_of_char double_quote
let left_brace     : Char.char = Char.char_of_int 123
let s_left_brace   : string    = string_of_char left_brace
let right_brace    : Char.char = Char.char_of_int 123
let s_right_brace  : string    = string_of_char right_brace
let comma          : Char.char = Char.char_of_int 44
let s_comma        : string    = string_of_char comma
let colon          : Char.char = Char.char_of_int 58
let s_colon        : string    = string_of_char colon

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
  | String -> string
  | Object l ->
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) (fun (j' : json_schema {j' << Object l}) -> as_gtype j') l)

assume val as_gtype_object (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l)}) : Lemma
  (ensures (as_gtype (Object l) == DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type (Object l) (fun (j' : json_schema {j' << Object l}) -> as_gtype j') l))) // TODO: WHY WHY WHY does it NOT work by reflexivity?

let as_gtype_string: squash (as_gtype String == string) = ()

let rec as_value_type (j: json_schema) : Tot Type0 =
  match j with
  | String -> Buffer.buffer Char.char
  | Object l ->
    DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l) }) (object_as_type j as_value_type l)

let as_struct_ptr_type (j: json_schema) : Tot Type = Struct.struct_ptr (as_value_type j)

let rec object_gprint
  (j: json_schema)
  (gprint: (j': json_schema {j' << j}) -> (data: as_gtype j') -> GTot string)
  (l: list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ l << j})
  (data: DependentMap.t (s: key {List.Tot.mem s (List.Tot.map fst l)}) (object_as_type j as_gtype l))
  (l': list (key * json_schema) {List.Tot.noRepeats (List.Tot.map fst l) /\ (list_precedes l' l \/ l' == l)})
: GTot string
= match l' with
  | [] -> s_right_brace
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
    Seq.append (Key?.s s) (gprint j' data')

let rec gprint (j: json_schema) (data: as_gtype j) : GTot string =
  match j with
  | String -> data
  | Object l ->
    as_gtype_object l;
    list_precedes_or_eq_nil l;
    object_gprint j (fun (j': json_schema {j' << j}) data' -> gprint j' data') l data []

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
