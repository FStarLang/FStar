module RecordFieldAttributes

module T = FStar.Tactics

type description (d : string) = ()

type r = 
    {
        #[@@@ (description "This is a number") ] field1 : int;
        #[@@@ (description "This is a string") ] field2 : string;
    }

type r2 = 
    {
        [@@@ (description "This is a number") ] field1_explicit : int;
        [@@@ (description "This is a string") ] field2_explicit : string;
    }

// Compares if two fully qualified names are equal
let rec fv_eq (fv1 : list string) (fv2 : list string) : bool = 
    match fv1, fv2 with
    | [], [] -> true
    | x :: xs, y :: ys -> if x = y then fv_eq xs ys else false
    | _, _ -> false

let unpack_field (b : T.binder) : T.Tac (string * option T.term * T.term) = 
    let (bv, (_, attrs)) =
      let bview = T.inspect_binder b in
      bview.binder_bv, (bview.binder_qual, bview.binder_attrs) in
    let attr_opt = match attrs with | [] -> None | _ -> Some (FStar.List.Tot.hd attrs) in
    let bvv = T.inspect_bv bv in
    (T.name_of_bv bv, attr_opt, T.binder_sort b)

// returns a list of (field name, optional attribute, field type)
let rec unpack_fields (qname : list string) (ty : T.term) : T.Tac (list (string * option T.term * T.term)) = 
    // type of the constructor should contain an Arrow type (there's at least one field in a record)
    match T.inspect_ln ty with
    | T.Tv_Arrow binder comp -> begin
        let f = unpack_field binder in
        match T.inspect_comp comp with
        | T.C_Total ty2 -> f :: unpack_fields qname ty2
        | _ -> T.fail "Unsupported computation type"
        end
    | T.Tv_FVar fv -> begin
        // The most inner part of 'ty' should be the name of the record type
        let qname2 = T.inspect_fv fv in
        if fv_eq qname qname2
            then []
            else T.fail ("Expected " ^ (T.implode_qn qname) ^ " got " ^ (T.implode_qn qname2))
        end
    | _ -> T.fail "Expected an arrow type"

let get_record_fields (env : T.env) (qname : list string) : T.Tac (list (string * option T.term * T.term)) = 
    match T.lookup_typ env qname with
    | Some s -> begin
        // Check if sig in an enum definition
        match T.inspect_sigelt s with
        | T.Sg_Inductive _ _ _ _ cts -> begin
            if List.Tot.length cts = 1
                then unpack_fields qname (snd (List.Tot.hd cts))
                else T.fail "Expected record, got inductive with more than one constructor"
            end
        | _ -> T.fail ("Expected inductive, got " ^ (T.term_to_string (T.pack (T.Tv_FVar (T.pack_fv qname)))))
        end
    | None -> T.fail ("Could not find type " ^ (T.implode_qn qname))

let validate_attribute (expectedDescription : string) (attr : T.term) : T.Tac unit = 
    match T.inspect_ln attr with
    | T.Tv_App attr_type (attr_value, _) -> begin
        match T.inspect_ln attr_type, T.inspect_ln attr_value with
        | T.Tv_FVar fv, T.Tv_Const c -> begin
            let desc = 
                match c with 
                | T.C_String d -> d
                | _ -> T.fail "Expected description to be string"
            in
            let _ = 
                if fv_eq ([ "RecordFieldAttributes"; "description" ]) (T.inspect_fv fv) 
                then ()
                else T.fail "Bad attribute"
            in
            if expectedDescription = desc then () else T.fail "Bad description"
            end
        | _ -> T.fail "Expected Tv_FVar"
        end
    | _ -> T.fail "Unexpected shape of the attribute"

let _ =
    assert True by begin
        let fields = get_record_fields (T.top_env ()) (T.explode_qn (`%r)) in
        let field1, field2 = 
            match fields with 
            | field1 :: field2 :: [] -> (field1, field2)
            | _ -> T.fail "Expected 2 fields"
        in 
        let (name1, attr1_opt, _) = field1 in
        let (name2, attr2_opt, _) = field2 in
        T.print name1;
        T.print name2;
        match attr1_opt with 
        | Some attr -> validate_attribute "This is a number" attr
        | _ -> T.fail "Expected attribute on field1 to be present";
        match attr2_opt with 
        | Some attr -> validate_attribute "This is a string" attr
        | _ -> T.fail "Expected attribute on field2 to be present"
    end 

let _ = 
        assert True by begin
        let fields = get_record_fields (T.top_env ()) (T.explode_qn (`%r2)) in
        let field1, field2 = 
            match fields with 
            | field1 :: field2 :: [] -> (field1, field2)
            | _ -> T.fail "Expected 2 fields"
        in 
        let (name1, attr1_opt, _) = field1 in
        let (name2, attr2_opt, _) = field2 in
        T.print name1;
        T.print name2;
        match attr1_opt with 
        | Some attr -> validate_attribute "This is a number" attr
        | _ -> T.fail "Expected attribute on field1 to be present";
        match attr2_opt with 
        | Some attr -> validate_attribute "This is a string" attr
        | _ -> T.fail "Expected attribute on field2 to be present"
    end
