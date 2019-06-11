#light "off"

module FStar.SMTEncoding.QIReport
open FStar
open FStar.All
open FStar.Common
open FStar.List
open FStar.Range
open FStar.Syntax.Syntax
open FStar.Syntax
open FStar.Util
open FStar.SMTEncoding.Term
open FStar.BaseTypes
module DEP = FStar.Parser.Dep

let max (i : int) (j : int) : int = if i < j then j else i

type pretty_alignment =
    | PrettyLeft
    | PrettyRight
    | PrettyMark of string

let prettyprint_table (fmt : list<pretty_alignment>) (tab : list<(list<string>)>) : string * int =
    let max (i : int) (j : int) : int = if i < j then j else i in
    let mark_split (align : pretty_alignment) (s : string) : (string * string) = match align with
        | PrettyLeft -> ("" , s)
        | PrettyRight -> (s , "")
        | PrettyMark sep -> 
            let spl : list<string> = split s sep in
            ((List.hd spl) ^ sep , List.tl spl |> String.concat sep)
    in
    let len (align : pretty_alignment) ((l , r) : (int * int)) (s : string) : (int * int) =
        let (ls , rs) : (string * string) = mark_split align s in
        let (lx , rx) : (int * int) = (String.length ls , String.length rs) in
        ((max l lx) , (max r rx))
    in
    let rec maxlength (fmt : list<pretty_alignment>) (ln : list<(int * int)>) (row : list<string>) : list<(int * int)> = match (fmt , ln , row) with
        | (fmt_hd :: fmt_tl , ln_hd :: ln_tl , row_hd :: row_tl) ->
            (len fmt_hd ln_hd row_hd) :: (maxlength fmt_tl ln_tl row_tl)
        | _ -> []
    in
    let maxlength_init : list<(int * int)> = tabulate (List.length fmt) (fun _ -> (0 , 0)) in
    let maxlength_list : list<(int * int)> = List.fold_left (maxlength fmt) maxlength_init tab in
    let totallength : int = List.fold_left (fun (x : int) ((l , r) : int * int) -> x + l + r) 0 maxlength_list in
    let enlarge ((sl , sr) : (string * string)) ((l , r) : (int * int)) : string =
        (repeat (l - String.length sl) " ") ^ sl ^ sr ^ (repeat (r - String.length sr) " ")
    in
    let rec enlarge_row (fmt : list<pretty_alignment>) (ln : list<(int * int)>) (row : list<string>) : list<string> = match (fmt , ln , row) with
        | (fmt_hd :: fmt_tl , (ln_l , ln_r) :: ln_tl , row_hd :: row_tl) ->
            let (sl , sr) : (string * string) = mark_split fmt_hd row_hd in
            (enlarge (sl , sr) (ln_l , ln_r)) :: (enlarge_row fmt_tl ln_tl row_tl)
        | _ -> []
    in
    let lines : list<string> = List.map (enlarge_row fmt maxlength_list) tab |> List.map (fun l -> String.concat "  " l) in
    let totallength : int = List.fold_left (fun (x : int) (s : string) -> max x (String.length s)) 0 lines in
    (lines |> String.concat "\n" , totallength)

type query_info = {
    query_info_name    : string ;
    query_info_index   : int ;
    query_info_range   : Range.range ;
}

type qiprofile_map = psmap<(int * int * int)>

type quantifier_info = {
    quantifier_info_query : query_info ;
    quantifier_info_quantifier : term ;
    quantifier_info_context : term ;
}

type qiprofile = {
    qiprofile_id : string ;
    qiprofile_quantifiers : list<quantifier_info> ;
    qiprofile_instances : int ;
    qiprofile_generation : int ;
    qiprofile_cost : int ;
}

let query_name (q : query_info) : string =
    let fn : string = file_of_range q.query_info_range in
    let rg : string = if String.length fn = 0 || char_at fn 0 = '<' then "" else
        let s1 : string = q.query_info_range |> start_of_range |> string_of_pos in
        let s2 : string = q.query_info_range |> end_of_range |> string_of_pos in
        format " (%s-%s)" [s1 ; s2]
    in
    "(" ^ q.query_info_name ^ " , " ^ (string_of_int q.query_info_index) ^ ") from " ^ fn ^ rg

let quantifier_file (q : quantifier_info) : string = file_of_range (q.quantifier_info_quantifier.rng)

let quantifier_module (q : quantifier_info) : string =
    let fn : string = quantifier_file q in
    if String.length fn = 0 || char_at fn 0 = '<' then fn else DEP.module_name_of_file fn

let quantifier_range (q : quantifier_info) : string =
    let fn : string = quantifier_file q in
    if String.length fn = 0 || char_at fn 0 = '<' then "" else
        let s1 : string = q.quantifier_info_quantifier.rng |> start_of_range |> string_of_pos in
        let s2 : string = q.quantifier_info_quantifier.rng |> end_of_range |> string_of_pos in
        format "(%s-%s)" [s1 ; s2]

let parse_qiprofile (s : string) : qiprofile_map =
    let parse_line (line : string) : option<(string * int * int * int)> =
        if starts_with line "[quantifier_instances]" then begin
            match split (substring_from line 22) ":" |> List.map trim_string with
                | [id ; inst ; gen ; cost] -> Some (id , int_of_string inst , int_of_string gen , int_of_string cost)
                | _ -> failwith "could not parse quantifier instantiation info"
        end else None
    in
    let comp ((qid1 , inst1 , gen1 , cost1) : string * int * int * int) ((qid2 , inst2 , gen2 , cost2) : string * int * int * int) : int = 
        compare qid1 qid2
    in
    let conflate (l : list<(string * int * int * int)>): list<(string * int * int * int)> =
        let rec aux (qid : string) (inst : int) (gen : int) (cost : int) (l : list<(string * int * int * int)>) (o : list<(string * int * int * int)>) =
            match l with
                | [] -> List.rev ((qid , inst , gen , cost) :: o)
                | (hd_qid , hd_inst , hd_gen , hd_cost) :: tl ->
                    if hd_qid = qid then aux qid (inst + hd_inst) (max gen hd_gen) (max cost hd_cost) tl o
                    else aux hd_qid hd_inst hd_gen hd_cost tl ((qid , inst , gen , cost) :: o)
        in
        match l with
            | [] -> []
            | (qid , inst , gen , cost) :: tl -> aux qid inst gen cost l []
    in
    let add (o : qiprofile_map) ((qid , inst , gen , cost) : (string * int * int * int)) : qiprofile_map =
        psmap_add o qid (inst , gen , cost)
    in
    String.split ['\n'] s |>
        List.map trim_string |>
        List.map parse_line |>
        collect_some |>
        sort_with comp |>
        conflate |>
        List.fold_left add (psmap_empty ())
    

let rec extract_quantifiers_from_decls (query : query_info) (decl : decl) : list<(string * quantifier_info)> =
    let from_term (context : term) (tm0 : term) : list<(string * quantifier_info)> =
        let rec aux (tm : term) : list<(string * quantifier_info)> = match tm.tm with
            | App (_ , tms) -> List.flatten (List.map aux tms)
            | Quant (_ , _ , _ , _ , t , qid) -> begin match !qid with
                | Some id -> (id , {
                        quantifier_info_query = query ;
                        quantifier_info_quantifier = tm ;
                        quantifier_info_context = context }) :: (aux t)
                | None ->
                    print ("Could not extract quantifiers from SMT term:\n" ^ (print_smt_term tm) ^ "\n") [] ;
                    aux t
            end
            | Let (tms , t) -> (aux t) @ (List.collect aux tms)
            | Labeled (t , _ , _)
            | LblPos (t , _) -> aux t
            | _ -> []
        in
        aux tm0
    in
    match decl with
        | DefineFun (nm , args , ret , tm , _) -> from_term tm tm
        | Assume a -> from_term a.assumption_term a.assumption_term
        | Module (s , ds) -> extract_quantifiers (query , ds)
        | _ -> []

and extract_quantifiers ((query , decls) : query_info * list<decl>) : list<(string * quantifier_info)> =
    List.fold_left (fun (l : list<(string * quantifier_info)>) (d : decl) -> (extract_quantifiers_from_decls query d) @ l) [] decls
    

let profile_quantifiers (queries : list<(query_info * list<decl>)>) (qiprofile_output : string) : psmap<qiprofile> =
    let comp ((id1 , q1) : (string * quantifier_info)) ((id2 , q2) : (string * quantifier_info)) : int = 
        compare id1 id2
    in
    let conflate (l : list<(string * quantifier_info)>) : list<(string * list<quantifier_info>)> =
        let rec aux (i : list<(string * quantifier_info)>) (id : string) (ls : list<quantifier_info>) (o : list<(string * list<quantifier_info>)>) : list<(string * list<quantifier_info>)> =
            match i with
                | (idx , qinfo) :: tl ->
                    if id = idx then aux tl id (qinfo :: ls) o
                    else aux tl idx [qinfo] ((id , List.rev ls) :: o)
                | [] -> (id , List.rev ls) :: o
        in
        match l with
            | [] -> []
            | (s , q) :: tl -> List.rev (aux tl s [q] [])
    in
    let remove_duplicates (l : list<quantifier_info>) : list<quantifier_info> =
        let equal_range (q1 : quantifier_info) (q2 : quantifier_info) : bool =
            (quantifier_file q1 = quantifier_file q2) && (quantifier_range q1 = quantifier_range q2)
        in
        let rec rm (q : quantifier_info) (i : list<quantifier_info>) (o : list<quantifier_info>) : list<quantifier_info> =
            match i with
                | hd :: tl -> rm q tl (if equal_range hd q then o else hd :: o)
                | [] -> List.rev o
        in
        let rec aux (i : list<quantifier_info>) (o : list<quantifier_info>) =
            match i with
                | hd :: tl -> aux (rm hd i []) (hd :: o)
                | [] -> List.rev o
        in
        aux l []
    in
    let qip : qiprofile_map = parse_qiprofile qiprofile_output in
    let insert (o : psmap<qiprofile>) ((id , info) : string * list<quantifier_info>) : psmap<qiprofile> =
        let (inst , gen , cost) : (int * int * int) = match psmap_try_find qip id with
            | None -> (0 , 0 , 0)
            | Some x -> x
        in
        let value = {
            qiprofile_id = id ;
            qiprofile_quantifiers = info ;
            qiprofile_instances = inst ;
            qiprofile_generation = gen ;
            qiprofile_cost = cost ; }
        in
        psmap_add o id value
    in
    List.collect extract_quantifiers queries |> 
    sort_with comp |>
    conflate |>
    List.map (fun ((s , q) : string * list<quantifier_info>) -> (s , remove_duplicates q)) |>
    List.fold_left insert (psmap_empty ())

let tabular_profile (q : psmap<qiprofile>) : list<(list<string>)> =
    let comp ((i1 , q1) : int * string) ((i2 , q2) : int * string) : int = if i1 < i2 then 1 else (if i1 > i2 then -1 else 0) in
    let qid_to_tail_rows (info : quantifier_info) : list<string> =
        [ "" ; "" ; quantifier_module info ; quantifier_file info ; quantifier_range info ]
    in
    let qid_to_rows (o : list<(list<string>)>) (k : string) : list<(list<string>)> =
        let prof : qiprofile = must (psmap_try_find q k) in
        if prof.qiprofile_instances > 0 then
            match prof.qiprofile_quantifiers with
                | [] -> failwith "QID not found"
                | hd :: tl ->
                    o @ ([ prof.qiprofile_id ;
                            string_of_int (prof.qiprofile_instances) ;
                            quantifier_module hd ;
                            quantifier_file hd ;
                            quantifier_range hd ] :: (List.map qid_to_tail_rows tl))
        else o
    in
    psmap_fold q (fun (k : string) (v : qiprofile) (acc : list<(int * string)>) -> (v.qiprofile_instances , k) :: acc) [] |>
    sort_with comp |>
    List.map (fun ((i , q) : int * string) -> q) |>
    List.fold_left qid_to_rows []
    
let qiprofile_analysis (queries : list<(query_info * list<decl>)>) (qiprofile_output : string) : unit =
    match queries with
        | [] -> ()
        | _ -> 
            let q : psmap<qiprofile> = profile_quantifiers queries qiprofile_output in
            let tab : list<(list<string>)> = tabular_profile q in
            let fmt : list<pretty_alignment> = [PrettyRight ; PrettyRight ; PrettyLeft ; PrettyRight ; PrettyLeft] in
            let (content_string , content_length) : string * int = prettyprint_table fmt tab in
            let (header_string , header_length) : string * int =
                let headers : list<string> = queries |> List.map (fun ((q , ds) : query_info * list<decl>) -> query_name q) in
                String.concat "\n" headers , List.fold_left (fun (x : int) (s : string) -> max x (String.length s)) 0 headers
            in
            let line : string = repeat (max content_length header_length) "-" in
            print (line ^ "\n" ^ header_string ^ "\n" ^ line ^ "\n" ^ content_string ^ "\n" ^ line ^ "\n\n" ) []
