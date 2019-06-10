open Prims
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun i  -> fun j  -> if i < j then j else i 
type pretty_alignment =
  | PrettyLeft 
  | PrettyRight 
  | PrettyMark of Prims.string 
let (uu___is_PrettyLeft : pretty_alignment -> Prims.bool) =
  fun projectee  ->
    match projectee with | PrettyLeft  -> true | uu____46 -> false
  
let (uu___is_PrettyRight : pretty_alignment -> Prims.bool) =
  fun projectee  ->
    match projectee with | PrettyRight  -> true | uu____57 -> false
  
let (uu___is_PrettyMark : pretty_alignment -> Prims.bool) =
  fun projectee  ->
    match projectee with | PrettyMark _0 -> true | uu____70 -> false
  
let (__proj__PrettyMark__item___0 : pretty_alignment -> Prims.string) =
  fun projectee  -> match projectee with | PrettyMark _0 -> _0 
let (prettyprint_table :
  pretty_alignment Prims.list ->
    Prims.string Prims.list Prims.list -> (Prims.string * Prims.int))
  =
  fun fmt  ->
    fun tab  ->
      let max1 i j = if i < j then j else i  in
      let mark_split align s =
        match align with
        | PrettyLeft  -> ("", s)
        | PrettyRight  -> (s, "")
        | PrettyMark sep ->
            let spl = FStar_Util.split s sep  in
            let uu____177 =
              let uu____179 = FStar_List.hd spl  in
              Prims.op_Hat uu____179 sep  in
            let uu____182 =
              let uu____184 = FStar_List.tl spl  in
              FStar_All.pipe_right uu____184 (FStar_String.concat sep)  in
            (uu____177, uu____182)
         in
      let len align uu____222 s =
        match uu____222 with
        | (l,r) ->
            let uu____249 = mark_split align s  in
            (match uu____249 with
             | (ls,rs) ->
                 let uu____268 = uu____249  in
                 let uu____275 =
                   ((FStar_String.length ls), (FStar_String.length rs))  in
                 (match uu____275 with
                  | (lx,rx) ->
                      let uu____296 = uu____275  in
                      let uu____303 = max1 l lx  in
                      let uu____305 = max1 r rx  in (uu____303, uu____305)))
         in
      let rec maxlength fmt1 ln row =
        match (fmt1, ln, row) with
        | (fmt_hd::fmt_tl,ln_hd::ln_tl,row_hd::row_tl) ->
            let uu____426 = len fmt_hd ln_hd row_hd  in
            let uu____433 = maxlength fmt_tl ln_tl row_tl  in uu____426 ::
              uu____433
        | uu____448 -> []  in
      let maxlength_init =
        FStar_Common.tabulate (FStar_List.length fmt)
          (fun uu____490  -> ((Prims.parse_int "0"), (Prims.parse_int "0")))
         in
      let maxlength_list =
        FStar_List.fold_left (maxlength fmt) maxlength_init tab  in
      let totallength =
        FStar_List.fold_left
          (fun x  ->
             fun uu____530  -> match uu____530 with | (l,r) -> (x + l) + r)
          (Prims.parse_int "0") maxlength_list
         in
      let enlarge uu____568 uu____569 =
        match (uu____568, uu____569) with
        | ((sl,sr),(l,r)) ->
            let uu____620 =
              FStar_Util.repeat (l - (FStar_String.length sl)) " "  in
            let uu____623 =
              let uu____625 =
                let uu____627 =
                  FStar_Util.repeat (r - (FStar_String.length sr)) " "  in
                Prims.op_Hat sr uu____627  in
              Prims.op_Hat sl uu____625  in
            Prims.op_Hat uu____620 uu____623
         in
      let rec enlarge_row fmt1 ln row =
        match (fmt1, ln, row) with
        | (fmt_hd::fmt_tl,(ln_l,ln_r)::ln_tl,row_hd::row_tl) ->
            let uu____736 = mark_split fmt_hd row_hd  in
            (match uu____736 with
             | (sl,sr) ->
                 let uu____752 = uu____736  in
                 let uu____759 = enlarge (sl, sr) (ln_l, ln_r)  in
                 let uu____765 = enlarge_row fmt_tl ln_tl row_tl  in
                 uu____759 :: uu____765)
        | uu____770 -> []  in
      let lines =
        let uu____795 = FStar_List.map (enlarge_row fmt maxlength_list) tab
           in
        FStar_All.pipe_right uu____795
          (FStar_List.map (fun l  -> FStar_String.concat "  " l))
         in
      let totallength1 =
        FStar_List.fold_left
          (fun x  -> fun s  -> max1 x (FStar_String.length s))
          (Prims.parse_int "0") lines
         in
      let uu____836 = FStar_All.pipe_right lines (FStar_String.concat "\n")
         in
      (uu____836, totallength1)
  
type query_info =
  {
  query_info_name: Prims.string ;
  query_info_index: Prims.int ;
  query_info_range: FStar_Range.range }
let (__proj__Mkquery_info__item__query_info_name :
  query_info -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { query_info_name; query_info_index; query_info_range;_} ->
        query_info_name
  
let (__proj__Mkquery_info__item__query_info_index : query_info -> Prims.int)
  =
  fun projectee  ->
    match projectee with
    | { query_info_name; query_info_index; query_info_range;_} ->
        query_info_index
  
let (__proj__Mkquery_info__item__query_info_range :
  query_info -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { query_info_name; query_info_index; query_info_range;_} ->
        query_info_range
  
type qiprofile_map = (Prims.int * Prims.int * Prims.int) FStar_Util.psmap
type quantifier_info =
  {
  quantifier_info_query: query_info ;
  quantifier_info_quantifier: FStar_SMTEncoding_Term.term ;
  quantifier_info_context: FStar_SMTEncoding_Term.term }
let (__proj__Mkquantifier_info__item__quantifier_info_query :
  quantifier_info -> query_info) =
  fun projectee  ->
    match projectee with
    | { quantifier_info_query; quantifier_info_quantifier;
        quantifier_info_context;_} -> quantifier_info_query
  
let (__proj__Mkquantifier_info__item__quantifier_info_quantifier :
  quantifier_info -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { quantifier_info_query; quantifier_info_quantifier;
        quantifier_info_context;_} -> quantifier_info_quantifier
  
let (__proj__Mkquantifier_info__item__quantifier_info_context :
  quantifier_info -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { quantifier_info_query; quantifier_info_quantifier;
        quantifier_info_context;_} -> quantifier_info_context
  
type qiprofile =
  {
  qiprofile_id: Prims.string ;
  qiprofile_quantifiers: quantifier_info Prims.list ;
  qiprofile_instances: Prims.int ;
  qiprofile_generation: Prims.int ;
  qiprofile_cost: Prims.int }
let (__proj__Mkqiprofile__item__qiprofile_id : qiprofile -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { qiprofile_id; qiprofile_quantifiers; qiprofile_instances;
        qiprofile_generation; qiprofile_cost;_} -> qiprofile_id
  
let (__proj__Mkqiprofile__item__qiprofile_quantifiers :
  qiprofile -> quantifier_info Prims.list) =
  fun projectee  ->
    match projectee with
    | { qiprofile_id; qiprofile_quantifiers; qiprofile_instances;
        qiprofile_generation; qiprofile_cost;_} -> qiprofile_quantifiers
  
let (__proj__Mkqiprofile__item__qiprofile_instances : qiprofile -> Prims.int)
  =
  fun projectee  ->
    match projectee with
    | { qiprofile_id; qiprofile_quantifiers; qiprofile_instances;
        qiprofile_generation; qiprofile_cost;_} -> qiprofile_instances
  
let (__proj__Mkqiprofile__item__qiprofile_generation :
  qiprofile -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { qiprofile_id; qiprofile_quantifiers; qiprofile_instances;
        qiprofile_generation; qiprofile_cost;_} -> qiprofile_generation
  
let (__proj__Mkqiprofile__item__qiprofile_cost : qiprofile -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { qiprofile_id; qiprofile_quantifiers; qiprofile_instances;
        qiprofile_generation; qiprofile_cost;_} -> qiprofile_cost
  
let (query_name : query_info -> Prims.string) =
  fun q  ->
    let fn = FStar_Range.file_of_range q.query_info_range  in
    let rg =
      let uu____1092 =
        ((FStar_String.length fn) = (Prims.parse_int "0")) ||
          (let uu____1097 = FStar_Util.char_at fn (Prims.parse_int "0")  in
           uu____1097 = 60)
         in
      if uu____1092
      then ""
      else
        (let s1 =
           let uu____1109 =
             FStar_All.pipe_right q.query_info_range
               FStar_Range.start_of_range
              in
           FStar_All.pipe_right uu____1109 FStar_Range.string_of_pos  in
         let s2 =
           let uu____1113 =
             FStar_All.pipe_right q.query_info_range FStar_Range.end_of_range
              in
           FStar_All.pipe_right uu____1113 FStar_Range.string_of_pos  in
         FStar_Util.format " (%s-%s)" [s1; s2])
       in
    let uu____1119 =
      let uu____1121 =
        let uu____1123 =
          let uu____1125 = FStar_Util.string_of_int q.query_info_index  in
          Prims.op_Hat uu____1125
            (Prims.op_Hat ") from " (Prims.op_Hat fn rg))
           in
        Prims.op_Hat " , " uu____1123  in
      Prims.op_Hat q.query_info_name uu____1121  in
    Prims.op_Hat "(" uu____1119
  
let (quantifier_file : quantifier_info -> Prims.string) =
  fun q  ->
    FStar_Range.file_of_range
      (q.quantifier_info_quantifier).FStar_SMTEncoding_Term.rng
  
let (quantifier_module : quantifier_info -> Prims.string) =
  fun q  ->
    let fn = quantifier_file q  in
    let uu____1148 =
      ((FStar_String.length fn) = (Prims.parse_int "0")) ||
        (let uu____1153 = FStar_Util.char_at fn (Prims.parse_int "0")  in
         uu____1153 = 60)
       in
    if uu____1148 then fn else FStar_Parser_Dep.module_name_of_file fn
  
let (quantifier_range : quantifier_info -> Prims.string) =
  fun q  ->
    let fn = quantifier_file q  in
    let uu____1172 =
      ((FStar_String.length fn) = (Prims.parse_int "0")) ||
        (let uu____1177 = FStar_Util.char_at fn (Prims.parse_int "0")  in
         uu____1177 = 60)
       in
    if uu____1172
    then ""
    else
      (let s1 =
         let uu____1189 =
           FStar_All.pipe_right
             (q.quantifier_info_quantifier).FStar_SMTEncoding_Term.rng
             FStar_Range.start_of_range
            in
         FStar_All.pipe_right uu____1189 FStar_Range.string_of_pos  in
       let s2 =
         let uu____1193 =
           FStar_All.pipe_right
             (q.quantifier_info_quantifier).FStar_SMTEncoding_Term.rng
             FStar_Range.end_of_range
            in
         FStar_All.pipe_right uu____1193 FStar_Range.string_of_pos  in
       FStar_Util.format "(%s-%s)" [s1; s2])
  
let (parse_qiprofile : Prims.string -> qiprofile_map) =
  fun s  ->
    let parse_line line =
      if FStar_Util.starts_with line "[quantifier_instances]"
      then
        let uu____1245 =
          let uu____1249 =
            let uu____1253 =
              FStar_Util.substring_from line (Prims.parse_int "22")  in
            FStar_Util.split uu____1253 ":"  in
          FStar_All.pipe_right uu____1249
            (FStar_List.map FStar_Util.trim_string)
           in
        match uu____1245 with
        | id1::inst1::gen1::cost::[] ->
            let uu____1292 =
              let uu____1305 = FStar_Util.int_of_string inst1  in
              let uu____1307 = FStar_Util.int_of_string gen1  in
              let uu____1309 = FStar_Util.int_of_string cost  in
              (id1, uu____1305, uu____1307, uu____1309)  in
            FStar_Pervasives_Native.Some uu____1292
        | uu____1327 ->
            failwith "could not parse quantifier instantiation info"
      else FStar_Pervasives_Native.None  in
    let comp uu____1394 uu____1395 =
      match (uu____1394, uu____1395) with
      | ((qid1,inst1,gen1,cost1),(qid2,inst2,gen2,cost2)) ->
          FStar_Util.compare qid1 qid2
       in
    let conflate l =
      let rec aux qid inst1 gen1 cost l1 o =
        match l1 with
        | [] -> FStar_List.rev ((qid, inst1, gen1, cost) :: o)
        | (hd_qid,hd_inst,hd_gen,hd_cost)::tl1 ->
            if hd_qid = qid
            then
              let uu____1774 = max gen1 hd_gen  in
              let uu____1776 = max cost hd_cost  in
              aux qid (inst1 + hd_inst) uu____1774 uu____1776 tl1 o
            else
              aux hd_qid hd_inst hd_gen hd_cost tl1 ((qid, inst1, gen1, cost)
                :: o)
         in
      match l with
      | [] -> []
      | (qid,inst1,gen1,cost)::tl1 -> aux qid inst1 gen1 cost l []  in
    let add1 o uu____1907 =
      match uu____1907 with
      | (qid,inst1,gen1,cost) ->
          FStar_Util.psmap_add o qid (inst1, gen1, cost)
       in
    let uu____1944 =
      let uu____1959 =
        let uu____1974 =
          let uu____1989 =
            let uu____2006 =
              FStar_All.pipe_right (FStar_String.split [10] s)
                (FStar_List.map FStar_Util.trim_string)
               in
            FStar_All.pipe_right uu____2006 (FStar_List.map parse_line)  in
          FStar_All.pipe_right uu____1989 FStar_Util.collect_some  in
        FStar_All.pipe_right uu____1974 (FStar_Util.sort_with comp)  in
      FStar_All.pipe_right uu____1959 conflate  in
    let uu____2165 =
      let uu____2184 = FStar_Util.psmap_empty ()  in
      FStar_List.fold_left add1 uu____2184  in
    FStar_All.pipe_right uu____1944 uu____2165
  
let rec (extract_quantifiers_from_decls :
  query_info ->
    FStar_SMTEncoding_Term.decl ->
      (Prims.string * quantifier_info) Prims.list)
  =
  fun query  ->
    fun decl  ->
      let from_term context tm0 =
        let rec aux tm =
          match tm.FStar_SMTEncoding_Term.tm with
          | FStar_SMTEncoding_Term.App (uu____2307,tms) ->
              let uu____2313 = FStar_List.map aux tms  in
              FStar_List.flatten uu____2313
          | FStar_SMTEncoding_Term.Quant
              (uu____2335,uu____2336,uu____2337,uu____2338,t,qid) ->
              let uu____2365 = FStar_ST.op_Bang qid  in
              (match uu____2365 with
               | FStar_Pervasives_Native.Some id1 ->
                   let uu____2404 = aux t  in
                   (id1,
                     {
                       quantifier_info_query = query;
                       quantifier_info_quantifier = tm;
                       quantifier_info_context = context
                     }) :: uu____2404
               | FStar_Pervasives_Native.None  ->
                   ((let uu____2420 =
                       let uu____2422 =
                         let uu____2424 =
                           FStar_SMTEncoding_Term.print_smt_term tm  in
                         Prims.op_Hat uu____2424 "\n"  in
                       Prims.op_Hat
                         "Could not extract quantifiers from SMT term:\n"
                         uu____2422
                        in
                     FStar_Util.print uu____2420 []);
                    aux t))
          | FStar_SMTEncoding_Term.Let (tms,t) ->
              let uu____2435 = aux t  in
              let uu____2443 = FStar_List.collect aux tms  in
              FStar_List.append uu____2435 uu____2443
          | FStar_SMTEncoding_Term.Labeled (t,uu____2462,uu____2463) -> aux t
          | FStar_SMTEncoding_Term.LblPos (t,uu____2467) -> aux t
          | uu____2470 -> []  in
        aux tm0  in
      match decl with
      | FStar_SMTEncoding_Term.DefineFun (nm,args,ret1,tm,uu____2487) ->
          from_term tm tm
      | FStar_SMTEncoding_Term.Assume a ->
          from_term a.FStar_SMTEncoding_Term.assumption_term
            a.FStar_SMTEncoding_Term.assumption_term
      | FStar_SMTEncoding_Term.Module (s,ds) ->
          extract_quantifiers (query, ds)
      | uu____2505 -> []

and (extract_quantifiers :
  (query_info * FStar_SMTEncoding_Term.decl Prims.list) ->
    (Prims.string * quantifier_info) Prims.list)
  =
  fun uu____2511  ->
    match uu____2511 with
    | (query,decls) ->
        FStar_List.fold_left
          (fun l  ->
             fun d  ->
               let uu____2557 = extract_quantifiers_from_decls query d  in
               FStar_List.append uu____2557 l) [] decls

let (profile_quantifiers :
  (query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list ->
    Prims.string -> qiprofile FStar_Util.psmap)
  =
  fun queries  ->
    fun qiprofile_output  ->
      let comp uu____2628 uu____2629 =
        match (uu____2628, uu____2629) with
        | ((id1,q1),(id2,q2)) -> FStar_Util.compare id1 id2  in
      let conflate l =
        let rec aux i id1 ls o =
          match i with
          | (idx,qinfo)::tl1 ->
              if id1 = idx
              then aux tl1 id1 (qinfo :: ls) o
              else aux tl1 idx [qinfo] ((id1, (FStar_List.rev ls)) :: o)
          | [] -> (id1, (FStar_List.rev ls)) :: o  in
        match l with
        | [] -> []
        | (s,q)::tl1 ->
            let uu____2878 = aux tl1 s [q] []  in FStar_List.rev uu____2878
         in
      let remove_duplicates l =
        let equal_range q1 q2 =
          (let uu____2933 = quantifier_file q1  in
           let uu____2935 = quantifier_file q2  in uu____2933 = uu____2935)
            &&
            (let uu____2940 = quantifier_range q1  in
             let uu____2942 = quantifier_range q2  in uu____2940 = uu____2942)
           in
        let rec rm q i o =
          match i with
          | hd1::tl1 ->
              let uu____2977 =
                let uu____2980 = equal_range hd1 q  in
                if uu____2980 then o else hd1 :: o  in
              rm q tl1 uu____2977
          | [] -> FStar_List.rev o  in
        let rec aux i o =
          match i with
          | hd1::tl1 ->
              let uu____3014 = rm hd1 i []  in aux uu____3014 (hd1 :: o)
          | [] -> FStar_List.rev o  in
        aux l []  in
      let qip = parse_qiprofile qiprofile_output  in
      let insert o uu____3039 =
        match uu____3039 with
        | (id1,info) ->
            let uu____3061 =
              let uu____3071 = FStar_Util.psmap_try_find qip id1  in
              match uu____3071 with
              | FStar_Pervasives_Native.None  ->
                  ((Prims.parse_int "0"), (Prims.parse_int "0"),
                    (Prims.parse_int "0"))
              | FStar_Pervasives_Native.Some x -> x  in
            (match uu____3061 with
             | (inst1,gen1,cost) ->
                 let uu____3146 = uu____3061  in
                 let value =
                   {
                     qiprofile_id = id1;
                     qiprofile_quantifiers = info;
                     qiprofile_instances = inst1;
                     qiprofile_generation = gen1;
                     qiprofile_cost = cost
                   }  in
                 FStar_Util.psmap_add o id1 value)
         in
      let uu____3157 =
        let uu____3167 =
          let uu____3177 =
            let uu____3185 = FStar_List.collect extract_quantifiers queries
               in
            FStar_All.pipe_right uu____3185 (FStar_Util.sort_with comp)  in
          FStar_All.pipe_right uu____3177 conflate  in
        FStar_All.pipe_right uu____3167
          (FStar_List.map
             (fun uu____3275  ->
                match uu____3275 with
                | (s,q) ->
                    let uu____3298 = remove_duplicates q  in (s, uu____3298)))
         in
      let uu____3304 =
        let uu____3320 = FStar_Util.psmap_empty ()  in
        FStar_List.fold_left insert uu____3320  in
      FStar_All.pipe_right uu____3157 uu____3304
  
let (tabular_profile :
  qiprofile FStar_Util.psmap -> Prims.string Prims.list Prims.list) =
  fun q  ->
    let comp uu____3385 uu____3386 =
      match (uu____3385, uu____3386) with
      | ((i1,q1),(i2,q2)) ->
          if i1 < i2
          then (Prims.parse_int "1")
          else
            if i1 > i2
            then ~- (Prims.parse_int "1")
            else (Prims.parse_int "0")
       in
    let qid_to_tail_rows info =
      let uu____3460 =
        let uu____3464 =
          let uu____3468 = quantifier_module info  in
          let uu____3470 =
            let uu____3474 = quantifier_file info  in
            let uu____3476 =
              let uu____3480 = quantifier_range info  in [uu____3480]  in
            uu____3474 :: uu____3476  in
          uu____3468 :: uu____3470  in
        "" :: uu____3464  in
      "" :: uu____3460  in
    let qid_to_rows o k =
      let prof =
        let uu____3524 = FStar_Util.psmap_try_find q k  in
        FStar_Util.must uu____3524  in
      if prof.qiprofile_instances > (Prims.parse_int "0")
      then
        match prof.qiprofile_quantifiers with
        | [] -> failwith "QID not found"
        | hd1::tl1 ->
            let uu____3549 =
              let uu____3555 =
                let uu____3559 =
                  let uu____3563 =
                    FStar_Util.string_of_int prof.qiprofile_instances  in
                  let uu____3565 =
                    let uu____3569 = quantifier_module hd1  in
                    let uu____3571 =
                      let uu____3575 = quantifier_file hd1  in
                      let uu____3577 =
                        let uu____3581 = quantifier_range hd1  in
                        [uu____3581]  in
                      uu____3575 :: uu____3577  in
                    uu____3569 :: uu____3571  in
                  uu____3563 :: uu____3565  in
                (prof.qiprofile_id) :: uu____3559  in
              let uu____3589 = FStar_List.map qid_to_tail_rows tl1  in
              uu____3555 :: uu____3589  in
            FStar_List.append o uu____3549
      else o  in
    let uu____3606 =
      let uu____3610 =
        let uu____3619 =
          FStar_Util.psmap_fold q
            (fun k  ->
               fun v1  -> fun acc  -> ((v1.qiprofile_instances), k) :: acc)
            []
           in
        FStar_All.pipe_right uu____3619 (FStar_Util.sort_with comp)  in
      FStar_All.pipe_right uu____3610
        (FStar_List.map
           (fun uu____3708  -> match uu____3708 with | (i,q1) -> q1))
       in
    FStar_All.pipe_right uu____3606 (FStar_List.fold_left qid_to_rows [])
  
let (qiprofile_analysis :
  (query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list ->
    Prims.string -> unit)
  =
  fun queries  ->
    fun qiprofile_output  ->
      match queries with
      | [] -> ()
      | uu____3774 ->
          let q = profile_quantifiers queries qiprofile_output  in
          let tab = tabular_profile q  in
          let fmt =
            [PrettyRight; PrettyRight; PrettyLeft; PrettyRight; PrettyLeft]
             in
          let uu____3795 = prettyprint_table fmt tab  in
          (match uu____3795 with
           | (content_string,content_length) ->
               let uu____3808 = uu____3795  in
               let uu____3815 =
                 let headers =
                   FStar_All.pipe_right queries
                     (FStar_List.map
                        (fun uu____3847  ->
                           match uu____3847 with | (q1,ds) -> query_name q1))
                    in
                 let uu____3861 =
                   FStar_List.fold_left
                     (fun x  -> fun s  -> max x (FStar_String.length s))
                     (Prims.parse_int "0") headers
                    in
                 ((FStar_String.concat "\n" headers), uu____3861)  in
               (match uu____3815 with
                | (header_string,header_length) ->
                    let uu____3881 = uu____3815  in
                    let line =
                      let uu____3890 = max content_length header_length  in
                      FStar_Util.repeat uu____3890 "-"  in
                    FStar_Util.print
                      (Prims.op_Hat line
                         (Prims.op_Hat "\n"
                            (Prims.op_Hat header_string
                               (Prims.op_Hat "\n"
                                  (Prims.op_Hat line
                                     (Prims.op_Hat "\n"
                                        (Prims.op_Hat content_string
                                           (Prims.op_Hat "\n"
                                              (Prims.op_Hat line "\n\n")))))))))
                      []))
  