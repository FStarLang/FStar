open Prims
type file_name = Prims.string[@@deriving yojson,show]
type pos = {
  line: Prims.int ;
  col: Prims.int }[@@deriving yojson,show]
let (__proj__Mkpos__item__line : pos -> Prims.int) =
  fun projectee  -> match projectee with | { line; col;_} -> line 
let (__proj__Mkpos__item__col : pos -> Prims.int) =
  fun projectee  -> match projectee with | { line; col;_} -> col 
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun i  -> fun j  -> if i < j then j else i 
let (pos_geq : pos -> pos -> Prims.bool) =
  fun p1  ->
    fun p2  ->
      (p1.line > p2.line) || ((p1.line = p2.line) && (p1.col >= p2.col))
  
type rng = {
  file_name: file_name ;
  start_pos: pos ;
  end_pos: pos }[@@deriving yojson,show]
let (__proj__Mkrng__item__file_name : rng -> file_name) =
  fun projectee  ->
    match projectee with | { file_name; start_pos; end_pos;_} -> file_name
  
let (__proj__Mkrng__item__start_pos : rng -> pos) =
  fun projectee  ->
    match projectee with | { file_name; start_pos; end_pos;_} -> start_pos
  
let (__proj__Mkrng__item__end_pos : rng -> pos) =
  fun projectee  ->
    match projectee with | { file_name; start_pos; end_pos;_} -> end_pos
  
type range = {
  def_range: rng ;
  use_range: rng }[@@deriving yojson,show]
let (__proj__Mkrange__item__def_range : range -> rng) =
  fun projectee  ->
    match projectee with | { def_range; use_range;_} -> def_range
  
let (__proj__Mkrange__item__use_range : range -> rng) =
  fun projectee  ->
    match projectee with | { def_range; use_range;_} -> use_range
  
let (dummy_pos : pos) =
  { line = (Prims.parse_int "0"); col = (Prims.parse_int "0") } 
let (dummy_rng : rng) =
  { file_name = "<dummy>"; start_pos = dummy_pos; end_pos = dummy_pos } 
let (dummyRange : range) = { def_range = dummy_rng; use_range = dummy_rng } 
let (use_range : range -> rng) = fun r  -> r.use_range 
let (def_range : range -> rng) = fun r  -> r.def_range 
let (range_of_rng : rng -> rng -> range) =
  fun d  -> fun u  -> { def_range = d; use_range = u } 
let (set_use_range : range -> rng -> range) =
  fun r2  ->
    fun use_rng  ->
      if use_rng <> dummy_rng
      then
        let uu___324_34397 = r2  in
        { def_range = (uu___324_34397.def_range); use_range = use_rng }
      else r2
  
let (set_def_range : range -> rng -> range) =
  fun r2  ->
    fun def_rng  ->
      if def_rng <> dummy_rng
      then
        let uu___329_34412 = r2  in
        { def_range = def_rng; use_range = (uu___329_34412.use_range) }
      else r2
  
let (mk_pos : Prims.int -> Prims.int -> pos) =
  fun l  ->
    fun c  ->
      {
        line = (max (Prims.parse_int "0") l);
        col = (max (Prims.parse_int "0") c)
      }
  
let (mk_rng : file_name -> pos -> pos -> rng) =
  fun file_name  ->
    fun start_pos  -> fun end_pos  -> { file_name; start_pos; end_pos }
  
let (mk_range : Prims.string -> pos -> pos -> range) =
  fun f  -> fun b  -> fun e  -> let r = mk_rng f b e  in range_of_rng r r 
let (union_rng : rng -> rng -> rng) =
  fun r1  ->
    fun r2  ->
      if r1.file_name <> r2.file_name
      then r2
      else
        (let start_pos =
           if pos_geq r1.start_pos r2.start_pos
           then r2.start_pos
           else r1.start_pos  in
         let end_pos =
           if pos_geq r1.end_pos r2.end_pos then r1.end_pos else r2.end_pos
            in
         mk_rng r1.file_name start_pos end_pos)
  
let (union_ranges : range -> range -> range) =
  fun r1  ->
    fun r2  ->
      {
        def_range = (union_rng r1.def_range r2.def_range);
        use_range = (union_rng r1.use_range r2.use_range)
      }
  
let (rng_included : rng -> rng -> Prims.bool) =
  fun r1  ->
    fun r2  ->
      if r1.file_name <> r2.file_name
      then false
      else
        (pos_geq r1.start_pos r2.start_pos) &&
          (pos_geq r2.end_pos r1.end_pos)
  
let (string_of_pos : pos -> Prims.string) =
  fun pos  ->
    let uu____34528 = FStar_Util.string_of_int pos.line  in
    let uu____34530 = FStar_Util.string_of_int pos.col  in
    FStar_Util.format2 "%s,%s" uu____34528 uu____34530
  
let (string_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let uu____34542 = FStar_Options.ide ()  in
    if uu____34542
    then
      try
        (fun uu___356_34549  ->
           match () with
           | () ->
               let uu____34551 =
                 let uu____34555 = FStar_Util.basename f  in
                 FStar_Options.find_file uu____34555  in
               (match uu____34551 with
                | FStar_Pervasives_Native.None  -> f
                | FStar_Pervasives_Native.Some absolute_path -> absolute_path))
          ()
      with | uu___355_34563 -> f
    else f
  
let (file_of_range : range -> Prims.string) =
  fun r  -> let f = (r.def_range).file_name  in string_of_file_name f 
let (set_file_of_range : range -> Prims.string -> range) =
  fun r  ->
    fun f  ->
      let uu___368_34589 = r  in
      {
        def_range =
          (let uu___370_34592 = r.def_range  in
           {
             file_name = f;
             start_pos = (uu___370_34592.start_pos);
             end_pos = (uu___370_34592.end_pos)
           });
        use_range = (uu___368_34589.use_range)
      }
  
let (string_of_rng : rng -> Prims.string) =
  fun r  ->
    let uu____34600 = string_of_file_name r.file_name  in
    let uu____34602 = string_of_pos r.start_pos  in
    let uu____34604 = string_of_pos r.end_pos  in
    FStar_Util.format3 "%s(%s-%s)" uu____34600 uu____34602 uu____34604
  
let (string_of_def_range : range -> Prims.string) =
  fun r  -> string_of_rng r.def_range 
let (string_of_use_range : range -> Prims.string) =
  fun r  -> string_of_rng r.use_range 
let (string_of_range : range -> Prims.string) =
  fun r  -> string_of_def_range r 
let (start_of_range : range -> pos) = fun r  -> (r.def_range).start_pos 
let (end_of_range : range -> pos) = fun r  -> (r.def_range).end_pos 
let (file_of_use_range : range -> Prims.string) =
  fun r  -> (r.use_range).file_name 
let (start_of_use_range : range -> pos) = fun r  -> (r.use_range).start_pos 
let (end_of_use_range : range -> pos) = fun r  -> (r.use_range).end_pos 
let (line_of_pos : pos -> Prims.int) = fun p  -> p.line 
let (col_of_pos : pos -> Prims.int) = fun p  -> p.col 
let (end_range : range -> range) =
  fun r  ->
    mk_range (r.def_range).file_name (r.def_range).end_pos
      (r.def_range).end_pos
  
let (compare_rng : rng -> rng -> Prims.int) =
  fun r1  ->
    fun r2  ->
      let fcomp = FStar_String.compare r1.file_name r2.file_name  in
      if fcomp = (Prims.parse_int "0")
      then
        let start1 = r1.start_pos  in
        let start2 = r2.start_pos  in
        let lcomp = start1.line - start2.line  in
        (if lcomp = (Prims.parse_int "0")
         then start1.col - start2.col
         else lcomp)
      else fcomp
  
let (compare : range -> range -> Prims.int) =
  fun r1  -> fun r2  -> compare_rng r1.def_range r2.def_range 
let (compare_use_range : range -> range -> Prims.int) =
  fun r1  -> fun r2  -> compare_rng r1.use_range r2.use_range 
let (range_before_pos : range -> pos -> Prims.bool) =
  fun m1  ->
    fun p  -> let uu____34745 = end_of_range m1  in pos_geq p uu____34745
  
let (end_of_line : pos -> pos) =
  fun p  ->
    let uu___399_34752 = p  in
    { line = (uu___399_34752.line); col = FStar_Util.max_int }
  
let (extend_to_end_of_line : range -> range) =
  fun r  ->
    let uu____34759 = file_of_range r  in
    let uu____34761 = start_of_range r  in
    let uu____34762 =
      let uu____34763 = end_of_range r  in end_of_line uu____34763  in
    mk_range uu____34759 uu____34761 uu____34762
  
let (prims_to_fstar_range :
  ((Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int)) *
    (Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int))) ->
    range)
  =
  fun r  ->
    let uu____34854 = r  in
    match uu____34854 with
    | (r1,r2) ->
        let uu____34975 = r1  in
        (match uu____34975 with
         | (f1,s1,e1) ->
             let uu____35024 = r2  in
             (match uu____35024 with
              | (f2,s2,e2) ->
                  let s11 =
                    mk_pos (FStar_Pervasives_Native.fst s1)
                      (FStar_Pervasives_Native.snd s1)
                     in
                  let e11 =
                    mk_pos (FStar_Pervasives_Native.fst e1)
                      (FStar_Pervasives_Native.snd e1)
                     in
                  let s21 =
                    mk_pos (FStar_Pervasives_Native.fst s2)
                      (FStar_Pervasives_Native.snd s2)
                     in
                  let e21 =
                    mk_pos (FStar_Pervasives_Native.fst e2)
                      (FStar_Pervasives_Native.snd e2)
                     in
                  let r11 = mk_rng f1 s11 e11  in
                  let r21 = mk_rng f2 s21 e21  in
                  { def_range = r11; use_range = r21 }))
  
let (json_of_pos : pos -> FStar_Util.json) =
  fun pos  ->
    let uu____35101 =
      let uu____35104 =
        let uu____35105 = line_of_pos pos  in FStar_Util.JsonInt uu____35105
         in
      let uu____35107 =
        let uu____35110 =
          let uu____35111 = col_of_pos pos  in FStar_Util.JsonInt uu____35111
           in
        [uu____35110]  in
      uu____35104 :: uu____35107  in
    FStar_Util.JsonList uu____35101
  
let (json_of_range_fields : Prims.string -> pos -> pos -> FStar_Util.json) =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____35131 =
          let uu____35139 =
            let uu____35147 =
              let uu____35153 = json_of_pos b  in ("beg", uu____35153)  in
            let uu____35156 =
              let uu____35164 =
                let uu____35170 = json_of_pos e  in ("end", uu____35170)  in
              [uu____35164]  in
            uu____35147 :: uu____35156  in
          ("fname", (FStar_Util.JsonStr file)) :: uu____35139  in
        FStar_Util.JsonAssoc uu____35131
  
let (json_of_use_range : range -> FStar_Util.json) =
  fun r  ->
    let uu____35201 = file_of_use_range r  in
    let uu____35203 = start_of_use_range r  in
    let uu____35204 = end_of_use_range r  in
    json_of_range_fields uu____35201 uu____35203 uu____35204
  
let (json_of_def_range : range -> FStar_Util.json) =
  fun r  ->
    let uu____35211 = file_of_range r  in
    let uu____35213 = start_of_range r  in
    let uu____35214 = end_of_range r  in
    json_of_range_fields uu____35211 uu____35213 uu____35214
  