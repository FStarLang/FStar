open Prims
type entry =
  {
  ue_key: Prims.string ;
  ue_decl: FStarC_Custard_Syntax.decl ;
  ue_type: FStarC_Custard_Syntax.type_info FStar_Pervasives_Native.option ;
  ue_home: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkentry__item__ue_key (projectee : entry) : Prims.string=
  match projectee with | { ue_key; ue_decl; ue_type; ue_home;_} -> ue_key
let __proj__Mkentry__item__ue_decl (projectee : entry) :
  FStarC_Custard_Syntax.decl=
  match projectee with | { ue_key; ue_decl; ue_type; ue_home;_} -> ue_decl
let __proj__Mkentry__item__ue_type (projectee : entry) :
  FStarC_Custard_Syntax.type_info FStar_Pervasives_Native.option=
  match projectee with | { ue_key; ue_decl; ue_type; ue_home;_} -> ue_type
let __proj__Mkentry__item__ue_home (projectee : entry) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { ue_key; ue_decl; ue_type; ue_home;_} -> ue_home
type header =
  {
  uh_version: Prims.int ;
  uh_name: Prims.string ;
  uh_backend: Prims.string ;
  uh_options: (Prims.string * Prims.string) Prims.list ;
  uh_digests: (Prims.string * Prims.string) Prims.list ;
  uh_no_prefix: Prims.string Prims.list ;
  uh_header: Prims.string FStar_Pervasives_Native.option ;
  uh_init: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkheader__item__uh_version (projectee : header) : Prims.int=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_version
let __proj__Mkheader__item__uh_name (projectee : header) : Prims.string=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_name
let __proj__Mkheader__item__uh_backend (projectee : header) : Prims.string=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_backend
let __proj__Mkheader__item__uh_options (projectee : header) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_options
let __proj__Mkheader__item__uh_digests (projectee : header) :
  (Prims.string * Prims.string) Prims.list=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_digests
let __proj__Mkheader__item__uh_no_prefix (projectee : header) :
  Prims.string Prims.list=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_no_prefix
let __proj__Mkheader__item__uh_header (projectee : header) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_header
let __proj__Mkheader__item__uh_init (projectee : header) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { uh_version; uh_name; uh_backend; uh_options; uh_digests; uh_no_prefix;
      uh_header; uh_init;_} -> uh_init
type iface = {
  ui_header: header ;
  ui_entries: entry Prims.list }
let __proj__Mkiface__item__ui_header (projectee : iface) : header=
  match projectee with | { ui_header; ui_entries;_} -> ui_header
let __proj__Mkiface__item__ui_entries (projectee : iface) : entry Prims.list=
  match projectee with | { ui_header; ui_entries;_} -> ui_entries
let current_version : Prims.int= Prims.of_int 12
let layout_options (uu___ : unit) : (Prims.string * Prims.string) Prims.list=
  let uu___1 =
    let uu___2 = FStarC_Options.custard_backend () in
    ("custard_backend", uu___2) in
  let uu___2 =
    let uu___3 =
      let uu___4 =
        let uu___5 = FStarC_Options.custard_monomorphize_types () in
        Prims.string_of_bool uu___5 in
      ("custard_monomorphize_types", uu___4) in
    let uu___4 =
      let uu___5 =
        let uu___6 =
          let uu___7 = FStarC_Options.custard_sizet_32 () in
          if uu___7 then "32" else "native" in
        ("custard_sizet_width", uu___6) in
      let uu___6 =
        let uu___7 =
          let uu___8 =
            let uu___9 = FStarC_Options.custard_int128 () in
            Prims.string_of_bool uu___9 in
          ("custard_int128", uu___8) in
        [uu___7] in
      uu___5 :: uu___6 in
    uu___3 :: uu___4 in
  uu___1 :: uu___2
let type_key (n : FStarC_Custard_Syntax.name) : Prims.string=
  let uu___ = FStarC_Custard_Syntax.string_of_name n in
  Prims.strcat "<type>" uu___
let is_type_key (k : Prims.string) : Prims.bool=
  if (FStarC_String.length k) >= (Prims.of_int 6)
  then
    let uu___ = FStarC_String.substring k Prims.int_zero (Prims.of_int 6) in
    uu___ = "<type>"
  else false
let write_iface (fn : Prims.string) (i : iface) : unit=
  FStarC_Util.save_value_to_file fn i
let bad (fn : Prims.string) (msg : FStar_Pprint.document Prims.list) : 
  'a=
  FStarC_Errors.raise_error0
    FStarC_Errors_Codes.Error_CustardBadUnitInterface ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
    (Obj.magic
       ((FStarC_Errors_Msg.text
           (FStarC_Format.fmt1 "Cannot link the Custard unit interface %s."
              fn)) :: msg))
let read_iface (fn : Prims.string) : iface=
  let i =
    let uu___ = FStarC_Util.load_value_from_file fn in
    match uu___ with
    | FStar_Pervasives_Native.Some i1 -> i1
    | FStar_Pervasives_Native.None ->
        bad fn
          [FStarC_Errors_Msg.text "The file is missing or could not be read."] in
  let h = i.ui_header in
  if h.uh_version <> current_version
  then
    (let uu___1 =
       let uu___2 =
         let uu___3 =
           let uu___4 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int
               h.uh_version in
           let uu___5 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int
               current_version in
           FStarC_Format.fmt2
             "It was written by a different version of Custard (format %s, but this F* speaks %s)."
             uu___4 uu___5 in
         FStarC_Errors_Msg.text uu___3 in
       [uu___2; FStarC_Errors_Msg.text "Rebuild the unit."] in
     bad fn uu___1)
  else ();
  (let mine = layout_options () in
   FStarC_List.iter
     (fun uu___2 ->
        match uu___2 with
        | (k, v) ->
            let uu___3 =
              FStarC_List.tryFind
                (fun uu___4 -> match uu___4 with | (k', uu___5) -> k = k')
                h.uh_options in
            (match uu___3 with
             | FStar_Pervasives_Native.Some (uu___4, v') when v = v' -> ()
             | FStar_Pervasives_Native.Some (uu___4, v') ->
                 bad fn
                   [FStarC_Errors_Msg.text
                      (FStarC_Format.fmt3
                         "It was built with --%s %s, but this run uses %s." k
                         v' v);
                   FStarC_Errors_Msg.text
                     "Layout decisions depend on that option, so the two cannot be mixed."]
             | FStar_Pervasives_Native.None ->
                 bad fn
                   [FStarC_Errors_Msg.text
                      (FStarC_Format.fmt1 "It records no value for --%s." k)]))
     mine;
   FStarC_List.iter
     (fun uu___3 ->
        match uu___3 with
        | (f, d) ->
            let found =
              if FStarC_Filepath.file_exists f
              then FStar_Pervasives_Native.Some f
              else FStarC_Find.find_file (FStarC_Filepath.basename f) in
            (match found with
             | FStar_Pervasives_Native.Some g when
                 let uu___4 = FStarC_Util.digest_of_file g in uu___4 <> d ->
                 bad fn
                   [FStarC_Errors_Msg.text
                      (FStarC_Format.fmt1
                         "It was built from a different version of %s."
                         (if g = f
                          then f
                          else FStarC_Format.fmt2 "%s (found here as %s)" f g));
                   FStarC_Errors_Msg.text "Rebuild the unit."]
             | uu___4 -> ())) h.uh_digests;
   i)
let type_info_to_string (ti : FStarC_Custard_Syntax.type_info) :
  Prims.string=
  let l =
    match ti.FStarC_Custard_Syntax.ti_layout with
    | FStarC_Custard_Syntax.L_erased -> "erased"
    | FStarC_Custard_Syntax.L_newtype nt ->
        FStarC_Format.fmt1 "newtype(%s)" nt.FStarC_Custard_Syntax.nt_field
    | FStarC_Custard_Syntax.L_struct cls ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Class_Show.showable_nat
            (FStarC_List.length cls) in
        FStarC_Format.fmt1 "struct(%s ctors)" uu___
    | FStarC_Custard_Syntax.L_abbrev uu___ -> "abbrev"
    | FStarC_Custard_Syntax.L_opaque -> "opaque" in
  if ti.FStarC_Custard_Syntax.ti_erased then Prims.strcat l ", erased" else l
let entry_to_string (e : entry) : Prims.string=
  let what =
    match e.ue_decl with
    | FStarC_Custard_Syntax.DType d ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Custard_Syntax.showable_name
            d.FStarC_Custard_Syntax.dt_name in
        let uu___1 =
          match e.ue_type with
          | FStar_Pervasives_Native.Some ti -> type_info_to_string ti
          | FStar_Pervasives_Native.None -> "?" in
        FStarC_Format.fmt2 "type %s [%s]" uu___ uu___1
    | FStarC_Custard_Syntax.DLet d ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Custard_Syntax.showable_name
            d.FStarC_Custard_Syntax.dl_name in
        FStarC_Format.fmt1 "let %s" uu___
    | FStarC_Custard_Syntax.DExternal d ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Custard_Syntax.showable_name
            d.FStarC_Custard_Syntax.dx_name in
        FStarC_Format.fmt1 "external %s" uu___
    | FStarC_Custard_Syntax.DExn d ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Custard_Syntax.showable_name
            d.FStarC_Custard_Syntax.de_name in
        FStarC_Format.fmt1 "exception %s" uu___ in
  FStarC_Format.fmt3 "  %s\n    key: %s%s\n" what e.ue_key
    (match e.ue_home with
     | FStar_Pervasives_Native.Some m -> Prims.strcat "\n    home: " m
     | FStar_Pervasives_Native.None -> "")
let iface_to_string (i : iface) : Prims.string=
  let h = i.ui_header in
  let opt label v =
    match v with
    | FStar_Pervasives_Native.Some f ->
        Prims.strcat "\n  " (Prims.strcat label (Prims.strcat ": " f))
    | FStar_Pervasives_Native.None -> "" in
  let uu___ =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int h.uh_version in
  let uu___1 =
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 =
              FStarC_List.map
                (fun uu___7 ->
                   match uu___7 with
                   | (k, v) -> Prims.strcat k (Prims.strcat "=" v))
                h.uh_options in
            FStarC_String.concat ", " uu___6 in
          let uu___6 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_nat
              (FStarC_List.length h.uh_digests) in
          let uu___7 =
            let uu___8 = FStarC_List.map entry_to_string i.ui_entries in
            FStarC_String.concat "" uu___8 in
          FStarC_Format.fmt3 "  options: %s\n  %s checked files\n\n%s" uu___5
            uu___6 uu___7 in
        Prims.strcat "\n" uu___4 in
      Prims.strcat (opt "init" h.uh_init) uu___3 in
    Prims.strcat (opt "header" h.uh_header) uu___2 in
  FStarC_Format.fmt4 "unit %s (format %s, backend %s)%s" h.uh_name uu___
    h.uh_backend uu___1
type unit_ref =
  {
  ur_name: Prims.string ;
  ur_header: Prims.string FStar_Pervasives_Native.option ;
  ur_init: Prims.string FStar_Pervasives_Native.option ;
  ur_no_prefix: Prims.string Prims.list }
let __proj__Mkunit_ref__item__ur_name (projectee : unit_ref) : Prims.string=
  match projectee with
  | { ur_name; ur_header; ur_init; ur_no_prefix;_} -> ur_name
let __proj__Mkunit_ref__item__ur_header (projectee : unit_ref) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ur_name; ur_header; ur_init; ur_no_prefix;_} -> ur_header
let __proj__Mkunit_ref__item__ur_init (projectee : unit_ref) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { ur_name; ur_header; ur_init; ur_no_prefix;_} -> ur_init
let __proj__Mkunit_ref__item__ur_no_prefix (projectee : unit_ref) :
  Prims.string Prims.list=
  match projectee with
  | { ur_name; ur_header; ur_init; ur_no_prefix;_} -> ur_no_prefix
type links =
  {
  lk_tbl: (Prims.string * entry) FStarC_SMap.t ;
  lk_units: unit_ref Prims.list }
let __proj__Mklinks__item__lk_tbl (projectee : links) :
  (Prims.string * entry) FStarC_SMap.t=
  match projectee with | { lk_tbl; lk_units;_} -> lk_tbl
let __proj__Mklinks__item__lk_units (projectee : links) :
  unit_ref Prims.list=
  match projectee with | { lk_tbl; lk_units;_} -> lk_units
let empty_links : links=
  let uu___ = FStarC_SMap.create Prims.int_one in
  { lk_tbl = uu___; lk_units = [] }
let load_links (fns : Prims.string Prims.list) : links=
  let tbl = FStarC_SMap.create (Prims.of_int 1000) in
  let units =
    FStarC_List.map
      (fun fn ->
         let i = read_iface fn in
         let u = (i.ui_header).uh_name in
         FStarC_List.iter
           (fun e ->
              let uu___1 = FStarC_SMap.try_find tbl e.ue_key in
              match uu___1 with
              | FStar_Pervasives_Native.Some uu___2 when is_type_key e.ue_key
                  -> ()
              | FStar_Pervasives_Native.Some (u', uu___2) when u' <> u ->
                  bad fn
                    [FStarC_Errors_Msg.text
                       (FStarC_Format.fmt2
                          "Both %s and %s export a definition for the same specialization key."
                          u' u);
                    FStarC_Errors_Msg.text
                      (FStarC_Format.fmt1 "The key is: %s" e.ue_key);
                    FStarC_Errors_Msg.text
                      "Link only one of them, or merge the two units."]
              | uu___2 -> FStarC_SMap.add tbl e.ue_key (u, e)) i.ui_entries;
         {
           ur_name = u;
           ur_header = ((i.ui_header).uh_header);
           ur_init = ((i.ui_header).uh_init);
           ur_no_prefix = ((i.ui_header).uh_no_prefix)
         }) fns in
  (let uu___1 =
     let uu___2 = FStarC_Options.custard_dump_cui () in
     if uu___2 then fns <> [] else false in
   if uu___1
   then
     let uu___2 =
       let uu___3 =
         let uu___4 = FStarC_SMap.keys tbl in FStarC_List.length uu___4 in
       FStarC_Class_Show.show FStarC_Class_Show.showable_nat uu___3 in
     FStarC_Format.print1 "Custard: linked %s specializations.\n" uu___2
   else ());
  { lk_tbl = tbl; lk_units = units }
let lookup (l : links) (k : Prims.string) :
  (Prims.string * entry) FStar_Pervasives_Native.option=
  FStarC_SMap.try_find l.lk_tbl k
let is_empty (l : links) : Prims.bool=
  let uu___ = let uu___1 = FStarC_SMap.keys l.lk_tbl in uu___1 = [] in
  if uu___
  then match l.lk_units with | [] -> true | uu___1 -> false
  else false
let link_homes (l : links) : Prims.string Prims.list=
  FStarC_SMap.fold l.lk_tbl
    (fun uu___ uu___1 acc ->
       match uu___1 with
       | (uu___2, e) ->
           (match e.ue_home with
            | FStar_Pervasives_Native.Some h ->
                if FStarC_List.mem h acc then acc else h :: acc
            | FStar_Pervasives_Native.None -> acc)) []
let link_headers (l : links) : Prims.string Prims.list=
  FStarC_List.collect
    (fun u ->
       match u.ur_header with
       | FStar_Pervasives_Native.Some h -> [h]
       | FStar_Pervasives_Native.None -> []) l.lk_units
let link_inits (l : links) : Prims.string Prims.list=
  FStarC_List.collect
    (fun u ->
       match u.ur_init with
       | FStar_Pervasives_Native.Some i -> [i]
       | FStar_Pervasives_Native.None -> []) l.lk_units
let link_no_prefix (l : links) : Prims.string Prims.list=
  FStarC_List.collect (fun u -> u.ur_no_prefix) l.lk_units
