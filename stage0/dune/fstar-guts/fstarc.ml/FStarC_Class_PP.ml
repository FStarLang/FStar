open Prims
type 'a pretty = {
  pp: 'a -> FStar_Pprint.document }
let __proj__Mkpretty__item__pp (projectee : 'a pretty) :
  'a -> FStar_Pprint.document= match projectee with | { pp;_} -> pp
let pp (projectee : 'a pretty) : 'a -> FStar_Pprint.document=
  match projectee with | { pp = pp1;_} -> pp1
let gparens (a : FStar_Pprint.document) : FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.nest (Prims.of_int (2)) (FStar_Pprint.parens a))
let gbrackets (a : FStar_Pprint.document) : FStar_Pprint.document=
  FStar_Pprint.group
    (FStar_Pprint.nest (Prims.of_int (2)) (FStar_Pprint.brackets a))
let pp_unit : unit pretty=
  { pp = (fun uu___ -> FStar_Pprint.doc_of_string "()") }
let pp_int : Prims.int pretty=
  {
    pp =
      (fun x ->
         let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int x in
         FStar_Pprint.doc_of_string uu___)
  }
let pp_bool : Prims.bool pretty= { pp = FStar_Pprint.doc_of_bool }
let pp_list (uu___ : 'a pretty) : 'a Prims.list pretty=
  {
    pp =
      (fun l ->
         let uu___1 =
           FStarC_Pprint.flow_map
             (FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                (FStar_Pprint.break_ Prims.int_one)) (pp uu___) l in
         gbrackets uu___1)
  }
let pp_option (uu___ : 'a pretty) : 'a FStar_Pervasives_Native.option pretty=
  {
    pp =
      (fun o ->
         match o with
         | FStar_Pervasives_Native.Some v ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = pp uu___ v in
                 FStar_Pprint.op_Hat_Slash_Hat
                   (FStar_Pprint.doc_of_string "Some") uu___3 in
               FStar_Pprint.nest (Prims.of_int (2)) uu___2 in
             FStar_Pprint.group uu___1
         | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "None")
  }
let pp_either (uu___ : 'a pretty) (uu___1 : 'b pretty) :
  ('a, 'b) FStar_Pervasives.either pretty=
  {
    pp =
      (fun e ->
         let uu___2 =
           let uu___3 =
             match e with
             | FStar_Pervasives.Inl x ->
                 let uu___4 = pp uu___ x in
                 FStar_Pprint.op_Hat_Slash_Hat
                   (FStar_Pprint.doc_of_string "Inl") uu___4
             | FStar_Pervasives.Inr x ->
                 let uu___4 = pp uu___1 x in
                 FStar_Pprint.op_Hat_Slash_Hat
                   (FStar_Pprint.doc_of_string "Inr") uu___4 in
           FStar_Pprint.nest (Prims.of_int (2)) uu___3 in
         FStar_Pprint.group uu___2)
  }
let comma_space : FStar_Pprint.document=
  FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
    (FStar_Pprint.break_ Prims.int_one)
let pp_tuple2 (uu___ : 'a pretty) (uu___1 : 'b pretty) : ('a * 'b) pretty=
  {
    pp =
      (fun uu___2 ->
         match uu___2 with
         | (x1, x2) ->
             let uu___3 =
               let uu___4 =
                 let uu___5 = pp uu___ x1 in
                 let uu___6 = let uu___7 = pp uu___1 x2 in [uu___7] in uu___5
                   :: uu___6 in
               FStar_Pprint.separate comma_space uu___4 in
             gparens uu___3)
  }
let pp_tuple3 (uu___ : 'a pretty) (uu___1 : 'b pretty) (uu___2 : 'c pretty) :
  ('a * 'b * 'c) pretty=
  {
    pp =
      (fun uu___3 ->
         match uu___3 with
         | (x1, x2, x3) ->
             let uu___4 =
               let uu___5 =
                 let uu___6 = pp uu___ x1 in
                 let uu___7 =
                   let uu___8 = pp uu___1 x2 in
                   let uu___9 = let uu___10 = pp uu___2 x3 in [uu___10] in
                   uu___8 :: uu___9 in
                 uu___6 :: uu___7 in
               FStar_Pprint.separate comma_space uu___5 in
             gparens uu___4)
  }
let pp_tuple4 (uu___ : 'a pretty) (uu___1 : 'b pretty) (uu___2 : 'c pretty)
  (uu___3 : 'd pretty) : ('a * 'b * 'c * 'd) pretty=
  {
    pp =
      (fun uu___4 ->
         match uu___4 with
         | (x1, x2, x3, x4) ->
             let uu___5 =
               let uu___6 =
                 let uu___7 = pp uu___ x1 in
                 let uu___8 =
                   let uu___9 = pp uu___1 x2 in
                   let uu___10 =
                     let uu___11 = pp uu___2 x3 in
                     let uu___12 = let uu___13 = pp uu___3 x4 in [uu___13] in
                     uu___11 :: uu___12 in
                   uu___9 :: uu___10 in
                 uu___7 :: uu___8 in
               FStar_Pprint.separate comma_space uu___6 in
             gparens uu___5)
  }
let pp_tuple5 (uu___ : 'a pretty) (uu___1 : 'b pretty) (uu___2 : 'c pretty)
  (uu___3 : 'd pretty) (uu___4 : 'e pretty) :
  ('a * 'b * 'c * 'd * 'e) pretty=
  {
    pp =
      (fun uu___5 ->
         match uu___5 with
         | (x1, x2, x3, x4, x5) ->
             let uu___6 =
               let uu___7 =
                 let uu___8 = pp uu___ x1 in
                 let uu___9 =
                   let uu___10 = pp uu___1 x2 in
                   let uu___11 =
                     let uu___12 = pp uu___2 x3 in
                     let uu___13 =
                       let uu___14 = pp uu___3 x4 in
                       let uu___15 = let uu___16 = pp uu___4 x5 in [uu___16] in
                       uu___14 :: uu___15 in
                     uu___12 :: uu___13 in
                   uu___10 :: uu___11 in
                 uu___8 :: uu___9 in
               FStar_Pprint.separate comma_space uu___7 in
             gparens uu___6)
  }
let pp_tuple6 (uu___ : 'a pretty) (uu___1 : 'b pretty) (uu___2 : 'c pretty)
  (uu___3 : 'd pretty) (uu___4 : 'e pretty) (uu___5 : 'f pretty) :
  ('a * 'b * 'c * 'd * 'e * 'f) pretty=
  {
    pp =
      (fun uu___6 ->
         match uu___6 with
         | (x1, x2, x3, x4, x5, x6) ->
             let uu___7 =
               let uu___8 =
                 let uu___9 = pp uu___ x1 in
                 let uu___10 =
                   let uu___11 = pp uu___1 x2 in
                   let uu___12 =
                     let uu___13 = pp uu___2 x3 in
                     let uu___14 =
                       let uu___15 = pp uu___3 x4 in
                       let uu___16 =
                         let uu___17 = pp uu___4 x5 in
                         let uu___18 =
                           let uu___19 = pp uu___5 x6 in [uu___19] in
                         uu___17 :: uu___18 in
                       uu___15 :: uu___16 in
                     uu___13 :: uu___14 in
                   uu___11 :: uu___12 in
                 uu___9 :: uu___10 in
               FStar_Pprint.separate comma_space uu___8 in
             gparens uu___7)
  }
let pretty_from_showable (uu___ : 'a FStarC_Class_Show.showable) : 'a pretty=
  {
    pp =
      (fun x ->
         let uu___1 = FStarC_Class_Show.show uu___ x in
         FStar_Pprint.arbitrary_string uu___1)
  }
let showable_from_pretty (uu___ : 'a pretty) : 'a FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun x -> let uu___1 = pp uu___ x in FStar_Pprint.render uu___1)
  }
