module Microsoft.FStar.Absyn.SSyntax

open Microsoft.FStar.Absyn.Syntax

type s_modul = { f: string }

let deserialize_modul (m: s_modul) :Syntax.modul =
    { name = Syntax.lid_of_path [] Syntax.dummyRange;
      declarations = [];
      exports = [];
      is_interface = false;
      is_deserialized = false }

let serialize_modul (m: Syntax.modul) :s_modul = { f = "" }
