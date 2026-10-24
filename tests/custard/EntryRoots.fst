module EntryRoots

module I32 = FStar.Int32

/// [--custard_entry_module] roots a module's externals, not only its
/// definitions.
///
/// [EntryRootsLib] is an entry module here, so both of its [assume val]s are
/// part of what this unit declares, even though the program only calls one.
/// They were not rooted, so a module of nothing but [assume val]s extracted
/// to an empty unit -- and a consumer reading both it and a unit where the
/// same names survived as imports got whichever of the two its linker kept.

let main () : I32.t = EntryRootsLib.used 0l
