(** * The paper name that imports shadow

    stdpp's [strict] (of relations, stdpp.base) shares its name with
    [strict W] (types/Worlds.v). A file that exports a module of lang/
    or lockfree/ after the types brings the wrong one back on top. Such a
    file exports this module last, which puts the paper's one on top
    again (soup/Soup.v). Everything else keeps the order of its imports,
    because the end notation [o‾] of lang/ and the point notation [x‾]
    of types/ also share a token, and soup/ reads the first. *)

From GV Require Import types.Worlds types.Types.

Notation strict := types.Worlds.strict (only parsing).
