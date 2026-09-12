#!/usr/bin/env python3
"""A retrieval server over `fstar.exe --export_docs`, spoken as MCP.

An agent writing a proof needs to find an existing lemma. Today it is told
to grep: the `fstar-coder` agent in FStarLang/proof-copilot instructs
itself to "search the F* standard library (`ulib/`) ... then `grep -rn`
for function definitions". Grep matches spellings, so it can only find a
lemma whose name you can already guess. The question an agent actually
has -- *which lemma guarantees something about `slice`?* -- has no
spelling.

The export answers it. A declaration's elaborated type names, in resolved
form, everything its precondition assumes and its postcondition
guarantees, so "guarantees something about `FStar.Seq.Base.slice`" is a
lookup rather than a search. That is the same structural index
`fstardoc_site.py` puts behind a search box, offered to an agent instead
of to a reader (whitepaper D7).

This is not the existing FStarLang/fstar-mcp server and does not overlap
it. That one is session-oriented -- create a session, typecheck a buffer,
`lookup_symbol` at a file, line and column -- and answers "what is this
thing I am pointing at". Everything here answers "what should I be
pointing at", over a whole library, and needs no session.

    # build the index once, from checked files
    fstardoc_mcp.py index --fstar out/bin/fstar.exe --out ulib.index.json \\
        --cache stage2/ulib.checked --include ulib --modules-from slice.txt

    # serve it on stdin/stdout
    fstardoc_mcp.py serve --index ulib.index.json

SCOPE
-----
The index holds a module's *public* surface, because that is what the
export reports. That is the right scope rather than a limitation: an
agent working inside a module already has the file open and can read it,
so an index earns its keep for the cross-module case -- and across
modules, only the public surface is referenceable anyway.

DEPENDENCIES
------------
`serve` uses the standard library only, so it can run wherever an agent
runs, with nothing to install. `index` borrows the contract and type-shape
analysis from `fstardoc_site.py`, which needs markdown-it; it is a build
step, run once, and the import is deferred so that serving never pays for
it.
"""

import argparse
import json
import os
import re
import sys

SCHEMA, VERSION = "fstar-module-docs", 4
INDEX_SCHEMA, INDEX_VERSION = "fstardoc-retrieval-index", 1

# A definition can be a whole proof term. Sending one unbidden is how a
# retrieval tool burns a context window, so it is truncated unless asked
# for. `lookup` takes `include_definition` to get the rest.
DEFINITION_PREVIEW = 600

PROTOCOL_FALLBACK = "2024-11-05"


# ----------------------------------------------------------- the index --


def build_index(fstar, modules, caches, includes):
    """Export each module and reduce it to per-declaration records."""
    # Deferred: only `index` needs these, and fstardoc_site imports
    # markdown-it at module load.
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import fstardoc_site as S

    out = []
    for m in modules:
        checked = S.find_checked(m, caches)
        if not checked:
            sys.stderr.write("no checked file for %s\n" % m)
            continue
        d = S.export(fstar, checked, os.getcwd(), includes)
        if not d:
            continue
        for x in d["declarations"]:
            info = S.analyse(x["type"])
            defn = x.get("definition_source") or x.get("definition")
            rec = {
                "name": x["name"],
                "module": m,
                "kind": x["kind"],
                "eff": info["eff"],
                "signature": re.sub(r"\s+", " ", x["signature"]).strip(),
                # A null doc stays null. An agent handed "" reads the slot
                # as filled and describes the declaration in the author's
                # voice; null lets it say the declaration is undocumented
                # and fall back to the type, which is checked.
                "doc": x.get("doc"),
                "pre": sorted(info["pre"]),
                "post": sorted(info["post"]),
                "args": info["args"],
                "res": info["res"],
                "refs": [r for r in x.get("refs", []) if r != x["name"]],
                "where": x.get("range"),
                "definition": defn,
            }
            out.append(rec)
    return {
        "schema": INDEX_SCHEMA,
        "version": INDEX_VERSION,
        "export_schema": SCHEMA,
        "export_version": VERSION,
        "declarations": out,
    }


class Index:
    def __init__(self, data):
        if data.get("schema") != INDEX_SCHEMA or data.get("version") != INDEX_VERSION:
            raise SystemExit("unexpected index %r version %r"
                             % (data.get("schema"), data.get("version")))
        self.decls = data["declarations"]
        self.by_name = {d["name"]: d for d in self.decls}
        # Reverse of `refs`: who mentions this declaration. The export
        # gives the forward direction only.
        self.mentioned_by = {}
        for d in self.decls:
            for r in d["refs"]:
                self.mentioned_by.setdefault(r, []).append(d["name"])

    def resolve(self, name):
        """Accept a fully qualified name, or a short one if unambiguous.

        An agent usually knows `slice`, not `FStar.Seq.Base.slice`. A short
        name that matches several declarations is reported as ambiguous
        rather than guessed at: picking one silently would send a proof
        after the wrong lemma.
        """
        if name in self.by_name:
            return name, None
        hits = [n for n in self.by_name if short(n) == name]
        if len(hits) == 1:
            return hits[0], None
        if not hits:
            return None, "No declaration is named %r." % name
        return None, ("%r is ambiguous; it could be %s."
                      % (name, ", ".join(sorted(hits)[:8])))


def short(fqn):
    parts = fqn.split(".")
    if len(parts) >= 2 and parts[-1] == "t":
        return parts[-2] + ".t"
    return parts[-1]


# ------------------------------------------------------- type  shapes --

# Mirrors the site's search so both answer the same query the same way:
# a lower-case single letter is any type, `nat` and `pos` also match `int`
# on a second pass, and explicit arguments match in any order.
ALIAS = {"nat": "int", "pos": "int"}


def words(s):
    out = []
    for w in re.split(r"\s+", re.sub(r"[(){}\[\],]", " ", s)):
        if not w:
            continue
        w = re.sub(r"^'", "", w)
        if re.fullmatch(r"[a-z]", w):
            out.append("*")
            continue
        parts = w.split(".")
        if len(parts) > 1 and parts[-1] != "t":
            w = parts[-1]
        out.append(w)
    return out


def tok_eq(a, b, loose):
    if a == "*" or b == "*" or a == b:
        return True
    return loose and ALIAS.get(a, a) == ALIAS.get(b, b)


def part_match(qt, dt, loose):
    if not qt:
        return True
    if len(qt) != len(dt):
        return False
    return all(tok_eq(x, y, loose) for x, y in zip(qt, dt))


def shape_score(parts, d):
    res, args = parts[-1], parts[:-1]
    for loose in (False, True):
        if not part_match(res, d["res"], loose):
            continue
        used = [False] * len(d["args"])
        ok = True
        for qa in args:
            j = next((k for k, da in enumerate(d["args"])
                      if not used[k] and part_match(qa, da, loose)), None)
            if j is None:
                ok = False
                break
            used[j] = True
        if ok:
            return 100 - 10 * (len(d["args"]) - len(args)) - (5 if loose else 0)
    return -1


# ------------------------------------------------------------- answers --


def brief(d):
    """What an agent needs to decide whether to read further."""
    out = {
        "name": d["name"],
        "kind": d["kind"],
        "effect": d["eff"],
        "signature": d["signature"],
        "documented": d["doc"] is not None,
    }
    if d["doc"]:
        out["doc"] = "\n".join(d["doc"])
    if d["where"]:
        out["at"] = "%s:%d" % (d["where"]["file"], d["where"]["start_line"])
    return out


def full(d, include_definition):
    out = brief(d)
    out["module"] = d["module"]
    out["requires_about"] = d["pre"]
    out["ensures_about"] = d["post"]
    out["mentions"] = d["refs"]
    defn = d.get("definition")
    if defn:
        if include_definition or len(defn) <= DEFINITION_PREVIEW:
            out["definition"] = defn
        else:
            out["definition_preview"] = defn[:DEFINITION_PREVIEW]
            out["definition_truncated"] = True
            out["definition_length"] = len(defn)
    if d["doc"] is None:
        out["note"] = ("This declaration has no documentation. Its type is "
                       "checked by F*, so the signature and contract above "
                       "are authoritative; do not present a description of "
                       "it as the author's.")
    return out


def tool_find_by_contract(idx, args):
    name = args.get("name") or ""
    side = args.get("side", "ensures")
    limit = int(args.get("limit", 20))
    if side not in ("ensures", "requires", "either"):
        return {"error": "side must be ensures, requires or either"}

    # Match on the resolved name when one is given, and otherwise on any
    # resolved name whose short form is the one asked for -- reporting
    # which module each group came from, so two `sorted` never merge.
    def hits(field):
        groups = {}
        for d in idx.decls:
            for n in d[field]:
                if n == name or short(n) == name:
                    groups.setdefault(n, []).append(d)
        return groups

    result = {"query": name, "side": side, "groups": []}
    for field, label in (("post", "ensures"), ("pre", "requires")):
        if side not in (label, "either"):
            continue
        for n, ds in sorted(hits(field).items()):
            result["groups"].append({
                "about": n,
                "side": label,
                "total": len(ds),
                "shown": min(len(ds), limit),
                "declarations": [brief(d) for d in ds[:limit]],
            })
    if not result["groups"]:
        result["note"] = ("No declaration's contract mentions %r. Contract "
                          "matching is exact on the last name component, so "
                          "try the whole name, or list_module to see what a "
                          "module offers." % name)
    return result


def tool_find_by_type(idx, args):
    shape = args.get("shape") or ""
    limit = int(args.get("limit", 20))
    if "->" not in shape:
        return {"error": "shape must contain '->', e.g. 'seq a -> nat -> a'"}
    parts = [words(p) for p in shape.split("->")]
    scored = []
    for d in idx.decls:
        s = shape_score(parts, d)
        if s >= 0:
            scored.append((s, d))
    scored.sort(key=lambda x: (-x[0], x[1]["name"]))
    return {
        "query": shape,
        "total": len(scored),
        "shown": min(len(scored), limit),
        "note": "Explicit arguments match in any order; nat and pos also match int.",
        "declarations": [brief(d) for _, d in scored[:limit]],
    }


def tool_lookup(idx, args):
    name = args.get("name") or ""
    resolved, err = idx.resolve(name)
    if err:
        return {"error": err}
    return full(idx.by_name[resolved], bool(args.get("include_definition")))


def tool_used_by(idx, args):
    name = args.get("name") or ""
    limit = int(args.get("limit", 20))
    resolved, err = idx.resolve(name)
    if err:
        return {"error": err}
    users = sorted(idx.mentioned_by.get(resolved, []))
    return {
        "name": resolved,
        "total": len(users),
        "shown": min(len(users), limit),
        "declarations": [brief(idx.by_name[u]) for u in users[:limit]
                         if u in idx.by_name],
    }


def tool_list_module(idx, args):
    module = args.get("module") or ""
    limit = int(args.get("limit", 200))
    ds = [d for d in idx.decls if d["module"] == module]
    if not ds:
        mods = sorted({d["module"] for d in idx.decls})
        return {"error": "No module %r in the index. It holds: %s"
                         % (module, ", ".join(mods))}
    return {
        "module": module,
        "total": len(ds),
        "documented": sum(1 for d in ds if d["doc"] is not None),
        "shown": min(len(ds), limit),
        "declarations": [brief(d) for d in ds[:limit]],
    }


def tool_modules(idx, args):
    mods = {}
    for d in idx.decls:
        m = mods.setdefault(d["module"], {"module": d["module"],
                                          "declarations": 0, "documented": 0})
        m["declarations"] += 1
        if d["doc"] is not None:
            m["documented"] += 1
    return {"modules": [mods[k] for k in sorted(mods)]}


TOOLS = [
    {
        "name": "find_by_contract",
        "description":
            "Find declarations whose contract mentions a name: what a lemma "
            "guarantees (its ensures) or assumes (its requires). This is the "
            "tool for 'which lemma gives me something about X', which cannot "
            "be expressed as a text search. Names are resolved, so two "
            "modules' `sorted` are reported separately.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string",
                         "description": "A declaration name, short or fully qualified."},
                "side": {"type": "string", "enum": ["ensures", "requires", "either"],
                         "description": "Default ensures."},
                "limit": {"type": "integer", "description": "Default 20."},
            },
            "required": ["name"],
        },
        "handler": tool_find_by_contract,
    },
    {
        "name": "find_by_type",
        "description":
            "Find declarations by the shape of their type, written with "
            "arrows, e.g. 'seq a -> nat -> a'. Explicit arguments match in "
            "any order; a lower-case single letter means any type; nat and "
            "pos also match int.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "shape": {"type": "string"},
                "limit": {"type": "integer", "description": "Default 20."},
            },
            "required": ["shape"],
        },
        "handler": tool_find_by_type,
    },
    {
        "name": "lookup",
        "description":
            "The full record of one declaration: signature, effect, what its "
            "contract assumes and guarantees, the names it mentions, its "
            "documentation if it has any, and its definition. A short name is "
            "accepted when it is unambiguous.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string"},
                "include_definition": {
                    "type": "boolean",
                    "description":
                        "Send the whole definition. It is truncated by "
                        "default, because a proof term can be very long.",
                },
            },
            "required": ["name"],
        },
        "handler": tool_lookup,
    },
    {
        "name": "used_by",
        "description":
            "Which declarations mention this one in their type or definition. "
            "Useful for finding worked uses of a lemma.",
        "inputSchema": {
            "type": "object",
            "properties": {"name": {"type": "string"},
                           "limit": {"type": "integer"}},
            "required": ["name"],
        },
        "handler": tool_used_by,
    },
    {
        "name": "list_module",
        "description": "Every public declaration of one module, briefly.",
        "inputSchema": {
            "type": "object",
            "properties": {"module": {"type": "string"},
                           "limit": {"type": "integer"}},
            "required": ["module"],
        },
        "handler": tool_list_module,
    },
    {
        "name": "modules",
        "description":
            "The modules in the index, with how many declarations each has "
            "and how many are documented.",
        "inputSchema": {"type": "object", "properties": {}},
        "handler": tool_modules,
    },
]


# ---------------------------------------------------------------- MCP --

# Line-delimited JSON-RPC 2.0 on stdin and stdout, which is all MCP over
# stdio is. Written against the standard library so the server can run
# wherever an agent runs.


def rpc_result(rid, result):
    return {"jsonrpc": "2.0", "id": rid, "result": result}


def rpc_error(rid, code, message):
    return {"jsonrpc": "2.0", "id": rid, "error": {"code": code, "message": message}}


def handle(idx, msg, state):
    method = msg.get("method")
    rid = msg.get("id")
    params = msg.get("params") or {}

    if method == "initialize":
        # Echo the client's protocol version when it names one: this is a
        # probe, and agreeing with the client is worth more than insisting
        # on a version.
        asked = params.get("protocolVersion")
        state["protocol"] = asked if isinstance(asked, str) else PROTOCOL_FALLBACK
        return rpc_result(rid, {
            "protocolVersion": state["protocol"],
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "fstardoc-retrieval", "version": "0.1"},
        })

    if method in ("notifications/initialized", "initialized"):
        return None

    if method == "ping":
        return rpc_result(rid, {})

    if method == "tools/list":
        return rpc_result(rid, {"tools": [
            {k: t[k] for k in ("name", "description", "inputSchema")} for t in TOOLS]})

    if method == "tools/call":
        name = params.get("name")
        args = params.get("arguments") or {}
        tool = next((t for t in TOOLS if t["name"] == name), None)
        if tool is None:
            return rpc_error(rid, -32602, "No such tool: %r" % name)
        try:
            payload = tool["handler"](idx, args)
        except Exception as e:                                  # noqa: BLE001
            return rpc_result(rid, {
                "content": [{"type": "text", "text": "error: %s" % e}],
                "isError": True,
            })
        return rpc_result(rid, {
            "content": [{"type": "text",
                         "text": json.dumps(payload, indent=1, ensure_ascii=False)}],
            "isError": bool(payload.get("error")) if isinstance(payload, dict) else False,
        })

    if rid is None:
        return None
    return rpc_error(rid, -32601, "Method not found: %r" % method)


def serve(idx, stdin=None, stdout=None):
    stdin = stdin or sys.stdin
    stdout = stdout or sys.stdout
    state = {}
    for line in stdin:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except ValueError:
            stdout.write(json.dumps(rpc_error(None, -32700, "Parse error")) + "\n")
            stdout.flush()
            continue
        reply = handle(idx, msg, state)
        if reply is not None:
            stdout.write(json.dumps(reply, ensure_ascii=False) + "\n")
            stdout.flush()
    return 0


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    b = sub.add_parser("index", help="build the retrieval index")
    b.add_argument("--fstar", required=True)
    b.add_argument("--out", required=True)
    b.add_argument("--cache", action="append", default=[])
    b.add_argument("--include", action="append", default=[])
    b.add_argument("--module", action="append", default=[])
    b.add_argument("--modules-from")

    s = sub.add_parser("serve", help="serve the index over MCP on stdio")
    s.add_argument("--index", required=True)

    args = ap.parse_args(argv[1:])

    if args.cmd == "index":
        modules = list(args.module)
        if args.modules_from:
            for line in open(args.modules_from, encoding="utf-8"):
                line = line.split("#", 1)[0].strip()
                if line:
                    modules.append(line)
        if not modules:
            sys.exit("no modules given: pass --module or --modules-from")
        data = build_index(args.fstar, modules, args.cache, args.include)
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        n = len(data["declarations"])
        documented = sum(1 for d in data["declarations"] if d["doc"] is not None)
        with_contract = sum(1 for d in data["declarations"] if d["pre"] or d["post"])
        sys.stderr.write(
            "%d declarations from %d modules -> %s\n"
            "  %d documented, %d with a contract\n"
            % (n, len({d["module"] for d in data["declarations"]}), args.out,
               documented, with_contract))
        return 0

    with open(args.index, encoding="utf-8") as f:
        return serve(Index(json.load(f)))


if __name__ == "__main__":
    sys.exit(main(sys.argv))
