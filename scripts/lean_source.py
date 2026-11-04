#!/usr/bin/env python3
"""Lexical helpers shared by the import-graph and retirement audits.

This is deliberately a small, conservative Lean source scanner, not a parser.
It removes nested comments and quoted strings so inactive text cannot
manufacture imports or obscure syntax-level integrity checks.
"""
import re


def executable_text(source: str) -> str:
    """Remove nested Lean comments and string contents, preserving line breaks."""
    out = []
    i = depth = 0
    in_string = False
    while i < len(source):
        c = source[i]
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            if c == "\\" and i + 1 < len(source):
                out.extend("  ")
                i += 2
            elif c == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif source.startswith("--", i):
            e = source.find("\n", i)
            if e < 0:
                e = len(source)
            out.extend(" " * (e - i))
            i = e
        elif source.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    if depth or in_string:
        raise ValueError("unclosed Lean comment or string")
    return "".join(out)


IMPORT_LINE = re.compile(r"^[ \t]*import[ \t]+(.+?)\s*$")
MODULE_NAME = re.compile(r"^[A-Za-z][A-Za-z0-9_.]*$")


def imports_from_code(code: str) -> list[str]:
    """Extract all modules in each active Lean import command.

    Import directives may name multiple modules on one line. Reject import
    syntax we do not understand rather than silently underapproximating the
    reachability graph used to decide which source files are removable.
    """
    result = []
    for number, line in enumerate(code.splitlines(), 1):
        match = IMPORT_LINE.fullmatch(line)
        if match is None:
            continue
        for name in match.group(1).split():
            if MODULE_NAME.fullmatch(name) is None:
                raise ValueError(f"unrecognised import at line {number}: {name!r}")
            result.append(name)
    return result


def lean_imports(source: str) -> list[str]:
    """Extract imports after masking nested Lean comments and strings."""
    return imports_from_code(executable_text(source))
