#!/usr/bin/env python3
"""Source scan of the Lean files against the Palomar layout rules (a text scan, not a proof check).

Checks every `.lean` file outside `.lake`, `.git` and `scratch`: a `module` header (comments may
precede it); at most 10,000 physical lines; no `native_decide`, `bv_decide`, `implemented_by`,
`extern`, `unsafe`, `axiom` or `opaque` declaration, and no bare `import Mathlib`; `sorry` (outside
comments) only in `Challenge.lean`, which must stay within 1,000 lines and 100 KiB and import only
Mathlib modules. Exit status 1 on any violation.
Usage: python3 -I scripts/check_sources.py [ROOT]
"""
import os
import re
import sys

root = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), ".."))
bad = []
count = 0
forbidden = re.compile(r"\b(native_decide|bv_decide|implemented_by|extern|unsafe)\b|^\s*(private\s+)?(axiom|opaque)\s", re.M)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


for d, dirs, files in os.walk(root):
    dirs[:] = [x for x in dirs if x not in (".lake", ".git", "scratch")]
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(d, f)
        rel = os.path.relpath(p, root)
        if os.path.islink(p):
            bad.append(f"{rel}: symbolic link")
            continue
        count += 1
        raw = open(p, "rb").read()
        text = raw.decode("utf-8")
        head = re.sub(r"\A(\s*(--[^\n]*\n|/-(?!-).*?-/))*\s*", "", text, flags=re.S)
        if not head.startswith("module"):
            bad.append(f"{rel}: no `module` header")
        lines = text.count("\n") + (0 if text.endswith("\n") or not text else 1)
        if lines > 10000:
            bad.append(f"{rel}: {lines} lines (> 10,000)")
        code = strip_comments(text)
        if forbidden.search(code):
            bad.append(f"{rel}: forbidden construct `{forbidden.search(code).group(0).strip()}`")
        if re.search(r"^\s*(public\s+)?import\s+Mathlib\s*$", code, re.M):
            bad.append(f"{rel}: bare `import Mathlib`")
        if rel == "Challenge.lean":
            if lines > 1000 or len(raw) > 100 * 1024:
                bad.append(f"{rel}: {lines} lines, {len(raw)} bytes (limit 1,000 lines, 100 KiB)")
            for m in re.finditer(r"^\s*(public\s+)?(meta\s+)?import\s+(\S+)", code, re.M):
                if not m.group(3).startswith("Mathlib."):
                    bad.append(f"{rel}: imports `{m.group(3)}` (only Mathlib allowed)")
        elif re.search(r"\bsorry\b", code):
            bad.append(f"{rel}: `sorry` outside Challenge.lean")
for b in bad:
    print("VIOLATION", b)
print(f"scanned {count} Lean files: {'FAILED' if bad else 'passed'}")
sys.exit(1 if bad else 0)
