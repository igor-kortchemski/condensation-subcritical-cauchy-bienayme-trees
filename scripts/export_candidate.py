#!/usr/bin/env python3
"""Export the verification candidate: the tracked files of this checkout that
belong to the Lean artifact, without campaign records, drafts for the author,
the manuscript or agent tooling. The files under `publication/` (the
reader-facing README and metadata) replace their development counterparts at
the same path relative to the root.

Usage: python3 -I scripts/export_candidate.py OUT_DIR
OUT_DIR must not exist. Nothing is committed, pushed or published.
"""
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HOME = str(Path.home())  # local paths in records are shown relative to the home directory

# Top-level paths left out of the candidate, with the reason.
EXCLUDED = {
    ".agents": "agent skills (separately licensed tooling)",
    ".claude": "agent configuration",
    ".orchestration": "campaign records",
    "scratch": "scratch files",
    "handover": "superseded drafts outside the import tree",
    "AGENTS.md": "agent instructions",
    "CLAUDE.md": "agent instructions",
    "HANDOVER.md": "campaign checkpoint",
    "CAMPAIGN_PLAN.md": "campaign plan and token ledger",
    "MANUSCRIPT_CORRECTIONS.md": "draft for the authors only",
    "CITED_WORKS_ERRATA.md": "register for the user only",
    "erratum-ECP2025.tex": "erratum source (the compiled PDF is exported)",
    "subcritical_cauchy_final_arxiv.tex": "manuscript (not relicensed)",
    "tree20000.pdf": "manuscript figure (not relicensed)",
    "00README.json": "arXiv packaging file",
    "publication": "reader-facing versions, copied over their development counterparts",
}
# Individual files left out: statement drafts with `sorry`, outside the import tree, and the
# dependency walk of report D18, which must run outside the module system to see proof terms
# (its recorded output stays in `verification/`), and the audits of the corrections draft,
# the erratum and the cited-works register, which are for the authors only.
EXCLUDED_GLOBS = ["docs/key-statements/*.lean", "scripts/PaperRouteDeps.lean",
                  "verification/2026-11-11-corrections-audit.md",
                  "verification/2026-11-11-cited-errata-audit.md",
                  "verification/2026-11-11-erratum-review.md"]


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    out = Path(sys.argv[1]).resolve()
    if out.exists():
        print(f"refusing existing output directory: {out}", file=sys.stderr)
        return 2
    files = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, check=True,
                           capture_output=True).stdout.decode().split("\0")
    skipped_globs = {str(p.relative_to(ROOT)) for g in EXCLUDED_GLOBS for p in ROOT.glob(g)}
    kept = []
    for rel in files:
        if not rel or rel.split("/")[0] in EXCLUDED or rel in skipped_globs:
            continue
        src = ROOT / rel
        if src.is_symlink() or not src.is_file():
            continue
        dst = out / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        if rel.startswith("verification/") and dst.suffix in {".log", ".txt", ".md", ".json"}:
            text = dst.read_text(errors="surrogateescape")
            if HOME in text:
                dst.write_text(text.replace(HOME, "~"), errors="surrogateescape")
        kept.append(rel)
    for rel in files:
        if rel.startswith("publication/"):
            src = ROOT / rel
            dst = out / rel.removeprefix("publication/")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
            if str(dst.relative_to(out)) not in kept:
                kept.append(str(dst.relative_to(out)))
    print(f"exported {len(kept)} files to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
