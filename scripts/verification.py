#!/usr/bin/env python3
"""Local verification commands. Fail closed; never dispatch or publish anything.

The compare/replay commands are local diagnostics, not the official Linux
Comparator. The linux command invokes the official sandboxed Lake command.
Each output directory is new or empty, so stale successes cannot be reused.
"""
import argparse
from contextlib import ExitStack
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PRIMITIVES = "Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String Char optParam autoParam semiOutParam outParam Quot Quot.mk Quot.lift Quot.ind".split()


class Failure(Exception):
    def __init__(self, message, code=1):
        super().__init__(message)
        self.code = code if 1 <= code <= 255 else 1


def capture(args):
    try:
        return subprocess.check_output(args, text=True, stderr=subprocess.PIPE).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise Failure(f"Cannot run {shlex.join(args)}: {exc}", 2) from exc


def config(path):
    try:
        data = json.loads(path.read_text())
        unknown = set(data) - {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms", "enable_nanoda"}
        if unknown or ("enable_nanoda" in data and not isinstance(data["enable_nanoda"], bool)):
            raise ValueError(f"unsupported keys or invalid enable_nanoda: {sorted(unknown)}")
        for field in ("challenge_module", "solution_module"):
            if not isinstance(data[field], str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", data[field]):
                raise ValueError(f"invalid {field}")
        for field in ("theorem_names", "definition_names", "permitted_axioms"):
            names = data.get(field, [])
            if not isinstance(names, list) or not all(isinstance(n, str) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", n) for n in names):
                raise ValueError(f"invalid {field}")
            if len(set(names)) != len(names):
                raise ValueError(f"duplicate {field}")
        if not data.get("theorem_names") or not set(data.get("permitted_axioms", [])) <= AXIOMS:
            raise ValueError("empty theorem list or forbidden permitted axiom")
        return data
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise Failure(f"Invalid Comparator configuration {path}: {exc}", 2) from exc


def toolchain_bin():
    try:
        prefix = capture(["lake", "env", "printenv", "LEAN_SYSROOT"])
    except Failure:
        prefix = ""
    if not prefix:
        prefix = str(Path(capture(["lake", "env", "which", "lean"])).parent.parent)
    path = Path(prefix) / "bin"
    if not path.is_dir():
        raise Failure(f"Lean toolchain bin directory does not exist: {path}", 2)
    return path


def run(label, args, output, status_log, stderr_path=None):
    """Record the actual child status before raising; never hide it behind tee."""
    print(f"== {label} (log: {output})", flush=True)
    with status_log.open("a") as log:
        log.write(f"{label} command={shlex.join([str(a) for a in args])}\n")
    started = time.monotonic()
    with ExitStack() as stack:
        log = stack.enter_context(output.open("w"))
        err = stack.enter_context(stderr_path.open("w")) if stderr_path else subprocess.STDOUT
        try:
            proc = subprocess.run([str(a) for a in args], stdout=log, stderr=err)
            code = proc.returncode
        except OSError as exc:
            log.write(f"{exc}\n")
            code = 127
    code = 128 - code if code < 0 else code
    with status_log.open("a") as log:
        log.write(f"{label} exit={code}\n")
        log.write(f"{label} seconds={time.monotonic() - started:.3f}\n")
    if code:
        failed_log = stderr_path if stderr_path and stderr_path.stat().st_size else output
        tail = "\n".join(failed_log.read_text(errors="replace").splitlines()[-12:])
        raise Failure(f"{label} failed (exit {code}); {output}\n{tail}", code)


def nonempty(path):
    if not path.is_file() or path.stat().st_size == 0:
        raise Failure(f"Missing or empty verification export: {path}")


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def compare(cfg, out):
    data = config(cfg)
    cfg_digest = sha256(cfg)
    bin_path = toolchain_bin()
    status = out / "run.log"
    targets = PRIMITIVES + data["theorem_names"] + data.get("permitted_axioms", []) + data.get("definition_names", [])
    for side, field in (("challenge", "challenge_module"), ("solution", "solution_module")):
        export = out / f"{side}.ndjson"
        run(f"export {side}", ["lake", "env", str(bin_path / "leanexport"), data[field], "--", *targets], export, status, out / f"{side}-export.log")
        nonempty(export)
    export_digests = {f"{side}_sha256": sha256(out / f"{side}.ndjson") for side in ("challenge", "solution")}
    run("compile diagnostic", ["lake", "env", "lean", "-c", str(out / "diag.c"), "scripts/LocalComparatorDiagnostic.lean"], out / "compile.log", status)
    run("link diagnostic", [str(bin_path / "leanc"), str(out / "diag.c"), "-o", str(out / "localdiag"), f"-L{bin_path.parent / 'lib/lean'}", "-lLeanExport", "-lLake", "-lLean", "-lStd", "-lInit", "-lleancpp", "-lleanrt"], out / "link.log", status)
    run("comparison", [str(out / "localdiag"), str(cfg), str(out / "challenge.ndjson"), str(out / "solution.ndjson")], out / "compare.log", status)
    text = (out / "compare.log").read_text()
    if "statements and reachable constants match" not in text or "only permitted axioms" not in text:
        raise Failure("Comparator diagnostic exited zero without both success confirmations")
    run("leanchecker", [str(bin_path / "leanchecker"), "--silent", "--from-export", str(out / "solution.ndjson")], out / "leanchecker.log", status)
    if sha256(cfg) != cfg_digest or any(sha256(out / f"{side}.ndjson") != export_digests[f"{side}_sha256"] for side in ("challenge", "solution")):
        raise Failure("Configuration or export changed during comparison/kernel checking")
    return {**export_digests, "config_sha256": cfg_digest}


def replay(cfg, solution, out):
    data = config(cfg)
    cfg_digest = sha256(cfg)
    nonempty(solution)
    bin_path = toolchain_bin()
    status = out / "kernels.log"
    digest = sha256(solution)
    status.write_text(f"solution SHA-256: {digest}\n")
    nanoda = out / "nanoda-config.json"
    nanoda.write_text(json.dumps({"use_stdin": False, "export_file_path": str(solution),
        "permitted_axioms": data.get("permitted_axioms", []), "unpermitted_axiom_hard_error": True,
        "num_threads": 2, "nat_extension": True, "string_extension": True}) + "\n")
    checks = (("leanchecker", "--silent", "--from-export", str(solution)),
              ("nanoda_bin", str(nanoda)),
              ("leanchecker-paranoid", "--silent", "--from-export", str(solution)),
              ("lean4lean", "--import", str(solution)),
              ("con-leche", str(solution)), ("con-ron", str(solution)))
    for name, *args in checks:
        label = "nanoda" if name == "nanoda_bin" else name
        run(label, [str(bin_path / name), *args], out / f"{label}.out", status)
    if sha256(solution) != digest or sha256(cfg) != cfg_digest:
        raise Failure("Solution export or configuration changed during kernel replay")
    return {"solution_sha256": digest, "config_sha256": cfg_digest}


def identity(out):
    status = capture(["git", "status", "--porcelain"])
    if status:
        raise Failure("Evidence collection requires a clean committed checkout; uncommitted changes were found", 2)
    data = {"commit": capture(["git", "rev-parse", "HEAD"]), "tree": capture(["git", "rev-parse", "HEAD^{tree}"]),
            "toolchain": Path("lean-toolchain").read_text().strip(), "platform": sys.platform,
            "lean_version": capture(["lake", "env", "lean", "--version"]),
            "lake_version": capture(["lake", "--version"]),
            "git_status": "clean", "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (out / "identity.json").write_text(json.dumps(data, indent=2) + "\n")


def finish_identity(out):
    data = json.loads((out / "identity.json").read_text())
    if (capture(["git", "status", "--porcelain"]) or
        capture(["git", "rev-parse", "HEAD"]) != data["commit"] or
        capture(["git", "rev-parse", "HEAD^{tree}"]) != data["tree"]):
        raise Failure("Checkout changed during verification; these results do not certify the starting commit")
    data["verified_unchanged_at_end"] = True
    (out / "identity.json").write_text(json.dumps(data, indent=2) + "\n")


def common_checks(out):
    status = out / "evidence.log"
    run("source-scan", [sys.executable, "-I", "scripts/check_sources.py"], out / "source-scan.log", status)
    run("build", ["lake", "build", "SubcriticalCauchy", "BGW", "Challenge", "Solution"], out / "build.log", status)
    run("axiom-audit", ["lake", "env", "lean", "scripts/AxiomAudit.lean"], out / "axiom-audit.log", status)
    text = (out / "axiom-audit.log").read_text()
    if "Axiom audit passed" not in text or "sorryAx" in text:
        raise Failure("Axiom audit did not confirm the permitted axioms")


def collect(out):
    identity(out)
    common_checks(out)
    status = out / "evidence.log"
    run("diagnostic", [sys.executable, "scripts/verification.py", "compare", "comparator.json", str(out / "compare")], out / "compare.log", status)
    run("replays", [sys.executable, "scripts/verification.py", "replay", "comparator.json", str(out / "compare" / "solution.ndjson"), str(out / "kernels")], out / "kernels.log", status)
    finish_identity(out)


def linux(out):
    if sys.platform != "linux":
        raise Failure("Official sandboxed checks require Linux; no sandbox bypass is permitted", 2)
    identity(out)
    common_checks(out)
    status = out / "evidence.log"
    data = config(Path("comparator.json"))
    data["enable_nanoda"] = True
    protected = out / "comparator.json"
    protected.write_text(json.dumps(data, indent=2) + "\n")
    run("official comparator", ["lake", "comparator", "--config", str(protected)], out / "comparator.log", status)
    finish_identity(out)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    p = sub.add_parser("compare"); p.add_argument("config"); p.add_argument("out")
    p = sub.add_parser("replay"); p.add_argument("config"); p.add_argument("solution"); p.add_argument("out")
    p = sub.add_parser("collect"); p.add_argument("out"); p.add_argument("root", nargs="?")
    p = sub.add_parser("linux"); p.add_argument("out")
    args = parser.parse_args()
    out = Path(args.out).resolve()
    root = Path(args.root).resolve() if args.mode == "collect" and args.root else ROOT
    try:
        if out == root or (args.mode in ("collect", "linux") and root in out.parents):
            raise Failure("Put collected evidence outside the checkout", 2)
        if out.exists() and any(out.iterdir()):
            raise Failure(f"Refusing nonempty output directory (old evidence is preserved): {out}", 2)
        out.mkdir(parents=True, exist_ok=True)
    except (Failure, OSError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return exc.code if isinstance(exc, Failure) else 2
    result = {"mode": args.mode, "status": "running", "official_palomar_report": False}
    result_path = out / "result.json"
    result["started_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    result_path.write_text(json.dumps(result, indent=2) + "\n")
    try:
        os.chdir(root)
        if args.mode == "compare": result.update(compare(Path(args.config).resolve(), out))
        elif args.mode == "replay": result.update(replay(Path(args.config).resolve(), Path(args.solution).resolve(), out))
        elif args.mode == "collect": collect(out)
        else: linux(out)
        result.update(status="passed", exit_code=0)
        code = 0
    except (Failure, OSError, ValueError) as exc:
        code = exc.code if isinstance(exc, Failure) else 2
        result.update(status="failed", exit_code=code, error=str(exc))
        print(f"ERROR: {exc}", file=sys.stderr)
    except KeyboardInterrupt:
        code = 130
        result.update(status="interrupted", exit_code=code)
    result["completed_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    result_path.write_text(json.dumps(result, indent=2) + "\n")
    return code


if __name__ == "__main__":
    sys.exit(main())
