import io, os, re, glob

ENVS = r"(theorem|lemma|proposition|corollary|definition)"
pat = re.compile(r"\\begin\{" + ENVS + r"\}(.*?)\\end\{\1\}", re.S)
proofpat = re.compile(r"\\begin\{proof\}(.*?)\\end\{proof\}", re.S)

rows = []
for fn in sorted(glob.glob(os.path.join("blueprint", "src", "parts", "*.tex"))):
    s = io.open(fn, encoding="utf-8").read()
    # walk the file, pairing each statement env with the proof block that follows it
    for m in pat.finditer(s):
        env, body = m.group(1), m.group(2)
        lab = re.search(r"\\label\{([^}]*)\}", body)
        if not lab:
            continue
        label = lab.group(1)
        stmt_ok = "\\leanok" in body
        has_lean = "\\lean{" in body
        notready = "\\notready" in body
        # the next proof block after this environment, if it starts before the next env
        rest = s[m.end():]
        nxt_env = pat.search(rest)
        nxt_proof = proofpat.search(rest)
        proof_ok = None
        if nxt_proof and (nxt_env is None or nxt_proof.start() < nxt_env.start()):
            proof_ok = "\\leanok" in nxt_proof.group(1)
        rows.append((os.path.basename(fn), label, env, has_lean, stmt_ok, notready, proof_ok))

check_only = "--check" in __import__("sys").argv

bad = []
lines = []
for fn, label, env, has_lean, stmt_ok, notready, proof_ok in rows:
    if not has_lean:
        continue
    flag = ""
    if stmt_ok and not notready and proof_ok is False:
        flag = "  <-- statement leanok, proof block NOT leanok"
        bad.append((fn, label))
    lines.append(f"{label:42} {env:12} {'y':5} {'y' if stmt_ok else '-':5} "
                 f"{('y' if proof_ok else ('-' if proof_ok is False else 'none')):6}{flag}")

if not check_only:
    print(f"{'label':42} {'env':12} {'lean':5} {'stmt':5} {'proof':6}")
    print("\n".join(lines))
    print()
    print(f"nodes with \\lean tag: {sum(1 for r in rows if r[3])}")
    print(f"statement \\leanok:    {sum(1 for r in rows if r[3] and r[4])}")

if bad:
    for fn, label in bad:
        print(f"  {fn}: {label} -- statement is \\leanok but its proof block is not")
    print(f"FAIL: {len(bad)} node(s) will paint blue in the dependency graph despite being proved.")
    print("      Add \\leanok inside the proof environment, or say in the node why not.")
    raise SystemExit(1)

if not check_only:
    print("MISMATCH (stmt ok, proof block present but not ok): 0")
else:
    print(f"OK: {sum(1 for r in rows if r[3] and r[4])} \\leanok statements, all proofs agree.")
