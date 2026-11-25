"""Build the living paper from a successful Lean audit and a source commit."""
import argparse, html, json, pathlib, re, shutil
p = argparse.ArgumentParser()
p.add_argument("--audit", required=True, type=pathlib.Path)
p.add_argument("--commit", required=True)
p.add_argument("--out", default="docs", type=pathlib.Path)
a = p.parse_args()
if not re.fullmatch(r"[0-9a-f]{40}", a.commit):
    raise SystemExit("Expected full source commit SHA")
root = pathlib.Path(__file__).resolve().parent.parent
claims = json.loads((root/"publication/claims.json").read_text())
audit = a.audit.read_text()
if re.search(r"sorryAx|error:|declaration uses .sorry.", audit):
    raise SystemExit("Unclean Lean audit")
assert len({c["id"] for c in claims}) == len(claims)
allowed = {"propext", "Classical.choice", "Quot.sound"}
rows = []
base = "https://github.com/Svyable/pythagorean-waffle/blob/"+a.commit+"/"
for c in claims:
    source = root/c["module"]
    name = c["theorem"].split(".")[-1]
    if not re.search(r"\btheorem\s+"+re.escape(name)+r"\b", source.read_text()):
        raise SystemExit("Missing declaration: "+c["theorem"])
    m = re.search(r"’"+re.escape(c["theorem"])+r"’ depends on axioms: \[(.*?)\]",audit)
    if not m:
        m = re.search(r"'"+re.escape(c["theorem"])+r"' depends on axioms: \[(.*?)\]",audit)
    if not m or not set(x.strip() for x in m[1].split(",") if x.strip()) <= allowed:
        raise SystemExit("Missing or unexpected axiom audit: "+c["theorem"])
    c["axioms"] = m[1]
    c["source_commit"] = a.commit
    e = html.escape
    rows.append(f'<tr><td>{e(c["id"])}</td><td><a href="{base+e(c["module"])}">{e(c["title"])}</a><br><code>{e(c["theorem"])}</code></td><td>{e(c["scope"])}</td></tr>')
a.out.mkdir(parents=True, exist_ok=True)
template=(root/"publication/whitepaper.html").read_text()
a.out.joinpath("index.html").write_text(template.replace("@@CLAIMS@@","".join(rows)).replace("@@COMMIT@@",a.commit).replace("@@COUNT@@",str(len(claims))))
# Cogentic-inspired persistent ledger, generated only from a clean audit.
ledger = {}
for name, ax in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", audit):
    axioms = sorted(x.strip() for x in ax.split(",") if x.strip())
    if not set(axioms) <= allowed:
        raise SystemExit("Unexpected axiom in ledger: "+name)
    if name in ledger and ledger[name]["axioms"] != axioms:
        raise SystemExit("Conflicting audit entries: "+name)
    ledger[name] = {"theorem": name, "axioms": axioms, "source_commit": a.commit}
if not ledger:
    raise SystemExit("Empty proof ledger")
a.out.joinpath("proof-ledger.json").write_text(json.dumps(list(ledger.values()),indent=2)+"\n")
a.out.joinpath("claims.json").write_text(json.dumps(claims,indent=2)+"\n")
shutil.copyfile(a.audit,a.out/"axiom-audit.txt")
raw=a.out/"raw_materials"
raw.mkdir(exist_ok=True)
for name in ["README.md","GEOMETRY.md","SIMILARITY.md","CHARACTERIZATION.md","RESEARCH.md"]:
    shutil.copyfile(root/name,raw/name)
shutil.copyfile(root/"publication/literature.md",raw/"literature.md")
shutil.copyfile(a.out/"claims.json",raw/"claims.json")
shutil.copyfile(a.audit,raw/"axiom-audit.txt")
a.out.joinpath(".nojekyll").touch()
print(f"Generated paper for {a.commit}: {len(claims)} audited claims")
