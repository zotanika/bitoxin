#!/usr/bin/env python3
"""Package the already-built article with a self-contained arXiv supplement."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--draft', action='store_true', help='permit pending authors; produce draft ZIP only')
args = parser.parse_args()
source = (ROOT/'paper/manuscript.tex').read_text()
author_match = re.search(r'\\author\{([^\n]*)\}', source)
authors_tex = author_match.group(1) if author_match else ''
pending = not authors_tex.strip() or 'Anonymous' in authors_tex
if pending and not args.draft:
    raise SystemExit('Publication author names are pending. Confirm them before building the upload ZIP.')
files = {}
for name in ['manuscript.tex','references.bib','figures/detection.tex','data/walk-rows.tex','data/scan-rows.tex']:
    files[name] = (ROOT/'paper'/name).read_bytes()
bbl = ROOT/'build/paper/manuscript.bbl'
if not bbl.is_file():
    raise SystemExit('Rebuild with tools/build_paper.sh to retain manuscript.bbl first.')
files['manuscript.bbl'] = bbl.read_bytes()
for name in ['bitoxin_core.c','bitoxin_core.h','bitoxin_lane.h',
             'experiments/observability.c','experiments/run_observability.py','experiments/PROTOCOL.md',
             'paper/data/trials.csv.gz','paper/data/summary.csv','paper/data/native-summary.json',
             'paper/data/portable-summary.json','paper/data/sanitize-summary.json']:
    files['anc/'+name] = (ROOT/name).read_bytes()
files['anc/README.md'] = (ROOT/'paper/ancillary-README.md').read_bytes()
license_bytes = (ROOT/'paper/GPL-2.txt').read_bytes()
assert b'GNU GENERAL PUBLIC LICENSE' in license_bytes and len(license_bytes)>15000
files['anc/COPYING'] = license_bytes
for path in sorted((ROOT/'output/verification').glob('*.log')):
    content = path.read_text().replace(str(ROOT), '<workspace>')
    # Terminal capture escape sequences are not useful in a reading copy.
    content = re.sub(r'\x1b\[[0-9;]*[A-Za-z]', '', content)
    files['anc/evidence/'+path.name] = content.encode()
for name in ['host-versions.txt','linux-versions.txt']:
    files['anc/evidence/'+name] = (ROOT/'output/verification'/name).read_bytes()
for name, content in files.items():
    if not name.endswith('.gz'):
        assert str(ROOT).encode() not in content, name
files['anc/SHA256SUMS'] = ''.join(hashlib.sha256(data).hexdigest()+'  '+name[4:]+'\n'
                               for name,data in sorted(files.items()) if name.startswith('anc/')).encode()
out = ROOT/'output/paper'
out.mkdir(parents=True, exist_ok=True)
name = 'bitoxin-arxiv-draft.zip' if pending or args.draft else 'bitoxin-arxiv-upload.zip'
with zipfile.ZipFile(out/name, 'w', zipfile.ZIP_DEFLATED) as z:
    for key, data in sorted(files.items()):
        z.writestr(key, data)
abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', source, re.S).group(1).strip()
assert '\\' not in abstract  # Keep form metadata as plain text.
metadata = {
    'title':'BITOXIN: Preserving State Dependencies to Expose Integrity Failures in Stateful Quality Assurance',
    'authors_status':'pending confirmation' if pending else 'specified in manuscript',
    'authors_latex':authors_tex,
    'abstract':abstract,
    'suggested_primary_category':'cs.SE',
    'comments':'7 pages, 2 figures, 2 tables; includes reproducibility code and data',
    'journal_reference':'', 'doi':'', 'license':'author selects during submission',
    'top_level_file':'manuscript.tex',
    'local_compiler':'Tectonic 0.16.9; arXiv rendering must be checked separately',
    'submitted':False,
}
(out/'arxiv-metadata.json').write_text(json.dumps(metadata, ensure_ascii=False, indent=2)+'\n')
print(out/name)
print(f'{len(files)} entries; publication authors '+('pending' if pending else 'specified'))
# Keep the repository artifact ledger consistent with the dedicated package.
manifest = out/'artifact-manifest.sha256'
paths = {line.split('  ',1)[1] for line in manifest.read_text().splitlines()}
paths.update(['output/paper/'+name, 'output/paper/arxiv-metadata.json'])
manifest.write_text(''.join(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()+'  '+p+'\n' for p in sorted(paths)))
