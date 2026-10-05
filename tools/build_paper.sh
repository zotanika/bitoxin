#!/bin/sh
set -eu
paper_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$paper_root"
"${PYTHON:-python3}" tools/prepare_paper.py
mkdir -p build/paper output/pdf output/paper
cd paper
tectonic "$@" --keep-logs --keep-intermediates --outdir ../build/paper manuscript.tex
cd "$paper_root"
cp build/paper/manuscript.pdf output/pdf/bitoxin-paper-en.pdf
"${PYTHON:-python3}" - <<'PY'
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import re
root = Path('.')
log = (root/'build/paper/manuscript.log').read_text()
if re.search(r'Overfull|There were undefined references|Citation .* undefined|Reference .* undefined', log):
    raise SystemExit('Unresolved layout/citation warning: inspect build/paper/manuscript.log')
inputs = ['manuscript.tex','references.bib','figures/detection.tex','data/walk-rows.tex','data/scan-rows.tex']
with ZipFile(root/'output/paper/bitoxin-paper-en-source.zip', 'w', ZIP_DEFLATED) as z:
    for name in inputs:
        z.write(root/'paper'/name, name)
    z.writestr('BUILD.txt', 'Compile manuscript.tex with Tectonic, or LaTeX + BibTeX + LaTeX twice.\nRequires standard article, geometry, AMS packages, booktabs, TikZ/PGFPlots, xurl, hyperref.\nThe supplied tables and plot contain the recorded experiment results.\nThis is an arXiv-oriented preprint. Use the dedicated arXiv package for submission; confirm publication author details first.\n')
print('output/pdf/bitoxin-paper-en.pdf')
print('output/paper/bitoxin-paper-en-source.zip')
PY
"${PYTHON:-python3}" - <<'PY'
from pathlib import Path
from hashlib import sha256
root = Path('.')
source_files = sorted(p for p in root.rglob('*') if p.is_file() and not any(
    part in {'.git', 'build', 'tmp', 'output', '__pycache__'} for part in p.parts))
def rows(files):
    return ''.join(sha256(p.read_bytes()).hexdigest()+'  '+p.as_posix()+'\n' for p in files)
(root/'output/pdf/source-manifest.sha256').write_text(rows(source_files))
artifact_files = sorted(set(source_files + list((root/'output/verification').glob('*')) + [
    root/'output/pdf/bitoxin-paper-en.pdf', root/'output/paper/bitoxin-paper-en-source.zip']))
(root/'output/paper/artifact-manifest.sha256').write_text(rows(artifact_files))
print('Source/data/artifact SHA-256 manifests refreshed')
PY
