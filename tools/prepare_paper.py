#!/usr/bin/env python3
"""Create manuscript tables and plot coordinates from checked experiment data."""
import csv
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
paper = ROOT / 'paper'
rows = list(csv.DictReader((paper / 'data/summary.csv').open()))
by = {(r['experiment'], r['policy'], int(r['boundary'])): r for r in rows}
fmt = lambda n: f'{int(n):,}'
walk, scan = [], []
for k in [0,128,256,384,512]:
    vals = [by['walk_boundary', p, k]['current_detected'] for p in ['retain_scan','walk_only','reset_replay']]
    walk.append(' & '.join([str(k)] + [fmt(v) for v in vals]) + r' \\')
for q in [0,16,32,48,63]:
    r = by['scan_boundary','retain_scan',q]
    scan.append(' & '.join([str(q)] + [fmt(r[c]) for c in ['current_detected','following_detected','max_detection_attempts']]) + r' \\')
(paper / 'data/walk-rows.tex').write_text(r'\begin{tabular}{r r r r}'+'\n'+r'\toprule'+'\n'+r'$k$ & Retain + scan & Walk only & Reset + replay \\'+'\n'+r'\midrule'+'\n'+'\n'.join(walk)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n')
(paper / 'data/scan-rows.tex').write_text(r'\begin{tabular}{r r r r}'+'\n'+r'\toprule'+'\n'+r'$q$ & Current pass & By following pass & Max. attempts \\'+'\n'+r'\midrule'+'\n'+'\n'.join(scan)+'\n'+r'\bottomrule'+'\n'+r'\end{tabular}'+'\n')
plot = [r'\begin{tikzpicture}',r'\begin{axis}[width=\columnwidth,height=4.7cm,',
        r'xlabel={Completed bit visits before injection},ylabel={Detected faults (\%)},',
        r'xmin=0,xmax=512,ymin=-4,ymax=104,xtick={0,128,256,384,512},ytick={0,25,50,75,100},',
        r'tick label style={font=\scriptsize},label style={font=\scriptsize},',
        r'legend style={font=\scriptsize,at={(0.5,-0.35)},anchor=north,draw=none},',
        r'grid=major,grid style={gray!20},legend cell align=left]']
for p, style, label in [('retain_scan','black,mark=square*','Retain + scan'),('walk_only','black,dashed,mark=*','Walk only'),('reset_replay','gray,dotted,mark=triangle*','Reset + replay')]:
    coords=[]
    for k in [0,128,256,384,512]:
        r=by['walk_boundary',p,k]
        coords.append(f'({k},{100*int(r["current_detected"])/int(r["trials"]):g})')
    plot += [r'\addplot['+style+'] coordinates {'+' '.join(coords)+'};',r'\addlegendentry{'+label+'}']
plot += [r'\end{axis}',r'\end{tikzpicture}']
(paper/'figures/detection.tex').write_text('\n'.join(plot)+'\n')
print('Paper tables and plot generated from paper/data/summary.csv')
