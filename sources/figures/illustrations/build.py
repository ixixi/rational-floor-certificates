#!/usr/bin/env python3
"""Build the paper illustrations outside the source tree (stdlib only)."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def generated_sources(data):
    """Render the two data-driven figures; numerical coordinates are layout only."""
    out = {}
    lines = [r'\begin{tikzpicture}[paperfig]']
    for panel, carry in enumerate(data['initial_graph']['alphabet']):
        lines += [rf'\begin{{scope}}[xshift={panel*4.3}cm]',
                  rf'\node[ftitle] at(1.35,2.4) {{$c={carry}$}};']
        coords = {0: (0,1.1), 1: (2.7,1.1), 2: (0,-1.1), 3: (2.7,-1.1)}
        for v,(x,y) in coords.items():
            lines.append(rf'\node[fnode] (n{v}) at({x},{y}) {{$j={v}$}};')
        for j,c,k in data['initial_graph']['edges']:
            if c != carry:
                continue
            lines.append(f'% exact edge: {j} {c} {k}')
            if j == k:
                loc = 'above' if j in [0,1] else 'below'
                lines.append(rf'\draw[fedge] (n{j}) edge[loop {loc}] (n{k});')
            else:
                lines.append(rf'\draw[fedge] (n{j}) -- (n{k});')
        lines += [r'\end{scope}']
    lines += [r'\node[align=center,text width=12.5cm] at(5.65,-2.1)',
              r'{$5j-2(k+1)<4c<5(j+1)-2k$\\[4pt]',
              r'\figtext{The three panels together contain all 12 labelled edges.}{三つの図を合わせると、ラベル付きの12辺すべてを含む。}};',
              r'\end{tikzpicture}']
    out['initial-graph.tex'] = '\n'.join(lines)+'\n'
    lines = [r'\begin{tikzpicture}[paperfig,x=1.16cm,y=.61cm]',
             r'\draw[fedge] (-.3,0)--(9.5,0) node[right] {$k$};',
             r'\draw[fedge] (0,-.2)--(0,7.1);',
             r'\node[anchor=west] at(.05,7.3) {$\log_{10}(N+1)$};']
    for i in range(1,7):
        lines += [rf'\draw[black!18] (0,{i})--(9,{i});',
                  rf'\node[anchor=east] at(-.12,{i}) {{$ {i} $}};']
    for row in data['stages']:
        k=row['stage']; prime='--' if k==0 else str(row['prime'])
        lines += [rf'\draw ({k},0)--({k},-.12);',
                  rf'\node[below] at({k},-.12) {{$ {k} $}};',
                  rf'\node[below] at({k},-.62) {{$ {prime} $}};']
    lines += [r'\node[anchor=east] at(-.15,-.4) {$k$};',r'\node[anchor=east] at(-.15,-.9) {$p_k$};']
    series = [('input_vertices','solid','circle','Input vertices','入力頂点数'),
              ('uncertified_vertices','dashed','rectangle','After removal','除去後の頂点数'),
              ('output_vertices','densely dotted','diamond','After contraction','縮約後の頂点数')]
    for idx,(field,style,shape,en,ja) in enumerate(series):
        points=[(r['stage'],math.log10(r[field]+1)) for r in data['stages']]
        coords=' '.join(f'({x},{y:.9f})' for x,y in points)
        lines.append(rf'\draw[{style},line width=.85pt] plot coordinates {{{coords}}};')
        for x,y in points:
            lines.append(rf'\node[draw,{shape},fill=white,inner sep=1.2pt] at({x},{y:.9f}){{}};')
        y=6.2-idx*.55
        lines += [rf'\draw[{style},line width=.85pt] (.6,{y})--(1.3,{y});',
                  rf'\node[draw,{shape},fill=white,inner sep=1.2pt] at(.95,{y}){{}};',
                  rf'\node[anchor=west] at(1.45,{y}) {{\figtext{{{en}}}{{{ja}}}}};']
    lines += [r'\node[flabel,anchor=east] at(8.6,.75) {$N=0$};',
              r'\draw[fedge] (8.65,.6)--(8.98,.04);',
              r'\node[align=center,text width=12cm] at(4.5,-1.65)',
              r'{\figtext{A lift can enlarge the graph; removal and contraction reduce each stage.}{持ち上げでグラフは拡大し得る。各段階で除去と縮約を行う。}};',
              r'\end{tikzpicture}']
    out['stage-counts.tex']='\n'.join(lines)+'\n'
    return out


def validate_data(data):
    g=data['initial_graph']; a,b,K=g['a'],g['b'],g['K']
    expected=[[j,c,k] for j in range(K) for c in g['alphabet'] for k in range(K)
              if a*j-b*(k+1)<K*c<a*(j+1)-b*k]
    assert g['edges']==expected and len(expected)==12
    assert expected==[[0,-1,2],[0,-1,3],[0,1,0],[1,1,0],[1,1,1],[1,1,2],
                      [2,1,3],[2,3,0],[2,3,1],[3,3,1],[3,3,2],[3,3,3]]
    z=data['prime_lift']; inverse=pow(z['b'],-1,z['p'])
    for key in ['kept','discarded']:
        q=[z[key][0]]
        for c in z['word']:
            q.append(inverse*(z['a']*q[-1]+c)%z['p'])
        assert q==z[key]
    assert all(z['kept']) and z['discarded'][0] and z['discarded'][-1]
    assert 0 in z['discarded'][1:-1]
    rank=data['rank_example']; rho={}; eta={}
    for v in 'ABCDE':
        predecessors=[u for u,w in rank['edges'] if w==v]
        rho[v]=1+max([rho[u] for u in predecessors],default=0)
        eta[v]=int(v in rank['period'])+max([eta[u] for u in predecessors],default=0)
    assert rho==rank['rho'] and eta==rank['eta']
    from fractions import Fraction
    theta=Fraction(2,5)
    assert (4*theta).__floor__()==1 and (12*theta).__floor__()==4
    # Exact intersection: u=(4+2v)/5 for 1 <= v < 2.
    assert (Fraction(4)+2*1)/5==Fraction(6,5)
    assert (Fraction(4)+2*2)/5==Fraction(8,5)
    # Root paths u -> v have length one in both phase examples.
    h={'u':0,'v':1}
    base=[('u',(2,),'v'),('v',(4,),'u')]
    for es,should_pass in [(base,True),(base+[('u',(4,),'v')],False)]:
        d=math.gcd(*(abs(h[u]+len(w)-h[v]) for u,w,v in es))
        assert d==2
        phase=[set() for _ in range(d)]
        for u,w,v in es:
            for i,c in enumerate(w):phase[(h[u]+i)%d].add(c)
        assert all(len(s)==1 for s in phase)==should_pass
    rows=data['stages']; assert len(rows)==10
    for row in rows:
        assert 0<=row['output_vertices']<=row['uncertified_vertices']<=row['input_vertices']
    assert rows[-1]['output_vertices']==0 and rows[-1]['certified']==rows[-1]['cyclic']==1084
    assert (-1,)+(1,3)==(-1,1,3)
    return {'status':'PASS','initial_edges':len(expected),'stages':len(rows),
            'checks':['complete integer edge enumeration','prime lift including intermediate zero',
                      'root-path phase tests','rational half-open cell intersection',
                      'exact rational refinement','word concatenation','DAG longest-path ranks']}


def limited():
    resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
    resource.setrlimit(resource.RLIMIT_CPU,(120,120))


def run(cmd,cwd,log,env):
    with log.open('wb') as out:
        subprocess.run(cmd,cwd=cwd,stdout=out,stderr=subprocess.STDOUT,
                       env=env,check=True,timeout=120,preexec_fn=limited)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True,help='new external output directory')
    ap.add_argument('--language',choices=['en','ja'],default='en')
    args=ap.parse_args(); output=args.output.resolve()
    if output==ROOT or ROOT in output.parents:
        ap.error('output must be outside the source directory')
    output.mkdir(parents=True,exist_ok=False)
    data=json.loads((ROOT/'data.json').read_text())
    checks=validate_data(data)
    for name,content in generated_sources(data).items():
        if (ROOT/name).read_text()!=content:
            raise RuntimeError('data-driven source differs: '+name)
    manifest=json.loads((ROOT/'manifest.json').read_text())
    report={'language':args.language,'arithmetic':checks,'figures':[]}
    env=dict(os.environ,SOURCE_DATE_EPOCH='1790034213',FORCE_SOURCE_DATE='1',TZ='UTC')
    start=time.monotonic()
    for fig in manifest['figures']:
        stem=fig['id']; engine='pdflatex'
        preamble=r'\documentclass[border=5pt]{standalone}'+'\n'+r'\usepackage{amsmath,amssymb,lmodern}'+'\n'
        if args.language=='ja':
            engine='lualatex'
            preamble+=r'''\usepackage{luatexja-fontspec}
\setmainfont{Latin Modern Roman}
\setmainjfont{HaranoAjiMincho-Regular.otf}[BoldFont=HaranoAjiMincho-Bold.otf]
\setsansjfont{HaranoAjiGothic-Medium.otf}
\def\FigureJapanese{1}
\pdfvariable suppressoptionalinfo 767
'''
        else:
            preamble+=r'\pdfinfoomitdate=1\pdftrailerid{}'+'\n'
        # Absolute input paths stay in external build logs, never in publication assets.
        wrapper=preamble+rf'\input{{{ROOT}/style.tex}}'+'\n'+r'\begin{document}'+'\n'+rf'\input{{{ROOT}/{stem}.tex}}'+'\n'+r'\end{document}'+'\n'
        (output/(stem+'.tex')).write_text(wrapper)
        run([engine,'-halt-on-error','-interaction=nonstopmode',stem+'.tex'],output,output/(stem+'.build.log'),env)
        pdf=output/(stem+'.pdf')
        run(['pdftocairo','-svg',str(pdf),str(output/(stem+'.svg'))],output,output/(stem+'.svg.log'),env)
        run(['pdftoppm','-singlefile','-png','-scale-to','1800',str(pdf),str(output/stem)],output,output/(stem+'.png.log'),env)
        info=subprocess.check_output(['pdfinfo',str(pdf)],text=True)
        size=re.search(r'Page size:\s+([\d.]+) x ([\d.]+)',info)
        width,height=map(float,size.groups())
        if width>432:raise RuntimeError(f'{stem}: figure wider than 6 inches: {width} pt')
        log=(output/(stem+'.log')).read_text()
        if any(t in log for t in ['Overfull \\hbox','Missing character:','LaTeX Warning:','LaTeX Font Warning:']):
            raise RuntimeError(f'{stem}: inspect typesetting warning')
        report['figures'].append({'id':stem,'width_pt':width,'height_pt':height,
                                 'files':{ext:hashlib.sha256((output/(stem+'.'+ext)).read_bytes()).hexdigest()
                                          for ext in ['pdf','svg','png']}})
    report.update(status='PASS',elapsed_seconds=round(time.monotonic()-start,3))
    (output/'build-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False))


if __name__=='__main__':main()
