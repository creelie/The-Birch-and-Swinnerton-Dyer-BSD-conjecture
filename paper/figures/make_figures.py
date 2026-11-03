"""Figures of the paper.  Run from paper/figures:  python3 make_figures.py [DATA_DIR]
DATA_DIR (default ../../results/data) holds rank3.jsonl.gz; without it the two rank-three
figures are skipped."""
import gzip
import json
import math
import os
import sys
from collections import defaultdict

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Wedge, Polygon
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401

plt.rcParams.update({'font.family': 'serif', 'mathtext.fontset': 'cm', 'font.size': 11})
DPI = 200
INK = '#1d2b3a'
BLUE = '#2f6690'
TEAL = '#3a7d44'
SAND = '#d9a441'
RED = '#b23a48'
GREY = '#8a96a3'


def save(fig, name):
    fig.savefig(name + '.png', dpi=DPI, bbox_inches='tight', facecolor='white')
    plt.close(fig)


# ---------------------------------------------------------------- 1. the logic of the proof
def fig_logic():
    fig, ax = plt.subplots(figsize=(9.2, 5.6))
    ax.set_xlim(0, 100); ax.set_ylim(0, 64); ax.axis('off')

    def box(x, y, w, h, text, col, fs=10.5):
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle='round,pad=0.6,rounding_size=1.6',
                                    fc=col, ec=INK, lw=1.1, alpha=0.95))
        ax.text(x + w / 2, y + h / 2, text, ha='center', va='center', fontsize=fs, color=INK)

    def arrow(x0, y0, x1, y1, label=None, off=(0, 0)):
        ax.add_patch(FancyArrowPatch((x0, y0), (x1, y1), arrowstyle='-|>', mutation_scale=16,
                                     lw=1.3, color=INK))
        if label:
            ax.text((x0 + x1) / 2 + off[0], (y0 + y1) / 2 + off[1], label, fontsize=9.5,
                    color=INK, ha='center', va='center', style='italic')

    box(2, 47, 28, 11, 'modular symbols\n$[b/p^2]^+,\\ [b/p]^+$', '#e7eef6')
    box(36, 47, 28, 11, 'coefficient $a_r$ of $T^r$\nin $L_p(E,T)$, mod $p^{n-1}$', '#e7eef6')
    box(70, 47, 28, 11, 'points $P_1,\\dots,P_r$\n$p$-adic regulator, $S$', '#e7eef6')
    box(30, 26, 40, 11, '$v_p(a_r)=v_p(S)<\\infty$', '#fbecd0', fs=12)
    box(2, 4, 29, 13, 'Kato:\n$f_E \\mid L_p(E,T)$ in $\\Lambda$', '#e3f0e5')
    box(69, 4, 29, 13, 'Schneider, Perrin-Riou:\n$\\mathrm{ord}\\,f_E\\geq\\mathrm{rank}$,\nleading term of $f_E$', '#e3f0e5', fs=10)
    box(35.5, 4, 29, 13, '$\\mathrm{rank}=r$,  $\\mathrm{Reg}_p\\neq0$\nШ$(E/\\mathbf{Q})[p^\\infty]=0$\n$L_p=f_E\\cdot$unit', '#f6dfe2', fs=10.5)
    arrow(30.5, 52.5, 35.5, 52.5, 'Riemann sums', (0, 8.6))
    arrow(50, 46.4, 50, 37.6)
    arrow(84, 46.4, 66, 37.6)
    arrow(50, 25.4, 50, 17.6, 'comparison', (8, 0))
    arrow(31.6, 10.5, 34.9, 10.5)
    arrow(68.4, 10.5, 65.1, 10.5)
    save(fig, 'fig_logic')


# ---------------------------------------------------------------- 2. the range of the results
def fig_landscape():
    fig, ax = plt.subplots(figsize=(8.6, 4.6))
    ax.add_patch(plt.Rectangle((1, 1.6), math.log10(30000) - 1, 1.8, fc='#e7eef6', ec=BLUE, lw=1.0))
    ax.text(2.6, 3.62, 'Stein–Wuthrich 2013:\n$N\\leq 30\\,000$, rank $2$ and $3$', fontsize=9.5,
            color=BLUE, ha='center', va='bottom')
    ax.add_patch(plt.Rectangle((math.log10(30000), 2.8), 1 - math.log10(3), 0.4, fc='#fbecd0',
                               ec=SAND, lw=1.2))
    ax.text(4.75, 2.55, '494 classes of rank $3$,\n$30\\,000<N\\leq 100\\,000$', fontsize=9.5,
            color='#8a5a00', ha='left', va='top')
    pts = [(234446, 4, '234446a1', 'every ordinary $p<1000$'),
           (19047851, 5, '19047851a1', '$7\\leq p\\leq 19$'),
           (5187563742, 6, '5187563742a1', '$p=7$')]
    for N, r, lab, pr in pts:
        x = math.log10(N)
        ax.scatter([x], [r], s=90, color=RED, zorder=5, edgecolor=INK)
        ax.text(x + 0.12, r + 0.12, lab, fontsize=10, color=INK)
        ax.text(x + 0.12, r - 0.3, pr, fontsize=9, color=GREY)
    ax.set_xlim(1, 11.2); ax.set_ylim(1.4, 6.8)
    ax.set_xlabel('$\\log_{10}$ of the conductor $N$')
    ax.set_ylabel('rank of $E(\\mathbf{Q})$')
    ax.set_yticks([2, 3, 4, 5, 6])
    for s in ('top', 'right'):
        ax.spines[s].set_visible(False)
    ax.grid(axis='y', color='#e5e5e5', lw=0.6)
    save(fig, 'fig_landscape')


# ---------------------------------------------------------------- 3. the cyclotomic tower
def fig_tower():
    fig = plt.figure(figsize=(8.0, 5.4))
    ax = fig.add_subplot(111, projection='3d')
    import numpy as np
    levels = [0, 1, 2, 3]
    names = ['$\\mathbf{Q}$', '$\\mathbf{Q}_1$', '$\\mathbf{Q}_2$', '$\\mathbf{Q}_3$']
    for k in levels:
        z = 1.25 * k
        sz = 1.0 + 0.35 * k
        xs = [-sz, sz, sz, -sz]; ys = [-sz, -sz, sz, sz]
        verts = [list(zip(xs, ys, [z] * 4))]
        from mpl_toolkits.mplot3d.art3d import Poly3DCollection
        pc = Poly3DCollection(verts, alpha=0.35, facecolor=['#cfe0ef', '#d6ead9', '#f5e3bf', '#efd2d6'][k],
                              edgecolor=INK, lw=0.8)
        ax.add_collection3d(pc)
        ax.text(sz + 0.25, 0, z, names[k], fontsize=13, color=INK)
        ax.text(-4.3 - 0.35 * k, -1.2, z + 0.62,
                ['$[\\mathbf{Q}_1:\\mathbf{Q}]=p$', '$[\\mathbf{Q}_2:\\mathbf{Q}_1]=p$', '$[\\mathbf{Q}_3:\\mathbf{Q}_2]=p$', ''][k],
                fontsize=10, color='#4a5866')
    ax.text(0, 0, 1.25 * 3 + 1.9, '$\\mathbf{Q}_\\infty\\subset\\mathbf{Q}(\\mu_{p^\\infty})$,'
            '  $\\Gamma=\\mathrm{Gal}(\\mathbf{Q}_\\infty/\\mathbf{Q})\\cong\\mathbf{Z}_p$', fontsize=11,
            ha='center', color=INK)
    ax.plot([0, 0], [0, 0], [0, 1.25 * 3 + 0.7], color=RED, lw=1.6)
    ax.text(0.15, 0.15, 0.55, '$\\gamma\\mapsto 1+T$', fontsize=10, color=RED)
    ax.set_xlim(-3.6, 2.2); ax.set_ylim(-2.2, 2.2); ax.set_zlim(0, 5.6)
    ax.view_init(elev=17, azim=-62)
    ax.set_axis_off()
    save(fig, 'fig_tower')


# ---------------------------------------------------------------- 4. the measure at p = 5
def fig_balls():
    """Residue classes of Z_5^x modulo 5 (inner ring) and 25 (outer ring) for 234446a1, with the
    modular symbols x(r) = 2[r]^+ (the values used in Section 8); the four classes
    omega(a)*6^4 that give the coefficient of T^4 are highlighted."""
    lev1 = {1: 8, 2: -8, 3: -8, 4: 8}
    lev2 = {1: -5, 2: 8, 3: 8, 4: -7, 6: -5, 7: 6, 8: 6, 9: -8, 11: -7, 12: 4, 13: 4, 14: -7, 16: -8,
            17: 6, 18: 6, 19: -5, 21: -7, 22: 8, 23: 8, 24: -5}
    hot = {21, 22, 3, 4}
    fig, ax = plt.subplots(figsize=(6.6, 6.6))
    ax.set_aspect('equal'); ax.axis('off')
    for a in range(1, 5):
        t0 = 90 - (a - 1) * 90; t1 = t0 - 90
        ax.add_patch(Wedge((0, 0), 1.0, t1, t0, width=0.55, fc=['#cfe0ef', '#d6ead9', '#f5e3bf', '#efd2d6'][a - 1],
                           ec=INK, lw=1.0))
        tm = math.radians((t0 + t1) / 2)
        ax.text(0.72 * math.cos(tm), 0.72 * math.sin(tm), f'${a}+5\\mathbf{{Z}}_5$\n$x={lev1[a]}$',
                ha='center', va='center', fontsize=10)
        bs = [b for b in range(1, 25) if b % 5 == a]
        for i, b in enumerate(bs):
            s0 = t0 - i * 18; s1 = s0 - 18
            ax.add_patch(Wedge((0, 0), 1.75, s1, s0, width=0.7,
                               fc=(SAND if b in hot else 'white'), ec=INK, lw=0.8, alpha=0.9))
            sm = math.radians((s0 + s1) / 2)
            ax.text(1.4 * math.cos(sm), 1.4 * math.sin(sm), f'{b}\n{lev2[b]:+d}', ha='center',
                    va='center', fontsize=8.6)
    ax.text(0, 0, '$\\mathbf{Z}_5^{\\times}$', ha='center', va='center', fontsize=15)
    ax.set_xlim(-1.95, 1.95); ax.set_ylim(-1.95, 1.95)
    save(fig, 'fig_balls')


# ---------------------------------------------------------------- 5, 6. rank three
def load_rank3(d):
    f = os.path.join(d, 'rank3.jsonl.gz')
    if not os.path.exists(f):
        return None
    return [json.loads(l) for l in gzip.open(f, 'rt')]


def fig_rank3_bars(R):
    import numpy as np
    bands = [(30000, 45000), (45000, 60000), (60000, 75000), (75000, 90000), (90000, 100001)]
    ps = sorted(set(r['p'] for r in R))
    H = np.zeros((len(bands), len(ps)))
    for r in R:
        if r['status'] != 'certified':
            continue
        b = [i for i, (lo, hi) in enumerate(bands) if lo < r['N'] <= hi or (i == 0 and r['N'] == lo)]
        H[b[0], ps.index(r['p'])] += 1
    fig = plt.figure(figsize=(9.2, 5.6))
    ax = fig.add_subplot(111, projection='3d')
    cols = ['#2f6690', '#3a7d44', '#d9a441', '#b23a48', '#6c4f8a']
    for i in range(len(bands)):
        ax.bar3d(np.arange(len(ps)) - 0.35, [i] * len(ps), 0, 0.7, 0.55, H[i], color=cols[i],
                 alpha=0.85, shade=True, edgecolor='white', linewidth=0.3)
    ax.set_xticks(range(0, len(ps), 2)); ax.set_xticklabels([str(p) for p in ps[::2]], fontsize=8)
    ax.set_yticks(range(len(bands)))
    ax.set_yticklabels(['30–45', '45–60', '60–75', '75–90', '90–100'], fontsize=8)
    ax.set_xlabel('prime $p$', labelpad=6); ax.set_ylabel('$N/1000$', labelpad=8)
    ax.set_zlabel('pairs proved', labelpad=4)
    ax.view_init(elev=24, azim=-58)
    save(fig, 'fig_rank3_bars')


def fig_irregular(R):
    tot = defaultdict(int); irr = defaultdict(int)
    for r in R:
        tot[r['p']] += 1
        if (r.get('vS') or 0) > 0:
            irr[r['p']] += 1
    ps = sorted(tot)
    y = [p * irr[p] / tot[p] for p in ps]
    fig, ax = plt.subplots(figsize=(8.2, 3.8))
    ax.bar(ps, y, width=1.4, color=BLUE, alpha=0.85)
    m = sum(irr.values()) and sum(p * irr[p] for p in ps) / sum(tot[p] for p in ps)
    ax.axhline(sum(y) / len(y), color=RED, lw=1.2, ls='--')
    ax.text(ps[-1] + 1, sum(y) / len(y) + 0.04, 'mean %.2f' % (sum(y) / len(y)), color=RED,
            fontsize=9.5, ha='right', va='bottom')
    ax.set_xlabel('prime $p$')
    ax.set_ylabel('$p\\,\\times$ proportion with $v_p(S)>0$')
    for s in ('top', 'right'):
        ax.spines[s].set_visible(False)
    save(fig, 'fig_irregular')


def fig_levels(R):
    import numpy as np
    ps = sorted(set(r['p'] for r in R))
    H = np.zeros((4, len(ps)))
    for r in R:
        H[(r.get('vS') or 0), ps.index(r['p'])] += 1
    fig = plt.figure(figsize=(9.2, 5.4))
    ax = fig.add_subplot(111, projection='3d')
    cols = ['#2f6690', '#3a7d44', '#d9a441', '#b23a48']
    for v in range(4):
        z = 1 + np.log10(np.maximum(H[v], 1))
        m = H[v] > 0
        ax.bar3d(np.arange(len(ps))[m] - 0.35, [3 - v] * int(m.sum()), 0, 0.7, 0.55, z[m], color=cols[v],
                 alpha=0.88, shade=True, edgecolor='white', linewidth=0.3)
    ax.set_xticks(range(0, len(ps), 2)); ax.set_xticklabels([str(p) for p in ps[::2]], fontsize=8)
    ax.set_yticks(range(4)); ax.set_yticklabels(['5', '4', '3', '2'], fontsize=9)
    ax.set_zticks([1, 2, 3, 4]); ax.set_zticklabels(['1', '10', '100', '1000'], fontsize=8)
    ax.set_zlim(0, 4)
    ax.set_xlabel('prime $p$', labelpad=6); ax.set_ylabel('level $n=v_p(S_p)+2$', labelpad=8)
    ax.set_zlabel('pairs (log scale)', labelpad=4)
    ax.view_init(elev=26, azim=-62)
    save(fig, 'fig_levels')


def fig_leading(L):
    import numpy as np
    fig = plt.figure(figsize=(11.2, 5.0))
    for k, p in enumerate((7, 13)):
        ax = fig.add_subplot(1, 2, k + 1, projection='3d')
        H = np.zeros((p, p))
        for r in L:
            if r['p'] != p: continue
            v = r['v']
            H[(r['a3'] // p ** (v + 1)) % p, (r['S'] // p ** (v + 1)) % p] += 1
        xs, ys = np.meshgrid(np.arange(p), np.arange(p), indexing='ij')
        xs, ys, hs = xs.ravel(), ys.ravel(), H.ravel()
        cols = ['#2f6690' if h > 0 else '#dfe3e8' for h in hs]
        ax.bar3d(xs - 0.4, ys - 0.4, 0, 0.8, 0.8, np.maximum(hs, 0.12), color=cols, alpha=1.0,
                 shade=True, edgecolor='white', linewidth=0.25)
        ax.set_xticks(range(0, p, 2)); ax.set_yticks(range(0, p, 2))
        ax.tick_params(labelsize=8)
        ax.set_xlabel('second digit of $a_3$', labelpad=4, fontsize=9)
        ax.set_ylabel('second digit of $S_p$', labelpad=4, fontsize=9)
        ax.set_zlabel('pairs', labelpad=2, fontsize=9)
        ax.set_title(f'$p={p}$, {int(H.sum())} pairs', fontsize=10)
        ax.view_init(elev=30, azim=-58)
    save(fig, 'fig_leading')


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    data = sys.argv[1] if len(sys.argv) > 1 else os.path.join('..', '..', 'results', 'data')
    fig_logic(); fig_landscape(); fig_tower(); fig_balls()
    R = load_rank3(data)
    if R:
        fig_rank3_bars(R); fig_irregular(R); fig_levels(R)
    lf = os.path.join(data, 'leading.jsonl')
    if os.path.exists(lf):
        fig_leading([json.loads(l) for l in open(lf)])
    print('done')
