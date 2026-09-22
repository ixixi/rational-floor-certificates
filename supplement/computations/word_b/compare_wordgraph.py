#!/usr/bin/env python3
"""compare_wordgraph.py -- element-wise comparison of normalised graph dumps (B's comparator).

Implements the comparison procedure of computations/word-schema.md §3 without relying on
counts or digests: header parameters, vertex set, edge triple set (endpoints + full word), row order
and duplicate-freeness in each file, and for Q75 the block partition as a family of member sets
(ids ignored) with per-block size / internal_edges / period / rho / eta / phase labels (exact, and
rotation-equivalence reported when not exact).  Missing files count as mismatches.

Usage:
  compare_wordgraph.py pair  FILE_A FILE_B [--json OUT.json] [--max-examples N]
  compare_wordgraph.py batch --out DIR [--max-examples N] LABEL=FILE_A:FILE_B ...

Formats: WORDGRAPH 2 (rows `V q cell`, `E qu cu qv cv w...`) and Q75GRAPH 2 (plus block rows
`B id size internal period rho eta L labels... M q:j ...`; the older marker-less B row form
`B id size internal period rho eta labels(period of them) q:j ...` is also accepted).
"""
import sys, os, json


def parse(path):
    """Returns dict with header params, vertex set, edge set, block dict, and order/dup diagnostics."""
    res = {'path': path, 'exists': os.path.isfile(path)}
    if not res['exists']:
        return res
    header = None
    vertices = set()
    edges = set()
    blocks = {}
    nV = nE = nB = 0
    prev_v = prev_e = None
    v_sorted = e_sorted = True
    v_dup = e_dup = 0
    section = 0   # 0 header, 1 V, 2 E, 3 B ; rows must come in this order
    order_ok = True
    b_ids = []
    block_dup_members = 0
    byte_ok = True
    first = True
    fb = open(path, 'rb')
    for rawline in fb:
        if first and rawline.startswith(b'\xef\xbb\xbf'): byte_ok = False
        first = False
        if not rawline.endswith(b'\n') or b'\r' in rawline or rawline == b'\n': byte_ok = False
        line = rawline.decode('utf-8').rstrip('\n')
        if line == '':
            continue
        if header is None:
            header = line
            continue
        t = line.split(' ')
        kind = t[0]
        if kind == 'V':
            if section > 1: order_ok = False
            section = 1
            v = (int(t[1]), int(t[2]))
            if len(t) != 3: order_ok = False
            if prev_v is not None:
                if v == prev_v: v_dup += 1
                elif v < prev_v: v_sorted = False
            prev_v = v
            vertices.add(v); nV += 1
        elif kind == 'E':
            if section > 2: order_ok = False
            section = 2
            e = (int(t[1]), int(t[2]), int(t[3]), int(t[4]), tuple(int(x) for x in t[5:]))
            if len(e[4]) == 0: order_ok = False
            if prev_e is not None:
                if e == prev_e: e_dup += 1
                elif e < prev_e: e_sorted = False
            prev_e = e
            edges.add(e); nE += 1
        elif kind == 'B':
            section = 3
            bid, size, internal, period, rho, eta = (int(x) for x in t[1:7])
            b_ids.append(bid)
            rest = t[7:]
            if rest and rest[0] == 'L':
                mi = rest.index('M')
                labels = tuple(int(x) for x in rest[1:mi])
                mem_tokens = rest[mi + 1:]
            else:   # marker-less form: `period` labels then members
                labels = tuple(int(x) for x in rest[:period])
                mem_tokens = rest[period:]
            mem_list = [tuple(int(y) for y in x.split(':')) for x in mem_tokens]
            members = frozenset(mem_list)
            if len(mem_list) != len(members) or mem_list != sorted(mem_list): block_dup_members += 1
            if len(members) != size:
                raise ValueError('block size mismatch in %s: %s' % (path, line[:80]))
            if members in blocks:
                block_dup_members += 1
            blocks[members] = {'size': size, 'internal_edges': internal, 'period': period, 'rho': rho, 'eta': eta, 'labels': labels}
            nB += 1
        else:
            raise ValueError('unknown row in %s: %s' % (path, line[:80]))
    fb.close()
    res['byte_format_ok'] = byte_ok
    hp = {}
    parts = header.split(' ')
    hp['kind'] = ' '.join(parts[:2])
    for p in parts[2:]:
        if '=' in p:
            k, v = p.split('=', 1)
            hp[k] = v
    res.update(header=hp, vertices=vertices, edges=edges, blocks=blocks, nV=nV, nE=nE, nB=nB,
               v_sorted=v_sorted, e_sorted=e_sorted, v_dup=v_dup, e_dup=e_dup, sections_in_order=order_ok,
               block_ids_sequential=(b_ids == list(range(len(b_ids)))), block_member_list_issues=block_dup_members,
               header_counts_match_rows=(int(hp.get('vertices', -1)) == nV and int(hp.get('edges', -1)) == nE
                                         and (('blocks' not in hp) or int(hp['blocks']) == nB)),
               edge_endpoints_are_vertices=all((e[0], e[1]) in vertices and (e[2], e[3]) in vertices for e in edges))
    return res


def rotations_equal(x, y):
    if len(x) != len(y):
        return False
    return any(x[i:] + x[:i] == y for i in range(len(x)))


def compare_pair(fa, fb, maxex=20):
    A = parse(fa); B = parse(fb)
    rep = {'file_a': fa, 'file_b': fb, 'exists_a': A['exists'], 'exists_b': B['exists']}
    if not (A['exists'] and B['exists']):
        rep['identical'] = False
        rep['reason'] = 'missing file'
        return rep
    for side, R in (('a', A), ('b', B)):
        rep['format_' + side] = {k: R[k] for k in ('byte_format_ok', 'v_sorted', 'e_sorted', 'v_dup', 'e_dup', 'sections_in_order',
                                                   'header_counts_match_rows', 'edge_endpoints_are_vertices', 'nV', 'nE', 'nB',
                                                   'block_ids_sequential', 'block_member_list_issues')}
        rep['header_' + side] = R['header']
    keys = (set(A['header']) | set(B['header'])) - {'vertices', 'edges', 'blocks'}
    rep['header_param_diff'] = {k: (A['header'].get(k), B['header'].get(k)) for k in keys if A['header'].get(k) != B['header'].get(k)}
    rep['header_count_diff'] = {k: (A['header'].get(k), B['header'].get(k)) for k in ('vertices', 'edges', 'blocks')
                                if A['header'].get(k) != B['header'].get(k)}
    va, vb, ea, eb = A['vertices'], B['vertices'], A['edges'], B['edges']
    v_only_a, v_only_b, e_only_a, e_only_b = va - vb, vb - va, ea - eb, eb - ea
    rep.update(vertices_a=len(va), vertices_b=len(vb), edges_a=len(ea), edges_b=len(eb),
               vertices_only_in_a=len(v_only_a), vertices_only_in_b=len(v_only_b),
               edges_only_in_a=len(e_only_a), edges_only_in_b=len(e_only_b))
    rep['examples'] = {'vertices_only_in_a': sorted(v_only_a)[:maxex], 'vertices_only_in_b': sorted(v_only_b)[:maxex],
                       'edges_only_in_a': sorted(e_only_a)[:maxex], 'edges_only_in_b': sorted(e_only_b)[:maxex]}
    fmt_ok = all(all([R['byte_format_ok'], R['v_sorted'], R['e_sorted'], R['v_dup'] == 0, R['e_dup'] == 0, R['sections_in_order'],
                      R['header_counts_match_rows'], R['edge_endpoints_are_vertices']]) for R in (A, B))
    identical = (not rep['header_param_diff'] and not rep['header_count_diff'] and not v_only_a and not v_only_b
                 and not e_only_a and not e_only_b)
    ba, bb = A['blocks'], B['blocks']
    if ba or bb:
        def covers(blocks, verts):
            tot = sum(len(bl) for bl in blocks)
            seen = set().union(*blocks) if blocks else set()
            return tot == len(verts) and seen == verts
        only_a = [bl for bl in ba if bl not in bb]
        only_b = [bl for bl in bb if bl not in ba]
        attr_diff, label_rot_equiv, label_diff = [], 0, 0
        cyclic_a = sum(1 for bl in ba if ba[bl]['internal_edges'] > 0)
        cyclic_b = sum(1 for bl in bb if bb[bl]['internal_edges'] > 0)
        uncert_a = sum(1 for bl in ba if ba[bl]['internal_edges'] > 0 and len(ba[bl]['labels']) == 0)
        uncert_b = sum(1 for bl in bb if bb[bl]['internal_edges'] > 0 and len(bb[bl]['labels']) == 0)
        d_equal = True
        for bl in ba:
            if bl not in bb:
                continue
            x, y = ba[bl], bb[bl]
            if x != y:
                attr_diff.append({'members_head': sorted(bl)[:3], 'a': x, 'b': y})
                if x['labels'] != y['labels']:
                    if rotations_equal(x['labels'], y['labels']): label_rot_equiv += 1
                    else: label_diff += 1
                if x['period'] != y['period']: d_equal = False
        rep.update(blocks_a=len(ba), blocks_b=len(bb), partition_covers_a=covers(ba, va), partition_covers_b=covers(bb, vb),
                   blocks_only_in_a=len(only_a), blocks_only_in_b=len(only_b), blocks_attribute_diff=len(attr_diff),
                   labels_rotation_equivalent_only=label_rot_equiv, labels_different=label_diff, period_d_equal_on_common_blocks=d_equal,
                   cyclic_blocks_a=cyclic_a, cyclic_blocks_b=cyclic_b, uncertified_cyclic_a=uncert_a, uncertified_cyclic_b=uncert_b,
                   max_rho_a=max((v['rho'] for v in ba.values()), default=0), max_rho_b=max((v['rho'] for v in bb.values()), default=0),
                   max_eta_a=max((v['eta'] for v in ba.values()), default=0), max_eta_b=max((v['eta'] for v in bb.values()), default=0),
                   max_period_a=max((v['period'] for v in ba.values()), default=0), max_period_b=max((v['period'] for v in bb.values()), default=0))
        rep['examples']['blocks_only_in_a'] = [sorted(bl)[:5] for bl in only_a[:maxex]]
        rep['examples']['blocks_only_in_b'] = [sorted(bl)[:5] for bl in only_b[:maxex]]
        rep['examples']['blocks_attribute_diff'] = attr_diff[:maxex]
        identical = identical and not only_a and not only_b and not attr_diff and rep['partition_covers_a'] and rep['partition_covers_b']
    rep['format_ok_both'] = fmt_ok
    rep['identical'] = identical
    rep['identical_and_format_ok'] = identical and fmt_ok
    return rep


def main(argv):
    if len(argv) < 2:
        print(__doc__); return 1
    mode = argv[1]
    maxex = 20
    if mode == 'pair':
        fa, fb = argv[2], argv[3]
        out = None
        i = 4
        while i < len(argv):
            if argv[i] == '--json': out = argv[i + 1]; i += 2
            elif argv[i] == '--max-examples': maxex = int(argv[i + 1]); i += 2
            else: i += 1
        rep = compare_pair(fa, fb, maxex)
        print(json.dumps(rep, default=list))
        if out:
            with open(out, 'w') as f: json.dump(rep, f, indent=1, default=list)
        return 0 if rep.get('identical_and_format_ok') else 3
    if mode == 'batch':
        outdir = None
        pairs = []
        i = 2
        while i < len(argv):
            if argv[i] == '--out': outdir = argv[i + 1]; i += 2
            elif argv[i] == '--max-examples': maxex = int(argv[i + 1]); i += 2
            else:
                label, rest = argv[i].split('=', 1)
                fa, fb = rest.split(':', 1)
                pairs.append((label, fa, fb)); i += 1
        os.makedirs(outdir, exist_ok=True)
        summary = []
        all_ok = True
        for label, fa, fb in pairs:
            rep = compare_pair(fa, fb, maxex)
            rep['label'] = label
            with open(os.path.join(outdir, 'compare-%s.json' % label), 'w') as f:
                json.dump(rep, f, indent=1, default=list)
            row = {k: rep.get(k) for k in ('label', 'file_a', 'file_b', 'exists_a', 'exists_b', 'vertices_a', 'vertices_b', 'edges_a', 'edges_b',
                                           'vertices_only_in_a', 'vertices_only_in_b', 'edges_only_in_a', 'edges_only_in_b',
                                           'header_param_diff', 'header_count_diff', 'blocks_a', 'blocks_b', 'blocks_only_in_a', 'blocks_only_in_b',
                                           'blocks_attribute_diff', 'labels_rotation_equivalent_only', 'labels_different',
                                           'period_d_equal_on_common_blocks', 'uncertified_cyclic_a', 'uncertified_cyclic_b',
                                           'max_rho_a', 'max_rho_b', 'max_eta_a', 'max_eta_b', 'max_period_a', 'max_period_b',
                                           'format_ok_both', 'identical', 'identical_and_format_ok')}
            summary.append(row)
            all_ok = all_ok and bool(rep.get('identical_and_format_ok'))
            print(json.dumps(row, default=list), flush=True)
        with open(os.path.join(outdir, 'summary.json'), 'w') as f:
            json.dump({'all_identical_and_format_ok': all_ok, 'pairs': summary}, f, indent=1, default=list)
        print(json.dumps({'event': 'batch_done', 'pairs': len(summary), 'all_identical_and_format_ok': all_ok}))
        return 0 if all_ok else 3
    print('unknown mode'); return 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
