#!/usr/bin/env python3
"""wgb_ref.py -- literal (brute-force) reference implementation B of the word-graph method.

Written independently of wgb.cpp from the mathematical specification in
proofs/audit-02-word-method.md (sections 2-7, 14).  Standard library only.
No enumeration shortcuts: initial edges by the direct strict inequalities over
all (j, c, k); lifting by iterating every start residue over every letter;
SCC by iterative Kosaraju (two passes); certification, removal and contraction
exactly as in the specification.  Output in the same normalised text format as
wgb.cpp so that the two implementations can be compared byte for byte.

Modes:
  pipeline --a A --b B --K K --carries c,... --primes p,... --out DIR [--stop-after k]
  q75      --a A --b B --M M --K K --carries c,... --out DIR        (E2/E3 factorised; see q75small)
  q75small --a A --b B --M M --K K --carries c,...                  (literal 5-fold loop vs factorised)
"""
import sys, json, time, math
from math import gcd

# ------------------------------------------------------------------ helpers

def parse_ints(s):
    return [int(x) for x in s.split(',') if x != '']


def write_graph(path, a, b, K, modulus, primes, vertices, edges):
    """vertices: iterable of (q, cell); edges: iterable of (u, w, v) with u,v names and w tuple."""
    vs = sorted(set(vertices))
    es = sorted(set((u, v, w) for (u, w, v) in edges))
    with open(path, 'w') as f:
        f.write('WORDGRAPH 2 a=%d b=%d K=%d modulus=%d primes=%s vertices=%d edges=%d\n'
                % (a, b, K, modulus, ','.join(str(p) for p in primes), len(vs), len(es)))
        for (q, c) in vs:
            f.write('V %d %d\n' % (q, c))
        for (u, v, w) in es:
            f.write('E %d %d %d %d %s\n' % (u[0], u[1], v[0], v[1], ' '.join(str(x) for x in w)))
    return len(vs), len(es)

# ------------------------------------------------------------------ initial graph

def initial_graph(a, b, K, carries):
    vertices = [(0, j) for j in range(K)]
    edges = []
    for j in range(K):
        for c in carries:
            for k in range(K):
                if a * j - b * (k + 1) < c * K < a * (j + 1) - b * k:
                    edges.append(((0, j), (c,), (0, k)))
    return vertices, edges

# ------------------------------------------------------------------ SCC (Kosaraju, iterative)

def scc_kosaraju(vertices, edges):
    adj = {v: [] for v in vertices}
    radj = {v: [] for v in vertices}
    for (u, w, v) in edges:
        adj[u].append(v)
        radj[v].append(u)
    order = []
    visited = set()
    for s in vertices:
        if s in visited:
            continue
        visited.add(s)
        stack = [(s, iter(adj[s]))]
        while stack:
            v, it = stack[-1]
            advanced = False
            for x in it:
                if x not in visited:
                    visited.add(x)
                    stack.append((x, iter(adj[x])))
                    advanced = True
                    break
            if not advanced:
                order.append(v)
                stack.pop()
    comp = {}
    ncomp = 0
    for s in reversed(order):
        if s in comp:
            continue
        comp[s] = ncomp
        stack = [s]
        while stack:
            v = stack.pop()
            for x in radj[v]:
                if x not in comp:
                    comp[x] = ncomp
                    stack.append(x)
        ncomp += 1
    return comp, ncomp


def check_partition(vertices, edges, comp, ncomp):
    """Independent check (audit-01 §5): every block strongly connected via internal edges,
    condensation acyclic (topological order exists)."""
    members = [[] for _ in range(ncomp)]
    for v in vertices:
        members[comp[v]].append(v)
    iadj = {v: [] for v in vertices}
    iradj = {v: [] for v in vertices}
    for (u, w, v) in edges:
        if comp[u] == comp[v]:
            iadj[u].append(v)
            iradj[v].append(u)
    for c in range(ncomp):
        if not members[c]:
            return False
        for A in (iadj, iradj):
            seen = {members[c][0]}
            st = [members[c][0]]
            while st:
                v = st.pop()
                for x in A[v]:
                    if x not in seen:
                        seen.add(x)
                        st.append(x)
            if len(seen) != len(members[c]):
                return False
    # condensation acyclic via Kahn
    indeg = [0] * ncomp
    cadj = [set() for _ in range(ncomp)]
    for (u, w, v) in edges:
        if comp[u] != comp[v] and comp[v] not in cadj[comp[u]]:
            cadj[comp[u]].add(comp[v])
            indeg[comp[v]] += 1
    st = [c for c in range(ncomp) if indeg[c] == 0]
    done = 0
    while st:
        c = st.pop()
        done += 1
        for d in cadj[c]:
            indeg[d] -= 1
            if indeg[d] == 0:
                st.append(d)
    return done == ncomp

# ------------------------------------------------------------------ certification (W2)

def certify(block_vertices, internal_edges):
    """Returns (cyclic, certified, d, lambda_list, all_phases_used)."""
    if not internal_edges:
        return False, False, 0, None, True
    root = min(block_vertices)
    iadj = {}
    for (u, w, v) in internal_edges:
        iadj.setdefault(u, []).append((w, v))
    h = {root: 0}
    queue = [root]
    qi = 0
    while qi < len(queue):
        v = queue[qi]; qi += 1
        for (w, x) in iadj.get(v, []):
            if x not in h:
                h[x] = h[v] + len(w)
                queue.append(x)
    if len(h) != len(block_vertices):
        raise RuntimeError('BFS did not cover block')
    d = 0
    for (u, w, v) in internal_edges:
        d = gcd(d, abs(h[u] + len(w) - h[v]))
    if d == 0:
        raise RuntimeError('d == 0 in cyclic block')
    lam = {}
    ok = True
    for (u, w, v) in internal_edges:
        for i, ch in enumerate(w):
            s = (h[u] + i) % d
            if s in lam:
                if lam[s] != ch:
                    ok = False
                    break
            else:
                lam[s] = ch
        if not ok:
            break
    all_used = (len(lam) == d) if ok else True
    if ok and not all_used:
        raise RuntimeError('W2-c violated: unused phase')
    return True, ok, d, ([lam[s] for s in range(d)] if ok else None), all_used

# ------------------------------------------------------------------ prune = contract(remove(G))

def prune(vertices, edges):
    stats = {}
    comp, ncomp = scc_kosaraju(vertices, edges)
    if not check_partition(vertices, edges, comp, ncomp):
        raise RuntimeError('partition check failed')
    members = [[] for _ in range(ncomp)]
    for v in vertices:
        members[comp[v]].append(v)
    internal = [[] for _ in range(ncomp)]
    for e in edges:
        if comp[e[0]] == comp[e[2]]:
            internal[comp[e[0]]].append(e)
    cyclic = certified = uncertified = unc_vertices = 0
    max_d = 0
    uncert_blocks = []
    for c in range(ncomp):
        cyc, cert, d, lam, used = certify(members[c], internal[c])
        if not cyc:
            continue
        cyclic += 1
        max_d = max(max_d, d)
        if cert:
            certified += 1
        else:
            uncertified += 1
            unc_vertices += len(members[c])
            uncert_blocks.append(c)
    # G' = internal edges of uncertified blocks, as a set of triples
    gp_edges = set()
    for c in uncert_blocks:
        for e in internal[c]:
            gp_edges.add((e[0], e[1], e[2]))
    outdeg = {}
    gp_vertices = set()
    for (u, w, v) in gp_edges:
        outdeg[u] = outdeg.get(u, 0) + 1
        gp_vertices.add(u); gp_vertices.add(v)
    for c in uncert_blocks:
        for v in members[c]:
            if outdeg.get(v, 0) == 0:
                raise RuntimeError("G' vertex with outdegree 0")
    macro = set(v for v in gp_vertices if outdeg.get(v, 0) >= 2)
    anchors = 0
    for c in uncert_blocks:
        if not any(v in macro for v in members[c]):
            macro.add(min(members[c]))
            anchors += 1
    out_adj = {}
    for (u, w, v) in gp_edges:
        out_adj.setdefault(u, []).append((w, v))
    macro_edges = set()
    macro_mult = {}
    limit = len(gp_vertices) + 1
    for u in macro:
        for (w, v) in out_adj[u]:
            word = list(w)
            cur = v
            steps = 0
            while cur not in macro:
                outs = out_adj[cur]
                if len(outs) != 1:
                    raise RuntimeError('chain vertex outdegree != 1')
                w2, cur = outs[0]
                word.extend(w2)
                steps += 1
                if steps > limit:
                    raise RuntimeError('chain did not terminate')
            me = (u, tuple(word), cur)
            macro_edges.add(me)
            macro_mult[me] = macro_mult.get(me, 0) + 1
    stats['out_edges_multiset'] = sum(macro_mult.values())
    stats.update(scc=ncomp, cyclic=cyclic, certified=certified, uncertified=uncertified,
                 uncertified_vertices=unc_vertices, max_d=max_d, anchors=anchors,
                 gprime_edges=len(gp_edges), out_vertices=len(macro), out_edges=len(macro_edges),
                 out_max_word_length=max((len(w) for (_, w, _) in macro_edges), default=0))
    return sorted(macro), sorted(macro_edges), stats, macro_mult

# ------------------------------------------------------------------ lift (W4)

def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, int(math.isqrt(p)) + 1))


def crt_name(q, P, s, p):
    """smallest q' in [0, P*p) with q' == q (mod P) and q' == s (mod p), by search over t."""
    for t in range(p):
        cand = q + P * t
        if cand % p == s:
            return cand
    raise RuntimeError('CRT failed')


def lift(vertices, edges, P, primes, p, a, b, mult=None):
    if not is_prime(p) or a % p == 0 or b % p == 0 or p in primes or P % p == 0:
        raise RuntimeError('bad prime')
    binv = next(x for x in range(1, p) if (b * x) % p == 1)
    new_edges = []
    new_mult = {}
    for (u, w, v) in edges:
        for s in range(1, p):
            q = s
            ok = True
            for c in w:
                q = ((a * q + c) % p) * binv % p
                if q == 0:
                    ok = False
                    break
            if ok:
                nu = (crt_name(u[0], P, s, p), u[1])
                nv = (crt_name(v[0], P, q, p), v[1])
                new_edges.append((nu, w, nv))
                new_mult[(nu, w, nv)] = new_mult.get((nu, w, nv), 0) + (mult.get((u, w, v), 1) if mult else 1)
    new_vertices = set()
    for (u, w, v) in new_edges:
        new_vertices.add(u); new_vertices.add(v)
    return sorted(new_vertices), sorted(set(new_edges)), new_mult

# ------------------------------------------------------------------ pipeline

def run_pipeline(args):
    a, b, K = args['a'], args['b'], args['K']
    carries, primes, outdir = args['carries'], args['primes'], args['out']
    stop_after = args.get('stop_after', -1)
    assert a > b >= 2 and gcd(a, b) == 1 and K >= 1
    assert all(1 - b <= c <= a - 1 for c in carries)
    print(json.dumps({'event': 'params', 'impl': 'python-reference', 'a': a, 'b': b, 'K': K,
                      'carries': carries, 'primes': primes}), flush=True)
    t_all = time.time()
    P = 1
    used = []
    vertices, edges = initial_graph(a, b, K, carries)
    mult = {e: 1 for e in edges}
    lift_t = 0.0
    for k in range(len(primes) + 1):
        t0 = time.time()
        nv, ne = write_graph('%s/stage%d_input.txt' % (outdir, k), a, b, K, P, used, vertices, edges)
        in_max = max((len(w) for (_, w, _) in edges), default=0)
        out_v, out_e, st, out_mult = prune(vertices, edges)
        write_graph('%s/stage%d_output.txt' % (outdir, k), a, b, K, P, used, out_v, out_e)
        rec = {'event': 'stage', 'stage': k, 'prime': (primes[k - 1] if k > 0 else 0), 'modulus': P,
               'in_vertices': nv, 'in_edges': ne, 'in_max_word_length': in_max}
        rec.update(st)
        rec['in_edges_multiset'] = sum(mult.values())
        rec['t_lift'] = round(lift_t, 3)
        rec['t_stage_total'] = round(time.time() - t0 + lift_t, 3)
        print(json.dumps(rec), flush=True)
        if k == stop_after:
            print(json.dumps({'event': 'stopped', 'after_stage': k}), flush=True)
            break
        if k == len(primes):
            print(json.dumps({'event': 'final', 'final_output_empty': (len(out_v) == 0 and len(out_e) == 0),
                              'final_out_vertices': len(out_v), 'final_out_edges': len(out_e),
                              't_total': round(time.time() - t_all, 3)}), flush=True)
            break
        if not out_v:
            print(json.dumps({'event': 'final', 'final_output_empty': True, 'note': 'empty before all primes used',
                              't_total': round(time.time() - t_all, 3)}), flush=True)
            break
        tl = time.time()
        p = primes[k]
        vertices, edges, mult = lift(out_v, out_e, P, used, p, a, b, out_mult)
        P *= p
        used = used + [p]
        lift_t = time.time() - tl

# ------------------------------------------------------------------ Q75

def q75_edges_factorised(a, b, M, K, carries, units):
    zs = {}
    for q in units:
        for c in carries:
            zs[(q, c)] = [z for z in range(M) if (b * z - a * q - c) % M == 0 and gcd(z, M) == 1]
    ks = {}
    for j in range(K):
        for c in carries:
            ks[(j, c)] = [k for k in range(K) if a * j - b * (k + 1) < c * K < a * (j + 1) - b * k]
    edges = []
    for q in units:
        for j in range(K):
            for c in carries:
                for z in zs[(q, c)]:
                    for k in ks[(j, c)]:
                        edges.append(((q, j), (c,), (z, k)))
    return edges


def q75_edges_literal(a, b, M, K, carries, units):
    edges = []
    for q in units:
        for j in range(K):
            for c in carries:
                for z in range(M):
                    if gcd(z, M) != 1:
                        continue
                    if (b * z - a * q - c) % M != 0:
                        continue
                    for k in range(K):
                        if a * j - b * (k + 1) < c * K < a * (j + 1) - b * k:
                            edges.append(((q, j), (c,), (z, k)))
    return edges


def run_q75(args, literal=False):
    a, b, M, K, carries = args['a'], args['b'], args['M'], args['K'], args['carries']
    assert a > b >= 2 and gcd(a, b) == 1 and K >= 1 and M >= 2
    t0 = time.time()
    units = [q for q in range(M) if gcd(q, M) == 1]
    vertices = [(q, j) for q in units for j in range(K)]
    edges = q75_edges_literal(a, b, M, K, carries, units) if literal else q75_edges_factorised(a, b, M, K, carries, units)
    edges = sorted(set(edges))
    comp, ncomp = scc_kosaraju(vertices, edges)
    if not check_partition(vertices, edges, comp, ncomp):
        raise RuntimeError('partition check failed')
    members = [[] for _ in range(ncomp)]
    for v in vertices:
        members[comp[v]].append(v)
    internal = [[] for _ in range(ncomp)]
    inter = []
    for e in edges:
        if comp[e[0]] == comp[e[2]]:
            internal[comp[e[0]]].append(e)
        else:
            inter.append((comp[e[0]], comp[e[2]]))
    info = []
    cyclic = certified = uncertified = 0
    max_d = 0
    for c in range(ncomp):
        cyc, cert, d, lam, used = certify(members[c], internal[c])
        info.append((cyc, cert, d, lam))
        if cyc:
            cyclic += 1
            max_d = max(max_d, d)
            if cert:
                certified += 1
            else:
                uncertified += 1
    # rho / eta by Kahn topological order over the condensation
    cadj = [set() for _ in range(ncomp)]
    indeg = [0] * ncomp
    for (cu, cv) in inter:
        if cv not in cadj[cu]:
            cadj[cu].add(cv)
            indeg[cv] += 1
    periodic = [1 if info[c][0] else 0 for c in range(ncomp)]
    rho = [1] * ncomp
    eta = periodic[:]
    st = [c for c in range(ncomp) if indeg[c] == 0]
    topo = []
    while st:
        c = st.pop()
        topo.append(c)
        for d in cadj[c]:
            rho[d] = max(rho[d], rho[c] + 1)
            eta[d] = max(eta[d], eta[c] + periodic[d])
            indeg[d] -= 1
            if indeg[d] == 0:
                st.append(d)
    assert len(topo) == ncomp
    rank_ok = all(rho[cv] >= rho[cu] + 1 for (cu, cv) in inter)
    cyc_ok = all(eta[cv] >= eta[cu] + periodic[cv] for (cu, cv) in inter) and all(eta[c] >= periodic[c] for c in range(ncomp))
    rho_max, eta_max = max(rho), max(eta)
    bounds_ok = rho_max <= 65 and eta_max <= 6 and max_d <= 13 and uncertified == 0 and rank_ok and cyc_ok
    if args.get('out'):
        order = sorted(range(ncomp), key=lambda c: min(members[c]))
        with open(args['out'] + '/q75_graph.txt', 'w') as f:
            f.write('Q75GRAPH 2 a=%d b=%d M=%d K=%d vertices=%d edges=%d blocks=%d\n'
                    % (a, b, M, K, len(vertices), len(edges), ncomp))
            for (q, j) in sorted(vertices):
                f.write('V %d %d\n' % (q, j))
            for (u, v, w) in sorted((u, v, w) for (u, w, v) in edges):   # (q_u, j_u, q_v, j_v, c) order
                f.write('E %d %d %d %d %d\n' % (u[0], u[1], v[0], v[1], w[0]))
            for bi, c in enumerate(order):
                cyc, cert, d, lam = info[c]
                parts = ['B', str(bi), str(len(members[c])), str(len(internal[c])), str(d if cyc else 0), str(rho[c]), str(eta[c]), 'L']
                if cert:
                    parts.extend(str(x) for x in lam)
                parts.append('M')
                parts.extend('%d:%d' % v for v in sorted(members[c]))
                f.write(' '.join(parts) + '\n')
    rec = {'event': 'q75', 'impl': 'python-reference', 'literal_enumeration': literal, 'a': a, 'b': b, 'M': M, 'K': K,
           'vertices': len(vertices), 'edges': len(edges), 'blocks': ncomp, 'cyclic': cyclic, 'certified': certified,
           'uncertified': uncertified, 'max_d': max_d, 'rho_max': rho_max, 'eta_max': eta_max,
           'rank_condition_ok': rank_ok, 'cyc_condition_ok': cyc_ok, 'bounds_ok': bounds_ok,
           't_total': round(time.time() - t0, 3)}
    print(json.dumps(rec), flush=True)
    return edges


def run_q75small(args):
    """Literal 5-fold loop (q,j,c,z,k) versus the factorised enumeration, small parameters."""
    a, b, M, K, carries = args['a'], args['b'], args['M'], args['K'], args['carries']
    units = [q for q in range(M) if gcd(q, M) == 1]
    e1 = sorted(set(q75_edges_literal(a, b, M, K, carries, units)))
    e2 = sorted(set(q75_edges_factorised(a, b, M, K, carries, units)))
    print(json.dumps({'event': 'q75small', 'a': a, 'b': b, 'M': M, 'K': K, 'carries': carries,
                      'literal_edges': len(e1), 'factorised_edges': len(e2), 'identical': e1 == e2}), flush=True)
    return e1 == e2

# ------------------------------------------------------------------ main

def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    mode = argv[1]
    args = {}
    i = 2
    while i < len(argv):
        k = argv[i].lstrip('-').replace('-', '_')
        v = argv[i + 1]
        if k in ('carries', 'primes'):
            args[k] = parse_ints(v)
        elif k == 'out':
            args[k] = v
        else:
            args[k] = int(v)
        i += 2
    args.setdefault('primes', [])
    if mode == 'pipeline':
        run_pipeline(args)
    elif mode == 'q75':
        run_q75(args, literal=False)
    elif mode == 'q75literal':
        run_q75(args, literal=True)
    elif mode == 'q75small':
        return 0 if run_q75small(args) else 3
    else:
        print('unknown mode', mode)
        return 1
    return 0


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    sys.exit(main(sys.argv))
