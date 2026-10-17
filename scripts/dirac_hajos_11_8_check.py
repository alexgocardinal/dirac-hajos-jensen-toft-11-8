"""Finite certificates for a counterexample to Jensen--Toft, Problem 11.8.

Run: python3 dirac_hajos_11_8_check.py [--write-json OUTPUT.json]
Vertices of B are 0,...,11. The shared clique is (0,1,2),
the deleted edge is 03, and the edge witnessing noncriticality is 01.
No nonstandard dependencies are required.
"""
from __future__ import annotations

import argparse
import itertools
import json

B_EDGES = tuple(sorted({
    (0,1),(0,2),(0,3),(0,4),(0,11),
    (1,2),(1,6),(1,7),(1,10),
    (2,9),(2,11),
    (3,5),(3,8),(3,11),
    (4,6),(4,7),(4,8),(4,9),
    (5,6),(5,8),
    (6,9),(6,10),
    (7,8),(8,10),
}))
T = (0,1,2)

def valid(colors, edges):
    return all(colors[u] != colors[v] for u, v in edges)

def normalized(colors):
    mapping = {}
    return ''.join(str(mapping.setdefault(c, len(mapping))) for c in colors)

def find_coloring(n, edges, q):
    """Independent DSATUR search; None means exhaustive failure."""
    adj = [set() for _ in range(n)]
    for u,v in edges:
        adj[u].add(v)
        adj[v].add(u)
    colors = [-1]*n
    def search(left):
        if left == 0:
            return tuple(colors)
        u = max((v for v in range(n) if colors[v] < 0),
                key=lambda v:(len({colors[w] for w in adj[v] if colors[w]>=0}),len(adj[v]),-v))
        forbidden = {colors[w] for w in adj[u] if colors[w]>=0}
        for c in range(q):
            if c not in forbidden:
                colors[u] = c
                result = search(left-1)
                if result is not None:
                    return result
        colors[u] = -1
        return None
    return search(n)

def fixed_colorings(edges, fixed):
    """Directly enumerate all 3-colorings with fixed colors on 0,1,2."""
    free = [v for v in range(12) if v not in fixed]
    result = []
    for assignment in itertools.product(range(3), repeat=len(free)):
        colors = [fixed.get(v,-1) for v in range(12)]
        for v,c in zip(free,assignment):
            colors[v] = c
        if valid(colors,edges):
            result.append(''.join(map(str,colors)))
    return result

def output_graph(k):
    assert k >= 5
    r = k-4
    # B_1 has labels 0,...,11. B_2 shares T and uses labels 12,...,20.
    second = {i: i if i in T else 12 + i-3 for i in range(12)}
    # The expression above would shift labels 3,...,11 to 12,...,20.
    assert [second[i] for i in range(3,12)] == list(range(12,21))
    Q1 = tuple(range(21,21+r))
    Q2 = tuple(range(21+r,21+2*r))
    edges = set(B_EDGES)
    edges.update(tuple(sorted((second[u],second[v]))) for u,v in B_EDGES)
    for clique, base in ((Q1,tuple(range(12))),(Q2,tuple(second[i] for i in range(12)))):
        edges.update(itertools.combinations(clique,2))
        edges.update(tuple(sorted((a,b))) for a in clique for b in base)
    edges.remove((0,3))
    edges.remove((0,second[3]))
    edges.add((3,second[3]))
    return 21+2*r, tuple(sorted(edges)), second, Q1, Q2

def input_graph(k):
    """One k-critical input K_(k-4) join B, with local labels."""
    assert k >= 5
    clique = tuple(range(12,k+8))
    edges = set(B_EDGES)
    edges.update(itertools.combinations(clique,2))
    edges.update((i,a) for i in range(12) for a in clique)
    return k+8, tuple(sorted(edges))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-json', metavar='PATH')
    args = parser.parse_args()
    assert len(B_EDGES)==24
    assert all(0<=u<v<12 for u,v in B_EDGES)
    assert {(0,1),(0,2),(1,2),(0,3)} <= set(B_EDGES)
    assert {(1,3),(2,3)}.isdisjoint(B_EDGES)
    less03 = tuple(e for e in B_EDGES if e != (0,3))
    less03_01 = tuple(e for e in less03 if e != (0,1))
    distinct = fixed_colorings(less03_01,{0:0,1:1,2:2})
    equal = fixed_colorings(less03_01,{0:0,1:0,2:1})
    assert distinct == ['012011202001','012022001121'],distinct
    assert equal == ['001122110022'],equal
    assert fixed_colorings(less03,{0:0,1:1,2:2})==distinct
    assert find_coloring(12,B_EDGES,3) is None
    four = find_coloring(12,B_EDGES,4)
    assert four is not None and valid(four,B_EDGES)
    certificates = {}
    for e in B_EDGES:
        c = find_coloring(12,tuple(f for f in B_EDGES if f!=e),3)
        assert c is not None
        assert valid(c,tuple(f for f in B_EDGES if f!=e))
        certificates['%d-%d'%e]=normalized(c)
    # Since B has no isolated vertices, these witnesses also give vertex criticality.
    assert all(any(i in e for e in B_EDGES) for i in range(12))
    # The explicit k-coloring uses a 3-coloring of B-y.
    by = tuple(e for e in B_EDGES if 3 not in e)
    three = find_coloring(12,by,3)
    assert three is not None
    examples = {}
    for k in (5,6,7):
        ni,ei = input_graph(k)
        assert find_coloring(ni,ei,k-1) is None
        for edge in ei:
            assert find_coloring(ni,tuple(f for f in ei if f!=edge),k-1) is not None
        n,edges,second,Q1,Q2 = output_graph(k)
        r=k-4
        assert n==2*k+13 and len(edges)==k*k+15*k-32,(k,n,len(edges))
        colors={i:three[i] for i in range(12) if i!=3}
        colors[3]=3
        colors.update({second[i]:three[i] for i in range(3,12) if i!=3})
        colors[second[3]]=4
        colors.update({v:c for v,c in zip(Q1,range(4,k))})
        colors.update({v:c for v,c in zip(Q2,(3,*range(5,k)))})
        assert len(colors)==n and valid(colors,edges)
        assert find_coloring(n,edges,k-1) is None
        deleted = tuple(e for e in edges if e!=(0,1))
        assert len(deleted)==len(edges)-1
        assert find_coloring(n,deleted,k-1) is None
        examples[str(k)]={'input':{'vertices':ni,'edges':[list(e) for e in ei]},
                         'output':{'vertices':n,'edges':[list(e) for e in edges]},
                         'k_coloring':[colors[v] for v in range(n)],
                         'witness_edge':[0,1]}
        print(f'k={k}: |V|={n}, |E|={len(edges)}, chi(D)=chi(D-01)={k}')
    print('B: 12 vertices, 24 edges; 4-critical; three normalized rigidity colorings')
    print('B 4-coloring:', ''.join(map(str,four)))
    print('B-3 3-coloring:', ''.join(map(str,three)))
    print('All B-e 3-coloring certificates:')
    for e,c in certificates.items():
        print(e,c)
    if args.write_json:
        with open(args.write_json,'w',encoding='utf-8') as stream:
            json.dump({'B':{'vertices':12,'edges':[list(e) for e in B_EDGES],
                             'edge_deletion_colorings':certificates,
                             'four_coloring':list(four)},
                       'outputs':examples},stream,indent=2)
            stream.write('\n')
        print('Wrote',args.write_json)

if __name__=='__main__':
    main()
