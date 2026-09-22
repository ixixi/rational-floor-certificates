"""Small, bounded tests of A; none of this code constitutes verifier B."""
from __future__ import annotations

import copy
import unittest
from fractions import Fraction

import verifier as a
from summarize import derived_tables


def literal_edges(states, numerator, denominator, modulus, cells):
    # Deliberately literal test oracle restricted to small finite inputs.
    return sorted([q, j, z, k, e] for q, j in states for z, k in states
                  for e in range(1-denominator, numerator)
                  if (denominator*z-numerator*q-e) % modulus == 0
                  and numerator*j-denominator*(k+1) < e*cells < numerator*(j+1)-denominator*k)


def edge_list(graph):
    states, adj, _ = graph
    return sorted(a.edge_record(states, u, v, e) for u, edges in enumerate(adj) for v, e in edges)


def graph_from_edges(count, edges):
    adj, rev = [[] for _ in range(count)], [[] for _ in range(count)]
    for u, v, e in edges:
        adj[u].append((v, e))
        rev[v].append(u)
    return [(1, u) for u in range(count)], adj, rev


class EdgeTests(unittest.TestCase):
    def test_small_literal_complete_edge_sets(self):
        for parameters in ((3, 2, 6, 5), (5, 4, 30, 5), (7, 5, 30, 8),
                           (5, 2, 7, 8), (3, 2, 2, 1), (7, 5, 30, 1)):
            with self.subTest(parameters=parameters):
                graph = a.build_graph(*parameters)
                self.assertEqual(edge_list(graph), literal_edges(graph[0], *parameters))
                a.check_adjacency(graph[1], graph[2])

    def test_all_allowed_subsets_of_four_state_graph(self):
        parameters = (3, 2, 6, 2)
        universe = a.build_graph(*parameters)[0]
        self.assertEqual(len(universe), 4)
        for mask in range(1 << len(universe)):
            allowed = {v for i, v in enumerate(universe) if (mask >> i) & 1}
            graph = a.build_graph(*parameters, allowed)
            self.assertEqual(edge_list(graph), literal_edges(graph[0], *parameters))

    def test_nonunit_all_solutions_and_no_solution(self):
        graph = a.build_graph(7, 5, 30, 1)
        outgoing = [edge for edge in edge_list(graph) if edge[:2] == [1, 0]]
        self.assertEqual([edge[2] for edge in outgoing if edge[-1] == -2], [1, 7, 13, 19])
        self.assertFalse(any(edge[-1] == -1 for edge in outgoing))

    def test_strict_equal_endpoints(self):
        edges = edge_list(a.build_graph(3, 2, 6, 5))
        self.assertNotIn([1, 1, 1, 3, -1], edges)
        self.assertNotIn([1, 0, 1, 4, -1], edges)
        self.assertIn([1, 1, 1, 4, -1], edges)

    def test_signed_floor_and_ceiling(self):
        for b in range(2, 12):
            for n in range(-80, 81):
                self.assertEqual((n - 1) // b, -((-n) // b) - 1)
                for k in range(-20, 21):
                    self.assertEqual(b*(k+1) > n, k >= n // b)
                    self.assertEqual(b*k < n, k <= (n-1) // b)

    def test_invalid_inputs(self):
        for parameters in ((2, 2, 6, 2), (4, 2, 6, 2), (3, 2, 1, 2), (3, 2, 6, 0)):
            with self.assertRaises(ValueError):
                a.build_graph(*parameters)
        for allowed in ({(0, 0)}, {(1, 2)}, {(1, -1)}, {(True, 0)}):
            with self.assertRaises(ValueError):
                a.build_graph(3, 2, 6, 2, allowed)


class PartitionTests(unittest.TestCase):
    def test_all_three_vertex_digraphs(self):
        for mask in range(1 << 9):
            edges = [(u, v, 0) for u in range(3) for v in range(3) if mask >> (3*u+v) & 1]
            _, adj, rev = graph_from_edges(3, edges)
            groups, owner = a.components(adj, rev)
            a.check_partition(adj, rev, groups, owner)
            # A bounded transitive-closure oracle, not an implementation B SCC routine.
            reach = [[u == v or (u, v, 0) in edges for v in range(3)] for u in range(3)]
            for k in range(3):
                for u in range(3):
                    for v in range(3):
                        reach[u][v] |= reach[u][k] and reach[k][v]
            for u in range(3):
                for v in range(3):
                    self.assertEqual(owner[u] == owner[v], reach[u][v] and reach[v][u])

    def test_duplicate_missing_vertex_rejected(self):
        with self.assertRaisesRegex(ValueError, "disjoint cover"):
            a.check_partition([[(1, 0)], [(0, 0)]], [[1], [0]], [[0, 0]], [0, 0])

    def test_inconsistent_reverse_rejected(self):
        with self.assertRaisesRegex(ValueError, "reverse adjacency"):
            a.check_partition([[(1, 0)], []], [[1], [0]], [[0, 1]], [0, 0])

    def test_invalid_partition_shapes_rejected(self):
        _, adj, rev = graph_from_edges(2, [(0, 1, 0), (1, 0, 0)])
        for groups, owner in (([[]], [0, 0]), ([[0, 1]], [0]), ([[0, 1]], [-1, 0]),
                              ([[0], [1]], [0, 1]), ([[0, 2]], [0, 0]), ([[0, 1]], [0, 1])):
            with self.subTest(groups=groups, owner=owner), self.assertRaises(ValueError):
                a.check_partition(adj, rev, groups, owner)
        _, adj, rev = graph_from_edges(2, [(0, 1, 0)])
        with self.assertRaisesRegex(ValueError, "strongly connected"):
            a.check_partition(adj, rev, [[0, 1]], [0, 0])

    def test_reverse_parallel_multiplicity(self):
        a.check_partition([[(0, -1), (0, 1)]], [[0, 0]], [[0]], [0])
        with self.assertRaisesRegex(ValueError, "reverse adjacency"):
            a.check_partition([[(0, -1), (0, 1)]], [[0]], [[0]], [0])

    def test_edge_endpoint_and_duplicate_rejected(self):
        for adj, rev in (([[(1, 0)]], [[]]), ([[(0, 0), (0, 0)]], [[0, 0]])):
            with self.assertRaises(ValueError):
                a.check_partition(adj, rev, [[0]], [0])

    def test_empty_graph(self):
        stage, certificate = a.analyze_stage(([], [], []), 1, 2)
        self.assertEqual(stage["vertices"], [])
        self.assertEqual(stage["components"], [])
        self.assertEqual(certificate["blocks"], [])


class CertificateTests(unittest.TestCase):
    def test_parallel_labels_prevent_certification(self):
        stage, certificate = a.analyze_stage(a.build_graph(3, 2, 2, 1), 1, 2)
        comp = stage["components"][0]
        self.assertEqual(stage["edges"], [[1, 0, 1, 0, -1], [1, 0, 1, 0, 1]])
        self.assertTrue(comp["cyclic"])
        self.assertFalse(comp["certified"])
        self.assertEqual(comp["collision"], stage["edges"])
        self.assertEqual(certificate["blocks"][0]["kind"], "retained")

    def test_noncyclic_and_self_loop(self):
        stage, _ = a.analyze_stage(graph_from_edges(2, [(1, 1, 2)]), 2, 2)
        self.assertEqual([(c["cyclic"], c["certified"], c["d"]) for c in stage["components"]],
                         [(False, False, 0), (True, True, 1)])

    def test_period_distinct_from_primitive_word(self):
        for labels, expected_word in (([-2, 4] * 3, [-2, 4]), ([2] * 6, [2])):
            graph = graph_from_edges(6, [(u, (u+1) % 6, labels[u]) for u in range(6)])
            stage, _ = a.analyze_stage(graph, 6, 2)
            comp = stage["components"][0]
            self.assertEqual(comp["d"], 6)
            self.assertEqual(comp["word"], expected_word)
            self.assertEqual(comp["phase_labels"], labels)

    def test_smallest_root_and_order_invariance(self):
        graph = graph_from_edges(3, [(0, 2, 9), (1, 2, 0), (2, 1, 0)])
        stage, certificate = a.analyze_stage(graph, 3, 2)
        self.assertEqual(stage["components"][1]["vertices"], [[1, 1], [1, 2]])
        self.assertEqual(stage["components"][1]["h"], [0, 1])
        reordered = (graph[0], [list(reversed(es)) for es in graph[1]],
                     [list(reversed(es)) for es in graph[2]])
        self.assertEqual((stage, certificate), a.analyze_stage(reordered, 3, 2))

    def test_outgoing_edges_do_not_pollute_internal_labels(self):
        stage, _ = a.analyze_stage(graph_from_edges(2, [(0, 0, 2), (0, 1, 9), (1, 1, 3)]), 2, 2)
        self.assertEqual([c["word"] for c in stage["components"]], [[2], [3]])

    def test_word_reduction_and_rotation(self):
        self.assertEqual(a.canonical_word([4, -2, 4, -2]), [-2, 4])
        self.assertEqual(a.canonical_word([4, 4, -2, -2]), [-2, -2, 4, 4])
        self.assertEqual(a.canonical_word([-4, 2, 2, -4, 2, 2, 2]), [-4, 2, 2, -4, 2, 2, 2])

    def test_block_certificate_mutations_rejected(self):
        graph = graph_from_edges(3, [(0, 1, 3), (1, 2, -2), (2, 1, 4)])
        _, cert = a.analyze_stage(graph, 3, 2)
        mutated = copy.deepcopy(cert)
        mutated["blocks"][0]["rank"] = mutated["blocks"][1]["rank"]
        with self.assertRaisesRegex(ValueError, "rank"):
            a.check_block_certificate(mutated, 2)
        mutated = copy.deepcopy(cert)
        mutated["phase"][1] = 9
        with self.assertRaisesRegex(ValueError, "Phase"):
            a.check_block_certificate(mutated, 2)
        mutated = copy.deepcopy(cert)
        mutated["blocks"][1]["phase_labels"][0] = 99
        with self.assertRaisesRegex(ValueError, "label"):
            a.check_block_certificate(mutated, 2)
        _, cert = a.analyze_stage(a.build_graph(3, 2, 2, 1), 1, 2)
        cert["retained"] = []
        with self.assertRaisesRegex(ValueError, "coverage"):
            a.check_block_certificate(cert, 2)

    def test_refinement_exact_children_and_boundaries(self):
        self.assertEqual(a.refine([[1, 0], [3, 2]], 3),
                         [[1, 0], [1, 1], [1, 2], [3, 6], [3, 7], [3, 8]])
        for cells in (1, 2, 5, 8):
            for factor in (2, 3, 4):
                for denominator in range(1, 33):
                    for numerator in range(denominator):
                        theta = Fraction(numerator, denominator)
                        coarse = (cells * theta).__floor__()
                        fine = (factor * cells * theta).__floor__()
                        self.assertEqual(fine // factor, coarse)

    def test_run_stage_limit_and_exact_next_cells(self):
        parameters = dict(a=3, b=2, M=2, K0=1, f=2, max_stages=2)
        science, certificate = a.run(parameters)
        self.assertEqual(science["termination"], "inconclusive")
        self.assertEqual(len(science["stages"]), 2)
        self.assertEqual(science["stages"][0]["refined_vertices"], science["stages"][1]["vertices"])
        self.assertEqual(certificate["termination"], "inconclusive")

    def test_success_stops_early_and_tables_are_derived(self):
        parameters = dict(a=4, b=3, M=30, K0=32, f=4, max_stages=8)
        science, _ = a.run(parameters)
        self.assertEqual(science["termination"], "success")
        self.assertEqual(len(science["stages"]), 1)
        table = derived_tables(science)["stages"][0]
        self.assertEqual(table["vertices"], len(science["stages"][0]["vertices"]))
        self.assertEqual(table["certified_components"], table["cyclic_components"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
