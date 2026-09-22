# Word-labelled graph comparison format

[English](#english) · [日本語](#japanese)

<a id="english"></a>

## English

The independent implementations share only mathematical definitions, normalization rules, and comparison procedures. The one-step format is [comparison-schema.md](comparison-schema.md).

The definitions in this document are restated self-containedly for this comparison. Their validity—that true orbits always walk in the graphs, that periodic removal, contraction, and lifting preserve tails, and that finite success implies the theorem—requires separate mathematical proofs, given in Sections 3–4 and 6 of the [public paper](../../paper-en.pdf). Agreement between A and B does not prove that the definitions are correct.

### 0. Mathematical definitions

#### 0.1 Parameters and adopted cases

| case | a/b | Initial cell count K | Carry set C | Prime sequence p_1, p_2, … | Stages |
| --- | --- | ---: | --- | --- | ---: |
| `five-halves` | 5/2 | 4 | {−1, 1, 3} | 3, 7, 11, 13, 17, 19, 23, 29, 31 | 10 (s = 0, …, 9) |
| `cross-75` | 7/5 | 2048 | {−4, −2, 2, 4, 6} | 3, 11, 13 | 4 (s = 0, …, 3) |
| `q75` | 7/5 | 2048 | {−4, −2, 2, 4, 6} | Use modulus M = 429 = 3·11·13 in one step | 1 |

The modulus at stage s is P_s = p_1 ⋯ p_s (P_0 = 1). The carry set C is an input supplied by the reductions in Sections 5.2–5.3 (Lemmas 23–24) of the [public paper](../../paper-en.pdf); A/B do not check these reductions.

#### 0.2 Word-labelled graphs

A vertex is a pair (q, cell), with 0 ≤ q < P_s and 0 ≤ cell < K (q = 0 when P_0 = 1). Here q is the **least nonnegative representative** modulo P_s. An edge is a triple (u, v, w): a source u, a target v, and a nonempty finite word w = (c_0, …, c_{ℓ−1}), with c_i ∈ C. Different words give different edges even with the same endpoints; edges with the same source, target, and word count as one edge (a set). The outdegree of a vertex u is the number of distinct edges with source u.

#### 0.3 Initial graph G_0^in

The vertex set consists of all cells {(0, j) : 0 ≤ j < K} (include all cells, whether or not they have edges). For c ∈ C and 0 ≤ j, k < K, the edges are

    (0, j) —(c)→ (0, k)   ⟺   a·j − b·(k+1) < c·K < a·(j+1) − b·k

Both inequalities are strict. These are integer comparisons that can involve negative values; if floor division is used, round towards −∞, not towards zero.

#### 0.4 Blocks, periods, and certification

A block of a word-labelled graph G is a strongly connected component: u and v are in the same block if and only if there is a walk following edges in their forward direction from u to v and from v to u (walks of length 0 are allowed, so every vertex is in the same block as itself). An internal edge has both endpoints in the same block. A **cyclic block** has at least 1 internal edge (including a singleton with only a self-loop).

For a cyclic block B:

- The root r(B) is the lexicographically least vertex of B.
- For each v ∈ B, choose a walk from r(B) to v consisting only of internal edges, and let h(v) be the sum of the lengths of its edge words (h(r(B)) = 0).
- The period is d_B = gcd { |h(u) + |w| − h(v)| : (u, v, w) is an internal edge of B }. Then d_B ≥ 1. It does not depend on the chosen walks (it equals the gcd of the lengths of internal closed walks of B).
- The phase is φ(v) = h(v) mod d_B. It too is independent of the chosen walks, and φ(r(B)) = 0.
- B is **certified** if and only if there is a map λ : {0, …, d_B − 1} → C such that, for every internal edge (u, v, w) of B and every 0 ≤ i < |w|, w_i = λ((φ(u) + i) mod d_B). In other words, all letters placed at the same phase are equal. In this case (λ_0, …, λ_{d_B − 1}) is called the **phase-label sequence**. Every phase is used by at least one letter.

No period is defined for an acyclic block (formally use 0).

#### 0.5 Uncertified part and contraction (output graph G_s^out)

- The uncertified vertex set U is the union of the vertices of the uncertified cyclic blocks.
- The uncertified edge set E_U consists of the internal edges of the uncertified cyclic blocks (discard edges between blocks, edges of certified blocks, and vertices of acyclic blocks).
- The set of **branch vertices** is A = { u ∈ U : the outdegree of u in E_U is ≥ 2 } ∪ { r(B) : B is an uncertified cyclic block with no vertex of outdegree ≥ 2 }.
- Contracted edges: for u ∈ A and each edge e_0 = (u, v_1, w_0) ∈ E_U with source u, follow the unique edge e_i = (v_i, v_{i+1}, w_i) of v_i in E_U as long as v_i ∉ A (such a vertex has outdegree exactly 1), starting with v_1, until the first branch vertex v_m ∈ A is reached (m ≥ 1). The contracted edge is (u, v_m, w_0 w_1 ⋯ w_{m−1}), with concatenation of words. A cycle avoiding branch vertices can only be an entire block consisting of vertices of outdegree 1; its root belongs to A. Thus this operation always terminates.
- The vertex set of G_s^out is A, and its edge set is the set of contracted edges (if different contracted edges give the same triple, count it once).

Define E_U and A using the distinct edges of G_s^in. Do not redefine branch vertices using the outdegrees after contraction.

#### 0.6 Prime lifting (next input graph G_{s+1}^in)

Let G_s^out be the output graph with modulus P = P_s, and let p = p_{s+1} be prime, with p ∤ ab and p ∤ P. For each edge ((q, cell), (q′, cell′), w) and each starting residue r ∈ {1, …, p − 1}, compute

    z_0 = r,   z_{i+1} ≡ b^{−1} (a·z_i + c_i)  (mod p)   (0 ≤ i < ℓ)

Include the edge

    (CRT(q, r), cell) —(w)→ (CRT(q′, z_ℓ), cell′)

only when **all** of z_0, …, z_ℓ are nonzero. Here CRT(q, r) is the unique integer with 0 ≤ x < P·p satisfying x ≡ q (mod P) and x ≡ r (mod p). The vertex set of G_{s+1}^in is the set of endpoints of lifted edges (exclude states without edges), and its edge set is the set of lifted edges.

#### 0.7 Stage progression and termination

The progression is G_s^in → (0.4–0.5) → G_s^out → (0.6, p_{s+1}) → G_{s+1}^in. Stop at the stage where G_s^out is empty (has no vertices). The limit is 10 stages for `five-halves` and 4 stages for `cross-75`; in both cases the expected result is emptiness at the last stage. Output G_s^in and G_s^out for every stage up to termination, including empty graphs. Reaching the stage limit without obtaining emptiness is not success.

#### 0.8 Q75 certificate (waiting time for 7/5)

a = 7, b = 5, M = 429, K = 2048, C = {−4, −2, 2, 4, 6}.

- The vertex set is V = {(q, j) : 0 ≤ q < M, gcd(q, M) = 1, 0 ≤ j < K}, with φ(429)·2048 = 491,520 vertices.
- The edge set E contains (q, j) —(c)→ (z, k) for every c ∈ C, (q, j) ∈ V, every solution z of b·z ≡ a·q + c (mod M) with gcd(z, M) = 1, and every k satisfying a·j − b·(k+1) < c·K < a·(j+1) − b·k. Include **all solutions**. Do not assume that b is invertible modulo M: if g = gcd(b, M) does not divide the right-hand side there is no solution; otherwise generate all g candidates from a solution modulo M/g (g = 1 in this case).
- Blocks are the strongly connected components of (V, E). Cyclic blocks, periods d_B, and phase-label sequences are as in 0.4, with word length 1. The certificate requires **every cyclic block to be certified**.
- The condensation graph has blocks as vertices and edges B → B′ between distinct blocks (B ≠ B′). It must be acyclic.
- Canonical ranks ρ, η: ρ(B) is the maximum length of a block sequence ending at B (a path in the condensation graph, counting B); η(B) is the maximum number of cyclic blocks on such a path (counting B). Equivalently, at a block without predecessors, ρ = 1 and η = [B cyclic]; otherwise ρ(B) = 1 + max{ρ(B′) : B′ → B} and η(B) = [B cyclic] + max{η(B′) : B′ → B}.
- Certificate conditions: for every inter-block edge B → B′, ρ(B′) ≥ ρ(B) + 1 and η(B′) ≥ η(B) + [B′ cyclic]; at every block, ρ ≥ 1 and η ≥ [B cyclic]. The constants in the paper are max ρ ≤ 65 (inter-block edges R = 64), max η ≤ 6 (m = 6), and max d_B ≤ 13 (D = 13).

### 1. File format

Use UTF-8, LF, no BOM, no empty lines, and no comment lines. Integers are decimal; negative integers start with `-`; no leading zeros or `+`. Every line ends with a newline. Use 1 file per graph.

#### 1.1 Word-labelled graph: `WORDGRAPH 2`

The first-line header is:

    WORDGRAPH 2 a=<a> b=<b> K=<K> modulus=<P> primes=<p1,p2,...> vertices=<n> edges=<m>

P is the product of the primes already used; the initial stage has `modulus=1 primes=` (nothing follows `primes=`). Next list all vertex lines `V <q> <cell>` in numerical lexicographic order of (q, cell), followed by all edge lines

    E <q_u> <cell_u> <q_v> <cell_v> <c_0> <c_1> ... <c_{ℓ-1}>

in numerical lexicographic order of (q_u, cell_u, q_v, cell_v, word). Words are compared element by element as integers; if one is a proper prefix of the other, the shorter comes first. Here q is the least nonnegative representative modulo the current modulus P (0 ≤ q < P). Duplicate edges with the same endpoints and word count once. The values of `vertices=` and `edges=` must equal the respective numbers of lines.

Example (`five-halves`, stage 0 input):

    WORDGRAPH 2 a=5 b=2 K=4 modulus=1 primes= vertices=4 edges=12
    V 0 0
    V 0 1
    V 0 2
    V 0 3
    E 0 0 0 0 1
    E 0 0 0 2 -1
    E 0 0 0 3 -1
    ...

Implementation A uses filenames `stage-<ss>-input.txt` / `stage-<ss>-output.txt`, where ss is a 2-digit stage number. B may choose its filenames freely; the comparison report records their correspondence to (stage, input/output).

#### 1.2 Q75: `Q75GRAPH 2`

Header:

    Q75GRAPH 2 a=7 b=5 M=429 K=2048 vertices=<n> edges=<m> blocks=<k>

Then vertex lines `V <q> <j>` (lexicographic order), edge lines `E <q_u> <j_u> <q_v> <j_v> <c>` (lexicographic order), and block lines

    B <id> <size> <internal_edges> <period> <rho> <eta> L <phase_labels_space_separated> M <q:j> <q:j> ...

- Renumber `id` from 0 in lexicographic order of the least vertex in each block. List the lines in that order.
- `size` is the number of members, `internal_edges` the number of internal edges, and `period` is d_B (0 for an acyclic block).
- After `L`, list the phase-label sequence (`period` labels, with phase 0 at the block's least vertex and the label of phase i in position i). If `period` is 0, `M` immediately follows `L`. If a cyclic block is uncertified, omit the labels and put `M` immediately after `L`; in that case the certificate is not valid.
- After `M`, list all members (q:j) in lexicographic order.
- Root distances h are implementation-dependent and are not output.

Implementation A uses the filename `q75.txt`. It also supplies `q75-cyclic-blocks-excerpt.txt`, an excerpt with the same header but only the `B` lines for cyclic blocks. The comparison uses `q75.txt`.

### 2. Normalization rules and conventions for implementation-dependent choices

The following conventions ensure that A/B **output using the same rules**.

- N1 Vertex names: q is the least nonnegative representative obtained by CRT. Names at stage s are modulo P_s; do not retain names from earlier stages.
- N2 Edge identity: a set of triples. Count identical triples once. Different words give different edges, even with the same endpoints.
- N3 Order: the lexicographic order of 1.1. Compare words as integer sequences, not as strings or unsigned bytes.
- N4 After lifting, the vertex set contains only edge endpoints (no isolated states). The initial graph contains all cells.
- N5 Branch vertices are determined by outdegree ≥ 2 among distinct edges in the uncertified edge set E_U of G_s^in. In an uncertified block without a branch vertex, use the least vertex as a branch vertex. **This fallback did not occur in the adopted data of implementation A** (0 occurrences at every stage). B must also report the occurrence count.
- N6 The phase root is the block's least vertex. In Q75 label sequences, place phase 0 at that root. If B computes with a different root, rotate the label sequence to align phase 0 with the least vertex before output.
- N7 Mathematically, the period d_B is independent of the choice of root. In A/B comparisons, compare certification status, consistency of the label sequence modulo d, ρ and η, and the partition element by element; **report agreement of d as a result**. If there is a mismatch, report it and investigate its cause; do not rewrite the output.
- N8 Renumber Q75 `id` by least vertex. Do not compare the numbers themselves.
- N9 Output the canonical (longest-path) values of ρ and η from 0.8. Besides comparing values, each implementation independently checks and reports the certificate conditions (inequalities).
- N10 Resource limits: A conservatively treats a cyclic block as uncertified when d_B exceeds its implementation limit. Among certified blocks in the adopted data, the maximum periods are 177 for `five-halves` (stage 8), 13 for `cross-75`, and 13 for `q75`. B must either impose no limit or report any exceedance.
- N11 Stage limits: at most 10 stages for `five-halves` and 4 for `cross-75`. Stop at the stage that becomes empty.
- N12 Meaning of counts: the edge counts in implementation A's internal totals with multiplicity, described under “Edge multiplicities” in Appendix A of the [public paper](../../paper-en.pdf), include repeated identical triples. For example, the 5/2 stage 9 input has 3,754,612 edges with multiplicity and 3,256,019 distinct edges; the stage 8 output has 201,199 and 171,256, respectively. In this contract, `edges=` counts distinct edges, so at some stages it differs from the totals with multiplicity. B reports distinct-edge counts and must not use the totals with multiplicity as target values. Vertex counts agree.
- N13 Neither A nor B opens the other's files before producing its own outputs.

### 3. Comparison procedure

Matching counts and hashes alone is insufficient. The comparator performs the following checks and saves the results in JSON: agreement or disagreement for each file and item, mismatch counts, and the first 20 examples of mismatches.

1. File matching: 20 (s, input/output) files for `five-halves`, 8 for `cross-75`, and 1 for `q75`. A missing file is a mismatch.
2. Word-labelled graphs: all header fields `a b K modulus primes vertices edges` must agree. Compare the sequence of `V` lines element by element, listing vertices present in A but absent in B and vice versa. Do the same for `E` lines. Check that both outputs follow the ordering rules (sorted, without duplicates).
3. Q75: compare `V` and `E` lines as in 2. Compare blocks as a **family of member sets**, so partition agreement is independent of numbering. For each pair of blocks matched by member set, compare `size internal_edges period rho eta` and the label sequence. Under N6, the label sequences are expected to agree exactly; if they do not, also report whether they agree up to rotation. If any cyclic-block line has no labels (uncertified), report certificate failure.
4. Self-checks of mathematical conditions: each of A/B verifies that the edge sets agree with those re-enumerated from the definitions in 0.3/0.6/0.8. For Q75, also verify that the blocks are strongly connected components, the phase condition for every internal edge, the rank inequalities for every inter-block edge, acyclicity of the condensation graph, and max ρ ≤ 65, max η ≤ 6, max d ≤ 13. Attach these reports to the comparison report.
5. Meaning of agreement: element-wise agreement is evidence that two implementations produced the same finite objects; it does not prove the mathematical validity of the definitions or the theorem. Report mismatches without changing the outputs, and identify their causes.
6. File SHA-256 hashes may record identity but do not replace element-wise comparison.

### 4. Cases and limits

| case | Limit for each implementation | On reaching a limit |
| --- | --- | --- |
| `five-halves` | 600 seconds; 4 GiB (address space) | `inconclusive` |
| `cross-75` | 300 seconds; 4 GiB | `inconclusive` |
| `q75` | 300 seconds; 4 GiB | `inconclusive` |

Before execution, record the input and code hashes, Python/compiler versions, command, and limits in the run record. After execution, record elapsed wall time, termination reason, and output hashes. Reaching a limit is neither a counterexample, a disproof of the theorem, nor a claim of minimality of the prime set.

### 5. Output files

The reproduction driver writes all graph outputs to the requested external directory. There are 20 five-halves graphs, 8 cross-application graphs, and one quantitative graph per implementation. The compact reference data are in [reference.json](../../checks/reference.json). See [the reproduction instructions](../../REPRODUCE.md) for the complete A/B comparison.

### 6. Connection to Lean

This output alone does not establish a Lean proof. The formalization must prove the mathematical soundness of the checking conditions (0.3–0.8) and acceptance of the actual adopted data. Certificate hashes establish identity, not soundness.

<a id="japanese"></a>

## 日本語

**語ラベル付きグラフの比較形式**

独立な実装が共有するのは、数学的定義、正規化規則、および比較手順だけである。1ステップ形式は [comparison-schema.md](comparison-schema.md#japanese) に示す。

本文書に書かれた定義は、この比較のために自己完結に書き直したものである。定義の妥当性（真の軌道が必ずグラフを歩くこと、周期除去・圧縮・持ち上げが尾部を保存すること、有限成功から定理が従うこと）は別に数学的証明を要し、[公開論文](../../paper-ja.pdf)の第3–4節および第6節で扱う。A/Bの一致は定義の正しさを証明しない。

### 0. 数学的定義

#### 0.1 パラメータと採用case

| case | a/b | 初期セル数 K | キャリー集合 C | 素数列 p_1, p_2, … | 段数 |
| --- | --- | ---: | --- | --- | ---: |
| `five-halves` | 5/2 | 4 | {−1, 1, 3} | 3, 7, 11, 13, 17, 19, 23, 29, 31 | 10（s = 0, …, 9） |
| `cross-75` | 7/5 | 2048 | {−4, −2, 2, 4, 6} | 3, 11, 13 | 4（s = 0, …, 3） |
| `q75` | 7/5 | 2048 | {−4, −2, 2, 4, 6} | 法 M = 429 = 3·11·13 を一度に使う | 1 |

段 s の法は P_s = p_1 ⋯ p_s（P_0 = 1）。キャリー集合 C は[公開論文](../../paper-ja.pdf)の第5.2–5.3節（補題23–24）の還元で与えられる入力であり、A/Bはこの還元を検査しない。

#### 0.2 語付きグラフ

頂点は組 (q, cell)、0 ≤ q < P_s、0 ≤ cell < K（P_0 = 1 のとき q = 0）。q は法 P_s の**最小非負代表**である。辺は三つ組 (u, v, w)：始点 u、終点 v、非空の有限語 w = (c_0, …, c_{ℓ−1})、c_i ∈ C。同じ端点でも語が異なれば別の辺であり、始点・終点・語がすべて同じ辺は1本として数える（集合）。頂点 u の出次数は、u を始点とする相異なる辺の個数。

#### 0.3 初期グラフ G_0^in

頂点集合は全セル {(0, j) : 0 ≤ j < K}（辺の有無に関係なく全部入れる）。辺は c ∈ C と 0 ≤ j, k < K について

    (0, j) —(c)→ (0, k)   ⟺   a·j − b·(k+1) < c·K < a·(j+1) − b·k

（両側とも厳密不等号）。負の値を含む整数比較であり、床除算を使う場合は −∞ 方向の床（ゼロ方向切り捨てではない）を用いる。

#### 0.4 ブロック・周期・認証

語付きグラフ G のブロックとは強連結成分である：u と v が同じブロック ⟺ u から v へ、v から u へ、辺を順向きに辿るウォークが存在する（長さ 0 のウォークを許すので各頂点は自分自身と同じブロック）。内部辺とは両端が同じブロックにある辺。**循環ブロック**とは内部辺を 1 本以上持つブロック（自己ループだけの単頂点を含む）。

循環ブロック B について：

- 根 r(B) は B の辞書順最小の頂点。
- 各 v ∈ B に、r(B) から v への内部辺だけのウォークを一つ選び、そのウォーク上の辺語の長さの和を h(v) とする（h(r(B)) = 0）。
- 周期 d_B = gcd { |h(u) + |w| − h(v)| : (u, v, w) は B の内部辺 }。d_B ≥ 1。d_B はウォークの選び方に依らない（B の内部閉ウォークの長さの gcd に等しい）。
- 位相 φ(v) = h(v) mod d_B。これもウォークの選び方に依らず、φ(r(B)) = 0。
- B が**認証される** ⟺ 写像 λ : {0, …, d_B − 1} → C が存在して、B の全内部辺 (u, v, w) と全 0 ≤ i < |w| について w_i = λ((φ(u) + i) mod d_B)。すなわち同じ位相に置かれる文字がすべて等しい。このとき (λ_0, …, λ_{d_B − 1}) を**位相ラベル列**と呼ぶ。全位相が少なくとも一つの文字で使われる。

非循環ブロックには周期を定義しない（形式上 0 とする）。

#### 0.5 未認証部分と圧縮（出力グラフ G_s^out）

- 未認証頂点集合 U = 認証されない循環ブロックの頂点の和集合。
- 未認証辺集合 E_U = 認証されない循環ブロックの内部辺の集合（ブロック間の辺、認証済みブロックの辺、非循環ブロックの頂点は捨てる）。
- **分岐点**の集合 A = { u ∈ U : E_U における u の出次数 ≥ 2 } ∪ { r(B) : B は認証されない循環ブロックで、B の頂点に出次数 ≥ 2 のものがない }。
- 圧縮辺：u ∈ A と u を始点とする各 e_0 = (u, v_1, w_0) ∈ E_U について、v_1 ∉ A である限り v_i の E_U における唯一の辺 e_i = (v_i, v_{i+1}, w_i) を辿り（v_i ∉ A なら出次数はちょうど 1）、最初に到達する分岐点 v_m ∈ A（m ≥ 1）まで進む。圧縮辺は (u, v_m, w_0 w_1 ⋯ w_{m−1})（語の連結）。分岐点を経由しない閉路は、出次数 1 の頂点だけからなるブロック全体に限られ、その根が A に入るので、この操作は必ず停止する。
- G_s^out の頂点集合は A、辺集合は圧縮辺の集合（相異なる圧縮辺が同じ三つ組になれば 1 本）。

E_U と A は G_s^in の相異なる辺で定める。圧縮後の出次数で分岐点を決め直してはならない。

#### 0.6 素数持ち上げ（次段入力グラフ G_{s+1}^in）

法 P = P_s の出力グラフ G_s^out と素数 p = p_{s+1}（p ∤ ab、p ∤ P）について。各辺 ((q, cell), (q′, cell′), w) と各開始剰余 r ∈ {1, …, p − 1} に対し

    z_0 = r,   z_{i+1} ≡ b^{−1} (a·z_i + c_i)  (mod p)   (0 ≤ i < ℓ)

を計算し、z_0, …, z_ℓ が**すべて** 0 でないときだけ辺

    (CRT(q, r), cell) —(w)→ (CRT(q′, z_ℓ), cell′)

を入れる。CRT(q, r) は x ≡ q (mod P) かつ x ≡ r (mod p) を満たす 0 ≤ x < P·p の唯一の整数。G_{s+1}^in の頂点集合は持ち上げ辺の端点の集合（辺を持たない状態は含めない）、辺集合は持ち上げ辺の集合。

#### 0.7 段の進行と停止

G_s^in →（0.4–0.5）→ G_s^out →（0.6、p_{s+1}）→ G_{s+1}^in。G_s^out が空（頂点なし）になった段で終了する。`five-halves` は最大 10 段、`cross-75` は最大 4 段で、いずれも最後の段で空になることが期待される結果である。終了までの全段について G_s^in と G_s^out を出力する（空グラフも出力する）。空にならずに段数上限に達した場合は成功ではない。

#### 0.8 Q75 証明書（7/5 の待ち時間）

a = 7、b = 5、M = 429、K = 2048、C = {−4, −2, 2, 4, 6}。

- 頂点集合 V = {(q, j) : 0 ≤ q < M, gcd(q, M) = 1, 0 ≤ j < K}（φ(429)·2048 = 491,520 個）。
- 辺集合 E：c ∈ C、(q, j) ∈ V、b·z ≡ a·q + c (mod M) の**全解** z のうち gcd(z, M) = 1 のもの、および a·j − b·(k+1) < c·K < a·(j+1) − b·k を満たす全 k について (q, j) —(c)→ (z, k)。b の法 M での逆元を仮定せず、g = gcd(b, M) が右辺を割らなければ解なし、割れば法 M/g の解から g 個の候補を全部作る（この case では g = 1）。
- ブロック = (V, E) の強連結成分。循環ブロック、周期 d_B、位相ラベル列は 0.4 と同じ（語長 1）。証明書は**全循環ブロックが認証される**ことを要求する。
- 縮約グラフ：ブロックを頂点とし、ブロック間辺 B → B′（B ≠ B′）を辺とする有向グラフ。非巡回でなければならない。
- 順位 ρ, η の正準定義：ρ(B) = B で終わるブロック列（縮約グラフの経路、B を含む）の最大長；η(B) = そのような経路上の循環ブロック数の最大値（B を含む）。同値な再帰：先行ブロックを持たないブロックで ρ = 1、η = [B 循環]；ρ(B) = 1 + max{ρ(B′) : B′ → B}、η(B) = [B 循環] + max{η(B′) : B′ → B}。
- 証明書条件：全ブロック間辺 B → B′ で ρ(B′) ≥ ρ(B) + 1 かつ η(B′) ≥ η(B) + [B′ 循環]；全ブロックで ρ ≥ 1、η ≥ [B 循環]。論文の定数は max ρ ≤ 65（ブロック間辺 R = 64）、max η ≤ 6（m = 6）、max d_B ≤ 13（D = 13）。

### 1. ファイル形式

UTF-8、LF、BOM なし、空行なし、コメント行なし。整数は十進、負数は先頭 `-`、先頭ゼロ・`+` なし。各行は改行で終わる。1 グラフ 1 ファイル。

#### 1.1 語付きグラフ `WORDGRAPH 2`

1 行目ヘッダ：

    WORDGRAPH 2 a=<a> b=<b> K=<K> modulus=<P> primes=<p1,p2,...> vertices=<n> edges=<m>

P は使用済み素数の積、初期段は `modulus=1 primes=`（`primes=` の後は空）。続いて頂点行 `V <q> <cell>` を (q, cell) の数値辞書順で全頂点分。続いて辺行

    E <q_u> <cell_u> <q_v> <cell_v> <c_0> <c_1> ... <c_{ℓ-1}>

を (q_u, cell_u, q_v, cell_v, word) の数値辞書順（語は要素ごとの整数比較、一方が他方の真の接頭辞なら短い方が先）で全辺分。q は現在の法 P を法とする最小非負代表（0 ≤ q < P）。同じ端点・同じ語の重複辺は 1 本。`vertices=`、`edges=` は行数に一致する。

例（`five-halves` 第 0 段入力）：

    WORDGRAPH 2 a=5 b=2 K=4 modulus=1 primes= vertices=4 edges=12
    V 0 0
    V 0 1
    V 0 2
    V 0 3
    E 0 0 0 0 1
    E 0 0 0 2 -1
    E 0 0 0 3 -1
    ...

実装 A のファイル名は `stage-<ss>-input.txt` / `stage-<ss>-output.txt`（ss は 2 桁の段番号）。B のファイル名は自由で、比較報告で (段, 入力/出力) の対応を記す。

#### 1.2 Q75 `Q75GRAPH 2`

ヘッダ：

    Q75GRAPH 2 a=7 b=5 M=429 K=2048 vertices=<n> edges=<m> blocks=<k>

頂点行 `V <q> <j>`（辞書順）、辺行 `E <q_u> <j_u> <q_v> <j_v> <c>`（辞書順）、ブロック行

    B <id> <size> <internal_edges> <period> <rho> <eta> L <phase_labels_space_separated> M <q:j> <q:j> ...

- `id` はブロックの最小頂点の辞書順で 0 から振り直す。行はその順。
- `size` はメンバー数、`internal_edges` は内部辺数、`period` は d_B（非循環ブロックは 0）。
- `L` の後に位相ラベル列（`period` 個、位相 0 = ブロック最小頂点、位相 i のラベルが i 番目）。`period` が 0 なら `L` の直後に `M` が来る。循環ブロックが認証されない場合はラベルを書かず `L` の直後に `M` を置く。このとき証明書は成立していない。
- `M` の後にメンバー (q:j) を辞書順で全部。
- 根距離 h は実装依存なので出力しない。

実装 A のファイル名は `q75.txt`。同じヘッダに循環ブロックの `B` 行だけを付けた抜粋 `q75-cyclic-blocks-excerpt.txt` も置くが、比較対象は `q75.txt`。

### 2. 正規化規約と実装依存箇所の規約化

以下は A/B が**同じ規約で出力する**ための取り決めである。

- N1 頂点名：q は CRT で合成した最小非負代表。段 s の名前は P_s を法とし、以前の段の名前を引きずらない。
- N2 辺の同一視：三つ組の集合。同一三つ組は 1 本。語が異なれば別辺（同じ端点でもよい）。
- N3 順序：1.1 の辞書順。語の比較は整数列の比較であり、文字列比較や符号なしバイト比較ではない。
- N4 持ち上げ後の頂点集合は辺の端点だけ（孤立状態を含めない）。初期グラフの頂点集合は全セル。
- N5 分岐点は G_s^in の未認証辺集合 E_U における相異なる辺の出次数 ≥ 2 で決める。分岐点のない未認証ブロックでは最小頂点を分岐点にする。**実装 A の採用データではこの代替が発生しなかった**（全段で 0 件）。B も発生件数を報告する。
- N6 位相の根はブロック最小頂点。Q75 のラベル列は位相 0 をその根に置く。B が別の根で計算した場合は、ラベル列を回転して最小頂点位相 0 に合わせてから出力する。
- N7 周期 d_B は数学的に根の選び方に依らないが、A/B の照合では「認証の可否」「ラベル列が d の下で整合すること」「ρ・η」「分割」を要素単位で照合し、**d の一致は結果として報告する**（不一致なら報告して原因を調べる；出力を書き換えない）。
- N8 Q75 の `id` は最小頂点順で振り直す。番号自体は比較しない。
- N9 ρ, η は 0.8 の正準（最長経路）値を出力する。比較では値の一致に加え、双方が証明書条件（不等式）を自分で検査して報告する。
- N10 資源上限：周期 d_B が実装の上限を超える循環ブロックを A は未認証扱いにする（保守的）。採用データで認証されたブロックの最大周期は `five-halves` で 177（第 8 段）、`cross-75` で 13、`q75` で 13。B は上限を設けないか、超えた場合に報告する。
- N11 段数：`five-halves` は最大 10 段、`cross-75` は最大 4 段。空になった段で終了する。
- N12 件数の意味：[公開論文](../../paper-ja.pdf)の付録A「辺の重複度」で説明する、実装 A の重複度を含む内部集計の「辺」数は、同一三つ組の重複を含む個数である（例：5/2 第 9 段入力は重複込み 3,754,612、相異なる辺 3,256,019；第 8 段出力は 201,199 と 171,256）。本契約の `edges=` は相異なる辺の個数であり、その重複度を含む数値と一致しない段がある。B は相異なる辺数で報告し、重複度を含む集計を目標値にしない。頂点数は一致する。
- N13 A/B とも、自分の出力を作るまで相手のファイルを開かない。

### 3. 比較手順

件数・ハッシュの一致だけで済ませない。比較器は次を行い、結果を JSON で保存する（各ファイル・各項目の一致/不一致、不一致の件数と最初の 20 件の例）。

1. ファイルの対応付け：`five-halves` の (s, input/output) 20 ファイル、`cross-75` の 8 ファイル、`q75` の 1 ファイル。欠けたファイルは不一致。
2. 語付きグラフ：ヘッダの `a b K modulus primes vertices edges` がすべて一致。`V` 行の列を要素単位で比較（A にあって B にない頂点、B にあって A にない頂点を列挙）。`E` 行も同様。順序が規約どおりか（整列・重複なし）を双方で検査。
3. Q75：`V` 行、`E` 行を 2. と同様。ブロックは**メンバー集合の族**として比較（分割の一致；番号非依存）。メンバー集合で対応付いたブロックごとに `size internal_edges period rho eta` とラベル列を比較。ラベル列は N6 の規約で完全一致を期待し、一致しなければ回転同値かどうかも報告する。循環ブロックにラベルがない（未認証）行があれば証明書失敗として報告。
4. 数学的条件の自己検査：A/B それぞれが、辺集合が 0.3/0.6/0.8 の定義から再列挙した集合と一致すること、Q75 ではブロックが強連結成分であること、全内部辺の位相条件、全ブロック間辺の順位不等式、縮約グラフの非巡回性、max ρ ≤ 65・max η ≤ 6・max d ≤ 13 を検査し、その報告を比較報告に添える。
5. 一致の意味：全要素一致は「二つの実装が同じ有限対象を出した」ことの証拠であり、定義の数学的妥当性や定理の成立を証明しない。不一致は出力を変えずに報告し、原因を特定する。
6. ファイルの SHA-256 は同一性の記録に使ってよいが、要素単位の比較の代わりにしない。

### 4. 検査する case と上限

| case | 各実装の上限 | 上限到達時 |
| --- | --- | --- |
| `five-halves` | 600 秒・4 GiB（アドレス空間） | `inconclusive` |
| `cross-75` | 300 秒・4 GiB | `inconclusive` |
| `q75` | 300 秒・4 GiB | `inconclusive` |

実行前に入力・コードのハッシュ、Python/コンパイラ版、コマンド、上限を run 記録に残し、実行後に実時間・終了理由・出力ハッシュを残す。上限到達は反例でも定理の否定でも素数集合の最小性でもない。

### 5. 出力ファイル

再現ドライバは、すべてのグラフ出力を指定した外部ディレクトリに書き出す。各実装につき、five-halvesのグラフが20個、cross-applicationのグラフが8個、定量的評価のグラフが1個ある。小さな参照データは [reference.json](../../checks/reference.json) に収録している。完全なA/B比較については[再現手順](../../REPRODUCE.md#japanese)を参照されたい。

### 6. Lean への接続

この出力だけで Lean 証明は成立しない。形式化担当が、検査条件（0.3–0.8）の数学的健全性と、実際の採用データの受理を証明する。証明書のハッシュは同一性の証拠であり健全性の代わりではない。
