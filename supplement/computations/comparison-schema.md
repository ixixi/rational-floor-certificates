# One-step graph comparison format

[English](#english) · [日本語](#japanese)

<a id="english"></a>

## English

The independently written implementations share mathematical definitions and this output format. Each computes its own outputs; expected values are used only for comparison.

### File organization

The scientific output of each case is UTF-8 JSON (optionally compressed with gzip), without execution dates, elapsed times, or absolute paths. Run records are kept in separate JSON files and record the command, Python version, limits fixed before execution, SHA-256 hashes of the inputs/code/outputs, and termination reason. Large scientific outputs, small summaries, and run records are stored in the requested output directory outside the distribution. See the [reproduction guide](../../REPRODUCE.md) for their locations and the execution procedure. For gzip files, compare the values of the decompressed JSON as well.

Required top-level keys:

- `schema_version`: `1`
- `parameters`: integers `a,b,M,K0,f,max_stages`
- `termination`: one of `success`, `inconclusive`, or `error`
- `stages`: an array of stages in execution order

### Stage

- `K`: a positive integer.
- `vertices`: `[q,j]` in lexicographic order, without duplicates. The whole set W used in the computation.
- `edges`: `[q,j,z,k,e]` in lexicographic order, without duplicates. Edges with different labels are distinct elements. Include all edges whose endpoints belong to W and satisfy E1–E3.
- `components`: the component objects described below. Each component's `vertices` are in lexicographic order; the components are ordered lexicographically by their least vertices. Include acyclic singleton components.
- `retained`: the union W′ of the uncertified cyclic components, in lexicographic order.
- `refined_vertices`: `[q,f*j+i]` (`[q,j]∈retained,0≤i<f`) in lexicographic order. Empty at the final successful stage. The next refinement set is also defined at a stage stopped by a limit, but if generating it would exceed the memory limit, do not generate it: use `null` and record `inconclusive`.

Required keys of each component object:

- `vertices`: the vertices of the component.
- `internal_edge_count`: the number of internal edges, counting different labels separately.
- `cyclic`: whether the component has an internal edge.
- `certified`: whether it is cyclic and all internal-edge labels at each phase are equal.
- `h`: internal shortest-path distances from the lexicographically least vertex, stored as an integer array in the same order as `vertices`. For an acyclic singleton, use `[0]`.
- `d`: the gcd of `abs(h(u)+1-h(v))` over all internal edges. For an acyclic component, use 0.
- `phase_labels`: if certified, an array of the unique label at each phase c=0,…,d−1; otherwise `null`.
- `word`: if certified, an array obtained by taking the primitive period of phase_labels and then its lexicographically least rotation; otherwise `null`. Do not confuse `len(word)` with d.
- `collision`: if cyclic and uncertified, two internal edges (each an array of 5 integers) that emit different labels from the same h(source) mod d; otherwise `null`. Witnesses may be chosen arbitrarily and need not be identical in A and B. Check the validity of each witness.

Additional fields are allowed, but the comparison report must specify which fields are compared and why any are excluded. Matching counts or hashes alone does not replace element-wise comparison. Each implementation independently maintains the implementation details of its SCC post-checks.

### Cases and limits

The main case `(7,5,4290,32,4)` has 4 stages. The three adopted known cases `(3,2,770,32,4)`, `(4,3,30,32,4)`, and `(5,4,6006,32,4)` each have 1 stage. The limits for each implementation and each case are 600 seconds and 4 GiB. Reaching a limit gives `inconclusive`. Record these limits in the run configuration before execution.

The comparator compares all edges, all vertices, the SCC partition, h, d, certification, words, retained sets, and refinement sets, and checks collision witnesses individually. Different witnesses are not an error. Table 1, Table 2, and the summary of the three cases are generated from this scientific output. Each of A and B compares its edge enumeration against a literal exhaustive search of E1–E3 on small examples and checks conditions involving nonunit b, negative e, equality at the E3 boundary, self-loops, and distinct labels.

### Connection to Lean

This output alone does not establish a Lean proof. The formalization must prove the mathematical soundness of the checker and its acceptance of the actual main case. If a minimal additional certificate (such as component ranks or phases) is needed, supply it through a separately versioned generator and format. Certificate hashes establish identity, not soundness.

<a id="japanese"></a>

## 日本語

**1ステップグラフの比較形式**

独立に作成した実装が共有するのは、数学的定義とこの出力形式である。各実装は自ら出力を計算し、期待値は比較にだけ用いる。

### ファイル構成

各caseの科学的出力はUTF-8 JSON（必要ならgzip）とし、実行日時・所要時間・絶対パスを含めない。run記録は別のJSONへ分離し、コマンド、Python版、実行前上限、入力/コード/出力のSHA-256、終了理由を保存する。大きな科学的出力、小さな集計、および実行記録は、配布物の外に指定した出力ディレクトリに保存する。配置と実行手順は[再現ガイド](../../REPRODUCE.md#japanese)を参照されたい。gzipの場合も展開後JSONの値を比較する。

トップレベルの必須キー:

- `schema_version`: `1`
- `parameters`: 整数 `a,b,M,K0,f,max_stages`
- `termination`: `success`, `inconclusive`, `error` のいずれか
- `stages`: 実行順のstage配列

### stage

- `K`: 正整数。
- `vertices`: `[q,j]` の辞書順、重複なし。実行したW全体。
- `edges`: `[q,j,z,k,e]` の辞書順、重複なし。ラベル違いの辺は別要素。端点がWに属しE1–E3を満たす全辺。
- `components`: 以下の成分オブジェクト。各成分の `vertices` は辞書順、成分群は最小頂点の辞書順。非循環の単頂点成分も含む。
- `retained`: 未認証循環成分の和集合W′を辞書順。
- `refined_vertices`: `[q,f*j+i]`（`[q,j]∈retained,0≤i<f`）を辞書順。最終成功段では空。上限停止段でも次の細分集合を定義できるが、メモリ上限を越す場合は生成せず `null` とし `inconclusive` を記録する。

成分オブジェクトの必須キー:

- `vertices`: 成分の頂点。
- `internal_edge_count`: ラベル込み内部辺の本数。
- `cyclic`: 内部辺を持つか。
- `certified`: cyclicかつ位相ごとの全内部辺ラベルが単一か。
- `h`: 辞書順最小頂点を根とする内部最短距離を、`vertices` と同じ順序の整数配列で保存。非循環単頂点は `[0]`。
- `d`: 全内部辺の `abs(h(u)+1-h(v))` のgcd。非循環成分は0。
- `phase_labels`: 認証済みの場合、c=0,…,d−1の各位相の唯一のラベルを並べた配列。それ以外は `null`。
- `word`: 認証済みの場合、phase_labelsの原始周期を取り辞書順最小回転にした配列。それ以外は `null`。`len(word)` とdを混同しない。
- `collision`: 循環・未認証の場合、同じh(source) mod dから異なるラベルを出す内部辺2本（各辺は5整数配列）。それ以外は `null`。証人の選び方は任意であり、A/Bで同一を要求しない。各証人の妥当性を検査する。

追加フィールドは許すが、比較報告には比較対象と除外理由を記載する。件数やhash一致だけで全要素比較の代用としない。SCC事後検査の実装詳細は各実装で独立に管理する。

### 検査するcaseと上限

主例 `(7,5,4290,32,4)` は4段。採用する既知三例 `(3,2,770,32,4)`, `(4,3,30,32,4)`, `(5,4,6006,32,4)` は1段。各実装・各caseで600秒、4 GiB。停止上限に達したら `inconclusive`。実行前にrun設定へ記録する。

比較器は全辺・全頂点・SCC分割・h・d・認証・語・残集合・細分集合を比較し、衝突証人を個別に検査する。異なる証人をエラーとしない。表1・表2・三例集計はこの科学的出力から生成する。A/Bそれぞれが小例の文字どおりのE1–E3全探索と辺列挙を照合し、非単元b、負のe、E3等号、自己ループ、異なるラベルを含む条件を点検する。

### Leanへの接続

この出力だけでLean証明は成立しない。形式化担当がチェッカーの数学的健全性と実際の主例の受理を証明する。最小限の追加証明書（成分順位や位相など）が必要な場合、別の版管理した生成器・形式で提供する。証明書のhashは同一性の証拠であり健全性の代わりではない。
