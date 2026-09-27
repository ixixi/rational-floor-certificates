# Finite computations

[English](#english) · [日本語](#japanese)

<a id="english"></a>

## English

[Reproduction commands](../REPRODUCE.md)

The programs construct finite graphs that contain the walks induced by true
orbits. Their use requires only the implication from an orbit to a graph walk;
a graph walk need not be realizable by an orbit. All proof computations use
integer arithmetic.

The source directories are:

| Directory | Role |
| --- | --- |
| [computations/implementation_a](computations/implementation_a/) | First implementation of the one-step graph method |
| [computations/implementation_b](computations/implementation_b/) | Independent implementation and comparisons for the one-step method |
| [computations/word_a](computations/word_a/) | First implementation of word-labelled graphs and the associated finite computations |
| [computations/word_b](computations/word_b/) | Independent implementation and checks for word-labelled graphs and the associated finite computations |
| [computations/five_thirds](computations/five_thirds/) | Producer with embedded checker, small Python reference, and recorded runs for the 5/3 certificate (Appendix F), as supplied with the research notes for this addition |
| [computations/word_b/five_thirds](computations/word_b/five_thirds/) | Records of implementation B's two-direction 5/3 run, the forward-only comparison, and the stage-by-stage comparison with the producer |
| [computations/additional_obstructions](computations/additional_obstructions/) | Direct checker and witness for the 5/3 return-word obstruction with the primes up to 23 (Corollary 78) |
| [computations/exploratory](computations/exploratory/) | Exploratory records of the addition: a smaller interval-based 7/5 certificate and base searches; not used by the paper's theorems |

The two implementations have separate scientific cores for edge generation,
component decomposition, and certification. They share input conventions and
comparison formats. The full reproduction covers the one-step certificates,
the word-labelled certificates for 5/2, 7/5, and 5/3, the finite graph
calculation for the 7/5 waiting-time bound, and the finite calculations
supporting the paper's appendices.

Comparisons inspect complete finite data, including edges and labels,
component partitions, phase certificates, and graph transformations. Word
refinement checks prime avoidance at intermediate letters as well as at the
final endpoint. Matching table counts alone would not establish these
properties.

From the package root, run:

```sh
python3 -B reproduce.py recompute --output /tmp/floor-paper-full
```

Choose a new output directory outside the package. The command generates the
graphs and comparison records anew. It compares the fresh outputs of the
implementations and checks the reference digests in
[checks/reference.json](../checks/reference.json). Digests identify data;
the mathematical justification comes from the paper's reduction and the
certificate checks. The generated records and logs remain in the chosen
output directory so individual stages can be inspected.

The finite runner allows at most 600 seconds per command and 8 GiB of
memory, and 1800 seconds overall for `check` and 3600 seconds for the full
run. A resource-limit stop is `inconclusive`;
it does not disprove a theorem or establish failure of the certificate
method. The `check` command performs only a preflight and does not replace
the complete `recompute` command. These commands do not rebuild the Lean
proofs; follow [FORMALIZATION.md](FORMALIZATION.md) for that separate check.

### The 5/3 computation

The 5/3 certificate (Appendix F and Section 9.5 of the paper) uses, besides
the operations of the other word-labelled certificates, the exact contraction
of in-degree-one chains. It is computed by two implementations.

- *Producer.* [five_thirds/certificate53.cpp](computations/five_thirds/certificate53.cpp)
  with its embedded checker [audit_basic.hpp](computations/five_thirds/audit_basic.hpp)
  was supplied with the research notes for this addition. The checker verifies
  the initial edges, every lifted edge by a forward residue-set calculation,
  sufficient rank and all-letter phase conditions on every edge, and every
  contracted edge. It is compiled into the same program and shares its
  representations. [reference53.py](computations/five_thirds/reference53.py)
  reconstructs the first five stages (through the prime 17) by a different
  method. The directory keeps its own `SHA256SUMS` and driver `reproduce.py`.
- *Implementation B.* `wgb pipeline ... --bidir` adds backward passes (reverse
  every edge and word, remove, out-contract, reverse back) with the iteration
  rule of Appendix F.3. The option was written from the mathematical
  statement without reading the producer, its checker, or its Python program.
  Without the option, B's output is unchanged.
- *Comparison.* [word_b/canon_wordgraph.cpp](computations/word_b/canon_wordgraph.cpp)
  writes each graph in a canonical text. B's vertices are ordered by cell and
  then by the residues modulo the primes in the order of addition, which is
  the producer's vertex order. [word_b/compare_five_thirds.py](computations/word_b/compare_five_thirds.py)
  compares the canonical texts of all 20 stage graphs, and the per-stage
  counts. The recorded comparison ([word_b/five_thirds/comparison.json](computations/word_b/five_thirds/comparison.json))
  compared the canonical texts byte for byte; the reproduction compares their
  SHA-256 digests with the values in `checks/reference.json`.

`recompute` runs both implementations through all ten stages, compares them,
checks that both final output graphs are empty, and records the outcome under
`five_thirds` in `finite/receipt.json`. `check` runs B through the prime 17,
compares it with the producer's recorded small graphs, reruns the small
Python reference comparison, and checks the obstruction witness. The full 5/3
graph dumps take about 8 GB in the output directory. The full runs of B and of
the producer each used about 2.5 GiB of memory and about three minutes on the
recorded machine.

The exploratory records under `computations/exploratory/` (a smaller 7/5
certificate with interval propagation, and the base searches) are included as
supplementary material. They are not used by any theorem of the paper and are
not run by the reproduction commands.

---

<a id="japanese"></a>

## 日本語

**有限計算**

[再現コマンド](../REPRODUCE.md#japanese)

プログラムは、真の軌道から生じるウォークを含む有限グラフを構成します。
証明に用いるのは、軌道からグラフ上のウォークへの含意です。
グラフ上のすべてのウォークが軌道として実現できる必要はありません。
証明用の計算はすべて整数演算で行います。

ソースの構成は次のとおりです。

| ディレクトリ | 役割 |
| --- | --- |
| [computations/implementation_a](computations/implementation_a/) | 一段階グラフ法の第 1 実装 |
| [computations/implementation_b](computations/implementation_b/) | 一段階グラフ法の独立実装と比較処理 |
| [computations/word_a](computations/word_a/) | 語ラベル付きグラフと関連する有限計算の第 1 実装 |
| [computations/word_b](computations/word_b/) | 語ラベル付きグラフと関連する有限計算の独立実装・検査 |
| [computations/five_thirds](computations/five_thirds/) | 5/3 の証明書（付録F）の生成プログラムと組込み検査器、小規模の Python 参照実装、実行記録（この追加の研究ノートに同梱されていたもの） |
| [computations/word_b/five_thirds](computations/word_b/five_thirds/) | 実装 B による 5/3 の両方向の計算、前向きのみの計算との比較、生成プログラムとの段ごとの照合の記録 |
| [computations/additional_obstructions](computations/additional_obstructions/) | 23 以下の素数に対する 5/3 の帰還語障害（系78）の直接検査器と証拠 |
| [computations/exploratory](computations/exploratory/) | この追加の探索記録（区間伝播を用いた小さな 7/5 の証明書、底の探索）。論文の定理には用いない |

二つの実装は、辺生成、成分分解、認証判定の科学的な中核を別々に実装しています。
入力規約と比較形式は共通です。完全な再現の対象は、一段階証明書、5/2、7/5、5/3 の
語ラベル付き証明書、7/5 の待ち時間上界に用いる有限グラフ計算、および論文の付録を
支える有限計算です。

比較では、辺とラベル、成分分割、位相証明書、グラフ変換を含む有限データの全要素を
調べます。語の細分では、最後の終点に加えて語の途中の各文字でも素数による整除を
避けているか検査します。表の件数が一致するだけでは、これらの性質は確認できません。

配布物のルートから実行します。

```sh
python3 -B reproduce.py recompute --output /tmp/floor-paper-full
```

出力先には、配布物の外にある未作成のディレクトリを指定してください。
このコマンドは、グラフと比較記録を新しく生成します。各実装の新しい出力同士を比較し、
[checks/reference.json](../checks/reference.json) の基準ダイジェストとも照合します。
ダイジェストはデータの同一性を示すものであり、数学的な根拠は論文中の還元と
証明書の検査にあります。各段階を確認できるよう、生成した記録とログは指定した
出力ディレクトリに保存します。

有限計算の実行上限は、コマンドごとに 600 秒、メモリは 8 GiB、全体では `check` が 1800 秒、完全な実行が 3600 秒です。
資源上限による停止は `inconclusive`（判定未完了）であり、定理への反例や
認証法の失敗を意味しません。`check` は事前確認だけを行うため、完全な `recompute`
の代わりにはなりません。また、これらのコマンドは Lean の証明を再構築しません。
Lean の検査は [FORMALIZATION.md](FORMALIZATION.md#japanese) の手順で別に行います。

### 5/3 の計算

5/3 の証明書（論文の付録Fと第9.5節）は、ほかの語ラベル付き証明書の操作に加えて、
入次数1の鎖の厳密な縮約を用います。二つの実装で計算します。

- *生成プログラム。* [five_thirds/certificate53.cpp](computations/five_thirds/certificate53.cpp)
  と組込み検査器 [audit_basic.hpp](computations/five_thirds/audit_basic.hpp) は、
  この追加の研究ノートに同梱されていたものです。検査器は、初期辺、前向きの剰余集合の計算による
  すべての持ち上げ辺、すべての辺の順位と全文字の位相の十分条件、およびすべての縮約辺を検査します。
  同じプログラムに組み込まれ、表現を共有します。
  [reference53.py](computations/five_thirds/reference53.py) は、最初の5段階（素数 17 まで）を
  別の方法で再構成します。このディレクトリは独自の `SHA256SUMS` と実行スクリプト `reproduce.py` を持ちます。
- *実装 B。* `wgb pipeline ... --bidir` は、付録F.3 の反復規則に従って後ろ向きのパス
  （すべての辺と語を反転し、除去と出方向の縮約を行い、反転して戻す）を加えます。
  このオプションは、生成プログラム、その検査器、Python 実装を読まずに、数学的な記述から書きました。
  オプションを付けなければ、B の出力は変わりません。
- *照合。* [word_b/canon_wordgraph.cpp](computations/word_b/canon_wordgraph.cpp) は、各グラフを
  正規化したテキストに書き出します。B の頂点は、セル、続いて追加した順の各素数を法とする剰余の順に並べます。
  これは生成プログラムの頂点の順序と一致します。
  [word_b/compare_five_thirds.py](computations/word_b/compare_five_thirds.py) は、全20個の段階グラフの
  正規化テキストと段ごとの件数を比較します。記録した照合
  （[word_b/five_thirds/comparison.json](computations/word_b/five_thirds/comparison.json)）では
  正規化テキストをバイト単位で比較しました。再現手順では、その SHA-256 を `checks/reference.json` の値と照合します。

`recompute` は二つの実装で全10段を計算し、照合し、両方の最後の出力グラフが空であることを確かめ、
結果を `finite/receipt.json` の `five_thirds` に記録します。`check` は B を素数 17 まで計算して
生成プログラムの記録済みの小さなグラフと照合し、小規模の Python 参照比較を再実行し、障害の証拠を検査します。
5/3 の全段のグラフの出力は、出力ディレクトリで約 8 GB を使います。記録した環境では、B と生成プログラムの
全段計算は、それぞれ約 2.5 GiB のメモリと約3分を要しました。

`computations/exploratory/` の探索記録（区間伝播を用いた小さな 7/5 の証明書と、底の探索）は補足資料として
収録しています。論文の定理には用いず、再現コマンドでも実行しません。
