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

The two implementations have separate scientific cores for edge generation,
component decomposition, and certification. They share input conventions and
comparison formats. The full reproduction covers the one-step certificates,
the word-labelled certificates for 5/2 and 7/5, the finite graph calculation
for the 7/5 waiting-time bound, and the finite calculations supporting the
paper's appendices.

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

The finite runner allows at most 600 seconds per command, 1800 seconds for
the full run, and 8 GiB of memory. A resource-limit stop is `inconclusive`;
it does not disprove a theorem or establish failure of the certificate
method. The `check` command performs only a preflight and does not replace
the complete `recompute` command. These commands do not rebuild the Lean
proofs; follow [FORMALIZATION.md](FORMALIZATION.md) for that separate check.

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

二つの実装は、辺生成、成分分解、認証判定の科学的な中核を別々に実装しています。
入力規約と比較形式は共通です。完全な再現の対象は、一段階証明書、5/2 と 7/5 の
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

有限計算の実行上限は、コマンドごとに 600 秒、全体で 1800 秒、メモリは 8 GiB です。
資源上限による停止は `inconclusive`（判定未完了）であり、定理への反例や
認証法の失敗を意味しません。`check` は事前確認だけを行うため、完全な `recompute`
の代わりにはなりません。また、これらのコマンドは Lean の証明を再構築しません。
Lean の検査は [FORMALIZATION.md](FORMALIZATION.md#japanese) の手順で別に行います。
