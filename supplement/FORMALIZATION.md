# Lean formalization

[English](#english) · [日本語](#japanese)

<a id="english"></a>

## English

[Reproduction overview](../REPRODUCE.md)

The 93 Lean modules in [lean/](lean/) formalize the paper's main divisibility
theorems and compositeness corollaries. The toolchain is Lean 4.29.1; use the
exact toolchain and dependency revisions specified by
[lean-toolchain](lean/lean-toolchain) and
[lake-manifest.json](lean/lake-manifest.json).

### Scope and trust

| Result | Declaration | Finite evaluation |
| --- | --- | --- |
| 7/5 divisibility, modulus 4290 | `MathPaper.floor_seven_fifths_visits` | Kernel evaluation with `decide +kernel` |
| 7/5 compositeness | `MathPaper.floor_seven_fifths_composite` | Uses the preceding kernel-checked certificate |
| 5/2 divisibility, modulus 40112098026 | `MathPaper.floor_five_halves_visits` | `native_decide` |
| 5/2 compositeness | `MathPaper.floor_five_halves_composite` | Uses the preceding word certificate |
| Alternative word proof of 7/5 divisibility | `MathPaper.floor_seven_fifths_visits_word` | `native_decide` |

The general soundness proofs are checked by the Lean kernel. The one-step
7/5 proof also checks the concrete finite certificate in the kernel. Its
final theorems use only the standard axioms `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx` or additional computation axiom.

For the word proofs, `native_decide` evaluates the finite pipeline for 5/2
and 7/5. In this Lean version it introduces the generated axioms
`MathPaper.five_halves_ok._native.native_decide.ax_1_1` and
`MathPaper.seven_fifths_ok._native.native_decide.ax_1_1`, respectively.
These proofs therefore additionally trust Lean's compiler and native
evaluation. Python and C++ success flags, graph files, and hashes are not
axioms of the Lean proof. [Audit.lean](lean/Audit.lean) prints the axiom
dependencies of the final declarations.

The formalization proves sufficient rank, phase, contraction, and refinement
conditions. It does not identify the supplied blocks as strongly connected
components or prove the paper's completeness theorem for the phase test
(Theorem 21 and Corollary 22). The quantitative waiting-time theorem and the
structural, obstruction, and appendix results are outside the formalized
main-theorem chain. Their arguments and applicable finite checks are given
in the paper. See §9.4 of the [English paper](../paper-en.pdf) for the scope
of formal verification.

### Check the included sources

Use a separate fresh checkout or copy of the package: the commands below
create `.lake` files under `supplement/lean/` and logs under
`supplement/build/`. Start without locally built project `.olean` files.
Install Elan and allow it to obtain the pinned Lean toolchain. Downloading
dependencies and their compiled cache may require network access.

From the root of that fresh checkout, run the following commands in order.
Python assertions must remain enabled; do not use `python -O`.

```sh
cd supplement
mkdir -p build
(cd lean && lake exe cache get)

python3 -B lean/tools/check_finite.py \
  MathPaper.Basic MathPaper.Orbit MathPaper.Nonperiodic MathPaper.Graph \
  MathPaper.Certificate MathPaper.Success MathPaper.Enumeration \
  MathPaper.Finite.Checker MathPaper.Finite.Fast

python3 -B lean/tools/check_finite.py

python3 -B lean/tools/check_finite.py MathPaper.Main

python3 -B lean/tools/check_finite.py \
  MathPaper.Word.Graph MathPaper.Word.Cert MathPaper.Word.Lift \
  MathPaper.Word.Chain MathPaper.Word.Alphabet \
  MathPaper.Word.Pipeline.Data MathPaper.Word.Pipeline.Check \
  MathPaper.Word.Pipeline.Compute MathPaper.Word.Pipeline.LiftArr \
  MathPaper.Word.Pipeline.Initial MathPaper.Word.Pipeline.Main \
  MathPaper.Word.FiveHalves MathPaper.Word.SevenFifths \
  MathPaper.Word MathPaper

(cd lean && lake build)
(cd lean && lake env lean Audit.lean)
```

The call with no module arguments reads the ordered list in
[verification-modules.json](lean/certificates/verification-modules.json)
and builds the generated finite data, verification modules, and concrete
certificate. The sequential order avoids compiling several large finite
checks simultaneously. The final `lake build` checks the aggregate project;
the last command reports its axiom dependencies.

The harness limits each module build to 1200 seconds and a sampled
process-group resident memory total of 8 GiB. Its JSON record and per-module
logs are written under `supplement/build/`. A time or memory limit means the
check is incomplete. These are separate limits from the finite computation
runner's limits in [COMPUTATION.md](COMPUTATION.md).

### Regenerate the one-step finite sources

Regeneration is optional: all Lean sources needed for the preceding check
are included. To regenerate the one-step certificate from newly computed
data, first complete `reproduce.py recompute` as described in
[REPRODUCE.md](../REPRODUCE.md). From the package root, use a new output path:

```sh
python3 -B supplement/lean/tools/generate_finite.py \
  --certificate /tmp/floor-paper-full/finite/step/a-main/raw/certificate.json \
  --output-root /tmp/floor-paper-generated

python3 -B supplement/lean/tools/generate_verification.py \
  --output-root /tmp/floor-paper-generated
```

The first command creates the output directory. The second uses that
directory and requires the generated data to be present. Outputs are placed
under `lean/MathPaper/Finite/` and `lean/certificates/` within it. Compare the
generated `.lean` files byte for byte, or by SHA-256, with their counterparts
under `supplement/lean/`. To check regenerated sources, copy them into another
fresh checkout and repeat the sequential Lean procedure. Source generation
itself does not constitute a Lean proof check.

---

<a id="japanese"></a>

## 日本語

**Lean による形式証明**

[再現手順の概要](../REPRODUCE.md#japanese)

[lean/](lean/) の 93 個の Lean モジュールは、論文の主結果である整除定理と
合成数に関する系を形式化しています。ツールチェーンは Lean 4.29.1 です。
[lean-toolchain](lean/lean-toolchain) と
[lake-manifest.json](lean/lake-manifest.json) に指定したツールチェーンと
依存ライブラリの版をそのまま使用してください。

### 範囲と信頼対象

| 結果 | 宣言 | 有限評価 |
| --- | --- | --- |
| 7/5 の整除定理、法 4290 | `MathPaper.floor_seven_fifths_visits` | `decide +kernel` によるカーネル評価 |
| 7/5 の合成数に関する系 | `MathPaper.floor_seven_fifths_composite` | 上記のカーネルで検査した証明書を使用 |
| 5/2 の整除定理、法 40112098026 | `MathPaper.floor_five_halves_visits` | `native_decide` |
| 5/2 の合成数に関する系 | `MathPaper.floor_five_halves_composite` | 上記の語証明書を使用 |
| 語による 7/5 の整除定理の別証明 | `MathPaper.floor_seven_fifths_visits_word` | `native_decide` |

一般的な健全性証明は Lean カーネルが検査します。7/5 の一段階証明では、
具体的な有限証明書もカーネル内で検査します。その最終定理の公理依存は、
標準公理 `propext`、`Classical.choice`、`Quot.sound` のみであり、`sorryAx` や
計算に関する追加公理は含みません。

語による証明では、5/2 と 7/5 の有限パイプラインを `native_decide` で評価します。
この Lean の版では、それぞれ
`MathPaper.five_halves_ok._native.native_decide.ax_1_1` と
`MathPaper.seven_fifths_ok._native.native_decide.ax_1_1` という公理が生成されます。
したがって、これらの証明では Lean のコンパイラとネイティブ評価も追加の信頼対象です。
Python や C++ の成功フラグ、グラフファイル、ハッシュ値を Lean の公理として
取り込むことはありません。[Audit.lean](lean/Audit.lean) は、最終宣言の
公理依存を表示します。

形式化が証明するのは、ランク、位相、縮約、細分に関する十分条件です。
与えられたブロックが強連結成分そのものであることや、位相判定の完全性定理
（定理 21 と系 22）は形式化していません。定量的な待ち時間定理、構造に関する結果、
障害に関する結果、付録の結果も、形式化された主定理の証明連鎖には含みません。
それらの議論と、該当する有限計算の検査は論文に記載しています。
形式検証の範囲は [日本語論文](../paper-ja.pdf) の §9.4 も参照してください。

### 同梱ソースを検査する

別の新しいチェックアウトまたは配布物のコピーを使用してください。
以下のコマンドは `supplement/lean/` に `.lake` のファイルを、
`supplement/build/` にログを生成します。プロジェクトのビルド済み `.olean` が
存在しない状態から始めてください。Elan を導入し、指定の Lean ツールチェーンを
取得できるようにします。依存ライブラリとそのコンパイル済みキャッシュの取得には、
ネットワーク接続が必要になる場合があります。

新しいチェックアウトのルートから、次のコマンドを順に実行します。
Python の assertion は有効のままにし、`python -O` は使わないでください。

```sh
cd supplement
mkdir -p build
(cd lean && lake exe cache get)

python3 -B lean/tools/check_finite.py \
  MathPaper.Basic MathPaper.Orbit MathPaper.Nonperiodic MathPaper.Graph \
  MathPaper.Certificate MathPaper.Success MathPaper.Enumeration \
  MathPaper.Finite.Checker MathPaper.Finite.Fast

python3 -B lean/tools/check_finite.py

python3 -B lean/tools/check_finite.py MathPaper.Main

python3 -B lean/tools/check_finite.py \
  MathPaper.Word.Graph MathPaper.Word.Cert MathPaper.Word.Lift \
  MathPaper.Word.Chain MathPaper.Word.Alphabet \
  MathPaper.Word.Pipeline.Data MathPaper.Word.Pipeline.Check \
  MathPaper.Word.Pipeline.Compute MathPaper.Word.Pipeline.LiftArr \
  MathPaper.Word.Pipeline.Initial MathPaper.Word.Pipeline.Main \
  MathPaper.Word.FiveHalves MathPaper.Word.SevenFifths \
  MathPaper.Word MathPaper

(cd lean && lake build)
(cd lean && lake env lean Audit.lean)
```

モジュール名を渡さない呼出しは、
[verification-modules.json](lean/certificates/verification-modules.json) の順序付き一覧を
読み込み、生成された有限データ、検証モジュール、具体的な証明書をビルドします。
この逐次実行により、大きな有限検査を複数同時にコンパイルすることを避けます。
最後の `lake build` はプロジェクト全体を検査し、その次のコマンドは公理依存を表示します。

実行ハーネスの上限は、モジュールのビルドごとに 1200 秒、定期測定する
プロセス群の常駐メモリ合計で 8 GiB です。JSON 記録とモジュールごとのログは
`supplement/build/` に保存します。時間またはメモリの上限に達した場合は検査未完了です。
これらは [COMPUTATION.md](COMPUTATION.md#japanese) に記載した有限計算の上限とは別です。

### 一段階証明の有限ソースを再生成する

再生成は任意です。上記の検査に必要な Lean ソースはすべて同梱しています。
新しく計算したデータから一段階証明書のソースを再生成するには、まず
[REPRODUCE.md](../REPRODUCE.md#japanese) の `reproduce.py recompute` を完了してください。
配布物のルートから、未作成の出力先を指定して実行します。

```sh
python3 -B supplement/lean/tools/generate_finite.py \
  --certificate /tmp/floor-paper-full/finite/step/a-main/raw/certificate.json \
  --output-root /tmp/floor-paper-generated

python3 -B supplement/lean/tools/generate_verification.py \
  --output-root /tmp/floor-paper-generated
```

最初のコマンドが出力ディレクトリを作成します。二つ目は同じディレクトリを使い、
生成済みデータを必要とします。出力はその中の `lean/MathPaper/Finite/` と
`lean/certificates/` に保存します。生成された `.lean` ファイルを、
`supplement/lean/` 内の対応するファイルとバイト単位、または SHA-256 で比較してください。
再生成したソース自体を検査する場合は、さらに別の新しいチェックアウトにコピーして、
上記の逐次 Lean 検査を繰り返します。ソース生成の完了だけでは、Lean の証明検査が
完了したことにはなりません。
