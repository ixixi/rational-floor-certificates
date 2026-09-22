# Reproduction

[English](#english) · [日本語](#japanese)

<a id="english"></a>

## English

[Paper and sources](README.md)

Run the commands below from the package root. Choose output paths outside the
package that do not already exist. Python assertions must be enabled; use
`python3 -B`, not `python -O`.

### Requirements

Start with [ENVIRONMENT.md](ENVIRONMENT.md): it supplies the Python project and
hash-locked dependencies, Linux/C++/TeX/font requirements, a pinned Docker
recipe, and prerequisite diagnostics. Finite calculations use Python's
standard library. PDF rebuilding additionally uses the locked `pdf` extra.
Lean has a separate pinned toolchain and checking procedure in
[FORMALIZATION.md](supplement/FORMALIZATION.md).

The finite runner enforces limits of 600 seconds per command, 1800 seconds
overall, and 8 GiB of memory.

### Verify the downloaded files

```sh
python3 -B reproduce.py verify
```

This checks the package manifest and file hashes. It establishes file
identity, not the correctness of the mathematical results.

### Run a preflight

```sh
python3 -B reproduce.py check --output /tmp/floor-paper-check
```

This runs unit checks, selected small examples and comparisons, the 7/5 word
case, and selected appendix checks. It does not run the full 5/2 word chain
or all appendix computations. Use it to check the environment before the
complete reproduction.

### Recompute all finite results

```sh
python3 -B reproduce.py recompute --output /tmp/floor-paper-full
```

This regenerates the finite computations, compares the two implementations'
new outputs element by element, and checks the fixed reference digests in
[checks/reference.json](checks/reference.json). The computation sources are
under `supplement/computations/`. Large graph outputs and execution logs are
created in the specified output directory. The scope and comparison
principles are described in [COMPUTATION.md](supplement/COMPUTATION.md).

Read `record.json` in the output directory for the overall result and
`finite/receipt.json` for the finite runner's result. The overall status is
`PASS`, `FAIL`, or `inconclusive`. A successful preflight is identified by
`PREFLIGHT_PASS` in the finite receipt; a successful full run by
`FINITE_COMPUTATIONS_PASS`. Successful commands exit with code 0; failures
and incomplete runs exit with a nonzero code. The command logs and comparison
records allow individual checks to be inspected.

A time or memory limit yields `inconclusive`: the computation has not
finished. It is not a counterexample to the paper's statements. A preflight
success is not a full computation result. Neither finite command builds
Lean; use the separate sequential procedure in
[FORMALIZATION.md](supplement/FORMALIZATION.md) to check the formal proofs.

### Regenerate the explanatory figures

```sh
python3 -B sources/figures/illustrations/build.py --output /tmp/floor-paper-figures
python3 -B sources/figures/illustrations/build.py --language ja --output /tmp/floor-paper-figures-ja
```

The figure sources use exact small examples, schematic constructions, or
included computed summaries as identified in their captions and manifest.
The builder writes vector PDF/SVG files, preview images, and a build record
outside the package. These illustrations explain the proof and algorithm;
they do not replace the finite computation or the Lean checks.

### Rebuild either PDF

```sh
python3 -B build_pdf.py --language en --output /tmp/floor-paper-en.pdf
python3 -B build_pdf.py --language ja --output /tmp/floor-paper-ja.pdf
```

The builder uses the corresponding file under `sources/`, runs without shell
escape, and repeats TeX passes until cross-references stabilize. Its limits
are 600 seconds, 4 GiB of address space, and 10 passes. Unresolved references
and other checked TeX diagnostics cause a failed build. A resource-limit stop
is incomplete.

For each requested PDF, a sibling `.build.json` record and `.build-logs/`
directory retain the build result and logs. For example,
`/tmp/floor-paper-ja.pdf` is accompanied by
`/tmp/floor-paper-ja.build.json` and `/tmp/floor-paper-ja.build-logs/`.
The build uses a fixed source date; different TeX or font versions can still
produce different PDF bytes.

---

<a id="japanese"></a>

## 日本語

**再現手順**

[論文とソース](README.md#japanese)

以下のコマンドは配布物のルートから実行します。出力先には、配布物の外にある
未作成のパスを指定してください。Python の assertion は有効にする必要があります。
`python3 -B` を使い、`python -O` は使わないでください。

### 必要なソフトウェア

まず [ENVIRONMENT.md](ENVIRONMENT.md#japanese) に従って環境を用意してください。
Python プロジェクトとハッシュ固定依存、Linux・C++・TeX・フォントの要件、固定した
Docker 構築手順、前提の診断方法を収録しています。有限計算は Python 標準ライブラリを
使います。PDF の再生成には追加で固定した `pdf` 依存が必要です。
Lean のツールチェーンと検査手順は
[FORMALIZATION.md](supplement/FORMALIZATION.md#japanese) に記載しています。

有限計算の実行上限は、コマンドごとに 600 秒、全体で 1800 秒、メモリは 8 GiB です。

### 取得したファイルを照合する

```sh
python3 -B reproduce.py verify
```

配布物のマニフェストとファイルのハッシュを照合します。これはファイルの同一性を
確認するものであり、数学的な結果の正しさを検査するものではありません。

### 事前確認を実行する

```sh
python3 -B reproduce.py check --output /tmp/floor-paper-check
```

単体検査、選択した小例と比較、7/5 の語の事例、および付録の一部の検査を実行します。
5/2 の語の全段階や、付録の全計算は実行しません。完全な再現の前に、環境を
確認するためのコマンドです。

### 有限計算全体を再実行する

```sh
python3 -B reproduce.py recompute --output /tmp/floor-paper-full
```

有限計算を新たに実行し、二つの実装の新しい出力を全要素で比較したうえで、
[checks/reference.json](checks/reference.json) の固定された基準ダイジェストとも照合します。
計算ソースは `supplement/computations/` にあります。大きなグラフ出力と実行ログは、
指定した出力ディレクトリに生成します。対象範囲と比較の考え方は
[COMPUTATION.md](supplement/COMPUTATION.md#japanese) に記載しています。

全体の結果は出力ディレクトリの `record.json`、有限計算の実行結果は
`finite/receipt.json` で確認できます。全体の状態は `PASS`、`FAIL`、`inconclusive`
のいずれかです。有限計算の記録では、事前確認の成功を `PREFLIGHT_PASS`、
完全な実行の成功を `FINITE_COMPUTATIONS_PASS` と表示します。
正常終了時の終了コードは 0、失敗または未完了の場合は非零です。
各検査の内容は、コマンドのログと比較記録で確認できます。

時間またはメモリの上限に達した場合は `inconclusive`（判定未完了）となり、
計算は完了していません。これは論文の主張への反例ではありません。
事前確認の成功も、全計算の完了を意味しません。どちらの有限計算コマンドも
Lean をビルドしないため、形式証明は
[FORMALIZATION.md](supplement/FORMALIZATION.md#japanese) の逐次実行手順で別に検査します。

### 説明図を再生成する

```sh
python3 -B sources/figures/illustrations/build.py --output /tmp/floor-paper-figures
python3 -B sources/figures/illustrations/build.py --language ja --output /tmp/floor-paper-figures-ja
```

図の入力は、各 caption と manifest で区別した厳密な小例、概念的な構成、または
同梱の計算済み要約です。図のビルダーはベクトル PDF・SVG、プレビュー画像、
ビルド記録を配布物の外へ出力します。図は証明とアルゴリズムの説明用であり、
有限計算や Lean の検査を置き換えるものではありません。

### PDF を再生成する

```sh
python3 -B build_pdf.py --language en --output /tmp/floor-paper-en.pdf
python3 -B build_pdf.py --language ja --output /tmp/floor-paper-ja.pdf
```

ビルダーは `sources/` 内の対応するファイルを使い、シェルエスケープを無効にして
TeX を実行し、相互参照が安定するまで繰り返します。上限は 600 秒、
アドレス空間 4 GiB、最大 10 パスです。未解決の参照や、検査対象のほかの
TeX 診断があるとビルド失敗になります。資源上限で停止した場合は未完了です。

指定した PDF ごとに、同じ親ディレクトリへ `.build.json` 記録と `.build-logs/`
ディレクトリを作り、ビルド結果とログを保存します。たとえば
`/tmp/floor-paper-ja.pdf` に対しては、`/tmp/floor-paper-ja.build.json` と
`/tmp/floor-paper-ja.build-logs/` が生成されます。
ビルド時のソース日時は固定していますが、TeX やフォントの版が異なると
PDF のバイト列も異なる場合があります。
