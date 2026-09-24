# Finite graph certificates for composite terms in rational floor sequences

[English](#english) · [日本語](#japanese)

<a id="english"></a>

## English

DOI (Zenodo): [10.5281/zenodo.22887589](https://doi.org/10.5281/zenodo.22887589).

This repository contains the paper, its computation programs, and its Lean
formalization. For every real number ξ > 0, the paper proves that each sequence
⌊ξ(7/5)ⁿ⌋ and ⌊ξ(5/2)ⁿ⌋ has infinitely many composite terms. The proof uses finite
labelled graphs to certify repeated divisibility by a fixed set of primes.
The paper also gives an explicit waiting-time bound for 7/5 and studies the
scope and limitations of the certificate method.

| Read or use | File |
| --- | --- |
| English paper | [paper-en.pdf](paper-en.pdf) |
| Japanese paper | [paper-ja.pdf](paper-ja.pdf) |
| TeX sources | [English](sources/paper.tex), [Japanese](sources/paper-ja.tex) |
| English Markdown source | [supplement/manuscript/paper.md](supplement/manuscript/paper.md) |
| Reproduction instructions | [REPRODUCE.md](REPRODUCE.md) |
| Environment and installation | [ENVIRONMENT.md](ENVIRONMENT.md) |
| Figure sources and regeneration | [sources/figures/illustrations/README.md](sources/figures/illustrations/README.md) |
| Finite computations | [supplement/COMPUTATION.md](supplement/COMPUTATION.md) |
| Lean scope and checking instructions | [supplement/FORMALIZATION.md](supplement/FORMALIZATION.md) |
| Japanese explanatory slides for readers with high-school mathematics (PowerPoint, 99 slides) | [slides/paper-explained-ja.pptx](slides/paper-explained-ja.pptx) |

The complete finite reproduction runs two implementations and compares their
newly generated data element by element. The small reference file
[checks/reference.json](checks/reference.json) supplies fixed comparison
criteria; large execution outputs are generated locally. The `check` command
is a preflight, while `recompute` runs the full finite reproduction. See
[REPRODUCE.md](REPRODUCE.md) for dependencies, commands, and resource limits.

The finite Python computations use the standard library. The repository also
includes `pyproject.toml`, `uv.lock`, hash-pinned PDF dependencies, and a Dockerfile
with a pinned base image and package snapshot for Python, C++, TeX, and fonts.
Lean and Mathlib are pinned separately in the formalization directory. Start with
[ENVIRONMENT.md](ENVIRONMENT.md) to select the environment for the checks you need.

The Lean sources cover the main divisibility and compositeness statements.
The one-step 7/5 proof checks its finite certificates in the Lean kernel.
The word-labelled proofs use kernel-checked soundness theorems and
`native_decide` for finite evaluation, adding trust in Lean's compiler and
native evaluation. The precise coverage is described in
[FORMALIZATION.md](supplement/FORMALIZATION.md).

[MANIFEST.json](MANIFEST.json) and [SHA256SUMS](SHA256SUMS) identify the bundled
files. `MANIFEST.json` records `source_sha256` for the source set. The Git commit
from which a checkout is obtained identifies its repository revision.

Repository: [ixixi/rational-floor-certificates](https://github.com/ixixi/rational-floor-certificates).

---

<a id="japanese"></a>

## 日本語

**有理数を底とする床関数列の合成数項に対する有限グラフ証明書**

DOI（Zenodo）: [10.5281/zenodo.22887589](https://doi.org/10.5281/zenodo.22887589)。

このリポジトリには、論文、計算プログラム、Lean による形式証明を収録しています。
論文では、任意の実数 ξ > 0 に対し、二つの数列 ⌊ξ(7/5)ⁿ⌋ と ⌊ξ(5/2)ⁿ⌋ が
それぞれ無限に多くの合成数項を持つことを証明します。有限個の素数のいずれかによる
整除が繰り返し起こることを、有限ラベル付きグラフで認証する方法を用います。
さらに、7/5 に対する明示的な待ち時間上界と、この認証法の適用範囲および限界を示します。

| 内容 | ファイル |
| --- | --- |
| 英語論文 | [paper-en.pdf](paper-en.pdf) |
| 日本語論文 | [paper-ja.pdf](paper-ja.pdf) |
| TeX ソース | [英語](sources/paper.tex)、[日本語](sources/paper-ja.tex) |
| 英語 Markdown 原稿 | [supplement/manuscript/paper.md](supplement/manuscript/paper.md) |
| 再現手順 | [REPRODUCE.md](REPRODUCE.md#japanese) |
| 環境とインストール | [ENVIRONMENT.md](ENVIRONMENT.md#japanese) |
| 図のソースと再生成 | [sources/figures/illustrations/README.md](sources/figures/illustrations/README.md#japanese) |
| 有限計算 | [supplement/COMPUTATION.md](supplement/COMPUTATION.md#japanese) |
| Lean の形式化範囲と検査手順 | [supplement/FORMALIZATION.md](supplement/FORMALIZATION.md#japanese) |
| 高校数学の知識で読める解説スライド（PowerPoint、99 枚） | [slides/paper-explained-ja.pptx](slides/paper-explained-ja.pptx) |

有限計算の完全な再現では、二つの実装を実行し、新しく生成したデータを全要素で比較します。
小さな基準ファイル [checks/reference.json](checks/reference.json) に固定された照合基準を
収録し、大きな実行出力は利用者の環境で生成します。`check` は事前確認、`recompute` は
有限計算全体の再実行です。依存ソフトウェア、コマンド、資源上限は
[REPRODUCE.md](REPRODUCE.md#japanese) に記載しています。

有限計算の Python コードは標準ライブラリを使用します。さらに `pyproject.toml`、
`uv.lock`、ハッシュ付きの PDF 依存指定、ベースイメージとパッケージの取得時点を
固定した Dockerfile を収録し、Python・C++・TeX・フォントの環境を用意しています。
Lean と Mathlib は形式証明ディレクトリで別に固定しています。
必要な検査に合う環境の準備は [ENVIRONMENT.md](ENVIRONMENT.md#japanese) から始めてください。

Lean ソースは、主結果の整除定理と合成数に関する系を形式化しています。
7/5 の一段階証明では、有限証明書も Lean カーネル内で検査します。
語ラベル付きグラフによる証明では、健全性定理をカーネルで検査し、有限評価に
`native_decide` を用いるため、Lean のコンパイラとネイティブ評価も信頼対象に含まれます。
正確な範囲は [FORMALIZATION.md](supplement/FORMALIZATION.md#japanese) を参照してください。

[MANIFEST.json](MANIFEST.json) と [SHA256SUMS](SHA256SUMS) は同梱ファイルを識別します。
`MANIFEST.json` の `source_sha256` はソース集合の識別情報です。
Git から取得した場合は、取得したコミットがリポジトリの版を特定します。

リポジトリ: [ixixi/rational-floor-certificates](https://github.com/ixixi/rational-floor-certificates)。
