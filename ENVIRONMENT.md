# Reproduction environment

[English](#english) · [日本語](#japanese)

<a id="english"></a>

## English

[Reproduction commands](REPRODUCE.md)

The finite calculations use Python's standard library and compiled C++17;
there is no numerical Python package to install. The PDF builder additionally
uses `pypdf`. Python dependencies are declared in [pyproject.toml](pyproject.toml)
and fixed, including archive hashes, in [uv.lock](uv.lock) and
[requirements-pdf.txt](requirements-pdf.txt). Linux is required for the
runner's `/proc`, process-group and resource-limit controls; Windows users can
use WSL2 or the Linux container below.

### Install Python dependencies

Use Python 3.10–3.13. Put the virtual environment outside the checkout so
that it is not confused with the published source set. The following example
uses an existing Python installation and installs only the locked PDF packages:

```sh
python3 -m venv ../floor-paper-venv
. ../floor-paper-venv/bin/activate
python3 -m pip install --require-hashes -r requirements-pdf.txt
```

Alternatively, with [uv](https://docs.astral.sh/uv/):

```sh
UV_PROJECT_ENVIRONMENT=../floor-paper-venv uv sync --locked --extra pdf --python python3
. ../floor-paper-venv/bin/activate
```

The `--locked` option checks that the lock agrees with the project, without
updating it. The pip alternative uses mandatory archive hashes. Neither
command installs C++, TeX, fonts, or Lean. See the
[uv lock documentation](https://docs.astral.sh/uv/concepts/projects/sync/) and
[pip hash-checking documentation](https://pip.pypa.io/en/stable/topics/secure-installs/).

### System dependencies

| Operation | Prerequisites |
| --- | --- |
| Manifest verification | Python 3.10–3.13 |
| Finite computation | Linux, Python, `g++` with C++17 |
| English PDF | Locked PDF extra, pdfLaTeX, AMS classes, Latin Modern, the LaTeX packages listed below |
| Japanese PDF | English dependencies, LuaLaTeX, `luatexja-fontspec`, Harano Aji Mincho/Gothic fonts |
| Figure regeneration | pdfLaTeX, PGF/TikZ, `standalone`, Latin Modern, Poppler `pdftocairo` for SVG and `pdftoppm`/`pdfinfo` for previews and dimensions; LuaLaTeX and Japanese fonts for Japanese figures |
| Lean proofs | Elan, Lean 4.29.1, Git, locked Lake dependencies; see [FORMALIZATION.md](supplement/FORMALIZATION.md) |

On Debian 12, the system package names are:

```sh
sudo apt-get update
sudo apt-get install python3 python3-venv g++ git ca-certificates curl elan \
  texlive-latex-base texlive-latex-recommended texlive-latex-extra \
  texlive-fonts-recommended texlive-luatex texlive-lang-japanese \
  texlive-pictures lmodern poppler-utils
```

These LaTeX collections supply `amsart`, `amsmath`, `amssymb`, `fvextra`,
`geometry`, `booktabs`, `array`, `longtable`, `needspace`, `xurl`, `hyperref`,
`graphicx`, `standalone`, and TikZ. Native package names can differ on other
distributions. This unpinned native installation is a convenience; the
container recipe below fixes the system package source to a dated archive.
The Japanese source loads the recent `lltjp-fancyvrb` compatibility patch
only when present; the same source also builds with the older LuaTeX-ja
in the pinned TeX Live 2022 container.

### Build the container environment

[Dockerfile](Dockerfile) fixes the Debian base by digest and the Debian and
Debian security repositories to the `20260901T000000Z` snapshot. The default
`complete` target includes the finite and PDF tools. The `compute` target
omits TeX, fonts, Poppler and the PDF extra. Neither target copies the paper,
precomputed graph data, credentials or host caches into the image.

```sh
docker build -t floor-paper .
# Optional smaller environment:
docker build --target compute -t floor-paper-compute .
mkdir -p ../floor-paper-results
docker run --rm --network none \
  --mount type=bind,src="$PWD",dst=/paper,readonly \
  --mount type=bind,src="$(realpath ../floor-paper-results)",dst=/results \
  floor-paper python3 -B reproduce.py verify
docker run --rm --network none \
  --mount type=bind,src="$PWD",dst=/paper,readonly \
  --mount type=bind,src="$(realpath ../floor-paper-results)",dst=/results \
  floor-paper python3 -B reproduce.py check --output /results/check
docker run --rm --network none \
  --mount type=bind,src="$PWD",dst=/paper,readonly \
  --mount type=bind,src="$(realpath ../floor-paper-results)",dst=/results \
  floor-paper python3 -B build_pdf.py --language ja --output /results/paper-ja.pdf
```

Use fresh result names. Replace `check` with `recompute` for all finite
computations; use `--language en` for English. The commands write results
outside the read-only source mount. They use the image's default root user,
so result files may be root-owned on a native Linux host. TeX font caches are written inside the temporary container, under its own
root home; they are not written into the read-only source mount. The build
needs network access; finite computation, verification and PDF building do not.
Allow at least 8 GiB of memory for full finite reproduction. TeX/font
installation and Lean dependency caches can use several GiB of disk space.
Base-digest pinning follows [Docker's guidance](https://docs.docker.com/build/building/best-practices/#pin-base-image-versions);
the dated packages are served by [Debian Snapshot](https://snapshot.debian.org/).

### Lean is a separate check

The exact toolchain is in [lean-toolchain](supplement/lean/lean-toolchain),
and every Lake dependency commit is in
[lake-manifest.json](supplement/lean/lake-manifest.json). In particular,
Mathlib is fixed to `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
The container installs Elan but does not download the Lean toolchain or
Mathlib cache at image-build time. For Lean, use a separate writable copy,
allow network access for setup, and follow the sequential procedure in
[FORMALIZATION.md](supplement/FORMALIZATION.md). A finite-computation PASS
or a successful environment diagnostic does not compile these proofs.

### Diagnose and record the environment

```sh
python3 -B check_environment.py --scope compute --output /tmp/floor-compute-env.json
python3 -B check_environment.py --scope pdf --output /tmp/floor-pdf-env.json
python3 -B check_environment.py --scope figures --output /tmp/floor-figure-env.json
# After Elan has obtained the specified toolchain:
python3 -B check_environment.py --scope lean --output /tmp/floor-lean-env.json
```

The diagnostic compiles a small C++17 integer program, records tool versions,
and checks the TeX packages and fonts for the selected scope. `--scope all`
combines the checks. Exit code 0 means the prerequisites were found, not that
the paper was proved. The diagnostic may request a toolchain download through
Elan when checking Lean. [environment-lock.json](environment-lock.json)
records the pinned inputs and observed publication environment.

Integer outputs have fixed reference digests independent of the TeX setup.
PDF bytes can differ across TeX, font and Poppler versions even with the fixed
source date. The older TeX container also has different text-extraction
mappings for some mathematical glyphs; rendered output was checked separately. Installing the Python lock alone does not reproduce the complete
publication toolchain; the container is a separate, reproducible build
recipe. Always inspect the actual `.build.json` result of a PDF rebuild.

---

<a id="japanese"></a>

## 日本語

[再現コマンド](REPRODUCE.md#japanese)

有限計算に必要な Python ライブラリは標準ライブラリだけで、ほかに C++17 の
コンパイル環境を使います。PDF ビルダーには追加で `pypdf` が必要です。
Python 依存は [pyproject.toml](pyproject.toml) に宣言し、取得アーカイブのハッシュも含めて
[uv.lock](uv.lock) と [requirements-pdf.txt](requirements-pdf.txt) に固定しています。
実行ハーネスが `/proc`、プロセス群、資源上限制御を使うため、Linux が必要です。
Windows では WSL2 または以下の Linux コンテナを利用できます。

### Python 依存を導入する

Python 3.10–3.13 を使います。公開ソース集合と混同しないよう、仮想環境は
チェックアウトの外に作成してください。既存の Python を使い、PDF 用の固定依存だけを
導入する例は次のとおりです。

```sh
python3 -m venv ../floor-paper-venv
. ../floor-paper-venv/bin/activate
python3 -m pip install --require-hashes -r requirements-pdf.txt
```

[uv](https://docs.astral.sh/uv/) を使う場合は、次の手順でも導入できます。

```sh
UV_PROJECT_ENVIRONMENT=../floor-paper-venv uv sync --locked --extra pdf --python python3
. ../floor-paper-venv/bin/activate
```

`--locked` は lock とプロジェクトの整合性を検査し、lock を更新しません。
pip の手順ではアーカイブのハッシュ照合を必須にします。どちらも C++、TeX、フォント、
Lean は導入しません。詳細は
[uv の lock 文書](https://docs.astral.sh/uv/concepts/projects/sync/) と
[pip のハッシュ検査文書](https://pip.pypa.io/en/stable/topics/secure-installs/) を参照してください。

### システムの依存ソフトウェア

| 操作 | 必要なもの |
| --- | --- |
| マニフェストの照合 | Python 3.10–3.13 |
| 有限計算 | Linux、Python、C++17 対応の `g++` |
| 英語 PDF | 固定した PDF 用 Python 依存、pdfLaTeX、AMS 文書クラス、Latin Modern、下記 LaTeX パッケージ |
| 日本語 PDF | 英語版の依存、LuaLaTeX、`luatexja-fontspec`、原ノ味明朝・角ゴシック |
| 図の再生成 | pdfLaTeX、PGF/TikZ、`standalone`、Latin Modern、SVG 用の Poppler `pdftocairo`、プレビュー・寸法確認用の `pdftoppm`・`pdfinfo`。日本語図には LuaLaTeX と日本語フォント |
| Lean 形式証明 | Elan、Lean 4.29.1、Git、固定 Lake 依存。[FORMALIZATION.md](supplement/FORMALIZATION.md#japanese) を参照 |

Debian 12 でのシステムパッケージ名は以下のとおりです。

```sh
sudo apt-get update
sudo apt-get install python3 python3-venv g++ git ca-certificates curl elan \
  texlive-latex-base texlive-latex-recommended texlive-latex-extra \
  texlive-fonts-recommended texlive-luatex texlive-lang-japanese \
  texlive-pictures lmodern poppler-utils
```

これらの LaTeX コレクションには `amsart`、`amsmath`、`amssymb`、`fvextra`、
`geometry`、`booktabs`、`array`、`longtable`、`needspace`、`xurl`、`hyperref`、
`graphicx`、`standalone`、TikZ が含まれます。ほかのディストリビューションでは
パッケージ名が異なる場合があります。この通常の導入例では OS パッケージの版を
固定しません。以下のコンテナでは日付指定のアーカイブに固定します。
日本語ソースは、新しい `lltjp-fancyvrb` 互換パッチが存在する場合だけ読み込みます。
同じソースを、固定コンテナの TeX Live 2022 に含まれる旧 LuaTeX-ja でも生成できます。

### コンテナ環境を構築する

[Dockerfile](Dockerfile) は Debian ベースをダイジェストで固定し、Debian と
Debian security の取得元を `20260901T000000Z` のスナップショットに固定します。
既定の `complete` ターゲットは有限計算と PDF の環境を含みます。
`compute` ターゲットは TeX、フォント、Poppler、PDF 用 Python 依存を省きます。
どちらも論文、計算済みグラフ、認証情報、ホストのキャッシュをイメージへコピーしません。

```sh
docker build -t floor-paper .
# 小さい計算専用環境が必要な場合:
docker build --target compute -t floor-paper-compute .
mkdir -p ../floor-paper-results
docker run --rm --network none \
  --mount type=bind,src="$PWD",dst=/paper,readonly \
  --mount type=bind,src="$(realpath ../floor-paper-results)",dst=/results \
  floor-paper python3 -B reproduce.py verify
docker run --rm --network none \
  --mount type=bind,src="$PWD",dst=/paper,readonly \
  --mount type=bind,src="$(realpath ../floor-paper-results)",dst=/results \
  floor-paper python3 -B reproduce.py check --output /results/check
docker run --rm --network none \
  --mount type=bind,src="$PWD",dst=/paper,readonly \
  --mount type=bind,src="$(realpath ../floor-paper-results)",dst=/results \
  floor-paper python3 -B build_pdf.py --language ja --output /results/paper-ja.pdf
```

出力先には未作成の名前を使います。有限計算全体には `check` を `recompute` に、
英語 PDF には `--language ja` を `--language en` に変えます。読み取り専用の
ソースマウントの外へ出力します。イメージ既定の root ユーザーで実行するため、
Linux ホストでは出力の所有者が root になる場合があります。TeX のフォントキャッシュは
一時コンテナ内の root のホームへ作られ、読み取り専用のソースには書き込みません。
イメージ構築時には
ネットワーク接続が必要ですが、有限計算、ファイル照合、PDF 生成時には不要です。
全有限計算には最低 8 GiB のメモリを確保してください。TeX・フォントの導入と
Lean 依存キャッシュには数 GiB のディスク容量が必要になる場合があります。
ベースの固定方法は [Docker の説明](https://docs.docker.com/build/building/best-practices/#pin-base-image-versions)、
日付指定のパッケージは [Debian Snapshot](https://snapshot.debian.org/) によります。

### Lean は別途検査する

ツールチェーンは [lean-toolchain](supplement/lean/lean-toolchain)、すべての Lake 依存の
コミットは [lake-manifest.json](supplement/lean/lake-manifest.json) に固定しています。
Mathlib は `5e932f97dd25535344f80f9dd8da3aab83df0fe6` です。
コンテナには Elan を導入しますが、イメージ構築時には Lean ツールチェーンや Mathlib
キャッシュを取得しません。Lean の検査には別の書込み可能なコピーを用意し、準備時の
ネットワーク接続を許可したうえで、
[FORMALIZATION.md](supplement/FORMALIZATION.md#japanese) の逐次手順を実行してください。
有限計算の PASS や環境診断の成功では、形式証明はコンパイルされません。

### 環境を診断し記録する

```sh
python3 -B check_environment.py --scope compute --output /tmp/floor-compute-env.json
python3 -B check_environment.py --scope pdf --output /tmp/floor-pdf-env.json
python3 -B check_environment.py --scope figures --output /tmp/floor-figure-env.json
# Elan で指定ツールチェーンを取得した後:
python3 -B check_environment.py --scope lean --output /tmp/floor-lean-env.json
```

診断は小さな C++17 の整数演算プログラムをコンパイルし、実行ツールの版と、選んだ
範囲の TeX パッケージ・フォントを確認します。`--scope all` は全項目を調べます。
終了コード 0 は前提の検出に成功したことを表し、論文の証明の検査完了ではありません。
Lean の診断では Elan によるツールチェーン取得が起こる場合があります。
[environment-lock.json](environment-lock.json) に固定した入力と公開物生成時の
実環境を記録しています。

整数演算の出力には、TeX 環境とは独立した固定基準ダイジェストがあります。
PDF のバイト列はソース日時を固定しても、TeX・フォント・Poppler の版によって
変わる場合があります。旧 TeX のコンテナでは一部の数式字形のテキスト抽出結果も
異なるため、描画した表示は別に確認しました。Python の lock だけでは組版環境全体を
再現できません。
コンテナは、それとは別の再構築可能な環境定義です。PDF 再生成時には、実際の
`.build.json` に記録された結果を確認してください。
