# Paper illustrations / 論文の説明図

<a id="english"></a>

## English

The nine figures explain existing definitions, operations, and finite results in the paper. [manifest.json](manifest.json) records each figure's role, insertion point, introductory sentence, and English and Japanese captions. [data.json](data.json) contains the small exact examples and the counts from Tables 5–7. The five-block condensation diagram is a conceptual example; its separate numerical box reports the computed certificate.

From this directory, regenerate all English SVGs and temporary rendering files into a new external directory:

```sh
python3 -B build.py --output /tmp/floor-paper-figures-en
python3 -B build.py --language ja --output /tmp/floor-paper-figures-ja
```

Use a fresh output directory for each run. The script checks the integer and rational examples, regenerates the two data-driven TeX fragments in memory, and checks them against the supplied sources. It then builds and renders every figure. Each child process is limited to 120 seconds and 2 GiB. The output includes a build report, PDF, SVG, preview PNG, and logs; only the final English SVGs are publication assets. Different TeX or Poppler versions may change rendering bytes.

Python uses only its standard library. Rendering requires `pdflatex`, `lualatex` for Japanese, `pdfinfo`, `pdftocairo`, and `pdftoppm`; TeX packages include `standalone`, `amsmath`, `amssymb`, `lmodern`, and TikZ with `arrows.meta`, `positioning`, `calc`, `patterns`, and `shapes.geometric`. Japanese labels use `luatexja-fontspec` and the Harano Aji Mincho/Gothic fonts used by the paper.

For TeX integration, load [style.tex](style.tex) in the preamble, then input the individual figure fragment inside a centered figure environment. Defining `\FigureJapanese` selects Japanese labels. Captions are supplied separately in the manifest. The plot uses floating-point logarithms only to place already verified integer counts on the page; the scientific checks use integer or rational arithmetic.

<a id="japanese"></a>

## 日本語

九つの図は、論文にある定義・操作・有限計算結果を説明する。[manifest.json](manifest.json)に、各図の種類、挿入位置、導入文、日英キャプションを記録している。[data.json](data.json)には、厳密な小例と表5–7の件数を収録した。五ブロックの凝縮図は概念例であり、別枠の数値は実計算の証明書の値である。

このディレクトリから次を実行すると、英語SVGと一時的な描画ファイルを外部の新規ディレクトリへ再生成できる。

```sh
python3 -B build.py --output /tmp/floor-paper-figures-en
python3 -B build.py --language ja --output /tmp/floor-paper-figures-ja
```

実行ごとに新規の出力先を使う。スクリプトは整数・有理数の例を検算し、データから作る二つのTeX断片をメモリ上で再生成して、同梱ソースと照合する。その後、全図を組版・描画する。各子プロセスの上限は120秒・2 GiB。出力にはビルド記録、PDF、SVG、確認用PNG、ログが含まれるが、公開資産とするのは英語の最終SVGのみである。TeXやPopplerの版が異なると描画結果のバイト列は変わり得る。

Pythonは標準ライブラリのみを使う。描画には`pdflatex`、日本語用の`lualatex`、`pdfinfo`、`pdftocairo`、`pdftoppm`が必要。TeXパッケージは`standalone`、`amsmath`、`amssymb`、`lmodern`、TikZの`arrows.meta`、`positioning`、`calc`、`patterns`、`shapes.geometric`を使う。日本語ラベルは論文と同じ`luatexja-fontspec`および原ノ味明朝・ゴシックを使う。

TeXへの組込みでは、プリアンブルで[style.tex](style.tex)を読み、中央揃えのfigure環境内で各図の断片を読み込む。`\FigureJapanese`を定義すると日本語ラベルになる。キャプションはmanifestに別途収録している。プロットの浮動小数点対数は、検証済みの整数件数を紙面に配置するためだけに使い、科学的な検算は整数・有理数演算で行う。
