# GitHub Pages assets

Files copied into the GitHub Pages site by `.github/workflows/pages.yml`.

| File | Published as | Purpose |
| --- | --- | --- |
| `favicon.svg`, `favicon.ico`, `apple-touch-icon.png` | `/favicon.svg`, `/favicon.ico`, `/apple-touch-icon.png` | Site icon (a floor bracket ⌊ ⌋ with a value dropping to the integer below it) |
| `og-explainer-ja.png` | `/ja/explainer/og.png` | Open Graph / Twitter card image (1200×630) of the Japanese explainer |
| `og-explainer-ja.html` | — | Source of `og-explainer-ja.png` (rendered at 1200×630 in a browser with the fonts loaded) |
| `og-one-step-en.png` | `/en/one-step/og.png` | Open Graph / Twitter card image (1200×630) of the English animation of the one-step method; drawn by the animation itself (`window.__anim.og()` in `slides/one-step-animation-en.html`) and reduced to a 128-color palette |
| `og-one-step-ja.png` | `/ja/one-step/og.png` | Open Graph / Twitter card image (1200×630) of the Japanese animation of the one-step method; drawn the same way from `slides/one-step-animation-ja.html` and reduced to a 128-color palette |
| `og-word-label-en.png` | `/en/word-label/og.png` | Open Graph / Twitter card image (1200×630) of the English animation of the word-labelled method; drawn by the animation itself (`window.__anim.og()` in `slides/word-label-animation-en.html`) and reduced to a 128-color palette |
| `og-word-label-ja.png` | `/ja/word-label/og.png` | Open Graph / Twitter card image (1200×630) of the Japanese animation of the word-labelled method; drawn the same way from `slides/word-label-animation-ja.html` and reduced to a 128-color palette |
| `og-frontier-en.png` | `/en/frontier/og.png` | Open Graph / Twitter card image (1200×630) of the English animation of waiting times, limits and open problems; drawn by the animation itself (`window.__anim.og()` in `slides/frontier-animation-en.html`) and reduced to a 128-color palette |
| `og-frontier-ja.png` | `/ja/frontier/og.png` | Open Graph / Twitter card image (1200×630) of the Japanese animation of waiting times, limits and open problems; drawn the same way from `slides/frontier-animation-ja.html` and reduced to a 128-color palette |
| `og-verification-en.png` | `/en/verification/og.png` | Open Graph / Twitter card image (1200×630) of the English animation of verification and Lean; drawn by the animation itself (`window.__anim.og()` in `slides/verification-animation-en.html`) and reduced to a 128-color palette |
| `og-verification-ja.png` | `/ja/verification/og.png` | Open Graph / Twitter card image (1200×630) of the Japanese animation of verification and Lean; drawn the same way from `slides/verification-animation-ja.html` and reduced to a 128-color palette |

`favicon.ico` holds 16, 32 and 48 px PNG renderings of `favicon.svg`; `apple-touch-icon.png` is a 180 px rendering with square corners.
