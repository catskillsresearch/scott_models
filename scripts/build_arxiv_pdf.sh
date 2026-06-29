#!/usr/bin/env bash
# Regenerate arxiv_with_code.md, build the .tex, and compile a PDF with LuaLaTeX.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> Regenerating arxiv_with_code.md"
bash scripts/generate_arxiv_with_code.sh

echo "==> Building arxiv_with_code.tex + lean-listings/"
python3 scripts/build_arxiv_pdf.py

echo "==> Compiling PDF (latexmk -> pdfLaTeX, see .latexmkrc)"
# Clean stale aux/out so an engine switch can never leave an unparseable bookmark file.
latexmk -C arxiv_with_code.tex >/dev/null 2>&1 || true
rm -f arxiv_with_code.aux arxiv_with_code.out arxiv_with_code.toc
latexmk -interaction=nonstopmode -halt-on-error arxiv_with_code.tex >/dev/null 2>&1 || {
  echo "latexmk reported errors; tail of log:" >&2
  tail -n 40 arxiv_with_code.log >&2 || true
  exit 1
}
echo "wrote arxiv_with_code.pdf ($(du -h arxiv_with_code.pdf | cut -f1))"
