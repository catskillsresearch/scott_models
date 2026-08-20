#!/usr/bin/env bash
# Regenerate arxiv_with_code.md from arxiv.md (Lean Code + appendix markdown → inlined).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/generate_arxiv_with_code.py
