#!/usr/bin/env bash
# Expand Lean sources into arxiv_with_code.md (full appendix for PDF build).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/generate_arxiv_with_code.py
