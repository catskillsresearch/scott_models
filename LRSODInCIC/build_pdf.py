#!/usr/bin/env python3
"""Build LRSODInCIC.tex and LRSODInCIC.pdf from LRSODInCIC.md.

A trimmed-down version of the repo's arxiv pipeline (scripts/build_arxiv_tex.py):
this document has no Lean appendix, no mermaid figures and no inventory tables,
so the whole job is

  1. lift the `# ...` title line and the Abstract/Scope paragraphs out of the
     markdown, so they become \\title and an `abstract` environment;
  2. pandoc the remaining body to LaTeX, demoting headings by one so `##` Parts
     become \\section;
  3. render fenced code with `listings` in the shared `leanbox` style, whose
     `literate` table already maps most Lean glyphs to real LaTeX symbols;
  4. reuse scripts/tex_preamble_arxiv.tex, extended with the glyphs this
     document uses that the arxiv paper does not (⤳, 𝓝, ᵒᵈ, ∖, ≡, …), so the
     shared preamble stays untouched;
  5. compile with latexmk.

Every non-ASCII glyph must be declared: pdfTeX fails loudly on an unknown one,
which is the point — a silently dropped character in a paper about notation
would be worse than a build error.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "LRSODInCIC.md"
LEAN = HERE / "LRSODInCIC.lean"
OUT_TEX = HERE / "LRSODInCIC.tex"
OUT_PDF = HERE / "LRSODInCIC.pdf"
PREAMBLE = HERE.parent / "scripts" / "tex_preamble_arxiv.tex"

# Same front matter as scripts/build_arxiv_tex.py.
AUTHOR = "Lars Warren Ericson"
COMPANY = "Catskills Research Company"
GITHUB_URL = r"https://github.com/catskillsresearch/scott_models/tree/main/LRSODInCIC"
ORCID = "0000-0001-8299-9361"
EMAIL = "lars.ericson@catskillsresearch.com"

# Glyphs used here but absent from the arxiv preamble's `literate` table
# (listings) and `\newunicodechar` declarations (prose).
EXTRA_LITERATE = r"""    {ï}{{\"{i}}}1
    {δ}{{\ensuremath{\delta}}}1
    {ζ}{{\ensuremath{\zeta}}}1
    {η}{{\ensuremath{\eta}}}1
    {ᵈ}{{\textsuperscript{d}}}1
    {ᵒ}{{\textsuperscript{o}}}1
    {∖}{{\ensuremath{\setminus}}}1
    {≡}{{\ensuremath{\equiv}}}1
    {⋯}{{\ensuremath{\cdots}}}1
    {⟺}{{\ensuremath{\Longleftrightarrow}}}2
    {⤳}{{\ensuremath{\rightsquigarrow}}}1
    {𝒫}{{\ensuremath{\mathcal{P}}}}1
    {𝒰}{{\ensuremath{\mathcal{U}}}}1
    {𝓝}{{\ensuremath{\mathcal{N}}}}1
"""

EXTRA_UNICODECHAR = r"""
% --- Glyphs specific to this document ---
\newunicodechar{ï}{\"{i}}
\newunicodechar{δ}{\ensuremath{\delta}}
\newunicodechar{ζ}{\ensuremath{\zeta}}
\newunicodechar{η}{\ensuremath{\eta}}
\newunicodechar{ᵈ}{\textsuperscript{d}}
\newunicodechar{ᵒ}{\textsuperscript{o}}
\newunicodechar{∖}{\ensuremath{\setminus}}
\newunicodechar{≡}{\ensuremath{\equiv}}
\newunicodechar{⋃}{\ensuremath{\bigcup}}
\newunicodechar{⋯}{\ensuremath{\cdots}}
\newunicodechar{⤳}{\ensuremath{\rightsquigarrow}}
\newunicodechar{⦃}{\textbraceleft\textbraceleft}
\newunicodechar{⦄}{\textbraceright\textbraceright}
\newunicodechar{𝒫}{\ensuremath{\mathcal{P}}}
\newunicodechar{𝒰}{\ensuremath{\mathcal{U}}}
\newunicodechar{𝓝}{\ensuremath{\mathcal{N}}}
"""


FENCE_RE = re.compile(r"^```[^\n]*\n(.*?)^```[ \t]*$", re.M | re.S)
PLACEHOLDER = "LRSODCODEBLOCK{}ENDBLOCK"


def extract_fences(md: str) -> tuple[str, list[str]]:
    """Pull fenced code out before pandoc sees it.

    Code goes straight into `lstlisting`, so the leanbox `literate` table renders
    the Lean glyphs and pandoc never gets a chance to escape or highlight them.
    """
    blocks: list[str] = []

    def take(match: re.Match[str]) -> str:
        blocks.append(match.group(1).rstrip("\n"))
        return PLACEHOLDER.format(len(blocks) - 1)

    return FENCE_RE.sub(take, md), blocks


def splice_fences(latex: str, blocks: list[str]) -> str:
    for i, code in enumerate(blocks):
        listing = "\\begin{lstlisting}\n" + code + "\n\\end{lstlisting}"
        token = PLACEHOLDER.format(i)
        if token not in latex:
            raise RuntimeError(f"code placeholder {i} vanished during conversion")
        latex = latex.replace(token, listing)
    return latex


def pandoc(markdown: str, shift: bool) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=preserve",
    ]
    if shift:
        cmd.append("--shift-heading-level-by=-1")
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def split_front_matter(md: str) -> tuple[str, str, str]:
    """Return (title_md, abstract_md, body_md)."""
    lines = md.splitlines()
    title = ""
    front: list[str] = []
    body_start = 0
    for i, line in enumerate(lines):
        if line.startswith("# ") and not title:
            title = line[2:].strip()
            continue
        if line.strip() == "---":
            body_start = i + 1
            break
        front.append(line)
    abstract = "\n".join(front).strip()
    # Inside an `abstract` environment the run-in "Abstract." label is redundant.
    abstract = re.sub(r"^\*\*Abstract\.\*\*\s*", "", abstract)
    body = "\n".join(lines[body_start:]).lstrip("\n")
    return title, abstract, body


def break_texttt_paths(latex: str) -> str:
    """Allow line breaks after `/` in \\texttt paths.

    The shared preamble already does this for `_`; without the same for `/`,
    Mathlib paths like `Topology/Spectral/Prespectral.lean` are single unbreakable
    words and run into the margin.
    """

    def fix(match: re.Match[str]) -> str:
        inner = match.group(1)
        if "/" not in inner:
            return match.group(0)
        return "\\texttt{" + inner.replace("/", "/\\allowbreak{}") + "}"

    return re.sub(r"\\texttt\{([^{}]*)\}", fix, latex)


def tidy(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n", "", latex)
    return break_texttt_paths(latex)


def build_preamble() -> str:
    text = PREAMBLE.read_text(encoding="utf-8")
    if "literate=\n" not in text:
        raise RuntimeError("could not find the `literate=` table in the shared preamble")
    text = text.replace("literate=\n", "literate=\n" + EXTRA_LITERATE, 1)
    # pandoc's LaTeX writer emits \passthrough around verbatim-ish spans; the
    # shared preamble is template-free, so supply the macro ourselves.
    return text + EXTRA_UNICODECHAR + "\n\\providecommand{\\passthrough}[1]{#1}\n"


def build_title_page(title_tex: str, abstract_tex: str) -> str:
    return "\n".join(
        [
            r"\title{\textbf{" + title_tex + "}}",
            "",
            r"\author[1]{\textbf{" + AUTHOR + "}}",
            r"\affil[1]{" + COMPANY + "}",
            r"\affil[1]{\url{" + GITHUB_URL + "}}",
            r"\affil[1]{\texttt{" + EMAIL + "}}",
            "",
            r"\date{\today}",
            "",
            r"\begin{document}",
            r"\maketitle",
            "",
            r"\begin{center}",
            r"  \small",
            r"  \textbf{ORCID:} " + ORCID,
            r"\end{center}",
            "",
            r"\begin{abstract}",
            abstract_tex,
            r"\end{abstract}",
        ]
    )


def build_appendix() -> str:
    """The Lean file verbatim, read at compile time so it cannot drift."""
    n_lines = len(LEAN.read_text(encoding="utf-8").splitlines())
    return "\n".join(
        [
            r"\appendix",
            r"\section{Complete Lean source}",
            "",
            f"\\texttt{{{LEAN.name}}} in full ({n_lines} lines), checked by "
            r"\texttt{lake build} against Lean 4 with no Mathlib dependency. "
            r"The layer structures are those of Part III; the closing sections are the "
            r"Sierpi\'nski witness for D1--D4 and its axiom audit.",
            "",
            r"\lstinputlisting{" + LEAN.name + "}",
        ]
    )


def main() -> int:
    title_md, abstract_md, body_md = split_front_matter(SRC.read_text(encoding="utf-8"))

    title_tex = tidy(pandoc(title_md, shift=False)).strip()
    abstract_tex = tidy(pandoc(abstract_md, shift=False)).strip()

    stripped_body, blocks = extract_fences(body_md)
    body_tex = splice_fences(tidy(pandoc(stripped_body, shift=True)), blocks)

    document = "\n".join(
        [
            build_preamble(),
            build_title_page(title_tex, abstract_tex),
            "",
            r"\tableofcontents",
            r"\newpage",
            "",
            body_tex,
            "",
            build_appendix(),
            "",
            r"\end{document}",
            "",
        ]
    )
    OUT_TEX.write_text(document, encoding="utf-8")
    print(f"wrote {OUT_TEX.name} ({OUT_TEX.stat().st_size:,} bytes)")

    proc = subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", OUT_TEX.name],
        cwd=HERE,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0 or not OUT_PDF.is_file():
        log = OUT_TEX.with_suffix(".log")
        sys.stderr.write(proc.stdout[-2000:])
        if log.is_file():
            sys.stderr.write("\n--- tail of LaTeX log ---\n")
            sys.stderr.write("\n".join(log.read_text(errors="replace").splitlines()[-40:]))
        return 1

    pages = subprocess.run(
        ["pdfinfo", OUT_PDF.name], cwd=HERE, capture_output=True, text=True, check=False
    ).stdout
    n_pages = next((l.split()[1] for l in pages.splitlines() if l.startswith("Pages:")), "?")
    print(f"wrote {OUT_PDF.name} ({OUT_PDF.stat().st_size:,} bytes, {n_pages} pages)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
