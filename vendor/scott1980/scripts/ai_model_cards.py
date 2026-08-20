"""Model-card registry for the AI-assisted development acknowledgements block.

Injected into `arxiv_with_code.md` / `arxiv.tex` by `build_arxiv_tex.py` at:
  <!-- AI_MODEL_TOOL_BULLETS --> … <!-- /AI_MODEL_TOOL_BULLETS -->
  <!-- AI_MODEL_REFERENCES --> … <!-- /AI_MODEL_REFERENCES -->
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    reference: str


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor",
        cite_key="Cur26",
        tool_note=(
            "agent-assisted editing in the Cursor IDE across the whole of this development: "
            "formalizing Scott's 1980 neighborhood-system layer in Lean 4 / mathlib, `lake build` "
            "repair, transcription and upkeep of `sources/PRG19.md`, drafting and maintaining this "
            "narrative (`arxiv.md`), and tracking the per-exercise formalized inventory. Generated "
            "Lean was provisional until it compiled sorry-free under the pinned toolchain."
        ),
        reference=(
            "Anysphere, Inc. *Cursor: AI-native code editor and agent environment*. "
            "<https://cursor.com> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Cursor Composer",
        cite_key="Cmp26",
        tool_note=(
            "unattended multi-hour autorun sessions on Exercise 7.22 (regular-event/automata "
            "combinators over the neighborhood system `Ssys`): scaffolding, dependency-ordered "
            "module wiring, and routine proof obligations where the strategy was already fixed, "
            "under a checklist-driven playbook (`Exercise722-Composer-Playbook.md`) that escalated "
            "the hardest sub-goals to a higher-reasoning model rather than looping on Composer alone."
        ),
        reference=(
            "Anysphere, Inc. *Composer*. Model announcement and documentation, "
            "<https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude (Sonnet family)",
        cite_key="Son26",
        tool_note=(
            "the primary day-to-day formalization and proof-engineering model throughout this "
            "project, used in Cursor at varying reasoning tiers: inventory and narrative "
            "maintenance, module wiring, choice-discipline audits (`#print axioms`), and the "
            "majority of the Lean proof obligations across Lectures I-VIII, including this file's "
            "own housekeeping (Exercises 8.25-8.27, the `arxiv.md` \"Lean Code\" appendix repair, "
            "and this LaTeX/PDF pipeline)."
        ),
        reference=(
            "Anthropic. *Claude Sonnet*. System cards and model documentation, "
            "<https://www.anthropic.com/claude>; as integrated in Cursor, "
            "<https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude Opus",
        cite_key="Ant26",
        tool_note=(
            "selective escalation for the heaviest proof obligations flagged in the Composer "
            "playbook as needing higher reasoning depth than routine autorun work (e.g. Exercise "
            "7.22's full language-equivalence decider). Every emitted proof term was checked by the "
            "Lean kernel regardless of which model produced it."
        ),
        reference=(
            "Anthropic. *Claude Opus*. System cards and model documentation, "
            "<https://www.anthropic.com/claude>; as integrated in Cursor, "
            "<https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
)

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** **[{card.cite_key}]** — {card.tool_note}" for card in MODEL_CARDS
    )


def render_model_references() -> str:
    return "\n".join(f"- **[{card.cite_key}]** {card.reference}" for card in MODEL_CARDS)


def inject_model_cards(text: str) -> str:
    """Expand acknowledgement markers; pass through unchanged if markers absent."""
    tool_block = f"{TOOL_BULLETS_BEGIN}\n{render_tool_bullets()}\n{TOOL_BULLETS_END}"
    ref_block = f"{REFERENCES_BEGIN}\n{render_model_references()}\n{REFERENCES_END}"

    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} in narrative; add markers to arxiv.md Acknowledgments"
        )
    if REFERENCES_BEGIN not in text:
        raise RuntimeError(
            f"missing {REFERENCES_BEGIN} in narrative; add markers to arxiv.md References"
        )

    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, render_model_references())
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    # Preserve one leading newline after begin marker when present.
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
