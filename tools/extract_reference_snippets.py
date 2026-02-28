#!/usr/bin/env python3
"""
Extract selected page snippets from local reference PDFs.

Requires PyMuPDF (`fitz`), which is available in this workspace.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

import fitz  # type: ignore


DEFAULT_TARGETS: dict[str, list[int]] = {
    "references/EGNO_TensorCategories_Full.pdf": [90, 91, 92, 93],
    "references/EGNO_TensorCategories.pdf": [70, 71, 72],
    "references/DGNO_BraidedFusionI.pdf": [9, 10, 11],
}


def clean_text(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def extract_pages(pdf_path: Path, pages: list[int]) -> list[tuple[int, str]]:
    doc = fitz.open(pdf_path)
    out: list[tuple[int, str]] = []
    for p in pages:
        if 1 <= p <= len(doc):
            txt = doc.load_page(p - 1).get_text("text")
            out.append((p, clean_text(txt)))
    return out


def build_markdown(targets: dict[str, list[int]]) -> str:
    lines: list[str] = []
    lines.append("# Reference Snippets")
    lines.append("")
    for pdf, pages in targets.items():
        pdf_path = Path(pdf)
        lines.append(f"## {pdf}")
        if not pdf_path.exists():
            lines.append(f"- Missing file: `{pdf}`")
            lines.append("")
            continue
        for page, text in extract_pages(pdf_path, pages):
            lines.append(f"### Page {page}")
            lines.append("")
            lines.append(text)
            lines.append("")
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Extract selected PDF pages to Markdown.")
    parser.add_argument(
        "--out",
        default="StringAlgebra/MTC/ReferenceSnippets.md",
        help="Output markdown path",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(build_markdown(DEFAULT_TARGETS), encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
