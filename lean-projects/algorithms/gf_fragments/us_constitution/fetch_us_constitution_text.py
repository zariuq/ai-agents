#!/usr/bin/env python3
from __future__ import annotations

import datetime as dt
import hashlib
import json
import re
from html.parser import HTMLParser
from pathlib import Path
from urllib.request import Request, urlopen


ARCHIVES_URL = "https://www.archives.gov/founding-docs/constitution-transcript"

ROOT = Path(__file__).resolve().parent
SOURCE_DIR = ROOT / "source"


class TextExtractor(HTMLParser):
    block_tags = {"p", "div", "h1", "h2", "h3", "h4", "li", "br", "tr"}

    def __init__(self) -> None:
        super().__init__()
        self.parts: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag in self.block_tags:
            self.parts.append("\n")

    def handle_endtag(self, tag: str) -> None:
        if tag in self.block_tags - {"br"}:
            self.parts.append("\n")

    def handle_data(self, data: str) -> None:
        self.parts.append(data)

    def lines(self) -> list[str]:
        text = "".join(self.parts).replace("\xa0", " ")
        lines = [re.sub(r"\s+", " ", line).strip() for line in text.splitlines()]
        return [line for line in lines if line]


def fetch_lines() -> list[str]:
    request = Request(ARCHIVES_URL, headers={"User-Agent": "zarwiki-gf-us-constitution-fetch/1.0"})
    html = urlopen(request, timeout=30).read().decode("utf-8", "replace")
    parser = TextExtractor()
    parser.feed(html)
    return parser.lines()


def index_of(lines: list[str], predicate, label: str) -> int:
    for i, line in enumerate(lines):
        if predicate(line):
            return i
    raise RuntimeError(f"Could not find {label} in National Archives transcript")


def extract_transcript(lines: list[str]) -> tuple[list[str], list[str]]:
    start = index_of(
        lines,
        lambda line: line.startswith("We the People of the United States"),
        "Preamble start",
    )
    full_stop = index_of(
        lines[start:],
        lambda line: line.startswith("For biographies of the non-signing delegates"),
        "post-transcript page footer",
    )
    full_lines = lines[start : start + full_stop]

    main_stop = index_of(
        full_lines,
        lambda line: line.startswith('The Word, "the," being interlined'),
        "attestation/interlineation boundary",
    )
    main_lines = full_lines[:main_stop]
    return main_lines, full_lines


def write_text(path: Path, lines: list[str]) -> None:
    path.write_text("\n\n".join(lines) + "\n", encoding="utf-8")


def sha256_text(lines: list[str]) -> str:
    return hashlib.sha256(("\n\n".join(lines) + "\n").encode("utf-8")).hexdigest()


def main() -> int:
    SOURCE_DIR.mkdir(parents=True, exist_ok=True)
    page_lines = fetch_lines()
    main_lines, full_lines = extract_transcript(page_lines)

    main_path = SOURCE_DIR / "us_constitution_1787_archives_main_text.txt"
    full_path = SOURCE_DIR / "us_constitution_1787_archives_full_transcript.txt"
    paragraphs_path = SOURCE_DIR / "us_constitution_1787_archives_paragraphs.json"
    metadata_path = SOURCE_DIR / "us_constitution_1787_archives_metadata.json"

    write_text(main_path, main_lines)
    write_text(full_path, full_lines)

    paragraphs = [
        {"index": i + 1, "text": line}
        for i, line in enumerate(full_lines)
    ]
    paragraphs_path.write_text(json.dumps(paragraphs, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    metadata = {
        "source": "National Archives, Constitution of the United States: A Transcription",
        "sourceUrl": ARCHIVES_URL,
        "fetchedAt": dt.datetime.now(dt.timezone.utc).isoformat(),
        "description": (
            "Official transcript of the Constitution as inscribed on parchment by Jacob Shallus. "
            "The main_text file contains the Preamble and Articles I-VII. "
            "The full_transcript file also includes interlineation notes, attestation, and signers."
        ),
        "mainTextFile": str(main_path.relative_to(ROOT)),
        "fullTranscriptFile": str(full_path.relative_to(ROOT)),
        "paragraphsFile": str(paragraphs_path.relative_to(ROOT)),
        "mainTextParagraphCount": len(main_lines),
        "fullTranscriptParagraphCount": len(full_lines),
        "mainTextSha256": sha256_text(main_lines),
        "fullTranscriptSha256": sha256_text(full_lines),
    }
    metadata_path.write_text(json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    print(f"wrote {main_path}")
    print(f"wrote {full_path}")
    print(f"wrote {paragraphs_path}")
    print(f"wrote {metadata_path}")
    print(f"main paragraphs: {len(main_lines)}")
    print(f"full paragraphs: {len(full_lines)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
