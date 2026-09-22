"""Select diagnostic headers, not package descriptions, from TeX logs.

The count is diagnostic starts; continuation lines remain in the retained log.
Engine warning case differs from LaTeX/package warning case. In particular,
infwarerr's 'Providing info/warning/error messages' is package metadata.
"""
import re


DIAGNOSTIC = re.compile(
    r"\b(?:pdfTeX|LuaTeX|XeTeX)\s+(?:warning|error)\b"
    r"|^\s*(?:LaTeX(?:\s+Font)?|Package\s+\S+|Class\s+\S+)\s+Warning\b"
    r"|^\s*(?:Overfull|Underfull)\s+\\[hv]box\b"
    r"|^\s*Missing character:"
    r"|^\s*!\s*(?:Undefined control sequence|LaTeX Error)",
    re.IGNORECASE,
)


def diagnostic_lines(log_text: str) -> list[str]:
    return [line for line in log_text.splitlines() if DIAGNOSTIC.search(line)]
