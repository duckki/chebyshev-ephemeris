"""Check local inline Markdown links and heading anchors in the public guides.

External URLs are skipped so this check runs offline. The guides use inline
links and ATX headings; fenced examples are excluded from both checks.
"""

import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit


def prose(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    return re.sub(
        r"^(`{3,}|~{3,})[^\n]*\n.*?^\1[ \t]*$",
        lambda match: "\n" * match[0].count("\n"),
        text,
        flags=re.MULTILINE | re.DOTALL,
    )


def anchors(text: str) -> set[str]:
    used = set()
    for heading in re.findall(r"^#{1,6}\s+(.+?)\s*#*$", text, re.MULTILINE):
        # GitHub retains words/spaces/hyphens and suffixes duplicate headings.
        slug = re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
        anchor = slug
        suffix = 0
        while anchor in used:
            suffix += 1
            anchor = f"{slug}-{suffix}"
        used.add(anchor)
    return used


def check(paths: list[Path]) -> list[str]:
    errors = []
    headings = {}
    for path in paths:
        text = prose(path)
        for match in re.finditer(
            r"\[[^\]\n]*\]\((<[^>]+>|[^\s)]+)(?:\s+[^)]*)?\)", text
        ):
            url = urlsplit(match[1].strip("<>"))
            if url.scheme or url.netloc:
                continue
            target = (
                (path.parent / unquote(url.path)).resolve()
                if url.path
                else path.resolve()
            )
            line = text.count("\n", 0, match.start()) + 1
            if not target.exists():
                errors.append(f"{path}:{line}: missing target {match[1]}")
            elif url.fragment and target.suffix == ".md":
                if target not in headings:
                    headings[target] = anchors(prose(target))
                if unquote(url.fragment) not in headings[target]:
                    errors.append(f"{path}:{line}: missing heading {match[1]}")
    return errors


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    paths = [root / "README.md", *sorted((root / "docs").rglob("*.md"))]
    errors = check(paths)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Local documentation links and headings passed in {len(paths)} files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
