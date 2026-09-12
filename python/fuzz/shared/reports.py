"""Execution provenance for checkout and installed-package fuzz reports."""

import hashlib
from pathlib import Path

import ephemeris


def _sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def provenance(sources, commands):
    """Hash available sources and the executables actually selected by clients.

    An installed wheel has Python sources but usually no Lean/Rust checkout.
    List unavailable sources explicitly; source hashes alone do not establish
    that an externally selected binary was built from those sources.
    """
    package_root = Path(ephemeris.__file__).resolve().parent.parent
    checkout = package_root.parent
    in_checkout = (checkout / "lakefile.toml").is_file()
    hashes = {}
    unavailable = []
    for source in sources:
        if source.startswith("python/"):
            path = package_root / source.removeprefix("python/")
        else:
            path = checkout / source if in_checkout else None
        if path is not None and path.is_file():
            hashes[source] = _sha256(path)
        else:
            unavailable.append(source)
    return {
        "source_sha256": hashes,
        "unavailable_sources": unavailable,
        "oracle_commands": {
            name: {"argv": command, "executable_sha256": _sha256(Path(command[0]))}
            for name, command in commands.items()
        },
    }
