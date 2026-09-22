"""Relocate supplement links while preserving the scientific PDF page streams."""
from __future__ import annotations

import hashlib
from pathlib import Path
from urllib.parse import urlsplit

from pypdf import PdfReader, PdfWriter
from pypdf.generic import ArrayObject, NameObject, TextStringObject


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical_uri(uri):
    if urlsplit(uri).scheme or uri.startswith("#"):
        return uri
    path = uri
    while path.startswith("../"):
        path = path[3:]
    if path.startswith(("supplement/", "checks/")) or path in {"README.md", "README.ja.md", "REPRODUCE.md", "REPRODUCE.ja.md", "MANIFEST.json", "SHA256SUMS"}:
        return path
    if path.startswith(("computations/", "lean/", "evidence/")):
        return "supplement/" + path
    raise ValueError(f"Unexpected relative PDF URI: {uri}")


def outline(reader, entries=None):
    result = []
    for entry in reader.outline if entries is None else entries:
        if isinstance(entry, list):
            result.append(outline(reader, entry))
        else:
            result.append({"title": entry.title,
                           "page": reader.get_destination_page_number(entry),
                           "destination": [str(x) for x in entry.dest_array[1:]],
                           "style": str(entry.get("/F", "")),
                           "color": str(entry.get("/C", ""))})
    return result


def stream_hashes(page):
    contents = page.get("/Contents")
    if contents is None:
        return []
    contents = contents.get_object()
    streams = contents if isinstance(contents, ArrayObject) else [contents]
    return [{"decoded": sha(stream.get_object().get_data()),
             "encoded": sha(stream.get_object()._data)} for stream in streams]


def annotations(reader):
    result = []
    for i, page in enumerate(reader.pages):
        for ref in page.get("/Annots", []):
            ann = ref.get_object()
            action = ann.get("/A")
            if action is not None:
                action = action.get_object()
            result.append({"page": i + 1, "subtype": str(ann.get("/Subtype")),
                           "rect": [str(x) for x in ann.get("/Rect", [])],
                           "kind": str(action.get("/S", "")) if action else "",
                           "uri": str(action["/URI"]) if action and "/URI" in action else None,
                           "destination": str(action.get("/D", "")) if action else str(ann.get("/Dest", ""))})
    return result


def relocate(source, target, packet_root):
    source, target, packet_root = map(Path, (source, target, packet_root))
    original = source.read_bytes()
    reader = PdfReader(source)
    writer = PdfWriter(clone_from=reader)
    changes = []
    for i, page in enumerate(writer.pages):
        for ref in page.get("/Annots", []):
            annotation = ref.get_object()
            action = annotation.get("/A")
            if action is None:
                continue
            action = action.get_object()
            if "/URI" not in action:
                continue
            before = str(action["/URI"])
            after = canonical_uri(before)
            if not urlsplit(after).scheme and not after.startswith("#"):
                destination = packet_root / urlsplit(after).path
                if not destination.is_file() or not destination.resolve().is_relative_to(packet_root.resolve()):
                    raise ValueError(f"Missing or escaping supplement link: {after}")
            if after != before:
                action[NameObject("/URI")] = TextStringObject(after)
                changes.append({"page": i + 1, "before": before, "after": after})
    with target.open("xb") as out:
        writer.write(out)
    copied = PdfReader(target)
    if len(reader.pages) != len(copied.pages):
        raise ValueError("PDF page count changed")
    page_records = []
    for i, (a, b) in enumerate(zip(reader.pages, copied.pages)):
        if stream_hashes(a) != stream_hashes(b):
            raise ValueError(f"Content stream changed on page {i+1}")
        if a.extract_text() != b.extract_text():
            raise ValueError(f"Extracted text changed on page {i+1}")
        for box in ("mediabox", "cropbox", "trimbox", "bleedbox", "artbox"):
            if list(getattr(a, box)) != list(getattr(b, box)):
                raise ValueError(f"Page {i+1} {box} changed")
        if a.rotation != b.rotation:
            raise ValueError(f"Page {i+1} rotation changed")
        page_records.append({"page": i + 1, "content_streams": stream_hashes(a)})
    if dict(reader.metadata or {}) != dict(copied.metadata or {}):
        raise ValueError("PDF metadata changed")
    if outline(reader) != outline(copied):
        raise ValueError("PDF outline changed")
    dest_a = {k: (reader.get_destination_page_number(v), str(v.dest_array[1:]))
              for k, v in reader.named_destinations.items()}
    dest_b = {k: (copied.get_destination_page_number(v), str(v.dest_array[1:]))
              for k, v in copied.named_destinations.items()}
    if dest_a != dest_b:
        raise ValueError("PDF named destinations changed")
    expected = annotations(reader)
    for annotation in expected:
        if annotation["uri"] is not None:
            annotation["uri"] = canonical_uri(annotation["uri"])
    if expected != annotations(copied):
        raise ValueError("PDF annotations changed beyond the approved URI relocation")
    if source.read_bytes() != original:
        raise ValueError("Source PDF changed")
    return {"status": "PASS", "source_sha256": sha(original),
            "output_sha256": sha(target.read_bytes()), "pages": len(reader.pages),
            "page_streams": page_records, "changed_links": changes,
            "metadata_preserved": True, "outline_preserved": True,
            "named_destinations_preserved": True, "text_preserved": True,
            "page_boxes_preserved": True, "other_annotations_preserved": True}
