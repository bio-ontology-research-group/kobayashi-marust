#!/usr/bin/env python3
"""Create the acquisition manifest for a frozen OBO Foundry registry export."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("registry", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--snapshot-date", required=True)
    args = parser.parse_args()

    document = json.loads(args.registry.read_text(encoding="utf-8"))
    ontologies = document.get("ontologies")
    if not isinstance(ontologies, list):
        raise SystemExit("registry does not contain an ontologies array")

    rows = []
    for ontology in ontologies:
        if ontology.get("activity_status") != "active":
            continue
        licence = ontology.get("license") or {}
        licence_url = licence.get("url", "")
        products = ontology.get("products") or []
        owl_products = [
            product for product in products
            if str(product.get("id", "")).lower().endswith((".owl", ".rdf", ".ttl"))
            and product.get("ontology_purl")
        ]
        preferred = ontology.get("ontology_purl")
        if not preferred and owl_products:
            preferred = owl_products[0]["ontology_purl"]
        status = "candidate"
        exclusion = ""
        if not preferred:
            status, exclusion = "excluded", "no_public_owl_product"
        elif not licence_url:
            status, exclusion = "excluded", "no_explicit_licence_url"
        rows.append(
            {
                "id": ontology.get("id", ""),
                "title": ontology.get("title", ""),
                "activity_status": ontology.get("activity_status", ""),
                "source_url": preferred or "",
                "licence_url": licence_url,
                "repository": ontology.get("repository", ""),
                "snapshot_date": args.snapshot_date,
                "registry_sha256": digest(args.registry),
                "acquisition_status": status,
                "exclusion_reason": exclusion,
            }
        )

    rows.sort(key=lambda row: row["id"])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0], delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)

    candidates = sum(row["acquisition_status"] == "candidate" for row in rows)
    print(
        json.dumps(
            {
                "active_entries": len(rows),
                "candidates": candidates,
                "excluded": len(rows) - candidates,
                "registry_sha256": digest(args.registry),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
