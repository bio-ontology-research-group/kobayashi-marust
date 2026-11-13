# Submitting KM to the Protégé plugin lists

Protégé's **File → Check for plugins** dialog reads two lists in
[protegeproject/autoupdate](https://github.com/protegeproject/autoupdate):

- Protégé 5: `update-info/5.0.0/plugins.repository`, one line per plugin
  pointing at an `update.properties` file that the plugin hosts itself.
- Protégé 6: `update-info/6.0.0/plugins.repository` plus one descriptor file
  per plugin kept in that repository. It lists only plugins released and
  tested with Protégé 6. CI runs `scripts/validate-protege-6-registry.sh`,
  which downloads each jar and checks that `Bundle-SymbolicName` equals `id`
  and `Bundle-Version` equals `version`.

This file holds the two pull requests to open there, and what must happen
first.

## Before opening either pull request

- [ ] Merge this branch, so that `main` holds
      `protege/update-info/protege-5/update.properties`,
      `protege/update-info/protege-5/readme.html` and the README.
      The Protégé 5 list and both readme links point at `main`.
- [ ] Run `.github/workflows/protege-plugin.yml` once by hand
      (`workflow_dispatch`) and check that it is green on all five
      platforms: km builds and classifies a small ontology on each runner,
      both jars pass `mvn verify -Dkm.native.require=all`, and both pass the
      installation smoke test in stock Protégé 5.6.9 and 6.0.0-alpha-1.
- [x] Settle the licence statement: BSD-3-Clause, copyright Robert
      Hoehndorf (maintainer decision, 2026-11-13).
- [ ] Release v1.6.3 by pushing the `v1.6.3` tag. `release.yml` creates the
      release; `protege-plugin.yml` attaches
      `kobayashi-marust-protege5-1.6.3.jar`,
      `kobayashi-marust-protege6-1.6.3.jar` and `SHA256SUMS-protege`.
- [ ] Check that both download URLs below return the jars, and that each jar
      reports `Bundle-SymbolicName: org.bioontology.kobayashi-marust` and
      `Bundle-Version: 1.6.3`:

      ```sh
      for line in 5 6; do
        curl -fsSL -o km$line.jar \
          https://github.com/bio-ontology-research-group/kobayashi-marust/releases/download/v1.6.3/kobayashi-marust-protege$line-1.6.3.jar
        unzip -p km$line.jar META-INF/MANIFEST.MF | grep -E '^Bundle-(SymbolicName|Version)'
      done
      ```

- [ ] Install each jar through **Check for plugins** once from a local copy
      of the registry with the new line (point the plugin registry location
      in **Preferences → Plugins** at it), then classify an ontology and use
      **Explain inference**. Do this on macOS and Windows as well as Linux:
      so far only Linux x86_64 has run the bundled executable inside
      Protégé.
- [ ] Fork protegeproject/autoupdate and run
      `./scripts/validate-protege-6-registry.sh` on the fork with the change
      below. It must print `Validated N Protégé 6 plugins.`

## Pull request 1: Protégé 5 list

Change to `update-info/5.0.0/plugins.repository`: append at the end of the
file.

```text

// Kobayashi-MaRust Reasoner
https://raw.githubusercontent.com/bio-ontology-research-group/kobayashi-marust/main/protege/update-info/protege-5/update.properties
```

The file it points at
([`protege/update-info/protege-5/update.properties`](update-info/protege-5/update.properties)):

```properties
id=org.bioontology.kobayashi-marust
version=1.6.3
download=https://github.com/bio-ontology-research-group/kobayashi-marust/releases/download/v1.6.3/kobayashi-marust-protege5-1.6.3.jar
name=Kobayashi-MaRust Reasoner
readme=https://raw.githubusercontent.com/bio-ontology-research-group/kobayashi-marust/main/protege/update-info/protege-5/readme.html
license=https://raw.githubusercontent.com/bio-ontology-research-group/kobayashi-marust/main/LICENSE
author=Robert Hoehndorf
```

Title:

```text
Add the Kobayashi-MaRust reasoner to the Protégé 5 plugin list
```

Body:

```markdown
This adds Kobayashi-MaRust (KM), an OWL 2 DL reasoner written in Rust, to the
Protégé 5 plugin list.

The plugin adds **Kobayashi-MaRust** to the Reasoner menu. It computes the
inferred class hierarchy, equivalent classes, unsatisfiable classes and
consistency, updates incrementally after edits, and explains inferred
named-class subclass relations through Protégé's Explain inference button. It
does not compute property hierarchies or answer individual queries.

The jar bundles the native reasoner for Linux (x86_64, aarch64), macOS (Intel,
Apple silicon) and Windows (x86_64), so users need to install nothing else.

- update.properties: https://raw.githubusercontent.com/bio-ontology-research-group/kobayashi-marust/main/protege/update-info/protege-5/update.properties
- jar: https://github.com/bio-ontology-research-group/kobayashi-marust/releases/download/v1.6.3/kobayashi-marust-protege5-1.6.3.jar
  (`Bundle-SymbolicName: org.bioontology.kobayashi-marust`, `Bundle-Version: 1.6.3`)
- tested with Protégé 5.6.9 on Linux x86_64 (add the other platforms you
  have tested)
- source and README: https://github.com/bio-ontology-research-group/kobayashi-marust/tree/main/protege

We will keep update.properties current with each KM release.
```

## Pull request 2: Protégé 6 list

Changes:

1. New file `update-info/6.0.0/kobayashi-marust.properties`, the content of
   [`protege/update-info/protege-6/kobayashi-marust.properties`](update-info/protege-6/kobayashi-marust.properties):

   ```properties
   id=org.bioontology.kobayashi-marust
   version=1.6.3
   download=https://github.com/bio-ontology-research-group/kobayashi-marust/releases/download/v1.6.3/kobayashi-marust-protege6-1.6.3.jar
   name=Kobayashi-MaRust Reasoner
   readme=https://raw.githubusercontent.com/bio-ontology-research-group/kobayashi-marust/main/protege/update-info/protege-5/readme.html
   license=https://raw.githubusercontent.com/bio-ontology-research-group/kobayashi-marust/main/LICENSE
   author=Robert Hoehndorf
   ```

2. In `update-info/6.0.0/plugins.repository`, append this line after the
   existing entries:

   ```text
   https://raw.githubusercontent.com/protegeproject/autoupdate/master/update-info/6.0.0/kobayashi-marust.properties
   ```

Title:

```text
Add the Kobayashi-MaRust reasoner to the Protégé 6 plugin registry
```

Body:

```markdown
This adds Kobayashi-MaRust (KM) 1.6.3, an OWL 2 DL reasoner written in Rust,
to the Protégé 6 registry.

The Protégé 6 jar is a separate build against Protégé 6.0.0-alpha-1,
OWL API 5.5.1 and OWL Explanation 5.0.1; it is not the Protégé 5 jar.

- descriptor: `update-info/6.0.0/kobayashi-marust.properties`
- jar: https://github.com/bio-ontology-research-group/kobayashi-marust/releases/download/v1.6.3/kobayashi-marust-protege6-1.6.3.jar
  (`Bundle-SymbolicName: org.bioontology.kobayashi-marust`, `Bundle-Version: 1.6.3`)
- `./scripts/validate-protege-6-registry.sh` passes with this change
- tested with Protégé 6.0.0-alpha-1 on Linux x86_64 (add the other
  platforms you have tested): the plugin resolves and starts in the OSGi
  container, classifies, updates incrementally after an edit, and returns
  explanations, using the native reasoner bundled in the jar
- the jar bundles the native reasoner for Linux (x86_64, aarch64), macOS
  (Intel, Apple silicon) and Windows (x86_64)
- source and README: https://github.com/bio-ontology-research-group/kobayashi-marust/tree/main/protege
```

## Later releases

For each KM release `X.Y.Z`:

- Protégé 5: update `version` and `download` in
  `protege/update-info/protege-5/update.properties` on `main` after the
  release jars are attached. No pull request is needed.
- Protégé 6: open a pull request that changes `version` and `download` in
  `update-info/6.0.0/kobayashi-marust.properties`, after running the
  validator.

## Licence

The plugin is released under the BSD 3-Clause licence, copyright Robert
Hoehndorf (maintainer decision, 2026-11-13). The descriptors point
`license=` at the repository `LICENSE`. Third-party components bundled in
the jars keep their own licences.
