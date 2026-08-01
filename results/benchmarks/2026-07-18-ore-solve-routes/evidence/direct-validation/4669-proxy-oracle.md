# Independent full-taxonomy oracle for ORE 4669

The original ontology has 36,495 private classes of the exact form

```text
N_F ≡ ¬∃R.F
```

Full Konclude classification of the original ontology timed out after 1,800
seconds at 51.5 GB. ELK's 402,776-pair result is only the positive base
taxonomy: it reports no negative-to-negative pairs, although complement
contravariance forces them.

This directory contains an independent projected-ontology oracle:

- `ProxyProjection4669.java` parses the source with OWLAPI, fails closed unless
  the private-mirror projection theorem applies, removes each private `N_F`,
  and adds a fresh `P_F ≡ ∃R.F`. It emits a projected ontology, an exact
  full-IRI `N_F`/`P_F` mapping, and a hashed structural certificate.
- `ElkCandidatePairs4669.java` names every anonymous operand and conclusion of
  all 7,515 conjunction GCIs. Its conservative extension lets an independent
  classifier test whether any proxy reaches an operand that can trigger a
  joint base/proxy consequence.
- `validate_4669_proxy_oracle.py` closes the externally classified projection,
  reverses every `P_F ⊑ P_G` into `N_G ⊑ N_F`, checks the cross-region proof,
  handles named aliases of top and bottom, reconstructs the complete original
  public taxonomy, and can compare it exactly with a KM JSON result.
- `ibex_4669_zero_cross_oracle.sbatch` regenerates every input, classifies the
  positive projection and augmented conservative extension with Konclude,
  classifies the projection with ELK as corroboration, writes the standalone
  gzip TSV oracle, and hashes every output.

The checker requires equality of the complete pair relation, UNSAT set,
consistency verdict, and source declaration universe. It reports counts for all
four regions: base→base, base→negative, negative→base, and
negative→negative.

## Why the reconstruction is complete

Removing the private definitions is conservative over the base signature.
Adding fresh `P_F` definitions is also conservative. Therefore an exact
classification of the projection gives the exact base→base and proxy→proxy
relations. Classical complement duality gives

```text
P_F ⊑ P_G  iff  ¬P_G ⊑ ¬P_F  iff  N_G ⊑ N_F.
```

The four public-taxonomy regions come from separate exact arguments:

- base→base is the externally classified projection restricted to base names;
- negative→negative is the reverse proxy hierarchy by complement duality;
- base→negative is empty under the independently checked zero-cross
  certificate, since `A ⊑ N_F` iff `A ⊓ P_F` is unsatisfiable;
- negative→base is absent for satisfiable non-top base targets by the isolated
  fresh-element argument below.

The cross-region check cannot rely on role separation alone. The source uses
the inverse role `BFO_0000050` (`part_of`) in positive definitions, while the
mirrors use `BFO_0000051` (`has_part`). The certificate instead checks every
place where a joint base/proxy consequence can first arise. It names all 6,735
anonymous conjunction operands and conclusions, then asks Konclude to classify
the conservative extension. Konclude reports zero proxy-to-definer edges and
zero proxies below any of the six named disjoint roots. Consequently no
base/proxy pair can first satisfy a conjunction GCI that reaches a disjoint
root, so all base→negative pairs are absent.

ELK corroborates most of the positive taxonomy but omits 54 inverse-role
consequences that Konclude derives. The checker records this difference and
uses Konclude as the authority. The augmented Konclude result independently
settles the premise for which ELK's omissions could matter.

HermiT independently adjudicates all 54 Konclude-only pairs in IBEX job
`49738974`. It reports every subsumption entailed and every corresponding
`sub ⊓ ¬super` counterexample unsatisfiable. The batch takes 26.07 seconds and
2,691,264 KiB peak RSS. The retained receipt is
`4669-hermit-konclude-only-report.json`; the tracked Java driver and extraction
script regenerate the exact 54-pair query set without embedding expected IRIs.

The structural certificate establishes the premises used by the projection
and isolated-element arguments:

- every `N_F` occurs in exactly one logical axiom, its definition;
- after removing those definitions, the TBox is positive EL plus named
  disjointness, with no top GCI or bottom constructor;
- there is no top GCI, bottom constructor, reflexive role, or universal role;
- there are no ABoxes, nominals, rules, or datatypes.

An isolated fresh element has no role edges and no base named-class
membership. It therefore belongs to every `¬P_F` while remaining outside each
non-top base class `A`, refuting `¬P_F ⊑ A`. The certificate's exclusions make
that model extension safe. The only exceptions are semantic top and bottom.
The checker derives those from the projected taxonomy:

- `P_F ≡ ⊥` means `N_F ≡ ⊤`, so every satisfiable public class is below `N_F`;
- `P_F ≡ ⊤` means `N_F ≡ ⊥`, so `N_F` enters the UNSAT set;
- a base named class equivalent to top is treated analogously.

The source also contains a mirror whose filler is the real `owl:Thing`.
Ordinary public taxonomies suppress every `F ⊑ owl:Thing` edge, so reversing
only the base taxonomy would miss the corresponding `N_Thing ⊑ N_F` block.
The oracle instead classifies the named proxy `P_Thing` and explicitly checks
that every `P_F ⊑ P_Thing` edge is reversed.

## Certified result

IBEX job `49734720` completed the end-to-end reconstruction in
`/ibex/scratch/hohndor/km/routing_20260715/4669-zero-cross-certified-v2-20260801`.
It produced:

- 846,306 exact public named-class subsumptions;
- zero unsatisfiable public classes;
- 402,776 base→base pairs;
- zero base→negative and negative→base pairs;
- 443,530 negative→negative pairs;
- taxonomy digest
  `d02decbafe66d8a9f1afaf7385785b6937fe46c1f288a33113c83c2bbe805b96`.

The retained receipt is `4669-zero-cross-certified-report.json`; the remote
artifact hashes are in `4669-zero-cross-output-manifest.sha256`.

## IBEX use

Copy the helper files together and submit the self-checking oracle run with a
new persistent output directory:

```bash
sbatch --export=ALL,RUN_ROOT=/ibex/scratch/hohndor/km/routing_20260715/4669-oracle-new,ORACLE_SOURCE_DIR=$PWD \
  ibex_4669_zero_cross_oracle.sbatch
```

Pass `--candidate-km` to `validate_4669_proxy_oracle.py` to check an existing
KM JSON classification against the reconstructed oracle. A successful check
ends with `"status": "match"`; any missing or extra pair, UNSAT class, unknown
public name, or failed structural premise returns nonzero.
