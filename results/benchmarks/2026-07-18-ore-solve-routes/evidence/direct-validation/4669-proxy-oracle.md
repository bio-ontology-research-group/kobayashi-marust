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
- `ProjectedDisjointOracle4669.java` loads that projection in HermiT and calls
  the complete reasoner's `getDisjointClasses(P_F)` for every proxy. It emits
  every base-to-negative pair `A ⊑ N_F`, with full IRIs, because this is
  equivalent to the disjointness of `A` and `P_F`.
- `validate_4669_proxy_oracle.py` closes the externally classified projection,
  reverses every `P_F ⊑ P_G` into `N_G ⊑ N_F`, incorporates the HermiT
  disjointness relation, handles named aliases of top and bottom, reconstructs
  the complete original public taxonomy, and compares it exactly with a KM
  JSON result.
- `ibex_4669_proxy_oracle.sbatch` compiles the projector, classifies the
  projection independently with Konclude, ELK, and HermiT, requires the
  Konclude and ELK full-IRI taxonomies to agree, writes the standalone gzip TSV
  oracle, and optionally validates a candidate KM binary or existing JSON
  output.

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
- base→negative is HermiT's complete named disjointness relation, since
  `A ⊑ N_F` iff `A ⊓ P_F` is unsatisfiable;
- negative→base is absent for satisfiable non-top base targets by the isolated
  fresh-element argument below.

The disjointness query is necessary. The source uses the inverse role
`BFO_0000050` (`part_of`) in positive definitions, while the mirrors use
`BFO_0000051` (`has_part`). A root class can therefore constrain the filler of
`P_F` and make it clash with `F`, producing genuine base→negative entailments.
The earlier role-separation shortcut would miss these edges.

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

## IBEX use

Copy the five files together to IBEX and submit either an oracle-only run:

```bash
sbatch ibex_4669_proxy_oracle.sbatch
```

or an end-to-end candidate validation:

```bash
sbatch --export=ALL,CANDIDATE_KM=/path/to/km,CANDIDATE_ROUTE=ht_bridge \
  ibex_4669_proxy_oracle.sbatch
```

An existing output can be checked with
`CANDIDATE_JSON=/path/to/km-output.json`. A successful candidate run ends with
`"status": "match"`; any missing or extra pair, UNSAT class, unknown public
name, reasoner disagreement, or failed structural premise returns nonzero.
