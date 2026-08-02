#!/usr/bin/env python3
"""Role-use census over a frontend clause set, for inverse-bridge audits.

Reads `{"clauses":[...]}` (the `ofn` output, the same payload `elc` and the CB
engine consume) and reports, per role name, every structural position the role
occupies. The classification mirrors `elcomplete.rs::to_nf` branch for branch,
so a role's counters say exactly which EL normal form the role lands in and
which occurrences fall through to the residual certificate.

The point of the census is the inverse-bridge question: the frontend emits
`InverseObjectProperties(R,S)` / `ObjectInverseOf` as a swapped role inclusion
`R(x,y) -> S(y,x)`, which EL cannot express. Canonicalising a *reciprocal* pair
(both swapped inclusions present) by rewriting every `S(x,y)` to `R(y,x)` is a
truth-preserving substitution, but only if every remaining occurrence of `S` is
rewritten too, and only if the resulting reverse-oriented normal forms are
supported. This script prints the occurrence table that decides both.

    python3 role_census.py clauses.json                 # human summary
    python3 role_census.py --json out.json clauses.json # machine-readable
    python3 role_census.py --residual-shapes clauses.json

Positions reported per role:

  nf3            A ⊑ ∃R.B          existential role half (`A(x) -> R(x,f(x))`)
  nf4            ∃R.C ⊑ D          `R(x,y) ∧ C(y) -> D(x)`
  domain         ∃R.⊤ ⊑ D          `R(x,y) -> D(x)`
  nf6_sub        R ⊑ S             R in sub position
  nf6_sup        S ⊑ R             R in super position (a HEAD occurrence)
  nf7_left       R∘S ⊑ T           R as the first chain link
  nf7_right      S∘R ⊑ T           R as the second chain link
  nf7_sup        S∘T ⊑ R           R as the chain super (a HEAD occurrence)
  reflexive      Reflexive(R)      `[] -> R(x,x)` (a HEAD occurrence)
  bridge_base    R⁻ ⊑ S            R in the body of a swapped inclusion
  bridge_head    S⁻ ⊑ R            R in the head of a swapped inclusion
  ground         r(a,b)            any role atom over an `ind`/`aux` term
  residual_body  every other body occurrence (cardinality, range, disjointness)
  residual_head  every other head occurrence (a DERIVING occurrence)
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict

POSITIONS = (
    "nf3",
    "nf4",
    "domain",
    "nf6_sub",
    "nf6_sup",
    "nf7_left",
    "nf7_right",
    "nf7_sup",
    "reflexive",
    "bridge_base",
    "bridge_head",
    "ground",
    "residual_body",
    "residual_head",
)

# Positions that put the role on the DERIVING side: some clause other than the
# bridge can add pairs to the role's extension. A one-way bridge `R⁻ ⊑ S` may be
# read as a definition `S ≡ R⁻` only when none of these fire for S.
DERIVING = ("nf3", "nf6_sup", "nf7_sup", "reflexive", "bridge_head", "residual_head")

# Positions whose EL rule reverses orientation once the role is rewritten to the
# transpose of its partner. These are the ones a canonicalising implementation
# must actually support (or fail closed on).
REVERSING = ("nf3", "nf4", "domain", "nf6_sub", "nf6_sup", "nf7_left", "nf7_right", "nf7_sup")


def var(t):
    return t["name"] if t["kind"] == "var" else None


def is_concept(a):
    return a["kind"] == "concept"


def is_role(a):
    return a["kind"] == "role"


class Census:
    def __init__(self):
        self.pos = defaultdict(Counter)  # role -> position -> count
        self.bridges = []  # (base, head) from `R(x,y) -> S(y,x)`
        self.clause_kinds = Counter()
        self.residual_shapes = Counter()
        self.residual_by_role = defaultdict(Counter)  # role -> shape -> count
        self.total = 0
        # (sub concept, skolem fn) -> role name, for the existential halves
        self.pending_ex = {}

    def hit(self, role, position, n=1):
        self.pos[role][position] += n

    # -- residual bookkeeping ------------------------------------------------
    def shape(self, c):
        def side(atoms):
            return (
                sum(1 for a in atoms if is_concept(a)),
                sum(1 for a in atoms if is_role(a)),
                sum(1 for a in atoms if a["kind"] == "eq"),
            )

        (bc, br, be) = side(c["body"])
        (hc, hr, he) = side(c["head"])
        return f"b{len(c['body'])}c{bc}r{br}e{be}/h{len(c['head'])}c{hc}r{hr}e{he}"

    def residual(self, c):
        self.clause_kinds["residual"] += 1
        sh = self.shape(c)
        self.residual_shapes[sh] += 1
        for a in c["body"]:
            if is_role(a):
                self.hit(a["role"], "residual_body")
                self.residual_by_role[a["role"]][sh] += 1
        for a in c["head"]:
            if is_role(a):
                self.hit(a["role"], "residual_head")
                self.residual_by_role[a["role"]][sh] += 1

    # -- the to_nf mirror ----------------------------------------------------
    def add(self, c):
        self.total += 1
        body, head = c["body"], c["head"]

        for a in body + head:
            if is_role(a) and (
                a["source"]["kind"] in ("ind", "aux")
                or a["target"]["kind"] in ("ind", "aux")
            ):
                self.hit(a["role"], "ground")

        if any(a["kind"] == "eq" for a in body + head):
            return self.residual(c)

        if not head:
            shared = var(body[0]["term"]) if body and is_concept(body[0]) else None
            if body and shared is not None and all(
                is_concept(a) and var(a["term"]) == shared for a in body
            ):
                self.clause_kinds["nf5"] += 1
                return
            return self.residual(c)

        if len(head) != 1:
            return self.residual(c)

        h = head[0]

        if is_concept(h) and h["term"]["kind"] == "var":
            hv = var(h["term"])
            if all(is_concept(a) and var(a["term"]) == hv for a in body):
                self.clause_kinds["nf1_nf2"] += 1
                return
            if len(body) == 1 and is_role(body[0]):
                a = body[0]
                s, t = var(a["source"]), var(a["target"])
                if s is not None and t is not None and s == hv and s != t:
                    self.clause_kinds["domain"] += 1
                    self.hit(a["role"], "domain")
                    return
                return self.residual(c)
            if len(body) == 2:
                roles = [a for a in body if is_role(a)]
                concepts = [a for a in body if is_concept(a)]
                if len(roles) == 1 and len(concepts) == 1:
                    a, f = roles[0], concepts[0]
                    s, t = var(a["source"]), var(a["target"])
                    if (
                        s is not None
                        and t is not None
                        and t == var(f["term"])
                        and s == hv
                        and s != t
                    ):
                        self.clause_kinds["nf4"] += 1
                        self.hit(a["role"], "nf4")
                        return
            return self.residual(c)

        if is_concept(h) and h["term"]["kind"] == "fun":
            if (
                len(body) == 1
                and is_concept(body[0])
                and var(body[0]["term"]) is not None
            ):
                self.clause_kinds["ex_filler_half"] += 1
                return
            return self.residual(c)

        if is_role(h):
            hs, ht = var(h["source"]), var(h["target"])
            if not body and hs is not None and hs == ht:
                self.clause_kinds["reflexive"] += 1
                self.hit(h["role"], "reflexive")
                return
            if h["target"]["kind"] == "fun" and hs is not None:
                if (
                    len(body) == 1
                    and is_concept(body[0])
                    and var(body[0]["term"]) is not None
                ):
                    self.clause_kinds["ex_role_half"] += 1
                    self.hit(h["role"], "nf3")
                    return
                return self.residual(c)

            roles = [a for a in body if is_role(a)]
            if ht is not None and len(body) == 1 and len(roles) == 1:
                b = roles[0]
                bs, bt = var(b["source"]), var(b["target"])
                if bs is not None and bt is not None:
                    if bs == hs and bt == ht:
                        self.clause_kinds["nf6"] += 1
                        self.hit(b["role"], "nf6_sub")
                        self.hit(h["role"], "nf6_sup")
                        return
                    if bs != bt and bs == ht and bt == hs:
                        self.clause_kinds["inverse_bridge"] += 1
                        self.bridges.append((b["role"], h["role"]))
                        self.hit(b["role"], "bridge_base")
                        self.hit(h["role"], "bridge_head")
                        return
                return self.residual(c)

            if ht is not None and len(body) == 2 and len(roles) == 2:
                a, b = roles
                a0, a1 = var(a["source"]), var(a["target"])
                b0, b1 = var(b["source"]), var(b["target"])
                if None not in (a0, a1, b0, b1, hs, ht):
                    if a1 == b0 and hs == a0 and ht == b1:
                        first, second = a["role"], b["role"]
                    elif b1 == a0 and hs == b0 and ht == a1:
                        first, second = b["role"], a["role"]
                    else:
                        return self.residual(c)
                    self.clause_kinds["nf7"] += 1
                    self.hit(first, "nf7_left")
                    self.hit(second, "nf7_right")
                    self.hit(h["role"], "nf7_sup")
                    return
            return self.residual(c)

        return self.residual(c)


def witness_sharing(clauses, roles, sample, seed):
    """How many contexts share one existential witness node.

    The completion gives filler concept `B` a single node, and sends it an
    in-edge from every context whose label contains the subject of an
    `A ⊑ ∃R.B` axiom. A reverse-oriented rule firing at that node writes into
    the named class `B`, so it is sound only if the rule's guard holds at ALL of
    those contexts. This reports how many there are.

    The count uses asserted unit subsumption only, so it is a LOWER bound: label
    growth through NF2 and NF4 adds more contexts. `min` over the sample is the
    number that matters, because a witness with a single context is the only one
    a reverse rule could be fired at without a guard.
    """
    import random

    supers = defaultdict(list)  # super -> [sub], asserted unit subsumption
    role_half, filler_half = {}, {}
    for c in clauses:
        if len(c["head"]) != 1 or len(c["body"]) != 1 or not is_concept(c["body"][0]):
            continue
        b, h = c["body"][0], c["head"][0]
        bv = var(b["term"])
        if bv is None:
            continue
        if is_concept(h) and var(h["term"]) == bv:
            supers[h["concept"]].append(b["concept"])
        elif is_role(h) and h["target"]["kind"] == "fun":
            role_half[(b["concept"], h["target"]["function"])] = h["role"]
        elif is_concept(h) and h["term"]["kind"] == "fun":
            filler_half[(b["concept"], h["term"]["function"])] = h["concept"]

    nodes = defaultdict(list)  # (role, filler) -> [axiom subject]
    for k, r in role_half.items():
        nodes[(r, filler_half.get(k, "owl:Thing"))].append(k[0])

    def descendants(seed_concept):
        seen, stack = {seed_concept}, [seed_concept]
        while stack:
            for y in supers.get(stack.pop(), ()):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return len(seen)

    rng = random.Random(seed)
    out = {"unit_subsumption_edges": sum(len(v) for v in supers.values()), "roles": {}}
    for r in roles:
        keys = [k for k in nodes if k[0] == r]
        if not keys:
            continue
        picked = rng.sample(keys, min(sample, len(keys)))
        vals = sorted(descendants(s) for k in picked for s in nodes[k])
        n = len(vals)
        out["roles"][r] = {
            "witness_nodes": len(keys),
            "sampled": n,
            "min": vals[0],
            "median": vals[n // 2],
            "p90": vals[int(0.9 * n)],
            "max": vals[-1],
            "mean": round(sum(vals) / n, 1),
        }
    return out


def analyse(cen):
    """Bridge pairing plus the per-pair canonicalisation gate table."""
    seen = set(cen.bridges)
    pairs, oneway = [], []
    done = set()
    for base, head in cen.bridges:
        if (base, head) in done:
            continue
        if (head, base) in seen:
            key = tuple(sorted((base, head)))
            if key in done:
                continue
            done.add(key)
            done.add((base, head))
            done.add((head, base))
            pairs.append(key)
        else:
            oneway.append((base, head))
    return pairs, oneway


def gate_row(cen, keep, drop):
    """Gates for `rewrite every drop(x,y) to keep(y,x)`."""
    kp, dp = cen.pos[keep], cen.pos[drop]
    reversing = {p: dp[p] for p in REVERSING if dp[p]}
    return {
        "keep": keep,
        "drop": drop,
        "keep_positions": {p: kp[p] for p in POSITIONS if kp[p]},
        "drop_positions": {p: dp[p] for p in POSITIONS if dp[p]},
        # occurrences of the dropped role that become reverse-oriented rules
        "reverse_oriented": reversing,
        "reverse_oriented_total": sum(reversing.values()),
        # residual/ground/side-channel occurrences that must be rewritten too
        "must_rewrite_residual": dp["residual_body"] + dp["residual_head"],
        "must_rewrite_ground": dp["ground"],
        # chains touching either half: no forward index answers a reversed link
        "chain_touch": sum(
            c[p] for c in (kp, dp) for p in ("nf7_left", "nf7_right", "nf7_sup")
        ),
        # forward edge volume the reverse rules must be replayed over
        "keep_nf3": kp["nf3"],
        "keep_nf4": kp["nf4"],
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("clauses", help="clause-set JSON, or - for stdin")
    ap.add_argument("--json", metavar="PATH", help="write the full census as JSON")
    ap.add_argument(
        "--residual-shapes",
        action="store_true",
        help="print the residual shape histogram",
    )
    ap.add_argument(
        "--top", type=int, default=20, help="roles to list in the summary (default 20)"
    )
    ap.add_argument(
        "--witness-sharing",
        type=int,
        metavar="N",
        help="sample N witness nodes per bridged role and report how many "
        "contexts share each (a lower bound; see witness_sharing)",
    )
    ap.add_argument("--seed", type=int, default=20260802, help="sampling seed")
    args = ap.parse_args()

    src = sys.stdin if args.clauses == "-" else open(args.clauses)
    with src as fh:
        data = json.load(fh)

    cen = Census()
    for c in data["clauses"]:
        cen.add(c)

    pairs, oneway = analyse(cen)

    out = {
        "clauses": cen.total,
        "clause_kinds": dict(cen.clause_kinds),
        "roles": len(cen.pos),
        "bridges": {
            "clauses": len(cen.bridges),
            "reciprocal_pairs": [list(p) for p in pairs],
            "one_way": [list(p) for p in oneway],
        },
        "gates": [],
        "role_positions": {
            r: {p: v for p, v in cnt.items() if v} for r, cnt in cen.pos.items()
        },
        "residual_shapes": dict(cen.residual_shapes),
    }
    for a, b in pairs:
        out["gates"].append(gate_row(cen, a, b))
        out["gates"].append(gate_row(cen, b, a))
    out["residual_shapes_by_bridged_role"] = {
        r: dict(cen.residual_by_role[r])
        for r in {x for p in pairs for x in p} | {x for p in oneway for x in p}
        if cen.residual_by_role[r]
    }

    if args.witness_sharing:
        bridged = sorted(
            {x for p in pairs for x in p} | {x for p in oneway for x in p}
        )
        out["witness_sharing"] = witness_sharing(
            data["clauses"], bridged, args.witness_sharing, args.seed
        )

    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1, sort_keys=True)

    print(f"clauses: {cen.total}   roles: {len(cen.pos)}")
    print("clause kinds:")
    for k, v in sorted(cen.clause_kinds.items(), key=lambda kv: -kv[1]):
        print(f"  {k:<18} {v}")
    print(f"\ninverse-bridge clauses: {len(cen.bridges)}")
    print(f"  reciprocal pairs: {len(pairs)}  ({2 * len(pairs)} clauses)")
    for a, b in pairs:
        print(f"    {a} <-> {b}")
    print(f"  one-way bridges: {len(oneway)}")
    for a, b in oneway:
        print(f"    {a}- <= {b}   (no converse clause)")

    if pairs:
        print("\ncanonicalisation gates (rewrite drop(x,y) := keep(y,x)):")
        hdr = f"  {'keep':<16}{'drop':<16}{'reverse':>9}{'resid':>7}{'ground':>7}{'chain':>7}"
        print(hdr)
        for g in out["gates"]:
            print(
                f"  {g['keep']:<16}{g['drop']:<16}{g['reverse_oriented_total']:>9}"
                f"{g['must_rewrite_residual']:>7}{g['must_rewrite_ground']:>7}"
                f"{g['chain_touch']:>7}"
            )

    print("\nper-role positions (roles with the most occurrences):")
    ranked = sorted(cen.pos.items(), key=lambda kv: -sum(kv[1].values()))
    for r, cnt in ranked[: args.top]:
        body = " ".join(f"{p}={cnt[p]}" for p in POSITIONS if cnt[p])
        print(f"  {r:<24} {body}")

    if args.witness_sharing:
        ws = out["witness_sharing"]
        print(
            f"\nwitness sharing (contexts per witness node, LOWER bound from "
            f"{ws['unit_subsumption_edges']} unit subsumptions):"
        )
        print(f"  {'role':<26}{'nodes':>8}{'min':>6}{'median':>8}{'p90':>7}{'max':>8}{'mean':>9}")
        for r, s in ws["roles"].items():
            print(
                f"  {r:<26}{s['witness_nodes']:>8}{s['min']:>6}{s['median']:>8}"
                f"{s['p90']:>7}{s['max']:>8}{s['mean']:>9}"
            )

    if args.residual_shapes:
        print("\nresidual shape histogram:")
        for sh, n in sorted(cen.residual_shapes.items(), key=lambda kv: -kv[1]):
            print(f"  {sh:<28} {n}")

    if args.json:
        print(f"\nwrote {args.json}")


if __name__ == "__main__":
    main()
