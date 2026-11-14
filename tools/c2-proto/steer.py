"""The steered construction of design section 3.4, run on a finite model.

Roots, an introduction forest, tree nodes that are copies of model
elements with one slot per witness, pairwise blocking by patterns, and
the two rules Expand and NI exactly as in the design note. The run
asserts the invariant of Lemma C2 before every NI step and the root
bound of Lemma C3 at the end, and reads the final structure as a
certificate (Lemma C6) for `cert.check_cert`.

For a finite model the construction is not needed (cert.model_to_cert is
simpler); running it anyway tests the pen proof's lemmas on concrete
inputs.
"""

from __future__ import annotations

from kb import KB, flipL


class SteerError(Exception):
    pass


def bound(kb: KB):
    """(℘, B) of design section 0, with minimal labels."""
    tt = len(kb.tree_types)
    P = tt * len(kb.labels) * tt
    wp = P + 2
    b = sum(k for (a, k, R, c) in kb.upper)
    roots0 = max(1, len(kb.noms))
    if b <= 1:
        B = roots0 * (wp + 1)
    else:
        B = roots0 * (b ** (wp + 1) - 1) // (b - 1)
    return wp, B


def steer(kb: KB, N, cext, rext, max_steps=200000):
    D = range(N)
    typ = {x: frozenset(a for a in range(kb.n) if x in cext[a]) for x in D}
    full = {(x, y): set() for x in D for y in D}
    for r, pairs in rext.items():
        for (x, y) in pairs:
            full[(x, y)].add(2 * r)
            full[(y, x)].add(2 * r + 1)
    need = {(x, y): set() for x in D for y in D}
    wit = {}
    for x in D:
        w = []
        for (a, k, R, b) in kb.lower:
            if a in typ[x]:
                got = [y for y in D if R in full[(x, y)] and b in typ[y]][:k]
                if len(got) < k:
                    raise SteerError("not a model")
                for y in got:
                    need[(x, y)].add(R)
                    if y not in w:
                        w.append(y)
        wit[x] = w
    wl = {(x, y): kb.up_close(frozenset(need[(x, y)]) | flipL(frozenset(need[(y, x)])))
          for x in D for y in D}
    own = {(x, y): kb.up_close(frozenset(need[(x, y)])) for x in D for y in D}
    nom_el = [x for x in D if typ[x] & kb.noms]
    wp, B = bound(kb)

    ip = {}  # root -> introduction parent (None for nominal elements / x0)
    for x in (nom_el or [0]):
        ip[x] = None
    root_slots = {y: {w: "empty" for w in wit[y]} for y in ip}
    nodes = {}  # id -> dict(img, parent, depth, slots, blocked)
    next_id = [0]
    stats = {"ni": 0, "expand": 0, "reparent": 0, "max_idep": 0, "max_depth": 0}

    def idep(y):
        d = 0
        while ip[y] is not None:
            y = ip[y]
            d += 1
            if d > len(ip) + 1:
                raise SteerError("introduction forest has a cycle")
        return d

    def img_of(parent):
        return parent[1] if parent[0] == "r" else nodes[parent[1]]["img"]

    def pattern(nid):
        nd = nodes[nid]
        p = img_of(nd["parent"])
        return (typ[nd["img"]], wl[(nd["img"], p)], typ[p])

    def new_node(img, parent, depth):
        nid = next_id[0]
        next_id[0] += 1
        pimg = img_of(parent)
        nodes[nid] = {"img": img, "parent": parent, "depth": depth,
                      "slots": {w: "empty" for w in wit[img] if w != pimg}, "blocked": False}
        if depth >= 2:
            pat = pattern(nid)
            a = parent
            while a[0] == "n":
                an = nodes[a[1]]
                if an["blocked"]:
                    raise SteerError("child of a blocked node")
                if an["depth"] >= 2 and pattern(a[1]) == pat:
                    nodes[nid]["blocked"] = True
                    break
                a = an["parent"]
        if depth > wp:
            raise SteerError(f"depth {depth} > ℘ = {wp} (Lemma C1)")
        stats["max_depth"] = max(stats["max_depth"], depth)
        return nid

    def delete(nid):
        stack = [nid]
        while stack:
            x = stack.pop()
            for st in nodes[x]["slots"].values():
                if isinstance(st, tuple):
                    stack.append(st[1])
            del nodes[x]

    for step in range(max_steps):
        # NI
        hit = None
        for nid, nd in nodes.items():
            if nd["blocked"]:
                continue
            for w, st in nd["slots"].items():
                if st == "core" and kb.counted(typ[w], flipL(own[(nd["img"], w)]), typ[nd["img"]]):
                    hit = (nid, w)
                    break
            if hit:
                break
        if hit:
            nid, d = hit
            nd = nodes[nid]
            if idep(d) + nd["depth"] > wp:
                raise SteerError("invariant of Lemma C2 violated")
            y = nd["img"]
            if y not in ip:
                ip[y] = d
                root_slots[y] = {w: "empty" for w in wit[y]}
            elif idep(y) > idep(d) + 1:
                ip[y] = d
                stats["reparent"] += 1
            parent = nd["parent"]
            delete(nid)
            if parent[0] == "r":
                root_slots[parent[1]][y] = "core"
            else:
                nodes[parent[1]]["slots"][y] = "core"
            for r, sl in root_slots.items():
                st = sl.get(y)
                if isinstance(st, tuple):
                    delete(st[1])
                    sl[y] = "core"
            stats["ni"] += 1
            stats["max_idep"] = max(stats["max_idep"], max(idep(r) for r in ip))
            continue
        # Expand
        done = False
        for r, sl in root_slots.items():
            for w, st in sl.items():
                if st == "empty":
                    sl[w] = "core" if w in ip else ("child", new_node(w, ("r", r), 1))
                    done = True
                    break
            if done:
                break
        if not done:
            for nid in list(nodes):
                nd = nodes.get(nid)
                if nd is None or nd["blocked"]:
                    continue
                for w, st in nd["slots"].items():
                    if st == "empty":
                        nd["slots"][w] = "core" if w in nom_el else \
                            ("child", new_node(w, ("n", nid), nd["depth"] + 1))
                        done = True
                        break
                if done:
                    break
        if done:
            stats["expand"] += 1
            continue
        break
    else:
        raise SteerError("no termination within max_steps")

    if len(ip) > B:
        raise SteerError(f"{len(ip)} roots > B = {B} (Lemma C3)")
    for y in ip:
        if ip[y] is not None:
            d = ip[y]
            if not kb.counted(typ[d], wl[(d, y)], typ[y]):
                raise SteerError("introduction parent does not count its child")
    # Lemma C6: read the certificate
    K = list(ip)
    idx = {r: i for i, r in enumerate(K)}

    def rec_of(nid):
        nd = nodes[nid]
        p = nd["parent"]
        if p[0] == "r":
            return (typ[nd["img"]], ("c", idx[p[1]], wl[(nd["img"], p[1])]))
        return (typ[nd["img"]], ("t", wl[(nd["img"], img_of(p))], typ[img_of(p)]))

    recs = {}
    for nid, nd in nodes.items():
        if nd["blocked"]:
            continue
        rid = rec_of(nid)
        if rid in recs:
            continue
        core = {}
        ch = []
        for w, st in nd["slots"].items():
            if st == "core":
                core[idx[w]] = own[(nd["img"], w)]
            elif isinstance(st, tuple):
                ch.append((wl[(nd["img"], w)], rec_of(st[1])))
            else:
                raise SteerError("empty slot in a final unblocked node")
        recs[rid] = (rid[0], rid[1], core, ch)
    kids = []
    for r in K:
        ks = []
        for w, st in root_slots[r].items():
            if isinstance(st, tuple):
                if nodes[st[1]]["img"] in ip:
                    raise SteerError("root child whose image is a root (Lemma C5)")
                ks.append(rec_of(st[1]))
            elif st != "core":
                raise SteerError("empty root slot at the end")
        kids.append(ks)
    cty = [typ[r] for r in K]
    lab = [[wl[(r, s)] for s in K] for r in K]
    stats["roots"] = len(K)
    stats["B"] = B
    stats["wp"] = wp
    return (cty, lab, kids, recs), stats
