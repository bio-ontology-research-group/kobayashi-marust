#!/usr/bin/env python3
"""Random small SHIQ ontologies in the normal form of km-sriq-fast-probe --sriq.

Usage: gen_random.py <seed> [names] [roles] [clauses]
Names 0..k-1 are concepts, name k is top (gci | k). Roles 0..m-1;
a role term is "r" or "-r". The output mixes disjunction, conjunction,
existentials, universals, inverse roles, a role hierarchy, functional and
inverse-functional roles, and at-least/at-most with numbers up to 3.
Counting clauses use only roles below which no transitive role lies
(transitivity is added on a separate role at most, to stay SHIQ)."""
import random, sys, os

def main():
    seed = int(sys.argv[1])
    rnd = random.Random(seed)
    k = int(sys.argv[2]) if len(sys.argv) > 2 else rnd.randint(4, 6)
    m = int(sys.argv[3]) if len(sys.argv) > 3 else rnd.randint(1, 2)
    nc = int(sys.argv[4]) if len(sys.argv) > 4 else rnd.randint(5, 9)
    top = k
    n = k + 1
    lines = [None, f"gci | {top}"]
    defs = [n]
    def newdef():
        d = defs[0]; defs[0] += 1; return d
    def name(): return rnd.randrange(k)
    def role(): 
        r = rnd.randrange(m)
        return f"-{r}" if rnd.random() < 0.4 else f"{r}"
    filler = lambda: top if rnd.random() < 0.25 else name()
    # role hierarchy
    if m >= 2 and rnd.random() < 0.6:
        lines.append(f"sub {role()} {role()}")
    kinds = ["negle", "neglux"] * int(os.environ.get("NEGW", "0")) + ["gci_or", "gci_and", "gci_disj", "ex", "all", "ge", "le", "func", "invfunc", "ex", "le", "ge"]
    for _ in range(nc):
        kd = rnd.choice(kinds)
        if kd == "gci_or":
            lines.append(f"gci {name()} | {name()} {name()}")
        elif kd == "gci_and":
            lines.append(f"gci {name()} {name()} | {name()}")
        elif kd == "gci_disj":
            a, b = name(), name()
            if a != b: lines.append(f"gci {a} {b} |")
        elif kd == "ex":
            lines.append(f"ex {name()} {role()} {filler()}")
        elif kd == "all":
            lines.append(f"all {rnd.choice([name(), top])} {role()} {name()}")
        elif kd == "ge":
            lines.append(f"ge {name()} {rnd.randint(1,3)} {role()} {filler()}")
        elif kd == "le":
            lines.append(f"le {rnd.choice([name(), top])} {rnd.randint(0,3)} {role()} {filler()}")
        elif kd == "negle":
            d = newdef()
            lines.append(f"gci | {name()} {d}")
            lines.append(f"le {d} {rnd.randint(0,2)} {role()} {filler()}")
        elif kd == "neglux":
            d1 = newdef(); d2 = newdef(); kk = rnd.randint(0,1)
            lines.append(f"gci | {name()} {d1} {d2}")
            lines.append(f"le {d1} {kk} {role()} {filler()}")
            lines.append(f"ge {d2} {kk+2} {role()} {filler()}")
        elif kd == "func":
            lines.append(f"le {top} 1 {rnd.randrange(m)} {top}")
        elif kd == "invfunc":
            lines.append(f"le {top} 1 -{rnd.randrange(m)} {top}")
    lines[0] = f"n {defs[0]} m {m}\nreq {n}"
    mb = os.environ.get("MAXBND")
    if mb is not None:
        bnd = sum(1 for l in lines if l.startswith("ex ")) + sum(int(l.split()[2]) for l in lines if l.startswith("ge "))
        if bnd > int(mb):
            # drop lower clauses from the end until the bound holds
            out = []
            budget = int(mb)
            for l in lines:
                if l.startswith("ex "):
                    if budget >= 1: budget -= 1; out.append(l)
                elif l.startswith("ge "):
                    k = int(l.split()[2])
                    if budget >= k: budget -= k; out.append(l)
                else: out.append(l)
            lines = out
    print("\n".join(lines))

main()
