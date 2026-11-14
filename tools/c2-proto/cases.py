"""Hand-written cases (design section 6.1). Each entry: name, source,
expected consistency, and a note. The expectations are the pen-and-paper
answers; validate.py compares them with the procedure, the brute-force
search, HermiT and km.
"""

CASES = [
    # --- shared anonymous elements forced by inverse counting at a nominal ---
    ("msh-fig5-share", """
nom Na
nom Nb
nom Nc
Na <= A
Nb <= A
A <= some r.B
B <= some r.C
C <= some s.Nc
Nc <= <=1 s-.T
T <= T
distinct Na Nb Nc
anon B C
""", True, "MSH 2009 (5): s2 and s4 must be one shared C element (S inverse functional)"),
    ("msh-fig5-clash", """
nom Na
nom Nb
nom Nc
Na <= A1
Nb <= A2
A1 <= some r.B1
B1 <= some r.C1
A2 <= some r.B2
B2 <= some r.C2
C1 <= some s.Nc
C2 <= some s.Nc
C1 & C2 <= F
Nc <= <=1 s-.T
T <= T
distinct Na Nb Nc
anon B1 C1 B2 C2
""", False, "as fig5 but the two C elements must differ: inconsistent"),
    ("msh-yoyo", """
nom Nb
nom Na
Nb <= A
A <= some r.A
A <= some s.Na
Na <= <=2 s-.T
T <= T
distinct Na Nb
""", True, "MSH 2009 (6): at most two A elements, the r-chain closes"),
    ("msh-yoyo-odd", """
nom Nb
nom Na
Nb <= A
A <= some r.A
A <= some s.Na
Na <= <=1 s-.T
T <= T
A <= P | Q
P & Q <= F
P <= all r.Q
Q <= all r.P
distinct Na Nb
""", False, "one A element, it needs an r-successor A of the other colour: inconsistent"),
    ("msh-yoyo-even", """
nom Nb
nom Na
Nb <= A
A <= some r.A
A <= some s.Na
Na <= <=2 s-.T
T <= T
A <= P | Q
P & Q <= F
P <= all r.Q
Q <= all r.P
distinct Na Nb
""", True, "two A elements alternate: consistent"),
    ("msh-caterpillar", """
nom Na
Na <= some s.Na
Na <= some r.B
B <= some r.C
C <= some s.D
D <= Na
T <= <=1 s-.T
""", True, "MSH 2009 (8): the C element is a"),
    ("msh-caterpillar-clash", """
nom Na
Na <= some s.Na
Na <= some r.B
B <= some r.C
C <= some s.D
D <= Na
T <= <=1 s-.T
C & Na <= F
""", False, "the C element must be a but may not be: inconsistent"),
    ("rg-fig1-cycle", """
nom O1
nom O2
nom O3
O1 <= some f.X1
X1 <= some s.Y1
Y1 <= some f-.O2
O2 <= some f.X2
X2 <= some s.Y2
Y2 <= some f-.O3
O3 <= some f.X3
X3 <= some s.Y3
Y3 <= some f-.O1
T <= <=1 f.T
distinct O1 O2 O3
anon X1 X2 X3 Y1 Y2 Y3
""", True, "Rudolph and Glimm 2010 Fig. 1: an s-cycle of new nominals"),
    ("rg-fig1-odd", """
nom O1
nom O2
nom O3
O1 <= some f.X1
X1 <= some s.Y1
Y1 <= some f-.O2
O2 <= some f.X2
X2 <= some s.Y2
Y2 <= some f-.O3
O3 <= some f.X3
X3 <= some s.Y3
Y3 <= some f-.O1
T <= <=1 f.T
T <= E | D
E & D <= F
E <= all s.D
D <= all s.E
distinct O1 O2 O3
anon X1 X2 X3 Y1 Y2 Y3
""", False, "the forced s-cycle has length 3 and must alternate: inconsistent"),
    ("rg-fig1-free", """
nom O1
nom O2
nom O3
O1 <= some f.X1
X1 <= some s.Y1
Y1 <= some f-.O2
O2 <= some f.X2
X2 <= some s.Y2
Y2 <= some f-.O3
O3 <= some f.X3
X3 <= some s.Y3
Y3 <= some f-.O1
T <= E | D
E & D <= F
E <= all s.D
D <= all s.E
distinct O1 O2 O3
anon X1 X2 X3 Y1 Y2 Y3
""", True, "without functionality the cycle is not forced: consistent"),
    # --- inverse functional roles with nominals ---
    ("invfun-hasvalue-clash", """
nom O
nom Pa
nom Pb
Pa <= A
Pb <= B
A <= some r.O
B <= some r.O
A & B <= F
T <= <=1 r-.T
""", False, "inverse functional r, two disjoint r-predecessors of o: inconsistent"),
    ("invfun-hasvalue-merge", """
nom O
nom Pa
nom Pb
Pa <= A
Pb <= B
A <= some r.O
B <= some r.O
T <= <=1 r-.T
""", True, "the two individuals merge (no unique names): consistent"),
    ("invfun-anon-chain", """
nom O
O <= some r-.A
A <= some r-.B
B <= some r-.C
C <= some r.O
T <= <=1 r-.T
A & C <= F
anon A B C
""", False, "inverse functional r: o's two r-predecessors (the A and the C element) coincide, A & C <= F: inconsistent"),
    ("invfun-anon-chain-ok", """
nom O
O <= some r-.A
A <= some r-.B
B <= some r-.C
C <= some r.O
T <= <=1 r-.T
B & C <= F
anon A B C
""", True, "the C element is the A element; the r-cycle a, b closes: consistent"),
    ("invfun-anon-two-levels", """
nom O
nom P
P <= some s.Y
Y <= some r.X
X <= some r.O
O <= <=1 r-.X
X <= <=1 r-.Y
P <= some t.Y2
Y2 <= Y
Y2 <= Z
Y <= W
distinct O P
anon X Y Y2
""", True, "a promoted element of level 2 (Y counted at the shared X)"),
    ("level2-clash", """
nom O
nom P
nom Q
P <= some s.Y1
Q <= some s.Y2
Y1 <= some r.X
Y2 <= some r.X
X <= some r.O
O <= <=1 r-.X
X <= <=1 r-.Y
Y1 <= Y
Y2 <= Y
Y1 & Y2 <= F
distinct O P Q
anon X Y Y1 Y2
""", False, "the X element is shared (level 1) and then Y1 = Y2 (level 2): inconsistent"),
    ("level2-ok", """
nom O
nom P
nom Q
P <= some s.Y1
Q <= some s.Y2
Y1 <= some r.X
Y2 <= some r.X
X <= some r.O
O <= <=1 r-.X
X <= <=2 r-.Y
Y1 <= Y
Y2 <= Y
Y1 & Y2 <= F
distinct O P Q
anon X Y Y1 Y2
""", True, "as level2-clash with two Y slots: consistent"),
    # --- an unnamed element forced equal to a nominal ---
    ("forced-equal", """
nom O
nom P
O <= some r.P
O <= <=1 r.T
O <= some r.A
A & P <= F
distinct O P
""", False, "o has one r-successor, which is p, so the A successor is p: inconsistent"),
    ("forced-equal-ok", """
nom O
nom P
O <= some r.P
O <= <=1 r.T
O <= some r.A
distinct O P
""", True, "the A successor is p: consistent"),
    ("forced-equal-inverse", """
nom O
nom P
P <= some r.O
O <= <=1 r-.T
O <= some r-.A
A <= some s.B
P <= all s.C
B & C <= F
distinct O P
""", False, "the A predecessor of o is p, so p needs an s-successor in B, but all of p's s-successors are C: inconsistent"),
    ("forced-equal-inverse-ok", """
nom O
nom P
P <= some r.O
O <= <=1 r-.T
O <= some r-.A
A <= some s.B
P <= all s.C
distinct O P
anon B
""", True, "p is the A predecessor; its B successor is also C: consistent"),
    ("forced-equal-inverse-clash", """
nom O
nom P
P <= some r.O
O <= <=1 r-.T
O <= some r-.A
A <= some s.B
P <= all s.C
B & C <= F
A <= Q
P <= R
Q & R <= F
distinct O P
""", False, "the A predecessor must be p but A and p's names clash: inconsistent"),
    # --- counting at nominals, blocking-free infinite models ---
    ("infinite-chain", """
nom O
O <= <=0 r-.T
T <= some r.T
T <= <=1 r-.T
""", True, "only infinite models (o has no predecessor, r injective): consistent"),
    ("infinite-chain-closed", """
nom O
O <= <=0 r-.T
T <= some r.T
T <= <=1 r-.T
T <= <=1 r.T
T <= Na
nom Na
""", False, "every element is o, which needs a successor without a predecessor: inconsistent"),
    ("ge-at-nominal", """
nom O
O <= >=3 r.C
C <= some r-.D
D <= O
T <= <=2 r.C
""", False, "o needs three C successors but has at most two: inconsistent"),
    ("ge-at-nominal-inverse", """
nom O
O <= >=2 r.C
C <= some s.O
O <= <=1 s-.C
anon C
""", False, "two C elements must both be s-predecessors of o, at most one allowed: inconsistent"),
    ("ge-at-nominal-inverse-ok", """
nom O
O <= >=2 r.C
C <= some s.O
O <= <=2 s-.C
anon C
""", True, "two allowed: consistent"),
    ("hs-nn-guess", """
nom O
A <= some r.O
O <= <=2 r-.A
nom P1
nom P2
nom P3
P1 <= A
P2 <= A
P3 <= A
P1 & P2 <= F
P2 & P3 <= F
P1 & P3 <= F
distinct O P1
distinct O P2
distinct O P3
""", False, "three distinct A individuals need o, at most two allowed (NN rule must guess m <= 2)"),
    ("hs-nn-guess-ok", """
nom O
A <= some r.O
O <= <=2 r-.A
nom P1
nom P2
nom P3
P1 <= A
P2 <= A
P3 <= A
P1 & P2 <= F
P2 & P3 <= F
distinct O P1
distinct O P2
distinct O P3
""", True, "P1 and P3 may merge: consistent"),
    ("nn-anon-guess", """
nom O
O <= some s.B
B <= >=3 t.A
A <= some r.O
O <= <=2 r-.A
anon A B
""", False, "three anonymous A elements all r-predecessors of o, at most two: inconsistent"),
    ("nn-anon-guess-ok", """
nom O
O <= some s.B
B <= >=2 t.A
A <= some r.O
O <= <=2 r-.A
anon A B
""", True, "two allowed: consistent"),
    # --- C2a sub-case (no inverse-counted need) ---
    ("c2a-functional", """
nom O
nom P
O <= some r.B
P <= some r.B
T <= <=1 r.T
B <= some r.O
distinct O P
""", True, "functional r, needs towards o are not counted at o: C2a, consistent"),
    ("c2a-functional-clash", """
nom O
O <= some r.B
O <= some r.C
B & C <= F
T <= <=1 r.T
""", False, "functional r with two disjoint successors: inconsistent"),
    # --- small cases that need a promoted (non-nominal) core element ---
    ("small-share", """
nom O
nom P
distinct O P
anon A B
P <= >=2 r.A
A <= some r.B
B <= some r-.O
O <= <=1 r.B
A & B <= F
""", True, "the two A elements share one B element, which is counted at o: core O, P and the B element"),
    ("small-share-clash", """
nom O
nom P
distinct O P
anon A1 A2 B1 B2
P <= some r.A1
P <= some r.A2
A1 <= some r.B1
A2 <= some r.B2
B1 <= B
B2 <= B
B1 & B2 <= F
B <= some r-.O
O <= <=1 r.B
""", False, "the two B elements differ but o has only one B successor: inconsistent"),
    ("small-share-two", """
nom O
nom P
distinct O P
anon A1 A2 B1 B2
P <= some r.A1
P <= some r.A2
A1 <= some r.B1
A2 <= some r.B2
B1 <= B
B2 <= B
B1 & B2 <= F
B <= some r-.O
O <= <=2 r.B
""", True, "two B slots at o: core O, P and both B elements"),
    ("small-level2", """
nom O
anon A B C
O <= some r-.C
C <= >=2 r-.A
A <= some r.B
B <= some r.O
O <= <=1 r-.B
B <= <=1 r-.A
""", False, "one B element (counted at o), both A elements of the C element need it and are counted there: inconsistent"),
    ("small-level2-ok", """
nom O
anon A B C
O <= some r-.C
C <= >=2 r-.A
A <= some r.B
B <= some r.O
O <= <=1 r-.B
B <= <=2 r-.A
""", True, "as small-level2 with room for two A elements at the B element"),
]
