# ore_ont_3794 (OpenGALEN7 full with property chains): KM against Konclude

Both the v1.5.3 PGO run (combined-v150-54539952, 2026-10-25) and the v1.5.4
held-out runs (arrays 54796887 and 54796888, 2026-10-29) mark this input as
a taxonomy disagreement with Konclude v0.7.0-1138, the only reference with
an answer for it; the paired analysis therefore lists it as "wrong" under
both policies. The two KM releases give the identical canonical taxonomy
(880,582 closure edges, same node fingerprints). Against Konclude's closure,
KM has ten extra subsumptions and nothing is missing:

- DividedRightHeartAtrium, DoubleOutletHeartVentricle,
  DoubleOutletLeftVentricle, DoubleOutletRightVentricle, HoodedPrepuce,
  IncompetentAnalSphincter, IndeterminateVentricle, UniventricularHeart
  ⊑ HollowPathologicalBodyPart;
- IneffectiveConceptionSymptom ⊑ PathologicalBodyProcessSymptom and
  ⊑ PathologicalBodyProcesswhichplaysConsultationRoleSymptomRole.

HermiT 1.4.3.456 (OWLAPI 4.5.29, `Entail.java`, entailment queries on the
original `ore_ont_3794.owl`, 44,956 logical axioms, consistent) confirms
each of them as entailed (`hermit-entail.txt`). KM's answer is therefore
exact on this input and Konclude's is incomplete; the input stays outside
the "verified" count because the audit's reference set has no HermiT
answer for it, and it is not a KM defect.
