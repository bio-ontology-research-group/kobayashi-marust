import random, sys
random.seed(11)
NC, NI, NALL, NEX, NROLE = map(int, sys.argv[1:6])
out = open(sys.argv[6], 'w')
out.write('Prefix(:=<http://syn/>)\nOntology(<http://syn/o>\n')
roles = ['r%d' % i for i in range(20)]
for i in range(1, NC):
    out.write('SubClassOf(:C%d :C%d)\n' % (i, (i - 1) // 4))
for _ in range(NALL):
    a = random.randrange(1000, NC); b = random.randrange(1, 300)
    out.write('SubClassOf(:C%d ObjectAllValuesFrom(:%s :C%d))\n' % (a, random.choice(roles), b))
for _ in range(NEX):
    a = random.randrange(1000, NC); b = random.randrange(300, 1000)
    out.write('SubClassOf(:C%d ObjectSomeValuesFrom(:%s :C%d))\n' % (a, random.choice(roles), b))
for i in range(NI):
    out.write('ClassAssertion(:C%d :i%d)\n' % (random.randrange(NC), i))
for _ in range(NROLE):
    out.write('ObjectPropertyAssertion(:%s :i%d :i%d)\n' % (random.choice(roles), random.randrange(NI), random.randrange(NI)))
out.write(')\n')
