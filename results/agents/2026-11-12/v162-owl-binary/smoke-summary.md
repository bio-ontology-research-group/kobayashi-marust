| kind | inputs | km ok | agreed | disagreed | declined | no check line |
|---|---:|---:|---:|---:|---:|---:|
| alc | 8 | 8 | 1 | 0 | 7 | 0 |
| el | 15 | 15 | 15 | 0 | 0 | 0 |
| non-f | 5 | 5 | 0 | 0 | 5 | 0 |
| other-f | 2 | 2 | 0 | 0 | 2 | 0 |
| all | 30 | 30 | 16 | 0 | 14 | 0 |

Procedures of agreements: {'el': 15, 'alc': 1}

| decline reason | inputs |
|---|---:|
| parse rejected: out of fragment: DataPropertyAssertion (ABox assertion) | 2 |
| alc budget: 18 concept names | 1 |
| alc budget: 31 concept names | 1 |
| alc budget: 46 concept names | 1 |
| alc budget: 102 concept names | 1 |
| alc budget: 4105 concept names | 1 |
| alc budget: 10338 concept names | 1 |
| alc budget: 13799 concept names | 1 |
| not recognised: neither OWL EL (first: EquivalentClasses) nor OWL ALC (first: EquivalentClasses) | 1 |
| not recognised: neither OWL EL (first: ObjectPropertyRange) nor OWL ALC (first: SubObjectPropertyOf) | 1 |
| parse rejected: out of fragment: ObjectPropertyAssertion (ABox assertion) | 1 |
| parse rejected: out of fragment: DataMinCardinality (data construct) | 1 |
| parse rejected: out of fragment: ClassAssertion (ABox assertion) | 1 |

| input | kind | MB | km status | km wall s | check | procedure | checker ms | phases (ms) |
|---|---|---:|---|---:|---|---|---:|---|
| clause_or_definer_fallback.ofn | alc | 0.0 | ok | 0.120 | agreed | alc | 101 | read:0,parse:0,names:0,translate:0,translate:0,types:2,rows:0,readout:0,output:0,total:2 |
| min_copy_successor_insufficient.ofn | alc | 0.0 | ok | 0.099 | declined | - | 81 | read:0,parse:0,names:0,translate:0,translate:0,total:0 |
| g203.ofn | alc | 0.0 | ok | 0.152 | declined | - | 122 | read:0,parse:0,names:0,translate:0,translate:0,total:0 |
| g107.ofn | alc | 0.0 | ok | 0.154 | declined | - | 122 | read:0,parse:0,names:0,translate:0,translate:0,total:0 |
| ore_ont_3842.owl | alc | 0.0 | ok | 0.117 | declined | - | 81 | read:0,parse:1,names:0,translate:0,translate:0,total:2 |
| ore_ont_15108.owl | alc | 0.9 | ok | 0.543 | declined | - | 123 | read:8,parse:33,names:1,translate:0,translate:5,total:51 |
| ore_ont_33.owl | alc | 2.0 | ok | 0.778 | declined | - | 184 | read:10,parse:55,names:5,translate:0,translate:12,total:91 |
| ore_ont_14066.owl | alc | 2.2 | ok | 1.219 | declined | - | 205 | read:20,parse:69,names:4,translate:0,translate:13,total:115 |
| automatic_el_fallback.ofn | el | 0.0 | ok | 0.099 | agreed | el | 81 | read:0,parse:0,names:0,translate:0,closure:0,rows:0,readout:0,output:0,total:0 |
| ore_ont_10174.owl | el | 0.0 | ok | 0.121 | agreed | el | 82 | read:0,parse:1,names:0,translate:0,closure:2,rows:0,readout:0,output:0,total:6 |
| ore_ont_9031.owl | el | 0.0 | ok | 0.152 | agreed | el | 122 | read:0,parse:2,names:0,translate:0,closure:6,rows:0,readout:0,output:0,total:11 |
| ore_ont_5742.owl | el | 0.0 | ok | 0.105 | agreed | el | 81 | read:0,parse:0,names:0,translate:0,closure:1,rows:0,readout:0,output:0,total:3 |
| ore_ont_4767.owl | el | 0.1 | ok | 0.129 | agreed | el | 101 | read:0,parse:2,names:0,translate:0,closure:6,rows:0,readout:0,output:0,total:11 |
| ore_ont_13301.owl | el | 0.1 | ok | 0.185 | agreed | el | 122 | read:0,parse:2,names:0,translate:0,closure:27,rows:5,readout:0,output:2,total:40 |
| ore_ont_3832.owl | el | 0.1 | ok | 0.137 | agreed | el | 101 | read:1,parse:3,names:0,translate:0,closure:9,rows:2,readout:0,output:1,total:18 |
| ore_ont_2713.owl | el | 0.1 | ok | 0.181 | agreed | el | 142 | read:1,parse:4,names:0,translate:0,closure:11,rows:1,readout:0,output:1,total:22 |
| ore_ont_16312.owl | el | 0.2 | ok | 0.200 | agreed | el | 142 | read:1,parse:10,names:1,translate:1,closure:36,rows:4,readout:0,output:1,total:60 |
| ore_ont_10160.owl | el | 0.4 | ok | 0.419 | agreed | el | 262 | read:3,parse:19,names:1,translate:3,closure:126,rows:8,readout:0,output:2,total:168 |
| ore_ont_6905.owl | el | 0.8 | ok | 0.615 | agreed | el | 404 | read:6,parse:30,names:2,translate:4,closure:197,rows:35,readout:2,output:10,total:293 |
| ore_ont_9020.owl | el | 1.6 | ok | 0.413 | agreed | el | 163 | read:7,parse:28,names:2,translate:5,closure:28,rows:0,readout:0,output:0,total:78 |
| ore_ont_14280.owl | el | 2.3 | ok | 2.940 | agreed | el | 2437 | read:12,parse:55,names:5,translate:11,closure:2072,rows:157,readout:6,output:13,total:2347 |
| ore_ont_16746.owl | el | 3.7 | ok | 23.132 | agreed | el | 22277 | read:17,parse:81,names:7,translate:14,closure:20807,rows:1200,readout:10,output:21,total:22176 |
| ore_ont_7831.owl | el | 6.6 | ok | 2.291 | agreed | el | 1353 | read:49,parse:157,names:12,translate:34,closure:875,rows:65,readout:3,output:14,total:1239 |
| m7004.ofn | non-f | 0.0 | ok | 0.143 | declined | - | 102 | read:0,parse:0,total:0 |
| m7066.ofn | non-f | 0.0 | ok | 0.179 | declined | - | 81 | read:0,parse:0,total:0 |
| m7146.ofn | non-f | 0.0 | ok | 0.104 | declined | - | 81 | read:0,parse:0,total:0 |
| m2092.ofn | non-f | 0.0 | ok | 0.183 | declined | - | 122 | read:0,parse:0,total:0 |
| ore_ont_13398.owl | non-f | 0.1 | ok | 0.118 | declined | - | 82 | read:0,parse:2,total:3 |
| inverse_forall_top_label.ofn | other-f | 0.0 | ok | 0.122 | declined | - | 101 | read:0,parse:0,names:0,translate:0,translate:0,total:0 |
| ore_ont_8949.owl | other-f | 0.1 | ok | 0.166 | declined | - | 122 | read:0,parse:3,names:0,translate:0,translate:0,total:4 |
