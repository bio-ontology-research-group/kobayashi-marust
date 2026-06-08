import sys, json
sys.path.insert(0, "py")
import frontend, cb_to_ht
ofn = sys.argv[1]
clauses = frontend.ofn_to_clauses(ofn)
rbox = frontend.ofn_rbox(ofn)
tin = cb_to_ht.convert(clauses, rbox)
json.dump(tin, sys.stdout)
