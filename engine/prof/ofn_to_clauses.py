import sys, json
sys.path.insert(0, "py")
import frontend
print(json.dumps({"clauses": frontend.ofn_to_clauses(sys.argv[1])}))
