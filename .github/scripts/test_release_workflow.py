"""Execute proposed workflow shell blocks with a local, stateful gh stub."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest

WORKFLOW = (Path(__file__).parent.parent / "workflows" / "release.yml").read_text()


def script(step):
    block = WORKFLOW.split("      - name: " + step + "\n", 1)[1].split("      - name:", 1)[0]
    return textwrap.dedent(block.split("        run: |\n", 1)[1])


GH = r'''#!/usr/bin/env python3
import json,os,pathlib,sys
p=pathlib.Path('state.json');s=json.loads(p.read_text());args=sys.argv[1:]
s['calls'].append(args)
def save():p.write_text(json.dumps(s))
assert args[0]=='release'
cmd=args[1]
if cmd=='view':
 save()
 if s['release'] is None:sys.exit(1)
 if '--json' in args:print(len(s['release']['assets']))
elif cmd=='create':
 assert s['release'] is None and '--verify-tag' in args
 assert pathlib.Path('release-notes.md').read_text().startswith('## [')
 s['release']={'draft':'--draft' in args,'assets':[]};save()
elif cmd=='upload':
 assert s['release']['draft'] and not s['release']['assets'] and '--clobber' not in args
 files=[x for x in args if x.startswith('release-assets/')]
 assert len(files)==6
 if os.environ.get('FAIL_UPLOAD'):
  s['release']['assets']=files[:1];save();sys.exit(1)
 s['release']['assets']=files;save()
elif cmd=='edit':
 assert s['release'] is not None
 if '--draft=false' in args:
  assert len(s['release']['assets'])==6
  s['release']['draft']=False
 save()
else:raise AssertionError(cmd)
'''


class DraftPublicationTests(unittest.TestCase):
    def run_flow(self, existing=None, fail_upload=False, tag="v1.5.1"):
        with tempfile.TemporaryDirectory(prefix="km-release-flow-") as temp:
            p = Path(temp); (p / "gh").write_text(GH); (p / "gh").chmod(0o755)
            (p / "state.json").write_text(json.dumps({"release": existing, "calls": []}))
            (p / "CHANGELOG.md").write_text("## [1.5.1]\nNew notes\n## [1.5.0]\nOld notes\n")
            env = dict(os.environ, PATH=temp + os.pathsep + os.environ["PATH"],
                       RELEASE_TAG=tag, GITHUB_REPOSITORY="example/repo")
            if fail_upload: env["FAIL_UPLOAD"] = "1"
            first = subprocess.run(["bash", "-e", "-o", "pipefail", "-c",
                                    script("Publish GitHub release")], cwd=temp, env=env,
                                   capture_output=True, text=True)
            second = None
            if first.returncode == 0 and tag == "v1.5.1":
                second = subprocess.run(["bash", "-e", "-o", "pipefail", "-c",
                                         script("Upload verified release assets and publish draft")],
                                        cwd=temp, env=env, capture_output=True, text=True)
            return first.returncode, second.returncode if second else None, json.loads((p / "state.json").read_text())

    def test_fresh_release_is_draft_until_all_assets_succeed(self):
        first, second, state = self.run_flow()
        self.assertEqual((first, second), (0, 0))
        self.assertFalse(state["release"]["draft"])
        self.assertEqual(len(state["release"]["assets"]), 6)
        create = next(args for args in state["calls"] if args[1] == "create")
        self.assertIn("--draft", create)
        self.assertEqual(state["calls"][-1][-1], "--draft=false")

    def test_partial_upload_failure_leaves_unpublished_draft(self):
        first, second, state = self.run_flow(fail_upload=True)
        self.assertEqual((first, second), (0, 1))
        self.assertTrue(state["release"]["draft"])
        self.assertEqual(len(state["release"]["assets"]), 1)
        self.assertFalse(any(args[1] == "edit" for args in state["calls"]))

    def test_existing_published_release_fails_without_any_mutation(self):
        existing = {"draft": False, "assets": ["prior"]}
        first, second, state = self.run_flow(existing=existing)
        self.assertEqual((first, second), (1, None))
        self.assertEqual(state["release"], existing)
        self.assertTrue(all(args[1] == "view" for args in state["calls"]))

    def test_existing_draft_fails_without_replacing_partial_assets(self):
        existing = {"draft": True, "assets": ["prior"]}
        first, second, state = self.run_flow(existing=existing)
        self.assertEqual((first, second), (1, None))
        self.assertEqual(state["release"], existing)

    def test_historical_tag_keeps_existing_notes_edit_flow(self):
        existing = {"draft": False, "assets": ["historical"]}
        first, second, state = self.run_flow(existing=existing, tag="v1.5.0")
        self.assertEqual((first, second), (0, None))
        self.assertEqual(state["release"], existing)
        self.assertTrue(any(args[1] == "edit" and "--notes-file" in args for args in state["calls"]))


if __name__ == "__main__":
    unittest.main(verbosity=2)
