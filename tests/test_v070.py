"""reachmap 0.7.0: parameters per endpoint, OpenAPI, SARIF, --fail-on, stable output."""
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import reachmap as rm  # noqa: E402
from test_reachmap import write  # noqa: E402

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def project(tmp_path):
    tmp_path = tmp_path / "proj"
    write(tmp_path, "api/Users.java", """
package api;
@RestController
@RequestMapping("/users")
public class Users {
    @GetMapping("/{id}")
    public String one(@PathVariable("id") String id, @RequestParam("verbose") String v,
                      @RequestHeader("X-Trace") String t) {
        return Runtime.getRuntime().exec(id).toString();
    }
    @PreAuthorize("hasRole('ADMIN')")
    @PostMapping("/add")
    public String add(@RequestBody String body) { return body; }
}
""")
    write(tmp_path, "web/app.js", """
const express = require('express');
const app = express();
app.post('/login', (req, res) => { res.send(req.body.user + req.query.next + req.cookies.sid); });
""")
    write(tmp_path, "pages/show.php", "<?php\n$f = $_GET['file'];\nreadfile($f);\n")
    return tmp_path


def _p(tmp_path):
    project(tmp_path)
    return tmp_path


def doc_of(tmp_path, *extra):
    out = tmp_path / "out"
    proj = tmp_path / "proj"
    r = subprocess.run([sys.executable, os.path.join(HERE, "reachmap.py"), str(proj), "--out", str(out), "-q",
                        "--baseline", "none", "--no-git", "--formats", "json,sarif,openapi", *extra],
                       capture_output=True, text=True)
    return r, out


def test_params_per_endpoint(tmp_path):
    r, out = doc_of(_p(tmp_path))
    d = json.load(open(out / "reachmap.json"))
    by = {(e["method"], e["path"]): {(p["in"], p["name"]) for p in e["params"]} for e in d["endpoints"]}
    assert {("path", "id"), ("query", "verbose"), ("header", "X-Trace")} <= by[("GET", "/users/{id}")]
    assert ("body", "(whole body)") in by[("POST", "/users/add")]
    assert {("body", "user"), ("query", "next"), ("cookie", "sid")} <= by[("POST", "/login")]
    assert ("query", "file") in next(v for (m, p), v in by.items() if p.endswith("show.php"))


def test_openapi_and_sarif(tmp_path):
    r, out = doc_of(_p(tmp_path))
    oa = json.load(open(out / "reachmap-openapi.json"))
    assert oa["openapi"].startswith("3.")
    op = oa["paths"]["/users/{id}"]["get"]
    assert {(p["in"], p["name"]) for p in op["parameters"]} == {("path", "id"), ("query", "verbose"), ("header", "X-Trace")}
    assert op["x-reachmap-access-check"] == "none" and "command" in op["x-reachmap-dangerous-calls"]
    assert oa["paths"]["/users/add"]["post"]["x-reachmap-access-check"] == "check"
    assert "requestBody" in oa["paths"]["/users/add"]["post"]
    sarif = json.load(open(out / "reachmap.sarif"))
    res = sarif["runs"][0]["results"]
    hit = [x for x in res if x["ruleId"] == "RM001"]
    assert hit and hit[0]["locations"][0]["physicalLocation"]["artifactLocation"]["uri"]
    assert all(x["ruleId"] != "RM001" or "/users/add" not in x["message"]["text"] for x in res)


def test_fail_on_exit_codes(tmp_path):
    p = project(tmp_path)
    r, _ = doc_of(tmp_path, "--fail-on", "unprotected-sink")
    assert r.returncode == 1 and "RM001" in r.stderr
    r, _ = doc_of(tmp_path)
    assert r.returncode == 0
    r, _ = doc_of(tmp_path, "--fail-on", "nonsense")
    assert r.returncode == 2


def test_fail_on_new_unprotected_with_baseline(tmp_path):
    p = project(tmp_path)
    r, out = doc_of(tmp_path)
    base = out / "reachmap.json"
    write(p, "web/more.js", "const express = require('express');\nconst app = express();\n"
                            "app.get('/extra', (req, res) => res.send(req.query.q));\n")
    out2 = tmp_path / "out2"
    r = subprocess.run([sys.executable, os.path.join(HERE, "reachmap.py"), str(p), "--out", str(out2), "-q", "--no-git",
                        "--baseline", str(base), "--formats", "json", "--fail-on", "new-unprotected"],
                       capture_output=True, text=True)
    assert r.returncode == 1 and "/extra" in r.stderr


def test_output_does_not_depend_on_hash_seed(tmp_path):
    p = project(tmp_path)
    docs = []
    for seed in ("1", "2", "3"):
        out = tmp_path / f"o{seed}"
        subprocess.run([sys.executable, os.path.join(HERE, "reachmap.py"), str(p), "--out", str(out), "-q", "--no-git",
                        "--baseline", "none", "--formats", "json"], env={**os.environ, "PYTHONHASHSEED": seed},
                       capture_output=True, check=True)
        d = json.load(open(out / "reachmap.json"))
        docs.append((d["nodes"], d["endpoints"], d["file_edges"]))
    assert docs[0] == docs[1] == docs[2]


def test_report_has_endpoint_details_and_ignores_test_routes(tmp_path):
    p = project(tmp_path)
    write(p, "test/api_test.js", "request(app).get('/only-in-a-test').expect(200);\nconst app = require('../web/app');\n")
    r, out = doc_of(tmp_path, "--formats", "html,json")
    html_ = (out / "reachmap.html").read_text()
    assert "function epDetail" in html_ and "tr[data-ep]" in html_      # lost once in 0.6.0: clicking a row did nothing
    d = json.load(open(out / "reachmap.json"))
    assert not any("only-in-a-test" in e["path"] for e in d["endpoints"])


def test_trace_in_terminal_and_report(tmp_path):
    p = project(tmp_path)
    write(p, "svc/util.py", "def helper(x):\n    return x\n\ndef deep(x):\n    return helper(x)\n")
    write(p, "svc/views.py", "from flask import Flask\nfrom svc.util import deep\napp = Flask(__name__)\n\n"
                             "@app.route('/go')\ndef go():\n    return deep(1)\n")
    r = subprocess.run([sys.executable, os.path.join(HERE, "reachmap.py"), str(p), "--trace", "helper", "--baseline", "none",
                        "--no-git", "-q", "--out", str(tmp_path / "o")], capture_output=True, text=True)
    assert r.returncode == 0
    up = r.stdout.split("Called from:")[1].split("Calls:")[0]
    assert "deep" in up and "go" in up and "entry point" in up        # helper <- deep <- go (entry)
    r2 = subprocess.run([sys.executable, os.path.join(HERE, "reachmap.py"), str(p), "--trace", "nonexistent_fn_xyz",
                         "--baseline", "none", "--no-git", "-q", "--out", str(tmp_path / "o")], capture_output=True, text=True)
    assert "no function matches" in r2.stdout
    r3, out = doc_of(tmp_path, "--formats", "html,json")
    html_ = (out / "reachmap.html").read_text()
    assert 'id="trview"' in html_ and "function trRender" in html_ and "data-trace" in html_


def test_source_in_report(tmp_path):
    import base64
    import re
    import zlib
    p = project(tmp_path)
    write(p, "test/helper_test.js", "const SECRET_IN_TEST = 1;\n")
    r, out = doc_of(tmp_path, "--formats", "html")
    html_ = (out / "reachmap.html").read_text()
    m = re.search(r"const SRC=(\{.*?\}),SRCINFO=(\{.*?\}),SRCC", html_, re.S)
    src, info = json.loads(m.group(1)), json.loads(m.group(2))
    assert info["mode"] == "production" and "pages/show.php" in src and "test/helper_test.js" not in src
    assert "readfile($f);" in zlib.decompress(base64.b64decode(src["pages/show.php"])).decode()
    for needle in ("function openCode", "function followLayers", 'id="codepane"', "data-follow"):
        assert needle in html_
    r, out = doc_of(tmp_path, "--formats", "html", "--source", "all")
    m = re.search(r"const SRC=(\{.*?\}),SRCINFO", (out / "reachmap.html").read_text(), re.S)
    assert "test/helper_test.js" in json.loads(m.group(1))
    r, out = doc_of(tmp_path, "--formats", "html", "--source", "none")
    m = re.search(r"const SRC=(\{.*?\}),SRCINFO", (out / "reachmap.html").read_text(), re.S)
    assert json.loads(m.group(1)) == {}
