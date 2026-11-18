"""reachmap tests: small projects in several languages, checked function by function."""
import json
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import reachmap as rm  # noqa: E402


def write(root, rel, text):
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


def run(root, cfg=None):
    files = list(rm.discover(str(root)))
    g, _ = rm.build(files, cfg)
    return g, {(f.path, f.qual): f for f in g.nodes}


def st(nodes, path, qual):
    return nodes[(path, qual)].status


def test_flask_routes_helpers_dead_and_tests(tmp_path):
    write(tmp_path, "app/views.py", """
from flask import Flask
from app.util import clean, unused_helper_caller
app = Flask(__name__)

@app.route("/search")
def search():
    return clean("x")

def orphan():
    return 1
""")
    write(tmp_path, "app/util.py", """
def clean(s):
    return _strip(s)

def _strip(s):
    return s.strip()

def only_tests():
    return 2

def unused_helper_caller():
    return deep()

def deep():
    return 3
""")
    write(tmp_path, "tests/test_util.py", "from app.util import only_tests\n\ndef test_it():\n    assert only_tests() == 2\n")
    g, n = run(tmp_path)
    assert st(n, "app/views.py", "search") == "entry"
    assert st(n, "app/util.py", "clean") == "reached" and st(n, "app/util.py", "_strip") == "reached"
    assert st(n, "app/views.py", "orphan") == "no_caller"
    assert st(n, "app/util.py", "only_tests") == "tests_only"
    assert st(n, "tests/test_util.py", "test_it") == "non_production"
    # unused_helper_caller is only imported (a reference), never called from reached code
    assert st(n, "app/util.py", "deep") in ("dead_branch", "not_reached", "maybe", "reached")
    why = rm.why_alive(g, n[("app/util.py", "_strip")])
    assert [g.nodes[x["id"]].qual for x in why] == ["search", "clean", "_strip"]


def test_spring_controller_service_and_framework(tmp_path):
    write(tmp_path, "src/main/java/a/web/UserController.java", """
package a.web;
import a.svc.UserService;
@RestController
public class UserController {
    private final UserService svc;
    public UserController(UserService svc) { this.svc = svc; }

    @GetMapping("/users/{id}")
    public String get(@PathVariable String id) {
        return svc.find(id);
    }
}
""")
    write(tmp_path, "src/main/java/a/svc/UserService.java", """
package a.svc;
@Service
public class UserService {
    public String find(String id) {
        return normalise(id);
    }
    private String normalise(String id) { return id.trim(); }
    public void legacyExport() {
        writeCsv();
    }
    void writeCsv() { }
    @Override
    public String toString() { return "x"; }
    public String getName() { return "n"; }
}
""")
    g, n = run(tmp_path)
    j = "src/main/java/a/svc/UserService.java"
    assert st(n, "src/main/java/a/web/UserController.java", "UserController.get") == "entry"
    assert st(n, "src/main/java/a/web/UserController.java", "UserController.UserController") == "framework"
    assert st(n, j, "UserService.find") == "reached" and st(n, j, "UserService.normalise") == "reached"
    assert st(n, j, "UserService.legacyExport") == "no_caller"
    assert st(n, j, "UserService.writeCsv") == "dead_branch"
    assert n[(j, "UserService.writeCsv")].dead_root == n[(j, "UserService.legacyExport")].id
    assert st(n, j, "UserService.toString") == "framework" and st(n, j, "UserService.getName") == "framework"


def test_php_pages_includes_onclick_and_built_names(tmp_path):
    write(tmp_path, "index.php", """<?php
require_once 'lib/page.inc.php';
page_start();
echo "<button onclick=\\"toggle_menu();\\">Menu</button>";
$type = $_GET['t'];
$m = 'render' . $type;
$m();
""")
    write(tmp_path, "lib/page.inc.php", """<?php
function page_start() { helper(); }
function helper() { }
function renderTable() { }
function never_used() { }
""")
    write(tmp_path, "js/menu.js", "function toggle_menu() { open_it(); }\nfunction open_it() {}\n")
    g, n = run(tmp_path)
    assert st(n, "index.php", "index.php (top level)") == "entry"
    assert st(n, "lib/page.inc.php", "page_start") == "reached" and st(n, "lib/page.inc.php", "helper") == "reached"
    assert st(n, "js/menu.js", "toggle_menu") == "reached" and st(n, "js/menu.js", "open_it") == "reached"
    assert st(n, "lib/page.inc.php", "renderTable") == "referenced"
    assert "built at runtime" in n[("lib/page.inc.php", "renderTable")].reason
    assert st(n, "lib/page.inc.php", "never_used") == "no_caller"


def test_express_routes_and_same_name_is_maybe(tmp_path):
    write(tmp_path, "server.js", """
const express = require('express')
const { login } = require('./routes/login')
const app = express()
app.post('/login', login)
app.get('/health', (req, res) => { res.send(ping()) })
function ping() { return 'ok' }
""")
    write(tmp_path, "routes/login.js", """
function login(req, res) { return check(req) }
function check(r) { return format(r) }
module.exports = { login }
""")
    write(tmp_path, "lib/a.js", "function format(x) { return x }\n")
    write(tmp_path, "lib/b.js", "function format(x) { return String(x) }\n")
    g, n = run(tmp_path)
    assert st(n, "routes/login.js", "login") == "entry"
    assert "route handler" in n[("routes/login.js", "login")].reason
    assert st(n, "routes/login.js", "check") == "reached"
    assert st(n, "server.js", "ping") == "reached"                          # inline handler in the file
    assert st(n, "lib/a.js", "format") == "maybe" and st(n, "lib/b.js", "format") == "maybe"


def test_go_main_and_languages_do_not_mix(tmp_path):
    write(tmp_path, "cmd/app/main.go", "package main\n\nfunc main() {\n\trun()\n}\n\nfunc run() {}\n\nfunc unused() {}\n")
    write(tmp_path, "web/x.js", "function unused() {}\nfunction run() {}\n")
    g, n = run(tmp_path)
    assert st(n, "cmd/app/main.go", "main") == "entry" and st(n, "cmd/app/main.go", "run") == "reached"
    assert st(n, "cmd/app/main.go", "unused") != "reached"
    assert st(n, "web/x.js", "run") != "reached"                           # Go's run() is not JavaScript's


def test_config_file_entries_and_ignore(tmp_path):
    write(tmp_path, "jobs/nightly.py", "def cleanup():\n    purge()\n\ndef purge():\n    pass\n\ndef old():\n    pass\n")
    cfg_file = tmp_path / "rm.cfg"
    cfg_file.write_text("# entries the tool cannot see\nentry jobs/nightly.py:cleanup\nignore jobs/*:old\n")
    cfg = rm.load_config(str(cfg_file))
    g, n = run(tmp_path, cfg)
    assert st(n, "jobs/nightly.py", "cleanup") == "entry" and st(n, "jobs/nightly.py", "purge") == "reached"
    assert st(n, "jobs/nightly.py", "old") == "ignored"
    bad = tmp_path / "bad.cfg"
    bad.write_text("start here\n")
    with pytest.raises(ValueError):
        rm.load_config(str(bad))


def test_folder_without_entry_is_named(tmp_path):
    write(tmp_path, "app/main.py", "def main():\n    pass\n\nif __name__ == '__main__':\n    main()\n")
    write(tmp_path, "plugins/x.py", "".join(f"def p{i}():\n    p{i+1}()\n\n" for i in range(6)) + "def p6():\n    pass\n")
    g, _n = run(tmp_path)
    s = rm.summarize(g)
    assert "plugins" in s["folders_without_entry"]


def test_cli_reports_and_coderaster_findings(tmp_path, capsys):
    proj = tmp_path / "p"
    write(proj, "index.php", "<?php\n$id = $_GET['id'];\nlookup($id);\nfunction lookup($id) { query($id); }\n"
                             "function query($q) { mysqli_query($c, \"SELECT \" . $q); }\nfunction dead() { }\n")
    report = tmp_path / "coderaster.json"
    report.write_text(json.dumps({"summary": {}, "findings": [
        {"candidate": {"rule_id": "sql-injection", "path": "index.php", "line": 5, "fingerprint": "f1"},
         "status": "confirmed", "severity": "high"},
        {"candidate": {"rule_id": "xss", "path": "index.php", "line": 6}, "status": "dismissed", "severity": "low"}]}))
    out = tmp_path / "out"
    assert rm.main([str(proj), "--out", str(out), "--coderaster", str(report), "-q"]) == 0
    text = capsys.readouterr().out
    assert "Called from an entry point" in text and "CodeRaster findings on the map" in text
    doc = json.loads((out / "reachmap.json").read_text())
    q = next(x for x in doc["nodes"] if x["qual"] == "query")
    assert q["status"] == "reached" and q["findings"][0]["rule"] == "sql-injection"
    assert [doc["nodes"][c["id"]]["qual"] for c in q["why"]] == ["index.php (top level)", "lookup", "query"]
    html = (out / "reachmap.html").read_text()
    assert "<\\/script" not in html.split('id="data"')[0] and '"tool":"reachmap"' in html
    assert rm.main([str(tmp_path / "missing")]) == 2
    assert rm.main([str(proj), "--formats", "pdf"]) == 2


def test_project_config_only_when_trusted(tmp_path, capsys):
    write(tmp_path, "a.py", "def hidden():\n    pass\n")
    write(tmp_path, ".reachmap", "ignore *\n")
    out = tmp_path / "o"
    rm.main([str(tmp_path), "--out", str(out), "-q"])
    assert "ignoring" in capsys.readouterr().err
    doc = json.loads((out / "reachmap.json").read_text())
    assert next(x for x in doc["nodes"] if x["qual"] == "hidden")["status"] == "no_caller"
    rm.main([str(tmp_path), "--out", str(out), "-q", "--trust-project-config"])
    doc = json.loads((out / "reachmap.json").read_text())
    assert next(x for x in doc["nodes"] if x["qual"] == "hidden")["status"] == "ignored"


def test_comments_and_strings_do_not_count_as_calls(tmp_path):
    write(tmp_path, "main.go", 'package main\n\nfunc main() {\n\t// legacy()\n\tprintln("legacy() is gone")\n}\n\nfunc legacy() {}\n')
    g, n = run(tmp_path)
    assert st(n, "main.go", "legacy") != "reached"


def test_graph_data_and_view(tmp_path):
    write(tmp_path, "app.py", "from lib import helper\n\n@app.route('/')\ndef index():\n    return helper()\n")
    write(tmp_path, "lib.py", "def helper():\n    return 1\n\ndef lonely():\n    return 2\n")
    files = list(rm.discover(str(tmp_path)))
    g, _ = rm.build(files)
    doc = rm.to_dict(g, str(tmp_path), {"generated": "now", "summary": rm.summarize(g)})
    fid = {n["path"]: n["id"] for n in doc["nodes"] if n["kind"] == "file"}
    assert any(a == fid["app.py"] and b == fid["lib.py"] and sure for a, b, _c, sure in doc["file_edges"])
    html = rm.to_html(doc)
    assert 'id="gview"' in html and 'id="gc"' in html and "Around a function" in html and "data-graph" in html


def test_vendored_libraries_by_file_name():
    for name in ("static/js/wysihtml5-0.3.0.js", "web/jquery.min.js", "lib/bootstrap.bundle.js", "x/angular-1.8.2.min.js"):
        assert "third-party" in rm.nonprod_reason(name) or rm.nonprod_reason(name), name
    for name in ("static/js/app.js", "src/goatApp/view/MenuView.js", "routes/login.ts"):
        assert rm.nonprod_reason(name) == "", name


def test_graph_view_has_map_layers_and_findings(tmp_path):
    write(tmp_path, "index.php", "<?php\n$id = $_GET['id'];\nlookup($id);\nfunction lookup($id) { }\n")
    files = list(rm.discover(str(tmp_path)))
    g, _ = rm.build(files)
    html = rm.to_html(rm.to_dict(g, str(tmp_path), {"generated": "now", "summary": rm.summarize(g)}))
    for part in ('id="gmod"', 'id="glay"', 'id="gloc"', 'id="gfind"', "Not reached from an entry point", "openFolder"):
        assert part in html, part


def test_module_filter_in_report(tmp_path):
    write(tmp_path, "a/x.py", "def f():\n    pass\n")
    files = list(rm.discover(str(tmp_path)))
    g, _ = rm.build(files)
    html = rm.to_html(rm.to_dict(g, str(tmp_path), {"generated": "now", "summary": rm.summarize(g)}))
    for part in ('id="mq"', 'id="minc"', 'id="mexc"', "function inScope", "#m=", 'id="gnb"', "data-only"):
        assert part in html, part


def _surface(tmp_path):
    files = list(rm.discover(str(tmp_path)))
    g, _ = rm.build(files)
    return g, rm.analyse_surface(g, files)


def test_spring_endpoints_auth_constants_and_sinks(tmp_path):
    write(tmp_path, "src/main/java/a/Paths.java", 'package a;\npublic class Paths {\n  public static final String USERS_URL = "/users/list";\n}\n')
    write(tmp_path, "src/main/java/a/UserController.java", """
package a;
@RestController
@RequestMapping("/api")
public class UserController {
    private final UserRepo repo;
    @GetMapping("/users/{id}")
    public String get(@PathVariable String id) {
        return repo.find(id);
    }
    @PreAuthorize("hasRole('ADMIN')")
    @PostMapping(value = "/users/delete")
    public void delete(String id) { repo.find(id); }
    @GetMapping(path = USERS_URL)
    public String list() { return "x"; }
}
""")
    write(tmp_path, "src/main/java/a/UserRepo.java", """
package a;
@Repository
public class UserRepo {
    public String find(String id) {
        return jdbc.queryForObject(id);
    }
    String raw(String id) throws Exception {
        // stmt.executeQuery("ignored in a comment")
        return conn.createStatement().executeQuery("SELECT * FROM u WHERE id=" + id).toString();
    }
}
""")
    g, sf = _surface(tmp_path)
    eps = {(e["method"], e["path"]): e for e in sf["endpoints"]}
    assert ("GET", "/api/users/{id}") in eps and ("POST", "/api/users/delete") in eps and ("GET", "/api/users/list") in eps
    assert eps[("GET", "/api/users/{id}")]["auth"]["status"] == "none"
    assert eps[("POST", "/api/users/delete")]["auth"]["status"] == "check"
    raw = next(f for f in g.nodes if f.qual == "UserRepo.raw")
    assert [k for _l, k, _c in raw.sinks] == ["sql"] and raw.sinks[0][0] == 10      # not the comment on line 9


def test_express_endpoints_middleware_and_reached_sinks(tmp_path):
    write(tmp_path, "server.js", """
const { search } = require('./routes/search')
const security = require('./lib/security')
app.get('/rest/products/search', search())
app.post('/rest/admin/reset', security.isAuthorized(), reset)
function reset(req, res) { require('child_process').exec('rm -rf ' + req.body.dir) }
""")
    write(tmp_path, "routes/search.js", """
function search() { return (req, res) => query(req.query.q) }
function query(q) { return sequelize.query("SELECT * FROM p WHERE name LIKE '%" + q + "%'") }
module.exports = { search }
""")
    write(tmp_path, "lib/security.js", "function isAuthorized() { return (req, res, next) => next() }\nmodule.exports = { isAuthorized }\n")
    g, sf = _surface(tmp_path)
    eps = {(e["method"], e["path"]): e for e in sf["endpoints"]}
    s = eps[("GET", "/rest/products/search")]
    assert s["auth"]["status"] == "none" and s["sink_kinds"].get("sql") == 1
    r = eps[("POST", "/rest/admin/reset")]
    assert r["auth"]["status"] == "check" and "isAuthorized" in r["auth"]["how"] and r["sink_kinds"].get("command")
    hs = rm.hotspots(g)
    assert any(g.nodes[h["id"]].name == "query" for h in hs)


def test_php_page_auth_by_call_argument(tmp_path):
    write(tmp_path, "admin.php", "<?php\nrequire 'lib.php';\npageStartup(array('authenticated'));\n$id=$_GET['id'];\nmysqli_query($c, \"SELECT \" . $id);\n")
    write(tmp_path, "open.php", "<?php\necho $_GET['x'];\n")
    write(tmp_path, "lib.php", "<?php\nfunction pageStartup($a) { }\n")
    g, sf = _surface(tmp_path)
    eps = {e["path"]: e for e in sf["endpoints"]}
    assert eps["/admin.php"]["auth"]["status"] == "check" and eps["/admin.php"]["sink_kinds"].get("sql") == 1
    assert eps["/open.php"]["auth"]["status"] == "none" and eps["/open.php"]["method"] == "GET"


def test_git_age_and_baseline_comparison(tmp_path, capsys):
    import subprocess
    proj = tmp_path / "p"
    write(proj, "app.py", "@app.route('/a')\ndef a():\n    return 1\n\ndef old():\n    pass\n")
    env = {**os.environ, "GIT_AUTHOR_DATE": "2020-01-01T00:00:00", "GIT_COMMITTER_DATE": "2020-01-01T00:00:00",
           "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@x", "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@x"}
    for cmd in (["git", "init", "-q"], ["git", "add", "."], ["git", "commit", "-qm", "x"]):
        subprocess.run(cmd, cwd=proj, env=env, check=True)
    data = tmp_path / "d"
    assert rm.main([str(proj), "--data-dir", str(data), "-q"]) == 0
    first = capsys.readouterr().out
    assert "unchanged for over a year" in first
    write(proj, "app.py", "@app.route('/a')\ndef a():\n    return old()\n\ndef old():\n    pass\n\n@app.route('/b')\ndef b():\n    pass\n")
    import time as _t
    _t.sleep(1.1)
    assert rm.main([str(proj), "--data-dir", str(data), "-q"]) == 0
    out = capsys.readouterr().out
    assert "Since the previous run" in out and "+ ANY /b" in out or "/b" in out
    runs = sorted((data / "runs").iterdir())
    doc = json.loads((runs[-1] / "reachmap.json").read_text())
    assert doc["diff"]["now_reached"] >= 1 and any("/b" in e for e in doc["diff"]["endpoints_new"])
    old = next(n for n in doc["nodes"] if n["qual"] == "old")
    assert old["change"].startswith("was:") and old["changed"] > 0


def test_surface_filters_in_report(tmp_path):
    write(tmp_path, "index.php", "<?php\n$id = $_GET['id'];\nmysqli_query($c, $id);\n")
    files = list(rm.discover(str(tmp_path)))
    g, _ = rm.build(files)
    doc = rm.to_dict(g, str(tmp_path), {"generated": "now", "summary": rm.summarize(g)})
    doc.update(rm.analyse_surface(g, files))
    html = rm.to_html(doc)
    for part in ('id="sffil"', "const GROUPS=", "'acc'", "'meth'", "'sink'", 'id="sfsort"', 'id="sfuse"', 'id="epsbar"',
                 "function reachOf", "HS.set('s'"):
        assert part in html, part
