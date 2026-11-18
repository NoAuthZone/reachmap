#!/usr/bin/env python3
"""reachmap: which modules and functions of a code base are called, and which are not.

A map for reviewing large projects: where the entry points are (routes, pages, main, scheduled jobs), what is
called from them, what only tests call, and what nothing calls. No model, no network, no dependencies.

How it works
  1. Find every function and method (Python with the built-in parser, all other languages with patterns).
  2. Find every call and every reference by name (callbacks, method references, strings, templates, config).
  3. Link each call to a definition. Same file or an imported file counts as sure; a name defined in several
     places is linked to all of them as "maybe".
  4. Mark the roots: entry points (an outsider can trigger them) and framework code (run by the framework).
  5. Walk the graph from the roots and give every function a status and the reason for it, including the
     chain of calls from an entry point ("why is this alive").

It reads text, not types. Calls through variables of an interface type, reflection, dependency injection by
type and generated code are only seen when the name of the function appears somewhere. "No caller found" is
a lead to check, not proof that the code is dead.
"""
from __future__ import annotations

import argparse
import zlib
import base64
import ast
import bisect
import datetime as dt
import fnmatch
import html
import json
import os
import re
import sys
import time
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field

VERSION = "0.8.0"

# --------------------------------------------------------------------------------------------------------------
# Files
# --------------------------------------------------------------------------------------------------------------
CODE = {".py": "python", ".pyw": "python", ".java": "java", ".kt": "kotlin", ".kts": "kotlin", ".scala": "scala",
        ".js": "javascript", ".jsx": "javascript", ".mjs": "javascript", ".cjs": "javascript",
        ".ts": "typescript", ".tsx": "typescript", ".mts": "typescript", ".cts": "typescript",
        ".vue": "vue", ".svelte": "svelte", ".go": "go", ".rb": "ruby", ".php": "php", ".phtml": "php",
        ".inc": "php", ".cs": "csharp", ".rs": "rust", ".c": "c", ".h": "c", ".cpp": "cpp", ".cc": "cpp",
        ".cxx": "cpp", ".hpp": "cpp", ".swift": "swift"}
# Pages, templates and configuration: they define nothing, but they call and name functions.
TEXT = {".jsp": "jsp", ".jspx": "jsp", ".html": "html", ".htm": "html", ".twig": "twig", ".erb": "erb",
        ".ejs": "ejs", ".hbs": "template", ".handlebars": "template", ".mustache": "template", ".j2": "template",
        ".jinja": "template", ".jinja2": "template", ".cshtml": "razor", ".razor": "razor", ".xml": "xml",
        ".yml": "config", ".yaml": "config", ".properties": "config", ".json": "config", ".toml": "config"}
SKIP_DIRS = {".git", ".hg", ".svn", "node_modules", "__pycache__", ".venv", "venv", "env", "dist", "build", "target",
             ".gradle", ".idea", ".vscode", "coverage", ".next", ".nuxt", ".tox", ".mypy_cache", ".pytest_cache",
             "obj", "reachmap-data", "coderaster-data", ".github", ".gitlab"}
SKIP_FILES = {"package-lock.json", "npm-shrinkwrap.json", "composer.lock", "yarn.lock", "pnpm-lock.yaml"}
# Directories that are not the running application
NON_PROD_DIRS = {"test", "tests", "spec", "specs", "__tests__", "__mocks__", "fixtures", "testdata", "testing",
                 "mocks", "e2e", "cypress", "example", "examples", "sample", "samples", "docs", "doc", "vendor",
                 "external", "third_party", "thirdparty", "benchmark", "benchmarks", "it", "bower_components",
                 "libs", ".mvn"}
NON_PROD_FILES = ["test_*.py", "*_test.py", "conftest.py", "*_test.go", "*Test.java", "*Tests.java", "*IT.java",
                  "*Test.kt", "*Tests.kt", "*Spec.scala", "*Test.scala", "*.spec.js", "*.spec.ts", "*.spec.tsx",
                  "*.test.js", "*.test.ts", "*.test.tsx", "*.test.jsx", "*_spec.rb", "*Test.php", "*Tests.cs",
                  "*.min.js", "*.bundle.js", "*.config.js", "*.config.ts", "*.config.mjs", "*.config.cjs",
                  "Gruntfile.js", "gulpfile.js", "karma.conf.js", "protractor.conf.js", "webpack.*.js", "jest.*.js"]
MAX_BYTES = 1024 * 1024
MAX_LINE = 3000                              # longer lines are minified or generated; not read for calls
BRACE = {"java", "kotlin", "scala", "javascript", "typescript", "vue", "svelte", "go", "php", "csharp", "rust",
         "c", "cpp", "swift"}
SCRIPT = {"python", "javascript", "typescript", "vue", "svelte", "php", "ruby"}     # importing runs top-level code
SAME_DIR_VISIBLE = {"java", "kotlin", "scala", "csharp", "go"}                     # same package without import


@dataclass
class SrcFile:
    path: str
    lang: str
    text: str
    kind: str                     # "code" | "text"
    nonprod: str = ""             # reason, "" if production code


VENDOR_FILE = re.compile(r"(?:^|[-_.])v?\d+\.\d+(?:\.\d+)?(?:[-.][\w]+)?(?:\.min)?\.(?:js|css)$|^(?:jquery|bootstrap|angular|"
                         r"backbone|underscore|lodash|moment|d3|require|knockout|handlebars|mustache|react(?:-dom)?|vue|"
                         r"popper|chart|highcharts|codemirror|ace|tinymce|ckeditor|modernizr|polyfills?|zepto|"
                         r"wysihtml5?|summernote|select2|datatables|plotly|three|sweetalert2?|toastr|marked|"
                         r"highlight|prism|ckeditor5)(?:[.-][\w.-]*)?\.js$", re.I)


def nonprod_reason(path: str) -> str:
    parts = path.split("/")
    for i, part in enumerate(parts[:-1]):
        if part.lower() in NON_PROD_DIRS:
            return f"under {'/'.join(parts[:i + 1])}/"
    name = parts[-1]
    if VENDOR_FILE.search(name):
        return "third-party library (file name)"
    for pat in NON_PROD_FILES:
        if fnmatch.fnmatchcase(name, pat):
            return f"file name {pat}"
    return ""


def discover(root: str, exclude: tuple = (), include_dirs: frozenset = frozenset(),
             max_bytes: int = MAX_BYTES, skipped: dict | None = None, skip_paths: tuple = ()):
    skip = SKIP_DIRS - include_dirs
    skip_abs = {os.path.abspath(p) for p in skip_paths}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in skip and os.path.join(dirpath, d) not in skip_abs)
        for name in sorted(filenames):
            ext = os.path.splitext(name)[1].lower()
            lang = CODE.get(ext) or TEXT.get(ext)
            if not lang or name in SKIP_FILES:
                continue
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            if os.path.islink(full) and not os.path.realpath(full).startswith(os.path.abspath(root) + os.sep):
                continue
            if any(fnmatch.fnmatch(rel, g) or fnmatch.fnmatch(name, g) for g in exclude):
                continue
            try:
                if os.path.getsize(full) > max_bytes:
                    if skipped is not None:
                        skipped.setdefault("too large", []).append(rel)
                    continue
                with open(full, "rb") as fh:
                    raw = fh.read()
            except OSError:
                if skipped is not None:
                    skipped.setdefault("unreadable", []).append(rel)
                continue
            if b"\x00" in raw[:2048]:
                continue
            kind = "code" if ext in CODE else "text"
            if kind == "text" and lang == "config" and len(raw) > 256 * 1024:
                continue                                             # big data files: nothing to learn
            yield SrcFile(rel, lang, raw.decode("utf-8", "replace"), kind, nonprod_reason(rel))


# --------------------------------------------------------------------------------------------------------------
# Comments and strings: blanked for reading code, strings kept for references
# --------------------------------------------------------------------------------------------------------------
_STR = r'"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\''
_SCAN = {
    "brace": re.compile(r"//[^\n]*|/\*.*?\*/|`(?:\\.|[^`\\])*`|" + _STR, re.S),
    "rust": re.compile(r"//[^\n]*|/\*.*?\*/|\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\\n])'", re.S),
    "go": re.compile(r"//[^\n]*|/\*.*?\*/|`[^`]*`|\"(?:\\.|[^\"\\\n])*\"|'(?:\\.|[^'\\\n])+'", re.S),
    "php": re.compile(r"//[^\n]*|#(?!\[)[^\n]*|/\*.*?\*/|<<<\s*['\"]?(\w+)['\"]?\n.*?\n\s*\1\b|"
                      r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'', re.S),
    "python": re.compile(r'#[^\n]*|"""[\s\S]*?"""|\'\'\'[\s\S]*?\'\'\'|[rbfuRBFU]{0,2}' + _STR),
    "ruby": re.compile(r"#[^\n]*|^=begin.*?^=end|\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\])*'", re.S | re.M),
}


def _family(lang: str) -> str:
    if lang in ("python", "ruby", "php", "rust", "go"):
        return lang
    return "brace"


def clean(text: str, lang: str) -> tuple[list[str], list[tuple[int, str]]]:
    """(lines with comments removed and string contents blanked, [(line, string content)])."""
    pat = _SCAN[_family(lang)]
    strings: list[tuple[int, str]] = []
    starts = [0] + [m.end() for m in re.finditer("\n", text)]

    def repl(m: re.Match) -> str:
        s = m.group(0)
        head = s[:3]
        if head.startswith(("//", "#", "/*", "=be")):
            return re.sub(r"[^\n]", " ", s)
        if s.startswith("<<<"):                                      # PHP heredoc: keep the markers, blank the body
            first = s.index("\n")
            last = s.rstrip().rfind("\n")
            body = s[first + 1:last]
            strings.append((bisect.bisect_right(starts, m.start() + first + 1), body))
            return s[:first + 1] + re.sub(r"[^\n]", " ", body) + s[last:]
        q = 3 if head in ('"""', "'''") else 1
        lead = len(s) - len(s.lstrip("rbfuRBFU"))
        body = s[lead + q:-q] if len(s) >= lead + 2 * q else ""
        if body:
            strings.append((bisect.bisect_right(starts, m.start()), body))
        return s[:lead + q] + re.sub(r"[^\n]", " ", body) + s[len(s) - q:] if len(s) >= lead + 2 * q else s

    return pat.sub(repl, text).split("\n"), strings


# --------------------------------------------------------------------------------------------------------------
# Definitions
# --------------------------------------------------------------------------------------------------------------
KEYWORDS = set("""if for while switch catch return new else throw throws case do try synchronized using foreach
elseif sizeof typeof instanceof super this self function def fn func await yield in of not and or with match when
lock fixed checked unchecked delete void assert import from export class interface enum struct trait impl where
select goto continue break default package namespace use extends implements static public private protected var
let const val defer go chan range type""".split())
CTRL = set("""if for while switch catch return new else throw case do try synchronized using foreach elseif sizeof
typeof instanceof function def fn func await yield assert import export class interface enum struct trait impl
goto continue break package namespace extends implements var let const val defer lambda not and or print echo
isset empty unset require require_once include include_once super this self""".split())
_MODS = (r"(?:(?:public|private|protected|internal|static|final|abstract|synchronized|native|default|override|"
         r"virtual|async|open|suspend|inline|sealed|partial|extern|unsafe|transient|strictfp|operator|infix|tailrec|"
         r"external|readonly|new)\s+)*")
_J_METHOD = re.compile(r"^\s*(?:@\w+(?:\([^)]*\))?\s+)*" + _MODS +
                       r"(?:<[^>]+>\s+)?(?P<t>[\w\[\]<>,.?]+(?:<[^()]*>)?)\s+(?P<n>[A-Za-z_]\w*)\s*\((?P<rest>.*)$")
DEF_PATTERNS = {
    "kotlin": [re.compile(r"^\s*(?:@\w+(?:\([^)]*\))?\s+)*" + _MODS + r"fun\s+(?:<[^>]+>\s*)?(?:[\w.]+\.)?(?P<n>\w+)\s*\(")],
    "scala": [re.compile(r"^\s*" + _MODS + r"def\s+(?P<n>\w+)")],
    "php": [re.compile(r"^\s*(?:(?:public|private|protected|static|final|abstract)\s+)*function\s+&?(?P<n>\w+)\s*\(")],
    "go": [re.compile(r"^func\s+(?:\((?P<recv>[^)]*)\)\s*)?(?P<n>\w+)\s*[(\[]")],
    "rust": [re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:(?:async|unsafe|const|extern(?:\s+\"[^\"]*\")?)\s+)*fn\s+(?P<n>\w+)")],
    "swift": [re.compile(r"^\s*(?:(?:public|private|internal|fileprivate|open|static|class|final|override|mutating|@\w+)\s+)*func\s+(?P<n>\w+)")],
    "python": [re.compile(r"^\s*(?:async\s+)?def\s+(?P<n>\w+)\s*\(")],
    "ruby": [re.compile(r"^\s*def\s+(?:self\.)?(?P<n>\w+[?!=]?)")],
    "c": [re.compile(r"^(?:[\w*&<>,~]+\s+)+\**&?(?:\w+::)*(?P<n>~?[A-Za-z_]\w*)\s*\((?P<rest>[^;]*)$")],
}
DEF_PATTERNS["cpp"] = DEF_PATTERNS["c"]
_JS = [
    re.compile(r"^\s*(?:export\s+)?(?:default\s+)?(?:async\s+)?function\s*\*?\s*(?P<n>[\w$]+)\s*[(<]"),
    re.compile(r"^\s*(?:export\s+)?(?:const|let|var)\s+(?P<n>[\w$]+)\s*(?::[^=]+)?=\s*(?:async\s+)?"
               r"(?:function\b|\([^)]*\)\s*(?::[^=]+)?=>|[\w$]+\s*=>)"),
    re.compile(r"^\s*(?P<n>[\w$]+)\s*:\s*(?:async\s+)?(?:function\b|\([^)]*\)\s*=>|[\w$]+\s*=>)"),
    re.compile(r"^\s*(?:(?:public|private|protected|static|readonly)\s+)*(?P<n>[\w$]+)\s*(?::[^=]+)?=\s*(?:async\s+)?"
               r"\([^)]*\)\s*(?::[^=]+)?=>"),
    re.compile(r"^\s*(?:(?:public|private|protected|static|async|readonly|override|abstract|get|set)\s+)*\*?"
               r"(?P<n>[\w$]+)\s*(?:<[^>]*>)?\s*\((?P<args>[^;]*)\)\s*(?::\s*[^{;=]+)?\{\s*$"),
]
CLASS_RE = re.compile(r"^\s*(?:@\w+(?:\([^)]*\))?\s+)*(?:(?:public|private|protected|internal|abstract|final|static|"
                      r"sealed|partial|export|default|open|data|inner|enum|case)\s+)*(?:class|interface|trait|object|"
                      r"struct|record|impl)\s+(?P<n>[A-Za-z_]\w*)(?P<rest>.*)$")


def def_on_line(line: str, lang: str) -> tuple[str, int] | None:
    """(name, column) if the (cleaned) line starts a function definition."""
    if lang in ("java", "csharp"):
        m = _J_METHOD.match(line)
        if m and m.group("t") not in CTRL and m.group("n") not in CTRL and \
                not m.group("rest").rstrip().endswith(";") and "=" not in line[:m.start("n")]:
            return m.group("n"), m.start("n")
        return None
    if lang in ("javascript", "typescript", "vue", "svelte"):
        for p in _JS:
            m = p.match(line)
            if m and m.group("n") not in CTRL:
                args = m.groupdict().get("args")
                if args is not None and ("=>" in args or "function" in args):
                    continue
                return m.group("n"), m.start("n")
        return None
    for p in DEF_PATTERNS.get(lang, ()):
        m = p.match(line)
        if m and m.group("n") not in CTRL:
            if lang in ("c", "cpp"):
                first = line.split(None, 1)[0]
                if first in CTRL or m.group("rest").rstrip().endswith(";"):
                    return None
            return m.group("n"), m.start("n")
    return None


def _indent(s: str) -> int:
    return len(s) - len(s.lstrip())


def span_end(lines: list[str], i: int, lang: str) -> int:
    """Index of the last line of the block that starts at line index i."""
    n = len(lines)
    if lang in ("python", "ruby") or (lang == "scala" and "{" not in lines[i]):
        base = _indent(lines[i])
        j, last = i + 1, i
        open_paren = lines[i].count("(") - lines[i].count(")")
        while j < n and open_paren > 0:                        # multi-line signature
            open_paren += lines[j].count("(") - lines[j].count(")")
            last = j
            j += 1
        while j < n:
            t = lines[j]
            if t.strip():
                if _indent(t) <= base:
                    if lang == "ruby" and t.strip() == "end" and _indent(t) == base:
                        last = j
                    break
                last = j
            j += 1
        return last
    depth, seen = 0, False
    for j in range(i, min(n, i + 20000)):
        t = lines[j]
        if not seen and j > i + 4:
            return i
        o, c = t.count("{"), t.count("}")
        if o:
            seen = True
        depth += o - c
        if seen and depth <= 0:
            return j
        if not seen and t.rstrip().endswith(";"):
            return j
    return i if not seen else n - 1


# --------------------------------------------------------------------------------------------------------------
# Entry points and framework code
# --------------------------------------------------------------------------------------------------------------
ENTRY_ANN = re.compile(
    r"""@(?:Get|Post|Put|Delete|Patch|Request|Message|Subscribe)Mapping\b | @(?:GET|POST|PUT|DELETE|PATCH|Path)\b
      | @(?:\w+\.)*(?:route|get|post|put|delete|patch|websocket|api_route)\s*\( | \[Http(?:Get|Post|Put|Delete|Patch)\b
      | \[Route\( | \#\[(?:get|post|put|delete|patch|route)\( | \#\[Route\(
      | @(?:Scheduled|KafkaListener|RabbitListener|JmsListener|SqsListener|EventListener|StreamListener|JobWorker)\b
      | @(?:\w+\.)*(?:task|shared_task|command|group|on_event|cron|job|consumer|subscriber|handler)\b
      | @(?:Command|CommandHandler|QueryHandler|Cron|Process|Get|Post|Put|Delete|Patch|MessagePattern|EventPattern)\(""", re.X)
FRAMEWORK_ANN = re.compile(
    r"""@(?:Override|Bean|PostConstruct|PreDestroy|Autowired|Inject|JsonCreator|JsonProperty|JsonValue|JsonGetter|
         JsonSetter|ModelAttribute|InitBinder|ExceptionHandler|Transactional|Provides|Before|After|Around|
         AfterReturning|AfterThrowing|Pointcut|Converter|Validator|PrePersist|PostLoad|PreUpdate|Subscribe|
         Input|Output|HostListener|ViewChild|Effect)\b
      | @(?:property|cached_property|\w+\.setter|\w+\.getter|staticmethod|classmethod|abstractmethod|receiver|
         validator|field_validator|model_validator|root_validator|validates|hookimpl|register)\b
      | @(?:\w+\.)*(?:errorhandler|before_request|after_request|teardown_request|context_processor|template_filter|
         middleware|exception_handler|listens_for)\b""", re.X)
DI_CLASS = re.compile(r"@(?:Component|Service|Repository|Controller|RestController|Configuration|ControllerAdvice|"
                      r"RestControllerAdvice|SpringBootApplication|Named|Singleton|ApplicationScoped|RequestScoped|"
                      r"Injectable|NgModule|Pipe|Directive|Entity|Embeddable|Module|WebServlet|WebFilter|WebListener)\b"
                      r"|\[(?:ApiController|Controller)\]|\bextends\s+\w*(?:Controller|Servlet|Command|Job|Listener)\b")
ENTRY_NAMES = {"main": "program start (main)", "Main": "program start (Main)",
               "doGet": "HTTP handler (servlet)", "doPost": "HTTP handler (servlet)", "doPut": "HTTP handler (servlet)",
               "doDelete": "HTTP handler (servlet)", "service": None, "ServeHTTP": "HTTP handler (net/http)",
               "doFilter": "HTTP filter (servlet)", "handle": None, "lambda_handler": "AWS Lambda handler",
               "handler": None}
FRAMEWORK_NAMES = {
    "toString", "equals", "hashCode", "compareTo", "compare", "run", "call", "close", "iterator", "init", "destroy",
    "configure", "afterPropertiesSet", "onApplicationEvent", "loadUserByUsername", "preHandle", "postHandle",
    "afterCompletion", "supports", "convert", "validate", "initialize", "isValid", "getObject", "accept", "apply",
    "test", "intercept", "invoke", "handle", "service", "onStartup", "contextInitialized", "contextDestroyed",
    "constructor", "render", "componentDidMount", "componentDidUpdate", "componentWillUnmount",
    "shouldComponentUpdate", "getDerivedStateFromProps", "ngOnInit", "ngOnDestroy", "ngOnChanges", "ngAfterViewInit",
    "connectedCallback", "disconnectedCallback", "attributeChangedCallback", "setup", "data", "mounted", "created",
    "beforeMount", "beforeDestroy", "unmounted", "init", "String", "Error", "Len", "Less", "Swap", "Dispose",
    "ToString", "Equals", "GetHashCode", "ConfigureServices", "Configure", "OnGet", "OnPost", "Invoke",
    "InvokeAsync", "Execute", "ExecuteAsync", "StartAsync", "StopAsync", "drop", "fmt", "from", "into", "default",
    "clone", "deref", "next", "boot", "register", "up", "down", "handle", "rules", "authorize", "messages",
    "offsetGet", "offsetSet", "offsetExists", "offsetUnset", "jsonSerialize", "getIterator", "count",
    "initialize", "to_s", "to_str", "inspect", "each", "method_missing", "respond_to_missing?", "setUp",
    "tearDown", "loadComponent", "loadChildren", "canActivate", "canDeactivate", "canLoad", "canMatch", "resolve",
    "useFactory", "transform", "writeValue", "registerOnChange", "registerOnTouched", "setDisabledState",
    "ngAfterContentInit", "ngDoCheck", "ngAfterViewChecked", "ngAfterContentChecked"}
PY_VIEW_METHODS = {"get", "post", "put", "patch", "delete", "head", "options", "dispatch", "list", "create",
                   "retrieve", "update", "partial_update", "destroy", "get_queryset", "get_object",
                   "get_serializer_class", "get_context_data", "form_valid", "form_invalid", "perform_create",
                   "perform_update", "perform_destroy"}
ROUTE_LINE = re.compile(
    r"""\b(?:app|router|api|server|bp|blueprint|routes?|r|e|mux|engine|fastify|express|group|v\d|admin|web)
          \.(?:get|post|put|delete|patch|all|use|route|options|head|HandleFunc|Handle|GET|POST|PUT|DELETE|PATCH|Any|
             add_url_rule|add_api_route|add_route|register|Get|Post|Put|Delete|Group|Route|Map(?:Get|Post|Put|Delete))\s*\(
      | \bRoute::(?:get|post|put|delete|patch|any|match|resource|apiResource|view)\s*\(
      | ^\s*(?:re_)?path\s*\( | \burl\s*\(\s*r?["']\^ | \bhttp\.HandleFunc\s*\( | \bendpoints\.Map\w*\(
      | \$app->(?:get|post|put|delete|patch|any|map)\s*\( | \bon\s*\(\s*["'](?:connection|message|request)["']""", re.X)
PHP_PAGE = re.compile(r"\$_(?:GET|POST|REQUEST|COOKIE|FILES)\b|^\s*(?:echo|print)\b|\bheader\s*\(")
PHP_DECL = re.compile(r"^\s*(?:<\?php|<\?=?|\?>|namespace\b|use\b|declare\b|[{}();,\]]+$|(?:abstract\s+|final\s+)?"
                      r"(?:class|interface|trait|enum|function)\b|define\s*\(|const\b|(?:require|include)(?:_once)?\b)")
PY_MAIN = re.compile(r"""^if\s+__name__\s*==\s*["']__main__["']""", re.M)
GETTER = re.compile(r"^(?:get|is|set|has)[A-Z]\w*$")

# --------------------------------------------------------------------------------------------------------------
# The graph
# --------------------------------------------------------------------------------------------------------------
@dataclass
class Func:
    id: int
    name: str
    qual: str                     # Class.name or name
    path: str
    line: int
    end: int
    lang: str
    kind: str = "function"        # "function" | "file" (top-level code of a file)
    nonprod: str = ""
    entry: str = ""               # reason if an entry point
    framework: str = ""           # reason if run by the framework
    ann: str = ""                 # annotations / decorators seen above the definition
    status: str = ""
    reason: str = ""
    pred: int = -1                # previous node on the path from a root
    depth: int = -1
    sure: bool = True
    dead_root: int = -1           # for code only reached from unreached code: the unreached function above it
    findings: list = field(default_factory=list)
    sinks: list = field(default_factory=list)       # (line, kind, code) of dangerous calls inside
    routes: list = field(default_factory=list)      # {"method", "path", "line"} from route registrations
    via_entries: int = 0                            # how many entry points reach this function
    changed: int = 0                                # last git commit touching the file (unix time)
    commits: int = 0


@dataclass
class Edge:
    src: int
    dst: int
    how: str                      # "same file" | "imported file" | "same folder" | "unique name" | "name in N places" ...
    kind: str                     # "call" | "reference" | "string" | "page" | "import" | "loaded"
    path: str
    line: int
    sure: bool
    count: int = 1


FAMILY = {"java": "jvm", "kotlin": "jvm", "scala": "jvm", "javascript": "js", "typescript": "js", "vue": "js",
          "svelte": "js", "c": "c", "cpp": "c"}


def family(lang: str) -> str:
    return FAMILY.get(lang, lang)


AMBIG_MAX = 4                     # a name defined in more places than this is not linked at all


class Graph:
    def __init__(self):
        self.nodes: list[Func] = []
        self.file_node: dict[str, int] = {}
        self.by_name: dict[str, list[int]] = defaultdict(list)
        self.edges: dict[tuple[int, int], Edge] = {}
        self.out: dict[int, list[int]] = defaultdict(list)
        self.inc: dict[int, list[int]] = defaultdict(list)
        self.unlinked: Counter = Counter()          # names not linked because they are defined too often
        self.words: Counter = Counter()             # every identifier in every file, for "name appears"
        self.classes: dict[str, list] = {}          # path -> [(name, start, end, header and annotations)]

    def add(self, f: Func) -> int:
        f.id = len(self.nodes)
        self.nodes.append(f)
        if f.kind == "function":
            self.by_name[f.name].append(f.id)
        return f.id

    def link(self, src: int, dst: int, how: str, kind: str, path: str, line: int, sure: bool) -> None:
        if src == dst:
            return
        key = (src, dst)
        e = self.edges.get(key)
        if e:
            e.count += 1
            if sure and not e.sure:
                e.sure, e.how, e.kind, e.path, e.line = True, how, kind, path, line
            return
        self.edges[key] = Edge(src, dst, how, kind, path, line, sure)
        self.out[src].append(dst)
        self.inc[dst].append(src)


# --------------------------------------------------------------------------------------------------------------
# Imports: which files does a file use
# --------------------------------------------------------------------------------------------------------------
class Resolver:
    """Finds project files from module names and relative paths."""
    JS_EXT = ("", ".js", ".ts", ".tsx", ".jsx", ".mjs", ".cjs", ".vue", ".svelte", "/index.js", "/index.ts",
              "/index.tsx", "/index.jsx")

    def __init__(self, paths: list[str]):
        self.paths = set(paths)
        self.suffix: dict[str, set[str]] = defaultdict(set)
        for p in paths:
            stem = os.path.splitext(p)[0]
            parts = stem.split("/")
            for i in range(len(parts)):
                self.suffix["/".join(parts[i:])].add(p)
            if parts[-1] in ("__init__", "index"):
                for i in range(len(parts) - 1):
                    self.suffix["/".join(parts[i:-1])].add(p)

    def by_suffix(self, mod: str, limit: int = 3) -> set[str]:
        hits = self.suffix.get(mod.strip("/"), set())
        return hits if 0 < len(hits) <= limit else set()

    def relative(self, base_file: str, spec: str, exts=JS_EXT) -> set[str]:
        base = os.path.dirname(base_file)
        target = os.path.normpath(os.path.join(base, spec)).replace(os.sep, "/").lstrip("/")
        if target.startswith(".."):
            return set()
        for ext in exts:
            if target + ext in self.paths:
                return {target + ext}
        return set()


IMPORT_RES = {
    "python": [re.compile(r"^\s*from\s+(\.*[\w.]*)\s+import\s+(.+)$"), re.compile(r"^\s*import\s+([\w.]+(?:\s*,\s*[\w.]+)*)")],
    "js": [re.compile(r"""\bfrom\s+["']([^"']+)["']"""), re.compile(r"""\bimport\s*\(?\s*["']([^"']+)["']"""),
           re.compile(r"""\brequire\s*\(\s*["']([^"']+)["']\s*\)""")],
    "java": [re.compile(r"^\s*import\s+(?:static\s+)?([\w.]+)")],
    "php": [re.compile(r"""\b(?:include|include_once|require|require_once)\b[^;"']*["']([^"']+)["']"""),
            re.compile(r"^\s*use\s+([\w\\]+)")],
    "go": [re.compile(r"""^\s*(?:import\s+)?(?:\w+\s+)?"([\w./-]+)"\s*$""")],
    "ruby": [re.compile(r"""\brequire_relative\s*\(?\s*["']([^"']+)["']"""), re.compile(r"""\brequire\s*\(?\s*["']([^"']+)["']""")],
    "csharp": [re.compile(r"^\s*using\s+(?:static\s+)?([\w.]+)\s*;")],
    "rust": [re.compile(r"^\s*(?:pub\s+)?(?:use|mod)\s+([\w:]+)")],
    "c": [re.compile(r"""^\s*#\s*include\s+"([^"]+)\"""")],
}


def imports_of(sf: SrcFile, res: Resolver) -> set[str]:
    lang = sf.lang
    fam = {"typescript": "js", "javascript": "js", "vue": "js", "svelte": "js", "kotlin": "java",
           "scala": "java", "cpp": "c"}.get(lang, lang)
    pats = IMPORT_RES.get(fam)
    out: set[str] = set()
    if not pats:
        return out
    for line in sf.text.split("\n"):
        if len(line) > MAX_LINE:
            continue
        for p in pats:
            for m in p.finditer(line):
                spec = m.group(1)
                if fam == "python":
                    out |= _py_import(sf.path, spec, m.group(2) if m.lastindex and m.lastindex > 1 else "", res)
                elif fam == "js":
                    out |= res.relative(sf.path, spec) if spec.startswith(".") else res.by_suffix(spec.lstrip("@/~"))
                elif fam == "java":
                    parts = spec.split(".")
                    for k in (len(parts), len(parts) - 1):          # a.b.C or a.b.C.member (static import)
                        hit = res.by_suffix("/".join(parts[:k]), 2)
                        if hit:
                            out |= hit
                            break
                elif fam == "php":
                    if "\\" in spec or not re.search(r"[./]", spec):
                        out |= res.by_suffix("/".join(spec.strip("\\").split("\\")[-2:]), 2) or \
                            res.by_suffix(spec.strip("\\").split("\\")[-1], 1)
                    else:
                        out |= res.relative(sf.path, spec, ("",)) or res.by_suffix(os.path.splitext(spec.lstrip("./"))[0], 2)
                elif fam == "go":
                    parts = spec.split("/")
                    for k in range(min(3, len(parts)), 0, -1):
                        d = "/".join(parts[-k:])
                        hits = {p for p in res.paths if os.path.dirname(p).endswith(d) and p.endswith(".go")}
                        if hits:
                            out |= hits
                            break
                elif fam == "ruby":
                    out |= res.relative(sf.path, spec, ("", ".rb")) or res.by_suffix(spec, 2)
                elif fam == "csharp":
                    pass                                             # namespaces do not name files
                elif fam == "rust":
                    out |= res.by_suffix(spec.replace("::", "/").replace("crate/", "").replace("super/", ""), 2)
                elif fam == "c":
                    out |= res.relative(sf.path, spec, ("",)) or res.by_suffix(os.path.splitext(spec)[0], 2)
    out.discard(sf.path)
    return out


def _py_import(path: str, mod: str, names: str, res: Resolver) -> set[str]:
    out: set[str] = set()
    names_l = [n.strip().split(" as ")[0].strip("() ") for n in names.split(",")] if names else []
    if mod.startswith("."):
        dots = len(mod) - len(mod.lstrip("."))
        base = os.path.dirname(path)
        for _ in range(dots - 1):
            base = os.path.dirname(base)
        rest = mod.lstrip(".").replace(".", "/")
        stem = "/".join(x for x in (base, rest) if x)
        cands = [stem] + [f"{stem}/{n}" for n in names_l if n and n != "*"]
        for c in cands:
            for p in (c + ".py", c + "/__init__.py"):
                if p.lstrip("/") in res.paths:
                    out.add(p.lstrip("/"))
        return out
    for m in [x.strip().split(" as ")[0] for x in mod.split(",")]:
        stem = m.replace(".", "/")
        out |= res.by_suffix(stem, 2)
        for n in names_l:
            if n and n != "*":
                out |= res.by_suffix(f"{stem}/{n}", 2)
    return out


# --------------------------------------------------------------------------------------------------------------
# Reading one file
# --------------------------------------------------------------------------------------------------------------
CALL_RE = re.compile(r"(?:(?P<q>\?\.|\.|->|::)\s*|(?<![\w$]))(?P<n>[A-Za-z_$][\w$]*[?!]?)\s*(?:<[^<>()]{0,60}>)?\s*\(")
REF_RE = re.compile(r"(?:(?P<q>\?\.|\.|->|::)\s*|(?<![\w$]))(?P<n>[A-Za-z_$][\w$]*)")
WORD_RE = re.compile(r"[A-Za-z_$][\w$]*")
TEMPLATE_PROP = re.compile(r"[\w)\]]\.(?P<p>[a-z]\w*)\b")
BUILT_NAME = re.compile(r"""["']([A-Za-z_]\w{2,})["']\s*(?:\.|\+)\s*[$\w(]|["']([A-Za-z_]\w{2,})\{?\$\w
                         |\bf["']([A-Za-z_]\w{2,})\{|`([A-Za-z_]\w{2,})\$\{""", re.X)
CALLBACK_STR = re.compile(r"^[A-Za-z_\\][\w.:@\\#/$-]{0,150}$")
DYN_PATH = re.compile(r"""["']((?:[\w.-]+/)+)(?:\{?\$\w|\$\{|["']\s*(?:\.|\+)\s*[$\w(])""")
FILE_IN_STRING = re.compile(r"(?<![\w/.-])((?:[\w.-]+/)*[\w-][\w.-]*\.(?:js|mjs|ts|php|inc|py|rb|jsp|html))\b")
SCRIPT_SRC = re.compile(r"""<script[^>]+src\s*=\s*["']([^"']+)["']""", re.I)
PAGE_LINK = re.compile(r"""(?:href|action|src)\s*=\s*["']([^"'?#]+\.(?:php|jsp))""", re.I)


@dataclass
class FileFacts:
    defs: list = field(default_factory=list)        # (name, qual, line, end, ann, col)
    classes: list = field(default_factory=list)     # (name, start, end, header)
    calls: list = field(default_factory=list)       # (line, name, qualifier, kind)
    route_lines: set = field(default_factory=set)
    strings: list = field(default_factory=list)     # (line, content) of string literals
    prefixes: list = field(default_factory=list)    # (line, prefix) of names built at runtime
    dyn_paths: list = field(default_factory=list)   # (line, folder) of file paths built at runtime
    owner: list = field(default_factory=list)       # per line: index into defs, or -1
    minified: bool = False
    top_code: int = 0                               # PHP: top-level statements that do something (not declarations)
    top_input: bool = False                         # PHP: top-level code reads request input or writes output


def read_python(sf: SrcFile) -> FileFacts | None:
    try:
        tree = ast.parse(sf.text)
    except (SyntaxError, ValueError):
        return None
    ff = FileFacts()
    lines = sf.text.split("\n")
    ff.owner = [-1] * (len(lines) + 2)

    def ann_text(node) -> str:
        out = []
        for d in getattr(node, "decorator_list", []):
            try:
                out.append("@" + ast.unparse(d))
            except Exception:                       # noqa: BLE001 - unparse of odd nodes
                pass
        return " ".join(out)

    def visit(node, cls: list[str], cls_bases: list[str]):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.ClassDef):
                bases = " ".join(ast.unparse(b) for b in child.bases) if child.bases else ""
                ff.classes.append((child.name, child.lineno, child.end_lineno or child.lineno, bases))
                visit(child, cls + [child.name], cls_bases + [bases])
            elif isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                qual = ".".join(cls + [child.name]) if cls else child.name
                start = min([child.lineno] + [d.lineno for d in child.decorator_list])
                extra = (" bases:" + cls_bases[-1]) if cls_bases else ""
                ff.defs.append((child.name, qual, child.lineno, child.end_lineno or child.lineno,
                                ann_text(child) + extra, 0, start))
                visit(child, cls, cls_bases)
            else:
                visit(child, cls, cls_bases)

    visit(tree, [], [])
    for idx, d in sorted(enumerate(ff.defs), key=lambda x: x[1][2]):
        for ln in range(d[6], d[3] + 1):
            ff.owner[ln] = idx
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            fn = node.func
            if isinstance(fn, ast.Name):
                ff.calls.append((node.lineno, fn.id, "", "call"))
            elif isinstance(fn, ast.Attribute):
                q = "self." if isinstance(fn.value, ast.Name) and fn.value.id in ("self", "cls") else "."
                ff.calls.append((node.lineno, fn.attr, q, "call"))
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            ff.calls.append((node.lineno, node.id, "", "reference"))
        elif isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
            ff.calls.append((node.lineno, node.attr, ".", "reference"))
        elif isinstance(node, ast.Constant) and isinstance(node.value, str):
            if CALLBACK_STR.match(node.value):
                for w in re.findall(r"[A-Za-z_]\w*", node.value)[:6]:
                    ff.calls.append((node.lineno, w, "", "string"))
            if "<" in node.value or "{{" in node.value:
                for m in _TPL.finditer(node.value):
                    for w in sorted(set(WORD_RE.findall(m.group(0)))):
                        ff.calls.append((node.lineno, w, "", "string"))
            ff.strings.append((node.lineno, node.value))
    for no, line in enumerate(lines, 1):
        if ROUTE_LINE.search(line):
            ff.route_lines.add(no)
    for m in BUILT_NAME.finditer(sf.text):
        ff.prefixes.append((sf.text.count("\n", 0, m.start()) + 1, next(x for x in m.groups() if x)))
    return ff


def _preamble(lines: list[str], raw_lines: list[str], i: int, lang: str) -> list[str]:
    """Annotations, attributes and decorators written above line i (also over several lines), top first."""
    ann = []
    for k in range(i - 1, max(-1, i - 10), -1):
        t = lines[k].strip()                                         # cleaned: comments and javadoc are gone
        if not t:
            continue
        if t.endswith((";", "{", "}")) or def_on_line(lines[k], lang) or CLASS_RE.match(lines[k]):
            break
        ann.append(raw_lines[k].strip())
    return list(reversed(ann))


def read_code(sf: SrcFile) -> FileFacts:
    if sf.lang == "python":
        got = read_python(sf)
        if got is not None:
            return got
    ff = FileFacts()
    raw_lines = sf.text.split("\n")
    if raw_lines and sum(len(x) for x in raw_lines) / max(1, len(raw_lines)) > 400:
        ff.minified = True
        ff.owner = [-1] * (len(raw_lines) + 2)
        return ff
    lines, strings = clean(sf.text, sf.lang)
    lang = "javascript" if sf.lang in ("vue", "svelte") else sf.lang
    ff.owner = [-1] * (len(lines) + 2)
    for i, line in enumerate(lines):
        if len(line) > MAX_LINE:
            continue
        m = CLASS_RE.match(line)
        if m and lang not in ("python",):
            end = span_end(lines, i, lang)
            ff.classes.append((m.group("n"), i + 1, end + 1, m.group("rest") + " " + " ".join(_preamble(lines, raw_lines, i, lang))
                               + " " + line[:m.start("n")]))
        d = def_on_line(line, lang)
        if not d:
            continue
        name, col = d
        end = span_end(lines, i, lang)
        ann = _preamble(lines, raw_lines, i, lang)
        head = raw_lines[i]
        inline = re.findall(r"@\w+(?:\([^)]*\))?", head[:col]) if lang not in ("php",) else []
        if lang == "go" and "recv" in (p := DEF_PATTERNS["go"][0].match(line)).groupdict() and p.group("recv"):
            recv = p.group("recv").split()[-1].lstrip("*")
            qual = f"{recv}.{name}"
        else:
            qual = name
        if lang in ("javascript", "typescript") and re.match(r"^\s*[\w$]+\s*:\s*(?:async\s+)?(?:function\b|\(|[\w$]+\s*=>)", line):
            inline.append("@object-property")
        ff.defs.append((name, qual, i + 1, end + 1, " ".join(ann + inline), col, i + 1))
    for name, start, end, _rest in ff.classes:                      # qualify methods with their class
        for k, d in enumerate(ff.defs):
            if start < d[2] <= end and d[1] == d[0]:
                ff.defs[k] = (d[0], f"{name}.{d[0]}") + d[2:]
    for idx, d in sorted(enumerate(ff.defs), key=lambda x: x[1][2]):
        for ln in range(d[2], d[3] + 1):
            ff.owner[ln] = idx
    if sf.lang == "php":
        in_class = set()
        for _n, cs, ce, _r in ff.classes:
            in_class.update(range(cs, ce + 1))
        for no, line in enumerate(lines, 1):
            if ff.owner[no] < 0 and no not in in_class and line.strip() and not PHP_DECL.match(line):
                ff.top_code += 1
                if PHP_PAGE.search(raw_lines[no - 1]):
                    ff.top_input = True
    def_at = {d[2]: (d[0], d[5]) for d in ff.defs}
    for cname, cs, _ce, _r in ff.classes:
        if cs not in def_at:
            m = CLASS_RE.match(lines[cs - 1])
            if m:
                def_at[cs] = (cname, m.start("n"))
    for no, line in enumerate(lines, 1):
        if len(line) > MAX_LINE:
            continue
        own = def_at.get(no)
        raw = raw_lines[no - 1] if no - 1 < len(raw_lines) else ""
        if ROUTE_LINE.search(raw):
            ff.route_lines.add(no)
        called = set()
        for m in CALL_RE.finditer(line):
            n = m.group("n")
            q = m.group("q") or ""
            if (n in CTRL and not q) or (own and own[0] == n and own[1] == m.start("n")):
                continue
            if q in (".", "->", "?.", "::"):
                before = line[max(0, m.start() - 6):m.start()]
                if re.search(r"(?:\bthis|\bself|\$this|\bstatic|\bSelf)\s*$", before):
                    q = "self."
            ff.calls.append((no, n, q, "call"))
            called.add((n, m.start("n")))
        for m in REF_RE.finditer(line):                              # callbacks, method references, bare names
            n = m.group("n")
            if (n, m.start("n")) in called or (n in KEYWORDS and not m.group("q")) or (own and own[0] == n and own[1] == m.start("n")):
                continue
            ff.calls.append((no, n, m.group("q") or "", "reference"))
    for no, s in strings:
        if CALLBACK_STR.match(s):                                    # 'handler', 'Controller@method', 'mod.func'
            for w in re.findall(r"[A-Za-z_]\w*", s)[:6]:
                ff.calls.append((no, w, "", "string"))
        if "<" in s or "{{" in s or "${" in s:                       # markup built in code: onclick="f()", {{ f() }}
            for m in _TPL.finditer(s):
                ln = no + s.count("\n", 0, m.start())
                for w in sorted(set(WORD_RE.findall(m.group(0)))):
                    ff.calls.append((ln, w, "", "string"))
        ff.strings.append((no, s))
    for m in BUILT_NAME.finditer(sf.text):                           # 'block' . $type, "inline{$x}", f"do_{x}"
        ff.prefixes.append((sf.text.count("\n", 0, m.start()) + 1, next(x for x in m.groups() if x)))
    for m in DYN_PATH.finditer(sf.text):                             # "source/{$file}", 'pages/' . $name
        ff.dyn_paths.append((sf.text.count("\n", 0, m.start()) + 1, m.group(1)))
    return ff


# Where pages and templates name code: template expressions, scriptlets, event handlers and attribute values.
# Prose text between tags is not read: a heading "Search" must not count as a call of search().
_TPL = re.compile(r"""\{\{.*?\}\}|\{%.*?%\}|\$\{.*?\}|\#\{.*?\}|<%.*?%>|@\{.*?\}|@[A-Za-z_][\w.]*\s*(?:\([^)]*\))?
                     |=\s*\\?"[^"]*"|=\s*\\?'[^']*'|\bon[a-z]+\s*=\s*\\?["'][^"'\\]*|<script\b[^>]*>.*?</script>""", re.S | re.X)
_CFG = re.compile(r"""^[^#!\n]*?[:=]\s*(.+)$|"[^"\n]*"|>([^<\n]+)<""", re.M)


_CFG_VALUE = re.compile(r"""[:=]\s*["']?([^"'\s,#]+)["']?\s*,?\s*$|=\s*"([^"]*)"|>\s*([^<\s]+)\s*<""", re.M)
CODE_REF = re.compile(r"^[A-Za-z_$][\w$]*(?:[.:#/@\\-][A-Za-z_$][\w$]*)*(?:\(\))?$")


def read_text(sf: SrcFile) -> list[tuple[int, str, str]]:
    """Names a page, template or config file mentions: (line, name, kind)."""
    text = sf.text
    starts = [0] + [m.end() for m in re.finditer("\n", text)]
    out = []
    if sf.lang in ("config", "xml"):                 # a value that is itself a name: init-method="setup", handler: a.b.run
        for m in _CFG_VALUE.finditer(text):
            val = next((x for x in m.groups() if x), "").strip()
            if val and CODE_REF.match(val):
                no = bisect.bisect_right(starts, m.start())
                for w in sorted(set(WORD_RE.findall(val))):
                    out.append((no, w, "page"))
        return out
    for m in _TPL.finditer(text):
        region = m.group(0)
        if len(region) > 20000:
            continue
        no = bisect.bisect_right(starts, m.start())
        for w in sorted(set(WORD_RE.findall(region))):
            out.append((no, w, "page"))
        for pm in TEMPLATE_PROP.finditer(region):                   # ${user.name} -> getName / isName
            p = pm.group("p")
            cap = p[0].upper() + p[1:]
            out += [(no, "get" + cap, "page"), (no, "is" + cap, "page")]
    return out


# --------------------------------------------------------------------------------------------------------------
# Building and walking the graph
# --------------------------------------------------------------------------------------------------------------
@dataclass
class Config:
    entries: list = field(default_factory=list)      # glob patterns on "path:Qual.name" or "path"
    framework: list = field(default_factory=list)
    ignore: list = field(default_factory=list)       # never report as unused


def load_config(path: str) -> Config:
    """Simple text file. Lines: 'entry PATTERN', 'framework PATTERN', 'ignore PATTERN', '# comment'.
    PATTERN is a glob on 'path/to/file.ext:Class.method' or on 'path/to/file.ext'."""
    cfg = Config()
    with open(path, encoding="utf-8") as fh:
        for no, line in enumerate(fh, 1):
            line = line.split("#", 1)[0].strip() if not line.lstrip().startswith("#") else ""
            if not line:
                continue
            kind, _, pat = line.partition(" ")
            pat = pat.strip()
            if kind not in ("entry", "framework", "ignore") or not pat:
                raise ValueError(f"{path}:{no}: expected 'entry|framework|ignore PATTERN', got {line!r}")
            getattr(cfg, {"entry": "entries", "framework": "framework", "ignore": "ignore"}[kind]).append(pat)
    return cfg


def _matches(pats: list[str], f: Func) -> str:
    key = f"{f.path}:{f.qual}"
    for p in pats:
        if fnmatch.fnmatchcase(key, p) or fnmatch.fnmatchcase(f.path, p) or fnmatch.fnmatchcase(f.qual, p):
            return p
    return ""


def build(files: list[SrcFile], cfg: Config | None = None, progress=None) -> tuple[Graph, dict]:
    cfg = cfg or Config()
    g = Graph()
    res = Resolver([f.path for f in files])
    facts: dict[str, FileFacts] = {}
    texts: dict[str, list] = {}
    stats = Counter()
    for k, sf in enumerate(files, 1):
        if progress:
            progress("read", k, len(files), sf.path)
        g.words.update(set(WORD_RE.findall(sf.text)) if len(sf.text) < 2_000_000 else ())
        fid = g.add(Func(0, os.path.basename(sf.path), f"{os.path.basename(sf.path)} (top level)", sf.path, 1, sf.text.count("\n") + 1, sf.lang,
                         "file", sf.nonprod))
        g.file_node[sf.path] = fid
        if sf.kind == "text":
            texts[sf.path] = read_text(sf)
            continue
        ff = read_code(sf)
        facts[sf.path] = ff
        if ff.minified:
            stats["minified"] += 1
        ff_ids = []
        for name, qual, line, end, ann, _col, _start in ff.defs:
            ff_ids.append(g.add(Func(0, name, qual, sf.path, line, end, sf.lang, "function", sf.nonprod, ann=ann)))
        ff.ids = ff_ids                                           # type: ignore[attr-defined]
        g.classes[sf.path] = ff.classes
        if not ff.minified and not sf.nonprod:                   # sinks in tests and vendored code are not attack surface
            for line, kind, code in sinks_in(sf, ff):
                o = ff.owner[line] if line < len(ff.owner) else -1
                g.nodes[ff_ids[o] if o >= 0 else fid].sinks.append((line, kind, code))
    imports = {sf.path: imports_of(sf, res) for sf in files if sf.kind == "code"}
    dirs: dict[str, list[str]] = defaultdict(list)
    for sf in files:
        if sf.kind == "code":
            dirs[os.path.dirname(sf.path)].append(sf.path)
    by_path = {sf.path: sf for sf in files}

    def resolve(name: str, src_path: str, q: str, any_lang: bool = False):
        cands = g.by_name.get(name)
        if cands and not any_lang:                 # Java code does not call a JavaScript function of the same name
            fam = family(by_path[src_path].lang)
            cands = [c for c in cands if family(g.nodes[c].lang) == fam]
        if cands and not by_path[src_path].nonprod:   # application code does not call into its tests
            cands = [c for c in cands if not g.nodes[c].nonprod]
        if not cands:
            return [], "", False
        same = [c for c in cands if g.nodes[c].path == src_path]
        if same:
            return same, "same file", True
        if q == "self.":
            pass                                                   # inherited: fall through to the rest
        imp = [c for c in cands if g.nodes[c].path in imports.get(src_path, ())]
        if imp:
            return imp, "imported file", True
        lang = by_path[src_path].lang if src_path in by_path else ""
        if lang in SAME_DIR_VISIBLE:
            near = [c for c in cands if os.path.dirname(g.nodes[c].path) == os.path.dirname(src_path)]
            if near:
                return near, "same package", True
        if len(cands) == 1:
            return cands, "unique name", True
        if len(cands) <= AMBIG_MAX:
            return cands, f"name defined in {len(cands)} places", False
        g.unlinked[name] += 1
        return [], "", False

    # calls from code
    for path, ff in facts.items():
        fid = g.file_node[path]
        ids = getattr(ff, "ids", [])
        for line, name, q, kind in ff.calls:
            if name not in g.by_name:
                continue
            o = ff.owner[line] if line < len(ff.owner) else -1
            src = ids[o] if o >= 0 else fid
            if kind == "string":                   # markup or a callback name: may name code of another language
                targets, how, sure = resolve(name, path, q, any_lang=True)
                how, sure = (f"named in a string ({how})", sure and how in ("same file", "imported file", "unique name"))
            else:
                targets, how, sure = resolve(name, path, q)
                if kind == "reference" and q in (".", "->", "?.") and how == "unique name":
                    sure = False                                    # obj.name: any object's member of that name
                if kind == "call" and q in (".", "->", "?.") and how == "unique name":
                    sure = False
            for t in targets:
                if kind == "reference" and g.nodes[t].lang == "python" and q == "" and \
                        path == g.nodes[t].path and line == g.nodes[t].line:
                    continue
                g.link(src, t, how, kind, path, line, sure)
        if ff.route_lines and not by_path[path].nonprod:            # routes in test code (RestAssured, supertest) are not endpoints
            route_src = by_path[path].text.split("\n")
            for line in ff.route_lines:
                raw = route_src[line - 1] if line - 1 < len(route_src) else ""
                cut = re.search(r"=>|\bfunction\b|\bfunc\s*\(|\blambda\b", raw)
                head = raw[:cut.start()] if cut else raw              # handlers named before any inline body
                head = re.sub(r"""(['"`])(?:\\.|(?!\1).)*\1""", "''", head)   # not the words of the URL path
                rt = route_from_line(raw)
                found = []
                for m in REF_RE.finditer(head):
                    targets, _how, _s = resolve(m.group("n"), path, m.group("q") or "")
                    if targets:
                        found.append(targets)
                for k, targets in enumerate(found):           # the last one named is the handler, the others middleware
                    last = k == len(found) - 1
                    for t in targets:
                        if not g.nodes[t].entry:
                            g.nodes[t].entry = (f"registered as a route handler at {path}:{line}" if last
                                                else f"middleware on a route at {path}:{line}")
                        if rt and last and "registered as a route" in g.nodes[t].entry:
                            g.nodes[t].routes.append({**rt, "line": line, "at": path})
            src_lines = by_path[path].text.split("\n")
            for line in ff.route_lines:                                # inline handlers live in the owner
                raw = src_lines[line - 1] if line - 1 < len(src_lines) else ""
                if "=>" in raw or "function" in raw or "func(" in raw or "lambda" in raw:
                    o = ff.owner[line] if line < len(ff.owner) else -1
                    node = g.nodes[ids[o]] if o >= 0 else g.nodes[fid]
                    if not node.entry:
                        node.entry = f"defines route handlers inline at {path}:{line}"
                    rt = route_from_line(raw)
                    if rt and "inline" in node.entry:
                        node.routes.append({**rt, "line": line, "at": path})
    # new X(...) / X(...) creates an object: link to the constructor of class X
    ctor_names = {"__construct", "__init__", "constructor", "initialize", "new"}
    ctors: dict[str, list[int]] = defaultdict(list)
    for path, ff in facts.items():
        ids = getattr(ff, "ids", [])
        for cname, cs, ce, _r in ff.classes:
            for k, d in enumerate(ff.defs):
                if cs < d[2] <= ce and (d[0] in ctor_names or d[0] == cname):
                    ctors[cname].append(ids[k])
    for path, ff in facts.items():
        fid = g.file_node[path]
        ids = getattr(ff, "ids", [])
        for line, name, q, kind in ff.calls:
            if kind == "call" and name in ctors and (q in ("", "::") or name[:1].isupper()):
                o = ff.owner[line] if line < len(ff.owner) else -1
                src = ids[o] if o >= 0 else fid
                cands = ctors[name]
                same = [c for c in cands if g.nodes[c].path in imports.get(path, ()) or g.nodes[c].path == path
                        or os.path.dirname(g.nodes[c].path) == os.path.dirname(path)]
                use = same or cands
                for t in use:
                    g.link(src, t, "creates an object (constructor)", "call", path, line, bool(same) or len(cands) == 1)
        # a string that names a project file: the file is loaded or linked from here
        for line, sval in ff.strings:
            for fm in FILE_IN_STRING.finditer(sval[:5000]):
                spec = fm.group(1)
                ln = line + sval.count("\n", 0, fm.start())
                hit = res.relative(path, spec, ("",)) or res.by_suffix(os.path.splitext(spec.lstrip("./"))[0], 1)
                o = ff.owner[ln] if ln < len(ff.owner) else -1
                src = ids[o] if o >= 0 else fid
                for t in hit:
                    if t != path:
                        g.link(src, g.file_node[t], "names this file in a string", "loaded", path, ln, True)
        g.prefixes = getattr(g, "prefixes", []) + [(path, ln, pre) for ln, pre in ff.prefixes]
        g.dyn_paths = getattr(g, "dyn_paths", []) + [(path, ln, re.sub(r"^(?:\.{1,2}/)+", "", d)) for ln, d in ff.dyn_paths
                                                     if re.sub(r"^(?:\.{1,2}/)+", "", d).strip("/")]
    # names in pages, templates and config
    for path, refs in texts.items():
        src = g.file_node[path]
        stem = os.path.basename(path).split(".")[0]
        here = os.path.dirname(path)
        for line, name, kind in refs:
            defs = g.by_name.get(name, ())
            if not defs:
                continue
            # x.component.html belongs to x.component.ts, Index.cshtml to Index.cshtml.cs: prefer the code next to it
            pair = [d for d in defs if os.path.dirname(g.nodes[d].path) == here
                    and os.path.basename(g.nodes[d].path).split(".")[0] == stem]
            near = pair or [d for d in defs if os.path.dirname(g.nodes[d].path) == here]
            if near:
                for d in near:
                    g.link(src, d, "named in its template" if pair else "named in a page in the same folder", "page",
                           path, line, True)
            elif len(defs) == 1:                    # a common name in a template says little about which function
                g.link(src, defs[0], "named in a page/template/config", "page", path, line, True)
            else:
                g.unlinked[name] += 1
        txt = by_path[path].text
        for m in SCRIPT_SRC.finditer(txt):
            spec = m.group(1)
            hit = res.relative(path, spec, ("",)) or res.by_suffix(os.path.splitext(spec.split("?")[0].lstrip("./"))[0], 1)
            for p in hit:
                g.link(src, g.file_node[p], "loaded by this page", "loaded", path, txt.count("\n", 0, m.start()) + 1, True)
    for sf in files:
        if sf.kind == "code" and sf.lang in ("php", "jsp"):
            for m in SCRIPT_SRC.finditer(sf.text):
                spec = m.group(1).split("?")[0]
                hit = res.relative(sf.path, spec, ("",)) or res.by_suffix(os.path.splitext(spec.lstrip("./"))[0], 1)
                for p in hit:
                    g.link(g.file_node[sf.path], g.file_node[p], "loaded by this page", "loaded", sf.path,
                           sf.text.count("\n", 0, m.start()) + 1, True)
    # pages link to pages (PHP/JSP): a linked page is reachable by a browser anyway, keeps the edge for the path view
    for sf in files:
        if sf.lang in ("php", "jsp", "html"):
            for m in PAGE_LINK.finditer(sf.text):
                hit = res.relative(sf.path, m.group(1), ("",))
                for p in hit:
                    g.link(g.file_node[sf.path], g.file_node[p], "linked page", "page", sf.path,
                           sf.text.count("\n", 0, m.start()) + 1, True)
    # imports run top-level code (script languages); a function's module is loaded when it runs
    for path, targets in imports.items():
        src = g.file_node[path]
        for t in sorted(targets):
            if by_path[t].lang in SCRIPT:
                g.link(src, g.file_node[t], "imports", "import", path, 1, True)
    for f in g.nodes:                      # running a function means its module / class body is in use
        if f.kind == "function":
            g.link(f.id, g.file_node[f.path], "its module is loaded" if f.lang in SCRIPT else "same class or file",
                   "loaded", f.path, f.line, True)
    mark_roots(g, files, facts, cfg)
    walk(g, cfg)
    return g, dict(stats)


def mark_roots(g: Graph, files: list[SrcFile], facts: dict, cfg: Config) -> None:
    by_path = {sf.path: sf for sf in files}
    classes: dict[str, list] = {p: ff.classes for p, ff in facts.items()}
    for f in g.nodes:
        sf = by_path[f.path]
        if f.kind == "file":
            if sf.kind == "text":
                if sf.lang in ("jsp",):
                    f.entry = "page (can be requested directly)"
                elif sf.lang in ("html", "twig", "erb", "ejs", "template", "razor"):
                    f.framework = "page or template (rendered by the web server or the framework)"
                elif sf.lang in ("xml", "config"):
                    f.framework = "configuration read by the framework"
                continue
            if sf.lang == "php" and not facts[f.path].minified:
                ff = facts[f.path]
                included = any(g.edges[(src, f.id)].kind == "import" for src in g.inc.get(f.id, ()))
                if ff.top_input:
                    f.entry = "PHP page (reads request input or writes output at top level)"
                elif ff.top_code and not included:
                    f.entry = "PHP page (runs code at top level and no other file includes it)"
                elif ff.top_code and re.search(r"\?>\s*<", sf.text):
                    f.entry = "PHP page (contains HTML)"
            elif sf.lang == "python" and PY_MAIN.search(sf.text):
                f.entry = "script (runs when started: if __name__ == '__main__')"
            elif sf.lang in ("javascript", "typescript") and sf.text.startswith("#!"):
                f.entry = "script (starts with #!)"
            if sf.lang in ("python", "javascript", "typescript", "ruby") and re.search(r"\b(?:argparse|sys\.argv|process\.argv|ARGV)\b", sf.text) \
                    and not f.entry and not f.nonprod:
                f.framework = f.framework or "reads the command line"
            continue
        a = f.ann
        if f.entry:
            pass
        elif ENTRY_ANN.search(a):
            f.entry = "entry by annotation: " + ENTRY_ANN.search(a).group(0).strip()
        elif f.name in ENTRY_NAMES and ENTRY_NAMES[f.name] and not (
                f.name == "main" and f.lang in ("python", "javascript", "typescript", "ruby", "php")):
            f.entry = ENTRY_NAMES[f.name]
        if not f.entry:
            cls_line = next((r for n, s, e, r in classes.get(f.path, ()) if s <= f.line <= e), "")
            cls_name = next((n for n, s, e, r in classes.get(f.path, ()) if s <= f.line <= e), "")
            if f.lang == "python" and f.name in PY_VIEW_METHODS and re.search(r"View|ViewSet|APIView|Resource|Handler", a + " " + cls_line):
                f.entry = f"method of a web view class ({f.name})"
            elif f.lang == "csharp" and cls_name.endswith("Controller") and re.search(r"^\s*public\b", by_path[f.path].text.split("\n")[f.line - 1]):
                f.entry = "public action of an ASP.NET controller"
            elif f.lang == "php" and cls_name.endswith("Controller") and not f.name.startswith("__") and re.search(r"^\s*public\s+function", by_path[f.path].text.split("\n")[f.line - 1]):
                f.framework = "public method of a controller class (usually routed)"
        if not f.entry and not f.framework:
            cls = next(((n, r) for n, s_, e_, r in classes.get(f.path, ()) if s_ <= f.line <= e_), None)
            if cls and (f.name == cls[0] or f.name in ("__construct", "__init__", "constructor", "initialize")) \
                    and DI_CLASS.search(cls[1]):
                f.framework = f"constructor of a class the framework creates ({DI_CLASS.search(cls[1]).group(0)})"
        if not f.entry and not f.framework:
            if FRAMEWORK_ANN.search(a):
                f.framework = "run by the framework: " + FRAMEWORK_ANN.search(a).group(0).strip()
            elif "@object-property" in a:
                f.framework = "function stored in an object literal (a callback handed to a library or framework)"
            elif f.name in FRAMEWORK_NAMES or (f.name.startswith("__") and f.name.endswith("__")):
                f.framework = f"well-known name ({f.name}): called by the language, a framework or an interface"
            elif GETTER.match(f.name) and f.lang in ("java", "kotlin", "csharp", "scala"):
                f.framework = "getter/setter: often called by frameworks, templates or serialisers"
            elif re.search(r"@(?:Test|ParameterizedTest|RepeatedTest|pytest)\b", a):
                f.framework = "test function"
        p = _matches(cfg.entries, f)
        if p:
            f.entry = f"entry point from the config ({p})"
        p = _matches(cfg.framework, f)
        if p and not f.entry:
            f.framework = f"framework code from the config ({p})"


STATUS = ["entry", "reached", "maybe", "framework", "via_framework", "dead_branch", "not_reached", "tests_only",
          "referenced", "no_caller", "ignored", "non_production"]
STATUS_LABEL = {
    "entry": "Entry point", "reached": "Called from an entry point", "maybe": "Maybe called (only by name)",
    "framework": "Run by the framework", "via_framework": "Called from framework code",
    "dead_branch": "Only called from unreached code", "not_reached": "Has callers, none reached",
    "tests_only": "Only called by tests", "referenced": "Name appears, no call found",
    "no_caller": "No caller found", "ignored": "Ignored by config", "non_production": "Test, docs or vendor code"}


def walk(g: Graph, cfg: Config) -> None:
    """Breadth-first from the roots: first entry points over sure links, then over links by name only, then the
    same from framework code. The first way that reaches a function is the one shown as its path."""
    prod = [f for f in g.nodes if not f.nonprod]
    origin: dict[int, str] = {}
    for f in g.nodes:
        f.pred, f.depth, f.sure = -1, -1, True
    entries = [f.id for f in prod if f.entry]
    fw = [f.id for f in prod if f.framework and not f.entry]

    def run(roots: list[int], kind: str, sure_only: bool) -> None:
        q = deque(roots)
        while q:
            n = q.popleft()
            for m in g.out.get(n, ()):
                e = g.edges[(n, m)]
                if sure_only and not e.sure:
                    continue
                tgt = g.nodes[m]
                if tgt.nonprod or m in origin and (origin[m] == "entry" or kind == "framework"):
                    continue
                if tgt.entry:
                    continue
                origin[m] = kind
                tgt.pred, tgt.depth = n, g.nodes[n].depth + 1
                tgt.sure = e.sure and g.nodes[n].sure
                q.append(m)

    for i in entries:
        origin[i], g.nodes[i].depth = "entry", 0
    run(entries, "entry", True)
    run([i for i, k in origin.items() if k == "entry"], "entry", False)
    for i in fw:
        if i not in origin:
            origin[i], g.nodes[i].depth = "framework", 0
    run([i for i, k in origin.items() if k == "framework"], "framework", True)
    run([i for i, k in origin.items() if k == "framework"], "framework", False)

    def prod_callers(f: Func) -> list[int]:
        return [s for s in g.inc.get(f.id, ()) if not g.nodes[s].nonprod and g.edges[(s, f.id)].kind != "loaded"]

    for f in g.nodes:
        if f.nonprod:
            f.status, f.reason = "non_production", f"not production code ({f.nonprod})"
            continue
        k = origin.get(f.id)
        if f.entry:
            f.status, f.reason = "entry", f.entry
        elif k == "entry" and f.depth > 0:
            f.status = "reached" if f.sure else "maybe"
            e = g.edges[(f.pred, f.id)]
            if f.sure:
                f.reason = f"called from {g.nodes[f.pred].qual} ({e.how}), {f.depth} step(s) from an entry point"
            else:
                weak = next((x for x in why_alive(g, f) if not x["sure"] and x["how"]), None)
                hop = g.nodes[weak["id"]] if weak else f
                f.reason = (f"{f.depth} step(s) from an entry point, but the path relies on a link matched by name only "
                            f"(to {hop.qual}: {weak['how'] if weak else e.how})")
        elif f.framework and k != "entry":
            f.status, f.reason = "framework", f.framework
        elif k == "framework" and f.depth > 0:
            f.status = "via_framework"
            e = g.edges[(f.pred, f.id)]
            f.reason = f"called from {g.nodes[f.pred].qual} ({e.how}), which the framework runs"
        else:
            pc = prod_callers(f)
            tc = [s for s in g.inc.get(f.id, ()) if g.nodes[s].nonprod]
            if pc:
                f.status = "not_reached"
                f.reason = (f"called from {len(pc)} place(s) in production code, but none of them is reached from an "
                            f"entry point")
            elif tc:
                f.status, f.reason = "tests_only", f"only called from test or example code ({len(tc)} place(s))"
            elif f.kind == "function" and (pre := next((x for x in getattr(g, "prefixes", [])
                                                        if f.name.startswith(x[2]) and len(f.name) > len(x[2])), None)):
                f.status = "referenced"
                f.reason = (f"probably called by a name built at runtime: '{pre[2]}' + … at {pre[0]}:{pre[1]}")
            elif f.kind == "function" and g.words.get(f.name, 0) > len({g.nodes[i].path for i in g.by_name.get(f.name, ())}):
                f.status = "referenced"
                f.reason = ("the name appears in other files, but not as a call this tool recognises (reflection, "
                            "configuration, a call through another name, or just the same word)")
            elif f.kind == "file" and (dp := next((x for x in getattr(g, "dyn_paths", [])
                                                     if ("/" + os.path.dirname(f.path) + "/").endswith("/" + x[2])), None)):
                f.status = "referenced"
                f.reason = f"probably loaded by a path built at runtime: '{dp[2]}' + … at {dp[0]}:{dp[1]}"
            elif f.kind == "file":
                f.status, f.reason = "no_caller", "no file imports, includes or links to this file"
            else:
                f.status, f.reason = "no_caller", "the name appears nowhere else in the project"
        if f.status in ("not_reached", "tests_only", "referenced", "no_caller") and _matches(cfg.ignore, f):
            f.status, f.reason = "ignored", f"ignored by the config ({_matches(cfg.ignore, f)})"
    rank = {s: i for i, s in enumerate(STATUS)}
    funcs_of: dict[str, list[Func]] = defaultdict(list)
    for f in g.nodes:
        if f.kind == "function":
            funcs_of[f.path].append(f)
    for f in g.nodes:
        if f.kind == "file" and f.lang in CODE.values() and f.lang not in SCRIPT and not f.nonprod:
            fs = funcs_of.get(f.path)
            if fs:
                best = min(fs, key=lambda x: rank[x.status])
                f.status, f.reason = best.status, f"best of its functions: {best.qual} ({STATUS_LABEL[best.status]})"
            else:
                f.status, f.reason = "referenced", "no functions found in this file (types, constants or interfaces only)"
    # unreached code reached only from other unreached code: report the top of each dead branch
    dead = {f.id for f in g.nodes if f.status in ("not_reached", "no_caller", "referenced")}
    for f in g.nodes:
        if f.status != "not_reached":
            continue
        pc = prod_callers(f)
        if pc and all(c in dead for c in pc):
            # walk up to a dead function without dead callers (cycle-safe)
            seen, cur = {f.id}, pc[0]
            while True:
                up = [c for c in prod_callers(g.nodes[cur]) if c in dead and c not in seen]
                if not up:
                    break
                seen.add(cur)
                cur = up[0]
            if cur != f.id:
                f.status, f.dead_root = "dead_branch", cur
                f.reason = f"only called from code that is itself not reached (top of that branch: {g.nodes[cur].qual})"


def why_alive(g: Graph, f: Func, limit: int = 30) -> list[dict]:
    """The chain from a root to f: [{node, how, sure}] (root first)."""
    chain, cur, seen = [], f, set()
    while cur is not None and cur.id not in seen and len(chain) < limit:
        seen.add(cur.id)
        if cur.pred == -1:
            chain.append({"id": cur.id, "how": "", "sure": True})
            break
        e = g.edges[(cur.pred, cur.id)]
        chain.append({"id": cur.id, "how": e.how, "sure": e.sure, "at": f"{e.path}:{e.line}"})
        cur = g.nodes[cur.pred]
    return list(reversed(chain))


# --------------------------------------------------------------------------------------------------------------
# Attack surface: endpoints, their access checks, dangerous calls they reach; hotspots; git age; run comparison
# --------------------------------------------------------------------------------------------------------------
# Calls that hand data to something dangerous. Matched on the code (comments and string contents do not count).
SINKS = [
    ("code", "code evaluation", re.compile(
        r"\beval\s*\(|\bnew\s+Function\s*\(|\bcreate_function\s*\(|\bScriptEngine\w*|\.evaluate\s*\(|"
        r"\brender_template_string\s*\(|\bvm\.run\w*\s*\(|\bexecjs\b|\bTemplate\s*\(\s*request")),
    ("command", "operating system command", re.compile(
        r"\bRuntime\.getRuntime\(\)\.exec\b|\bnew\s+ProcessBuilder\b|\bos\.(?:system|popen|exec\w*|spawn\w*)\s*\(|"
        r"\bsubprocess\.(?:call|run|Popen|check_output|check_call|getoutput|getstatusoutput)\s*\(|"
        r"(?<![\w.>$])(?:shell_exec|passthru|proc_open|popen|pcntl_exec)\s*\(|(?<![\w.>$:])(?:system|exec)\s*\(\s*\$|"
        r"\bchild_process\b|\b(?:exec|execSync|spawn|spawnSync|execFile)\s*\(\s*[`'\"]?\s*\w|\bexec\.Command\s*\(|"
        r"\bProcess\.Start\s*\(|\bCommandLine\.parse\b")),
    ("deserialization", "deserialization of data", re.compile(
        r"\bObjectInputStream\b|\.readObject\s*\(|\bXMLDecoder\b|\bunserialize\s*\(|\bpickle\.loads?\s*\(|"
        r"\byaml\.(?:load|unsafe_load)\s*\(|\bMarshal\.load\b|\bBinaryFormatter\b|\bXStream\b|\bjsonpickle\.decode\b|"
        r"\bdeserialize\s*\(|\bSerializationUtils\.deserialize\b|\bshelve\.open\b")),
    ("sql", "SQL query", re.compile(
        r"\.execute(?:Query|Update|LargeUpdate)?\s*\(|\bprepareStatement\s*\(|\bcreate(?:Native)?Query\s*\(|"
        r"\bjdbcTemplate\.\w+\s*\(|\bmysqli?_query\s*\(|\bmysqli_multi_query\s*\(|\bpg_query\s*\(|\bsqlite_query\s*\(|"
        r"->(?:query|exec|prepare)\s*\(|\bcursor\.execute\w*\s*\(|\bsequelize\.query\s*\(|\.raw\s*\(\s*[`'\"f]|"
        r"\bdb\.(?:Query|QueryRow|Exec)\w*\s*\(|\bSqlCommand\b|\.query\s*\(\s*[`'\"]\s*(?:SELECT|INSERT|UPDATE|DELETE|WITH)",
        re.I)),
    ("file", "file access", re.compile(
        r"\bnew\s+File(?:InputStream|OutputStream|Reader|Writer)?\s*\(|\bFiles\.(?:read\w*|write\w*|new\w+|copy|move|"
        r"delete\w*|lines)\s*\(|\bPaths\.get\s*\(|\bfopen\s*\(|\bfile_(?:get|put)_contents\s*\(|\breadfile\s*\(|"
        r"\bmove_uploaded_file\s*\(|\bunlink\s*\(|\b(?:include|require)(?:_once)?\s*\(?\s*\$|"
        r"\bfs\.(?:readFile|writeFile|appendFile|createReadStream|createWriteStream|unlink|readdir|rm|rename)\w*\s*\(|"
        r"\bsendFile\s*\(|\.download\s*\(|(?<![\w.])open\s*\(\s*(?![\"'])|\bos\.(?:Open|Create|ReadFile|WriteFile)\s*\(|"
        r"\bioutil\.(?:ReadFile|WriteFile)\s*\(|\bsend_file\s*\(|\bsend_from_directory\s*\(|\bZipFile\b|\bZipInputStream\b")),
    ("xml", "XML parser (external entities)", re.compile(
        r"\bDocumentBuilderFactory\b|\bSAXParserFactory\b|\bXMLInputFactory\b|\bSAXReader\b|\bSAXBuilder\b|"
        r"\bsimplexml_load_(?:string|file)\s*\(|->loadXML\s*\(|\betree\.(?:parse|fromstring|XML)\s*\(|"
        r"\bparseXml(?:String)?\s*\(|\bXmlDocument\b|\bUnmarshaller\b")),
    ("request", "outgoing request (SSRF)", re.compile(
        r"\.openConnection\s*\(|\.openStream\s*\(|\bRestTemplate\b|\bWebClient\b|\bHttpClient\b|\bOkHttpClient\b|"
        r"\brequests\.(?:get|post|put|delete|request|head)\s*\(|\burllib\.request\.urlopen\s*\(|\burlopen\s*\(|"
        r"\bcurl_exec\s*\(|\bfetch\s*\(|\baxios(?:\.\w+)?\s*\(|\bhttps?\.(?:get|request)\s*\(|\bhttp\.(?:Get|Post|NewRequest)\s*\(")),
    ("redirect", "redirect to a given address", re.compile(
        r"\bsendRedirect\s*\(|\bres\.redirect\s*\(|\bredirect\s*\(|header\s*\(\s*['\"]Location|\bRedirectView\b|"
        r"\bHttpResponseRedirect\b|\bRedirect(?:Permanent)?\s*\(")),
]
SINK_ORDER = [k for k, _l, _p in SINKS]
SINK_LABEL = {k: lbl for k, lbl, _p in SINKS}


def sinks_in(sf: SrcFile, ff: FileFacts) -> list[tuple[int, str, str]]:
    """(line, kind, code) of dangerous calls. A match inside a comment or a string does not count."""
    active = [(k, p) for k, _l, p in SINKS if p.search(sf.text)]      # one pass per file: most files have no sink at all
    if not active:
        return []
    raw = sf.text.split("\n")
    cleaned = clean(sf.text, sf.lang)[0] if sf.lang != "python" else \
        [re.sub(r"#.*$", "", x) for x in raw]
    out = []
    for no, line in enumerate(raw, 1):
        if len(line) > MAX_LINE or no - 1 >= len(cleaned):
            continue
        cl = cleaned[no - 1]
        for kind, pat in active:
            m = pat.search(line)
            while m and (m.start() >= len(cl) or cl[m.start()] != line[m.start()]):
                m = pat.search(line, m.start() + 1)                  # the match starts in a comment or string
            if m:
                out.append((no, kind, line.strip()[:160]))
                break
    return out


ROUTE_PARTS = re.compile(r"""\.(?P<m>get|post|put|delete|patch|all|use|route|options|head|any|match|HandleFunc|Handle|
    GET|POST|PUT|DELETE|PATCH|Any|Get|Post|Put|Delete|Patch|Map(?:Get|Post|Put|Delete)|add_url_rule|add_api_route)\s*\(\s*
    (?:\[[^\]]*\]\s*,\s*)?[`'"](?P<p>[^`'"]*)[`'"]""", re.X)
LARAVEL = re.compile(r"""Route::(?P<m>\w+)\s*\(\s*['"](?P<p>[^'"]*)['"]""")
DJANGO = re.compile(r"""\b(?:re_)?path\s*\(\s*r?['"](?P<p>[^'"]*)['"]|\burl\s*\(\s*r?['"](?P<p2>[^'"]*)['"]""")
HTTP_WORDS = {"get": "GET", "post": "POST", "put": "PUT", "delete": "DELETE", "patch": "PATCH", "options": "OPTIONS",
              "head": "HEAD", "all": "ANY", "any": "ANY", "use": "ANY", "route": "ANY", "match": "ANY",
              "handlefunc": "ANY", "handle": "ANY", "add_url_rule": "ANY", "add_api_route": "ANY",
              "mapget": "GET", "mappost": "POST", "mapput": "PUT", "mapdelete": "DELETE", "resource": "ANY",
              "apiresource": "ANY", "view": "GET"}


def route_from_line(raw: str) -> dict | None:
    m = ROUTE_PARTS.search(raw) or LARAVEL.search(raw)
    if m:
        return {"method": HTTP_WORDS.get(m.group("m").lower(), m.group("m").upper()), "path": m.group("p") or "/"}
    m = DJANGO.search(raw)
    if m:
        p = m.group("p") if m.group("p") is not None else m.group("p2")
        return {"method": "ANY", "path": "/" + p.lstrip("^").rstrip("$")}
    return None


_STRLIT = re.compile(r"""["']([^"']*)["']""")


CONSTS: dict[str, str] = {}


def _first_str(text: str) -> str:
    """The path in an annotation: the first string, or the value of a constant (path = URL_LABELS_MVC)."""
    text = text or ""
    m = _STRLIT.search(text)
    c = re.search(r"(?:^|\(|,)\s*(?:value\s*=\s*|path\s*=\s*)?\{?\s*([A-Z][A-Z0-9_]{2,}(?:\.[A-Z][A-Z0-9_]+)?)\b", text)
    if c and (not m or c.start() < m.start()):
        name = c.group(1).split(".")[-1]
        return CONSTS.get(name, "{" + name + "}")
    return m.group(1) if m else ""


def _join(base: str, path: str) -> str:
    base, path = (base or "").strip(), (path or "").strip()
    if not base:
        return path or "/"
    return "/" + "/".join(x.strip("/") for x in (base, path) if x.strip("/"))


SPRING = re.compile(r"@(Get|Post|Put|Delete|Patch|Request)Mapping\b(?:\s*\(([^)]*)\))?")
JAXRS_M = re.compile(r"@(GET|POST|PUT|DELETE|PATCH|HEAD|OPTIONS)\b")
JAXRS_P = re.compile(r"@Path\s*\(\s*\"([^\"]*)\"")
PY_ROUTE = re.compile(r"@[\w.]*?\.?(route|get|post|put|delete|patch|api_route|websocket)\(\s*['\"]([^'\"]*)['\"]([^)]*)")
ASPNET = re.compile(r"\[Http(Get|Post|Put|Delete|Patch)(?:\s*\(\s*\"([^\"]*)\")?")
ASP_ROUTE = re.compile(r"\[Route\s*\(\s*\"([^\"]*)\"")
RUST_ROUTE = re.compile(r"#\[(get|post|put|delete|patch)\s*\(\s*\"([^\"]*)\"")
WEB_SERVLET = re.compile(r"@WebServlet\s*\(\s*(?:urlPatterns\s*=\s*|value\s*=\s*)?\{?\s*\"([^\"]*)\"")
JOB = re.compile(r"@(Scheduled|KafkaListener|RabbitListener|JmsListener|SqsListener|EventListener|StreamListener|"
                 r"MessageMapping|SubscribeMapping|Cron|Process|EventPattern|MessagePattern)\b|"
                 r"@[\w.]*(?:task|shared_task|command|on_event|cron|job|consumer|subscriber)\b")
AUTH_ANN = re.compile(r"@(?:PreAuthorize|PostAuthorize|Secured|RolesAllowed|UseGuards|Authenticated|RequiresAuthentication|"
                      r"RequiresRoles|RequiresPermissions)\b(?:\s*\([^)]*\))?|\[Authorize\b[^\]]*\]|"
                      r"@[\w.]*(?:login_required|permission_required|user_passes_test|staff_member_required|"
                      r"jwt_required|auth_required|requires_auth|token_required|admin_required|roles_required|"
                      r"permission_classes|authentication_classes)\b(?:\([^)]*\))?")
PUBLIC_ANN = re.compile(r"@(?:PermitAll|AnonymousAllowed|Public)\b|\[AllowAnonymous\]|AllowAny\b")
AUTH_WORD = re.compile(r"(?i)(?:auth|login|logged|sign_?in|guard|jwt|token|session|permission|privilege|role|admin|acl|"
                       r"protect|isAuthorized|ensure\w*user|require\w*user|current_?user|is_?granted|has_?access|"
                       r"check_?access|csrf|authenticated)")
AUTH_CALL = re.compile(r"(?i)^(?:is|has|check|require|ensure|verify|validate|assert|must|do)?_?(?:auth\w*|logged\w*|"
                       r"login\w*|sign_?in\w*|session_?(?:check|valid\w*|require\w*)|permission\w*|privilege\w*|"
                       r"roles?|admin\w*|access\w*|token_?(?:valid\w*|check\w*|require\w*)|jwt\w*|csrf\w*|granted\w*|"
                       r"current_?user|user_?logged\w*|authorize\w*)$")
AUTH_ARG = re.compile(r"""(?<!\[)(?<!\[\s)["'](?:authenticated|logged_?in|login|admin|auth\w*|ROLE_\w+)["']""", re.I)
CENTRAL_AUTH = re.compile(r"\b(?:authorizeHttpRequests|authorizeRequests|authorizeExchange|SecurityFilterChain|"
                          r"WebSecurityConfigurerAdapter|antMatchers|requestMatchers|mvcMatchers)\b|"
                          r"\bapp\.use\s*\(\s*(?:['\"][^'\"]*['\"]\s*,\s*)?(?:[\w]+\.)*(?:isAuthorized|auth\w*|jwt\w*|passport\w*|"
                          r"session\w*|ensure\w*|require\w*Auth\w*)\b",
                          re.I)


def _cls(g: Graph, f: Func) -> tuple[str, str]:
    for name, s, e, rest in getattr(g, "classes", {}).get(f.path, ()):
        if s <= f.line <= e:
            return name, rest
    return "", ""


def endpoint_of(g: Graph, f: Func, text_lines: list[str]) -> dict:
    """What an entry point is from the outside: HTTP method and path, a page, a job or a program start."""
    a = f.ann
    cname, crest = _cls(g, f)
    if f.routes:
        r = f.routes[0]
        return {"kind": "http", "method": r["method"], "path": r["path"], "more": len(f.routes) - 1}
    m = SPRING.search(a)
    if m:
        args = m.group(2) or ""
        method = m.group(1).upper() if m.group(1) != "Request" else \
            "|".join(re.findall(r"RequestMethod\.(\w+)", args)) or "ANY"
        cb = SPRING.search(crest)
        base = _first_str(cb.group(2)) if cb and cb.group(1) == "Request" else ""
        return {"kind": "http", "method": method, "path": _join(base, _first_str(args))}
    if JAXRS_M.search(a) or (JAXRS_P.search(a) and f.lang in ("java", "kotlin")):
        mm = JAXRS_M.search(a)
        return {"kind": "http", "method": mm.group(1) if mm else "ANY",
                "path": _join(JAXRS_P.search(crest).group(1) if JAXRS_P.search(crest) else "",
                              JAXRS_P.search(a).group(1) if JAXRS_P.search(a) else "")}
    m = PY_ROUTE.search(a)
    if m:
        verb = m.group(1).upper()
        if verb in ("ROUTE", "API_ROUTE"):
            ms = re.findall(r"['\"](GET|POST|PUT|DELETE|PATCH)['\"]", m.group(3), re.I)
            verb = "|".join(x.upper() for x in ms) or "GET"
        return {"kind": "http", "method": verb, "path": m.group(2) or "/"}
    m = ASPNET.search(a)
    if m:
        cr = ASP_ROUTE.search(crest)
        base = (cr.group(1) if cr else "").replace("[controller]", re.sub(r"Controller$", "", cname))
        return {"kind": "http", "method": m.group(1).upper(), "path": _join(base, m.group(2) or "")}
    m = RUST_ROUTE.search(a)
    if m:
        return {"kind": "http", "method": m.group(1).upper(), "path": m.group(2)}
    if f.name in ("doGet", "doPost", "doPut", "doDelete", "service", "doFilter"):
        ws = WEB_SERVLET.search(crest)
        return {"kind": "http", "method": {"doGet": "GET", "doPost": "POST", "doPut": "PUT", "doDelete": "DELETE"}.get(f.name, "ANY"),
                "path": ws.group(1) if ws else "(servlet mapping in web.xml)"}
    if f.kind == "file" and f.lang in ("php", "jsp"):
        txt = "\n".join(text_lines)
        verbs = [v for v, pat in (("GET", r"\$_GET\b|\$_REQUEST\b"), ("POST", r"\$_POST\b|\$_FILES\b|\$_REQUEST\b"))
                 if re.search(pat, txt)]
        return {"kind": "page", "method": "|".join(verbs) or "GET", "path": "/" + f.path}
    m = JOB.search(a)
    if m:
        return {"kind": "job", "method": "JOB", "path": m.group(0)}
    if "main" in f.entry or "script" in f.entry:
        return {"kind": "program", "method": "RUN", "path": f.path}
    if f.entry.startswith("middleware"):
        return {"kind": "middleware", "method": "MW", "path": f.entry}
    if "route" in f.entry:
        return {"kind": "http", "method": "ANY", "path": "(route, path not read)"}
    return {"kind": "other", "method": "", "path": f.entry}


def auth_of(g: Graph, f: Func, text_lines: list[str], route_raw: list[str]) -> dict:
    """Is there a visible access check? Annotations first, then middleware on the route line, then a check call
    near the top of the handler. This is a reading of the code, not a test."""
    cname, crest = _cls(g, f)
    for where, text in (("annotation", f.ann), ("annotation on the class", crest)):
        m = PUBLIC_ANN.search(text)
        if m:
            return {"status": "public", "how": f"{where}: {m.group(0)}"}
        m = AUTH_ANN.search(text)
        if m:
            return {"status": "check", "how": f"{where}: {m.group(0)[:80]}"}
    for raw in route_raw:
        r = route_from_line(raw)
        head = raw.split(r["path"], 1)[-1] if r else raw
        names = [w for w in re.findall(r"[\w.$]+(?=\s*\()|[\w.$]+(?=\s*[,)])", head) if AUTH_CALL.search(w.split(".")[-1])]
        if names:
            return {"status": "check", "how": f"middleware on the route: {names[0]}"}
    body = text_lines[f.line:min(f.end, f.line + 25)] if f.kind == "function" else text_lines[:60]
    for ln in body:
        s = ln.strip()
        if not s or s.startswith(("//", "#", "*", "/*", "@", "[")):
            continue
        for m in re.finditer(r"([\w$]+)\s*\((?=([^()]*))", s):
            if AUTH_CALL.search(m.group(1)) or AUTH_ARG.search(m.group(2)):
                return {"status": "check", "how": f"check in the code: {s[:90]}"}
    return {"status": "none", "how": "no access check seen in annotations, route or the first lines"}


PATH_PARAM = re.compile(r"\{(?:\w+:)?(\w+)(?::[^}]*)?\}|<(?:\w+:)?(\w+)>|(?<=/):(\w+)")
PARAM_READS = [
    # (where, regex with the name in group 1)
    ("query", re.compile(r"""@(?:RequestParam|QueryParam)\s*\(\s*(?:value\s*=\s*|name\s*=\s*)?["'](\w[\w.-]*)["']""")),
    ("query", re.compile(r"""\b(?:req|request|ctx)\.(?:query|args|GET)(?:\.get\s*\(\s*|\.getlist\s*\(\s*|\[\s*|\.)['"]?(\w+)""")),
    ("query", re.compile(r"""\$_GET\s*\[\s*['"](\w+)['"]\s*\]|\$_REQUEST\s*\[\s*['"](\w+)['"]\s*\]""")),
    ("query", re.compile(r"""\bgetParameter\s*\(\s*["'](\w+)["']""")),
    ("query", re.compile(r"""\.(?:Query|DefaultQuery|QueryParam|FormValue)\s*\(\s*"(\w+)"|\bQuery\s*\(\s*["'](\w+)["']""")),
    ("path", re.compile(r"""@(?:PathVariable|PathParam)\s*\(\s*(?:value\s*=\s*|name\s*=\s*)?["'](\w+)["']""")),
    ("path", re.compile(r"""\b(?:req|request)\.params(?:\.get\s*\(\s*|\[\s*|\.)['"]?(\w+)""")),
    ("body", re.compile(r"""\b(?:req|request)\.(?:body|form|json|data|POST|FILES)(?:\.get\s*\(\s*|\[\s*|\.)['"]?(\w+)""")),
    ("body", re.compile(r"""\$_POST\s*\[\s*['"](\w+)['"]\s*\]|\$_FILES\s*\[\s*['"](\w+)['"]\s*\]""")),
    ("body", re.compile(r"""@FormParam\s*\(\s*["'](\w+)["']""")),
    ("header", re.compile(r"""@(?:RequestHeader|HeaderParam)\s*\(\s*(?:value\s*=\s*|name\s*=\s*)?["']([\w-]+)["']""")),
    ("header", re.compile(r"""\b(?:req|request)\.(?:headers|header|get)\s*(?:\(\s*|\[\s*|\.)['"]?([\w-]+)""")),
    ("cookie", re.compile(r"""\$_COOKIE\s*\[\s*['"](\w+)['"]\s*\]|\b(?:req|request)\.cookies(?:\.get\s*\(\s*|\[\s*|\.)['"]?(\w+)|@CookieValue\s*\(\s*["'](\w+)["']""")),
]
BODY_ANY = re.compile(r"@RequestBody\b|\b(?:req|request)\.(?:body|json|data)\b(?!\s*[.\[])|request\.get_json\s*\(|"
                      r"\bjson\.NewDecoder\s*\(\s*r\.Body|\bgetInputStream\s*\(|php://input")
NOT_PARAMS = {"get", "getlist", "length", "keys", "values", "items", "has", "toString", "append", "push", "map", "json",
              "forEach", "includes", "indexOf", "trim", "toLowerCase", "split", "filter", "slice"}


def params_of(f: Func, text_lines: list[str], ep: dict) -> list[dict]:
    """Parameters an entry point reads: path placeholders, query, form/body, header, cookie. Read from the handler's
    own lines (not from what it calls), so this is a lower bound."""
    out: dict[tuple[str, str], dict] = {}
    for m in PATH_PARAM.finditer(ep.get("path", "") if ep.get("kind") == "http" else ""):
        out[("path", next(x for x in m.groups() if x))] = {"name": next(x for x in m.groups() if x), "in": "path"}
    if f.kind == "function":
        lo, hi = max(0, f.line - 4), min(f.end, f.line + 150, len(text_lines))   # annotations above + the handler
    else:
        lo, hi = 0, min(len(text_lines), 300)
    body = [x for x in text_lines[lo:hi] if len(x) <= MAX_LINE]
    for i, ln in enumerate(body):
        for where, rx in PARAM_READS:
            for m in rx.finditer(ln):
                name = next((x for x in m.groups() if x), "")
                if name and name not in NOT_PARAMS and (where, name) not in out and len(out) < 40:
                    out[(where, name)] = {"name": name, "in": where, "line": lo + i + 1}
        if not any(k[0] == "body" and k[1] == "*" for k in out) and BODY_ANY.search(ln) \
                and not any(k[0] == "body" for k in out):
            out[("body", "*")] = {"name": "(whole body)", "in": "body", "line": lo + i + 1}
    return list(out.values())


def analyse_surface(g: Graph, files: list[SrcFile]) -> dict:
    """Endpoints, dangerous calls they reach, and how many entry points pass through each function."""
    by_path = {sf.path: sf for sf in files}
    lines_of: dict[str, list[str]] = {}

    def text_lines(p: str) -> list[str]:
        if p not in lines_of:
            lines_of[p] = by_path[p].text.split("\n")
        return lines_of[p]

    CONSTS.clear()
    for sf in files:
        if sf.kind == "code" and sf.lang in ("java", "kotlin", "scala", "csharp"):
            for m in re.finditer(r"\b([A-Z][A-Z0-9_]{2,})\s*=\s*\"([^\"]*)\"", sf.text):
                CONSTS.setdefault(m.group(1), m.group(2))
    # access checks registered for a path elsewhere: app.use('/api/Users', security.isAuthorized())
    guards = []
    for sf in files:
        if sf.kind != "code" or sf.nonprod or sf.lang not in ("javascript", "typescript"):
            continue
        for no, raw in enumerate(sf.text.split("\n"), 1):
            if len(raw) > MAX_LINE or not ROUTE_LINE.search(raw):
                continue
            r = route_from_line(raw)
            if not r:
                continue
            tail = raw.split(r["path"], 1)[-1]
            names = [m.group(1) for m in re.finditer(r"([\w$]+)\s*\(", tail)] + re.findall(r"[\w$.]+(?=\s*[,)])", tail)
            hit = next((n for n in names if AUTH_CALL.search(n.split(".")[-1])), None)
            if hit:
                pat = re.escape(r["path"].rstrip("/")).replace("\\*", ".*")
                pat = re.sub(r":\\?\w+", "[^/]+", pat) if ":" in r["path"] else pat
                prefix = bool(re.search(r"\.(?:use|all)\s*\(", raw))
                guards.append((r["method"], re.compile("^" + pat + ("(?:/.*)?$" if prefix else "/?$")),
                               f"{hit} for {r['path']} ({sf.path}:{no})"))
    for f in g.nodes:
        f.via_entries = 0
    endpoints = []
    entries = [f for f in g.nodes if f.status == "entry" and f.entry and not f.nonprod]
    for f in entries:
        tl = text_lines(f.path)
        ep = endpoint_of(g, f, tl)
        route_raw = [text_lines(r["at"])[r["line"] - 1] for r in f.routes
                     if r.get("at") in by_path and 0 < r.get("line", 0) <= len(text_lines(r["at"]))]
        auth = auth_of(g, f, tl, route_raw)
        if auth["status"] == "none" and ep["kind"] == "http":
            for meth, rx, how in guards:
                if (meth in ("ANY", ep["method"]) or ep["method"] == "ANY") and rx.match(ep["path"]):
                    auth = {"status": "check", "how": f"middleware registered for the path: {how}"}
                    break
        # forward walk: every function this entry point can reach, and the dangerous calls among them
        seen, q, sinks, weak = {f.id: 0}, deque([f.id]), [], set()
        while q:
            n = q.popleft()
            if seen[n] > 25 or len(seen) > 4000:
                break
            node = g.nodes[n]
            if node.sinks:
                for line, kind, code in node.sinks[:5]:
                    sinks.append({"id": n, "kind": kind, "line": line, "code": code, "steps": seen[n],
                                  "sure": n not in weak})
            for m in g.out.get(n, ()):
                e = g.edges[(n, m)]
                if e.kind == "loaded" or m in seen or g.nodes[m].nonprod:
                    continue
                seen[m] = seen[n] + 1
                if not e.sure or n in weak:
                    weak.add(m)
                q.append(m)
        for n in seen:
            if n != f.id and n not in weak:
                g.nodes[n].via_entries += 1
        kinds = Counter(s["kind"] for s in sinks if s["sure"])
        maybe = Counter(s["kind"] for s in sinks if not s["sure"])
        sinks.sort(key=lambda s: (SINK_ORDER.index(s["kind"]), s["steps"]))
        sinks.sort(key=lambda s: (not s["sure"], SINK_ORDER.index(s["kind"]), s["steps"]))
        endpoints.append({"id": f.id, **ep, "params": params_of(f, tl, ep), "auth": auth, "sink_kinds": dict(kinds), "sink_kinds_maybe": dict(maybe),
                          "sinks": sinks[:40], "reaches": len(seen) - 1 - len(weak),
                          "findings": len(f.findings)})
    order = {"http": 0, "page": 1, "job": 2, "program": 3, "middleware": 4, "other": 5}
    endpoints.sort(key=lambda e: (order.get(e["kind"], 9), e["path"], e["method"]))
    central = []
    for sf in files:
        if sf.kind == "code" and not sf.nonprod:
            m = CENTRAL_AUTH.search(sf.text)
            if m:
                central.append(f"{sf.path}:{sf.text.count(chr(10), 0, m.start()) + 1} ({m.group(0)[:40]})")
    return {"endpoints": endpoints, "central_auth": central[:10]}


def hotspots(g: Graph, limit: int = 40) -> list[dict]:
    funcs = [f for f in g.nodes if f.kind == "function" and not f.nonprod and f.status != "entry"]
    funcs.sort(key=lambda f: (-f.via_entries, -len(g.inc.get(f.id, ()))))
    return [{"id": f.id, "via_entries": f.via_entries, "callers": len(g.inc.get(f.id, ())),
             "sinks": sorted({k for _l, k, _c in f.sinks}, key=SINK_ORDER.index)} for f in funcs[:limit] if f.via_entries]


def git_info(root: str) -> dict:
    """Last change and number of commits per file, from git (if the folder is in a repository)."""
    import subprocess
    try:
        top = subprocess.run(["git", "-C", root, "rev-parse", "--show-prefix", "--is-shallow-repository"],
                             capture_output=True, text=True, timeout=20)
        if top.returncode != 0:
            return {}
        prefix, shallow = (top.stdout.split("\n") + ["", ""])[:2]
        log = subprocess.run(["git", "-C", root, "log", "--format=%x00%ct", "--name-only", "--no-renames", "--", "."],
                             capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError):
        return {}
    if log.returncode != 0:
        return {}
    files: dict[str, list] = {}
    ts = 0
    for line in log.stdout.split("\n"):
        if line.startswith("\x00"):
            ts = int(line[1:] or 0)
        elif line.strip():
            p = line.strip()
            if prefix and p.startswith(prefix):
                p = p[len(prefix):]
            cur = files.setdefault(p, [ts, 0])
            cur[1] += 1
    return {"files": files, "shallow": shallow.strip() == "true"}


def attach_git(g: Graph, info: dict) -> dict:
    files = info.get("files") or {}
    now = time.time()
    old = 0
    for f in g.nodes:
        rec = files.get(f.path)
        if rec:
            f.changed, f.commits = rec[0], rec[1]
            if f.kind == "function" and f.status in ("no_caller", "not_reached", "dead_branch", "referenced") and \
                    now - rec[0] > 365 * 86400:
                old += 1
    return {"available": bool(files), "shallow": info.get("shallow", False), "unreached_unchanged_1y": old}


def compare_runs(doc: dict, previous_path: str) -> dict:
    with open(previous_path, encoding="utf-8") as fh:
        prev = json.load(fh)
    key = lambda n: (n["path"], n["qual"], n["kind"])                            # noqa: E731
    old = {key(n): n for n in prev.get("nodes", [])}
    new = {key(n): n for n in doc["nodes"]}
    alive = {"entry", "reached", "maybe", "framework", "via_framework"}
    out = {"previous": previous_path, "previous_generated": prev.get("generated", ""), "new": 0, "removed": 0,
           "now_reached": 0, "no_longer_reached": 0, "status_changed": 0, "endpoints_new": [], "endpoints_removed": [],
           "auth_changed": []}
    for k, n in new.items():
        o = old.get(k)
        if o is None:
            if n["kind"] == "function":
                n["change"] = "new"
                out["new"] += 1
        elif o["status"] != n["status"]:
            n["change"] = f"was: {o['status']}"
            out["status_changed"] += 1
            if n["status"] in alive and o["status"] not in alive:
                out["now_reached"] += 1
            elif o["status"] in alive and n["status"] not in alive:
                out["no_longer_reached"] += 1
    out["removed"] = sum(1 for k, o in old.items() if k not in new and o["kind"] == "function")
    ep_key = lambda e, nodes: (e["method"], e["path"])                           # noqa: E731
    old_eps = {ep_key(e, None): e for e in prev.get("endpoints", [])}
    new_eps = {ep_key(e, None): e for e in doc.get("endpoints", [])}
    out["endpoints_new"] = [f"{m} {p}" for (m, p) in new_eps if (m, p) not in old_eps][:50]
    out["endpoints_removed"] = [f"{m} {p}" for (m, p) in old_eps if (m, p) not in new_eps][:50]
    out["auth_changed"] = [f"{m} {p}: {old_eps[(m, p)]['auth']['status']} -> {e['auth']['status']}"
                           for (m, p), e in new_eps.items() if (m, p) in old_eps
                           and old_eps[(m, p)].get("auth", {}).get("status") != e["auth"]["status"]][:50]
    out["new_unprotected"] = [f"{m} {p}" for (m, p), e in new_eps.items() if (m, p) not in old_eps
                              and e.get("kind") == "http" and e["auth"]["status"] == "none"]
    out["auth_removed"] = [f"{m} {p}" for (m, p), e in new_eps.items() if (m, p) in old_eps
                           and old_eps[(m, p)].get("auth", {}).get("status") == "check" and e["auth"]["status"] == "none"]
    return out


def find_previous(runs_dir: str, root: str, before: str) -> str | None:
    if not os.path.isdir(runs_dir):
        return None
    best = None
    for name in sorted(os.listdir(runs_dir), reverse=True):
        p = os.path.join(runs_dir, name, "reachmap.json")
        if os.path.abspath(os.path.join(runs_dir, name)) == os.path.abspath(before) or not os.path.isfile(p):
            continue
        try:
            with open(p, encoding="utf-8") as fh:
                head = fh.read(4000)
            m = re.search(r'"root":\s*"((?:\\.|[^"\\])*)"', head)
            if m and json.loads(f'"{m.group(1)}"') == root:
                best = p
                break
        except (OSError, ValueError):
            continue
    return best


# --------------------------------------------------------------------------------------------------------------
# CodeRaster findings on the map
# --------------------------------------------------------------------------------------------------------------
def attach_findings(g: Graph, report_path: str) -> dict:
    with open(report_path, encoding="utf-8") as fh:
        doc = json.load(fh)
    funcs_by_file: dict[str, list[Func]] = defaultdict(list)
    for f in g.nodes:
        if f.kind == "function":
            funcs_by_file[f.path].append(f)
    counts = Counter()
    for item in doc.get("findings", []):
        c = item.get("candidate", {})
        path, line = c.get("path", ""), int(c.get("line", 0) or 0)
        if item.get("status") not in ("confirmed", "uncertain"):
            continue
        inside = [f for f in funcs_by_file.get(path, []) if f.line <= line <= f.end]
        target = max(inside, key=lambda f: f.line) if inside else (g.nodes[g.file_node[path]] if path in g.file_node else None)
        if target is None:
            counts["not on the map"] += 1
            continue
        target.findings.append({"rule": c.get("rule_id", ""), "line": line, "status": item.get("status"),
                                "severity": item.get("severity", ""), "fingerprint": c.get("fingerprint", "")})
        counts[f"{item.get('status')}, in: {STATUS_LABEL.get(target.status, target.status)}"] += 1
    return dict(counts)


# --------------------------------------------------------------------------------------------------------------
# Output
# --------------------------------------------------------------------------------------------------------------
def to_dict(g: Graph, root: str, meta: dict) -> dict:
    nodes = []
    for f in g.nodes:
        callers = [{"id": s, "how": g.edges[(s, f.id)].how, "kind": g.edges[(s, f.id)].kind,
                    "at": f"{g.edges[(s, f.id)].path}:{g.edges[(s, f.id)].line}", "sure": g.edges[(s, f.id)].sure}
                   for s in g.inc.get(f.id, ()) if g.edges[(s, f.id)].kind != "loaded" or f.kind == "file"][:60]
        callees = [{"id": t, "how": g.edges[(f.id, t)].how, "sure": g.edges[(f.id, t)].sure}
                   for t in g.out.get(f.id, ()) if g.edges[(f.id, t)].kind != "loaded"][:60]
        nodes.append({"id": f.id, "name": f.name, "qual": f.qual, "path": f.path, "line": f.line, "end": f.end,
                      "lang": f.lang, "kind": f.kind, "status": f.status, "reason": f.reason,
                      "entry": f.entry, "framework": f.framework, "depth": f.depth, "sure": f.sure,
                      "dead_root": f.dead_root, "pred": f.pred,
                      "pred_how": g.edges[(f.pred, f.id)].how if f.pred >= 0 else "",
                      "pred_sure": g.edges[(f.pred, f.id)].sure if f.pred >= 0 else True,
                      "why": why_alive(g, f) if f.status in
                      ("reached", "maybe", "via_framework") else [],
                      "callers": callers, "n_callers": len(g.inc.get(f.id, ())), "callees": callees,
                      "findings": f.findings, "code": f.lang in CODE.values(),
                      "sinks": [{"line": ln, "kind": k, "code": c} for ln, k, c in f.sinks[:20]],
                      "via_entries": f.via_entries, "changed": f.changed, "commits": f.commits})
    # module graph: calls between files, summed up (for the graph view)
    fe: dict[tuple[int, int], list] = {}
    for (a, b), e in g.edges.items():
        pa, pb = g.nodes[a].path, g.nodes[b].path
        if pa == pb:
            continue
        key = (g.file_node[pa], g.file_node[pb])
        cur = fe.setdefault(key, [0, 0])
        cur[0] += e.count
        cur[1] = cur[1] or int(e.sure)
    return {"tool": "reachmap", "version": VERSION, "root": root, "generated": meta["generated"],
            "stats": meta, "nodes": nodes, "file_edges": [[a, b, c, s_] for (a, b), (c, s_) in fe.items()]}


def summarize(g: Graph) -> dict:
    funcs = [f for f in g.nodes if f.kind == "function"]
    by_status = Counter(f.status for f in funcs)
    files = [f for f in g.nodes if f.kind == "file"]
    folder_dead: Counter = Counter()
    folder_all: Counter = Counter()
    for f in funcs:
        if f.nonprod:
            continue
        d = os.path.dirname(f.path) or "."
        folder_all[d] += 1
        if f.status in ("not_reached", "no_caller", "dead_branch", "referenced", "tests_only"):
            folder_dead[d] += 1
    no_entry_folders = [d for d, n in folder_all.items() if n >= 5 and folder_dead[d] == n]
    return {"functions": len(funcs), "production_functions": sum(1 for f in funcs if not f.nonprod),
            "files": len(files), "code_files": sum(1 for f in files if f.lang in CODE.values()),
            "by_status": {s: by_status.get(s, 0) for s in STATUS},
            "file_status": dict(Counter(f.status for f in files)),
            "edges": len(g.edges), "edges_by_name_only": sum(1 for e in g.edges.values() if not e.sure),
            "unlinked_names": g.unlinked.most_common(10),
            "folders_unreached": sorted(((d, folder_dead[d], folder_all[d]) for d in folder_dead),
                                        key=lambda x: (-x[1], x[0]))[:15],
            "folders_without_entry": sorted(no_entry_folders)[:20]}


def surface_summary(doc: dict) -> dict:
    eps = doc.get("endpoints", [])
    web = [e for e in eps if e["kind"] in ("http", "page")]
    reach = Counter()
    for e in web:
        for k in e["sink_kinds"]:
            reach[k] += 1
    funcs_with = Counter(s["kind"] for n in doc["nodes"] if n["status"] != "non_production" for s in n["sinks"])
    return {"endpoints": len(eps), "web": len(web), "web_no_check": sum(1 for e in web if e["auth"]["status"] == "none"),
            "web_no_check_with_sinks": sum(1 for e in web if e["auth"]["status"] == "none" and e["sink_kinds"]),
            "sinks_by_kind": {k: funcs_with[k] for k in SINK_ORDER if funcs_with[k]},
            "endpoints_reaching": {k: reach[k] for k in SINK_ORDER if reach[k]},
            "central_auth": doc.get("central_auth", [])}


def render_terminal(summary: dict, root: str, paths: list[str], seconds: float, color: bool) -> str:
    def c(s, code):
        return f"\x1b[{code}m{s}\x1b[0m" if color else s
    bs = summary["by_status"]
    out = [c(f"reachmap {VERSION}", "1") + f"  {root}",
           f"{summary['files']} files, {summary['functions']} functions "
           f"({summary['production_functions']} in production code), {seconds:.1f} s", ""]
    colors = {"entry": "36", "reached": "32", "maybe": "32", "framework": "35", "via_framework": "35",
              "dead_branch": "33", "not_reached": "33", "tests_only": "33", "referenced": "2", "no_caller": "31",
              "ignored": "2", "non_production": "2"}
    for s in STATUS:
        if bs.get(s):
            out.append(f"  {c(STATUS_LABEL[s].ljust(34), colors[s])}{bs[s]:>7}")
    if summary["edges_by_name_only"]:
        out += ["", f"{summary['edges_by_name_only']} of {summary['edges']} links are by name only "
                    "(the same name is defined in several places); they are shown dashed in the report."]
    if summary["folders_unreached"]:
        out += ["", c("Folders with the most code not reached from an entry point:", "1")]
        for d, n, total in summary["folders_unreached"][:10]:
            out.append(f"  {n:>5} of {total:<5} {d}/")
    if summary["folders_without_entry"]:
        out += ["", c("Nothing in these folders is reached. If they are in use, an entry point is probably "
                      "missing (add it to the config, see README):", "33")]
        out += [f"  {d}/" for d in summary["folders_without_entry"][:10]]
    sf = summary.get("surface")
    if sf and sf["endpoints"]:
        out += ["", c("Attack surface:", "1"),
                f"  {sf['web']} web endpoints and pages ({sf['endpoints'] - sf['web']} jobs, programs, other)",
                f"  {sf['web_no_check']} without a visible access check, {sf['web_no_check_with_sinks']} of them reach a dangerous call"]
        if sf["endpoints_reaching"]:
            out.append("  endpoints reaching: " + ", ".join(f"{SINK_LABEL[k]} {n}" for k, n in sf["endpoints_reaching"].items()))
        if sf["central_auth"]:
            out.append(c(f"  access rules are also set centrally ({sf['central_auth'][0]}); not evaluated per endpoint", "33"))
    hs = summary.get("hotspots")
    if hs:
        out += ["", c("Hotspots (most entry points pass through):", "1")]
        out += [f"  {h['via_entries']:>4} entry points  {h['qual']}  ({h['where']})" for h in hs[:5]]
    gi = summary.get("git")
    if gi and gi.get("available"):
        out += ["", f"git: {gi['unreached_unchanged_1y']} unreached functions in files unchanged for over a year"
                + (" (shallow clone: dates are not reliable)" if gi.get("shallow") else "")]
    df = summary.get("diff")
    if df:
        out += ["", c(f"Since the previous run ({df['previous_generated']}):", "1"),
                f"  {df['new']} new and {df['removed']} removed functions, {df['now_reached']} now reached, "
                f"{df['no_longer_reached']} no longer reached",
                f"  endpoints: {len(df['endpoints_new'])} new, {len(df['endpoints_removed'])} removed, "
                f"{len(df['auth_changed'])} with changed access check"]
        out += [f"  + {x}" for x in df["endpoints_new"][:5]] + [f"  ! {x}" for x in df["auth_changed"][:5]]
    if summary.get("findings"):
        out += ["", c("CodeRaster findings on the map:", "1")]
        out += [f"  {n:>5}  {k}" for k, n in sorted(summary["findings"].items(), key=lambda x: -x[1])]
    out += [""] + [f"report: {p}" for p in paths]
    out.append("Text search, not a type-aware parser (except Python): 'no caller found' is a lead, not proof.")
    return "\n".join(out)


def default_data_dir() -> str:
    env = os.environ.get("REACHMAP_DATA_DIR")
    if env:
        return env
    here = os.path.dirname(os.path.abspath(__file__))
    if re.match(r"reachmap-\d", os.path.basename(here)):
        return os.path.join(os.path.dirname(here), "reachmap-data")
    return "reachmap-data"


# ---- exports: OpenAPI (what the code exposes) and SARIF (findings for CI) ---------------------------------------

RULES = {
    "unprotected-sink": ("RM001", "warning", "Web endpoint without a visible access check reaches a dangerous call"),
    "unprotected-endpoint": ("RM002", "note", "Web endpoint without a visible access check"),
    "new-endpoint": ("RM003", "note", "Endpoint added since the baseline run"),
    "new-unprotected": ("RM004", "warning", "Endpoint added since the baseline run, without a visible access check"),
    "auth-removed": ("RM005", "error", "Access check seen in the baseline run is no longer seen"),
}


def rule_hits(doc: dict) -> list[dict]:
    """Findings per rule. A hit means 'look here', not 'vulnerable': checks that live in central configuration are
    not visible to reachmap."""
    eps = {(e["method"], e["path"]): e for e in doc.get("endpoints", [])}
    diff = doc.get("diff") or {}
    hits = []

    def add(rule, e, text):
        n = doc["nodes"][e["id"]]
        hits.append({"rule": rule, "text": text, "path": n["path"], "line": n["line"],
                     "endpoint": f"{e['method']} {e['path']}"})
    for e in doc.get("endpoints", []):
        if e["kind"] != "http" or e["auth"]["status"] != "none":
            continue
        kinds = sorted(e.get("sink_kinds", {}))
        if kinds:
            add("unprotected-sink", e, f"{e['method']} {e['path']} has no visible access check and reaches: "
                + ", ".join(SINK_LABEL.get(k, k) for k in kinds))
        else:
            add("unprotected-endpoint", e, f"{e['method']} {e['path']} has no visible access check")
    for key, rule, text in (("endpoints_new", "new-endpoint", "new endpoint {}"),
                            ("new_unprotected", "new-unprotected", "new endpoint without a visible access check: {}"),
                            ("auth_removed", "auth-removed", "access check no longer seen: {}")):
        for label in diff.get(key, []):
            m, _, p = label.partition(" ")
            if (m, p) in eps:
                add(rule, eps[(m, p)], text.format(label))
    return hits


def to_sarif(doc: dict) -> dict:
    ids = list(RULES)
    return {
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json", "version": "2.1.0",
        "runs": [{
            "tool": {"driver": {"name": "reachmap", "version": VERSION,
                                "informationUri": "https://example.invalid/reachmap",
                                "rules": [{"id": RULES[r][0], "name": r, "shortDescription": {"text": RULES[r][2]},
                                           "defaultConfiguration": {"level": RULES[r][1]}} for r in ids]}},
            "results": [{"ruleId": RULES[h["rule"]][0], "ruleIndex": ids.index(h["rule"]),
                         "level": RULES[h["rule"]][1], "message": {"text": h["text"]},
                         "locations": [{"physicalLocation": {"artifactLocation": {"uri": h["path"]},
                                                              "region": {"startLine": max(1, h["line"])}}}]}
                        for h in rule_hits(doc)]}]}


def to_openapi(doc: dict) -> dict:
    """Endpoints and parameters as OpenAPI 3.0: a description of what the code exposes, with the reachmap reading
    (access check, dangerous calls reached) as x- fields. It carries no example values and no requests."""
    paths: dict = {}
    for e in doc.get("endpoints", []):
        if e["kind"] != "http" or not str(e["path"]).startswith("/"):
            continue
        path = re.sub(r"<(?:\w+:)?(\w+)>", r"{\1}", re.sub(r"(?<=/):(\w+)", r"{\1}", e["path"]))
        path = re.sub(r"\{(?:\w+:)?(\w+)(?::[^}]*)?\}", r"{\1}", path)
        n = doc["nodes"][e["id"]]
        for meth in (e["method"].split("|") if e["method"] not in ("ANY", "") else ["ANY"]):
            op = {"summary": f"{n['qual']}", "operationId": f"{meth.lower()}_{re.sub(r'[^A-Za-z0-9]+', '_', path).strip('_') or 'root'}_{e['id']}",
                  "parameters": [], "responses": {"default": {"description": "not read from the code"}},
                  "x-reachmap-source": f"{n['path']}:{n['line']}",
                  "x-reachmap-access-check": e["auth"]["status"], "x-reachmap-access-how": e["auth"]["how"],
                  "x-reachmap-dangerous-calls": sorted(e.get("sink_kinds", {}))}
            if meth == "ANY":
                op["x-reachmap-method-unknown"] = True
            body = [p for p in e.get("params", []) if p["in"] == "body"]
            for p in e.get("params", []):
                if p["in"] in ("path", "query", "header", "cookie"):
                    op["parameters"].append({"name": p["name"], "in": p["in"], "required": p["in"] == "path",
                                             "schema": {"type": "string"}})
            if body and meth in ("POST", "PUT", "PATCH", "ANY"):
                named = {p["name"]: {"type": "string"} for p in body if p["name"] != "(whole body)"}
                op["requestBody"] = {"content": {"application/json": {"schema": {
                    "type": "object", "properties": named, **({"additionalProperties": True} if len(named) < len(body) else {})}}}}
            if not op["parameters"]:
                del op["parameters"]
            paths.setdefault(path, {})["get" if meth == "ANY" else meth.lower()] = op
    return {"openapi": "3.0.3",
            "info": {"title": os.path.basename(doc["root"].rstrip("/")) or "project", "version": "reachmap " + VERSION,
                     "description": "Read from source code by reachmap. A lower bound: routes, parameters and "
                                    "methods that could not be read are missing or marked."},
            "paths": dict(sorted(paths.items()))}


def render_trace(doc: dict, query: str, depth: int = 3, limit: int = 12) -> str:
    """Follow a function in the terminal: who calls it, up to the entry points, and what it calls."""
    nodes = doc["nodes"]
    q = query.lower()
    hits = [n for n in nodes if n["kind"] == "function" and n["name"].lower() == q] or \
           [n for n in nodes if n["kind"] == "function" and (q in n["qual"].lower() or q in n["path"].lower())]
    hits.sort(key=lambda n: (n["status"] == "non_production", len(n["qual"])))
    if not hits:
        return f"no function matches '{query}'"
    out = []

    def tree(nid: int, key: str, level: int, path: tuple, lines: list) -> None:
        seen = set()
        kids = []
        for c in nodes[nid][key]:
            n = nodes[c["id"]]
            if c["id"] in seen or c.get("kind") == "loaded" or "module is loaded" in c.get("how", "") \
                    or n["status"] == "non_production":
                continue
            seen.add(c["id"])
            kids.append((c, n))
        kids.sort(key=lambda x: (not x[0]["sure"], x[1]["qual"]))
        for c, n in kids[:limit]:
            mark = "" if c["sure"] else " (by name only)"
            cyc = "  ↻ already on this path" if c["id"] in path else ""
            ent = f"  [entry point: {n['entry']}]" if key == "callers" and n["status"] == "entry" else ""
            lines.append(f"{'  ' * level}{'└ ' if level else ''}{n['qual']}  {n['path']}:{n['line']}  ({n['status']}){mark}{ent}{cyc}")
            if level < depth and not cyc:
                tree(c["id"], key, level + 1, path + (c["id"],), lines)
        if len(kids) > limit:
            lines.append(f"{'  ' * level}... and {len(kids) - limit} more")

    for n in hits[:3]:
        out.append(f"{n['qual']}  {n['path']}:{n['line']}-{n['end']}  [{n['status']}]  {n['reason']}")
        if n["sinks"]:
            out.append("  dangerous calls inside: " + ", ".join(sorted({s['kind'] for s in n['sinks']})))
        up, down = [], []
        tree(n["id"], "callers", 1, (n["id"],), up)
        tree(n["id"], "callees", 1, (n["id"],), down)
        out.append("Called from:" + ("" if up else " nothing found"))
        out += up
        out.append("Calls:" + ("" if down else " nothing found"))
        out += down
        out.append("")
    if len(hits) > 3:
        out.append(f"{len(hits) - 3} more match(es): " + ", ".join(h["qual"] for h in hits[3:8]))
    return "\n".join(out)


def pack_sources(files: list, mode: str, max_total: int = 14 * 1024 * 1024) -> tuple[dict, dict]:
    """Source text for the report's code view: zlib + base64 per file, decoded in the browser when a file is opened.
    mode: production (default: not tests, docs or vendored code), all, none."""
    out: dict[str, str] = {}
    info = {"mode": mode, "files": 0, "too_large": 0, "over_budget": 0, "bytes": 0}
    if mode == "none":
        return out, info
    for sf in sorted(files, key=lambda f: (bool(f.nonprod), len(f.text))):
        if mode == "production" and sf.nonprod:
            continue
        if len(sf.text) > 400 * 1024:
            info["too_large"] += 1
            continue
        blob = base64.b64encode(zlib.compress(sf.text.encode("utf-8", "replace"), 6)).decode("ascii")
        if info["bytes"] + len(blob) > max_total:
            info["over_budget"] += 1
            continue
        out[sf.path] = blob
        info["bytes"] += len(blob)
        info["files"] += 1
    return out, info


def write_reports(doc: dict, out: str, formats: list[str], sources: dict | None = None,
                  source_info: dict | None = None) -> list[str]:
    os.makedirs(out, exist_ok=True)
    paths = []
    if "json" in formats:
        p = os.path.join(out, "reachmap.json")
        with open(p, "w", encoding="utf-8") as fh:
            json.dump(doc, fh, separators=(",", ":"))
        paths.append(p)
    if "sarif" in formats:
        p = os.path.join(out, "reachmap.sarif")
        with open(p, "w", encoding="utf-8") as fh:
            json.dump(to_sarif(doc), fh, indent=1)
        paths.append(p)
    if "openapi" in formats:
        p = os.path.join(out, "reachmap-openapi.json")
        with open(p, "w", encoding="utf-8") as fh:
            json.dump(to_openapi(doc), fh, indent=1)
        paths.append(p)
    if "html" in formats:
        p = os.path.join(out, "reachmap.html")
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(to_html(doc, sources, source_info))
        paths.append(p)
    return paths


def to_html(doc: dict, sources: dict | None = None, source_info: dict | None = None) -> str:
    slim = dict(doc)
    slim["nodes"] = [{k: v for k, v in n.items() if k != "why"} for n in doc["nodes"]]
    data = json.dumps(slim, separators=(",", ":")).replace("</", "<\\/")
    title = html.escape(os.path.basename(doc["root"].rstrip("/")) or doc["root"])
    labels = json.dumps(STATUS_LABEL)
    return HTML.replace("__TITLE__", title).replace("__DATA__", data).replace("__LABELS__", labels) \
               .replace("__SINKS__", json.dumps(SINK_LABEL)) \
               .replace("__SRC__", json.dumps(sources or {}, separators=(",", ":")).replace("</", "<\\/")) \
               .replace("__SRCINFO__", json.dumps(source_info or {"mode": "none"})) \
               .replace("__VERSION__", VERSION)


HTML = r"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>reachmap: __TITLE__</title>
<style>
:root{--bg:#f6f7f9;--surface:#fff;--ink:#1d2330;--muted:#5d6676;--line:#d9dde4;--accent:#2457c5;--hover:#eef2f8;
--s-entry:#2457c5;--s-reached:#1f8a4c;--s-maybe:#6bb88a;--s-framework:#7a4cc2;--s-via_framework:#a98ad8;
--s-dead_branch:#c98a1a;--s-not_reached:#d9761c;--s-tests_only:#b8a02a;--s-referenced:#8d94a0;--s-no_caller:#c8322f;
--s-ignored:#b7bcc5;--s-non_production:#c9cdd4;--find:#c8322f}
@media (prefers-color-scheme:dark){:root:not([data-theme=light]){--bg:#14171c;--surface:#1c2027;--ink:#e3e7ee;--muted:#9aa3b2;
--line:#323844;--accent:#7aa2f7;--hover:#262b34;--s-entry:#7aa2f7;--s-reached:#4cc283;--s-maybe:#2f7a52;--s-framework:#b18cf0;
--s-via_framework:#6f58a0;--s-dead_branch:#e0a440;--s-not_reached:#f08a3c;--s-tests_only:#cdb848;--s-referenced:#7d8594;
--s-no_caller:#f06560;--s-ignored:#4c525e;--s-non_production:#3b414c;--find:#f06560}}
*{box-sizing:border-box}[hidden]{display:none!important}body{margin:0;background:var(--bg);color:var(--ink);font:14px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif}
header{padding:18px 20px 8px}h1{margin:0;font-size:22px}h1 small{font-weight:400;color:var(--muted);font-size:13px;margin-left:.5rem}
.meta{color:var(--muted);font-size:13px;margin-top:2px}
.bar{display:flex;height:14px;border-radius:3px;overflow:hidden;background:var(--line);margin:10px 0 6px}
.bar i{display:block;height:100%}
.legend{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0}
.chip{border:1px solid var(--line);background:var(--surface);color:var(--ink);border-radius:14px;padding:3px 10px 3px 8px;font:inherit;font-size:12.5px;cursor:pointer;display:flex;align-items:center;gap:6px}
.chip[aria-pressed=false]{opacity:.45}.chip b{font-weight:600}
.sw{width:10px;height:10px;border-radius:2px;display:inline-block;flex:none}
.note{background:var(--surface);border:1px solid var(--line);border-left:4px solid var(--s-not_reached);padding:8px 12px;border-radius:4px;margin:8px 0;font-size:13px}
.note ul{margin:4px 0 0;padding-left:18px}
main{display:grid;grid-template-columns:minmax(260px,360px) 1fr;gap:14px;padding:0 20px 30px}
@media(max-width:860px){main{grid-template-columns:1fr}#tree{max-height:45vh}}
@media(max-width:700px){thead{display:none}tr.fn{display:block;border-bottom:1px solid var(--line);padding:4px 0}
tr.fn td{display:block;border:0;padding:2px 12px}tr.detail,tr.detail td{display:block}}
.panel{background:var(--surface);border:1px solid var(--line);border-radius:6px;min-width:0}
.panel h2{font-size:13px;margin:0;padding:10px 12px;border-bottom:1px solid var(--line);display:flex;justify-content:space-between;gap:8px;align-items:center}
#tree{max-height:78vh;overflow:auto;padding:4px 0;font-size:13px}
.tn{display:flex;align-items:center;gap:6px;padding:2px 10px 2px calc(10px + var(--d)*14px);cursor:pointer;white-space:nowrap}
.tn:hover{background:var(--hover)}.tn.sel{background:var(--hover);box-shadow:inset 3px 0 var(--accent)}
.tn .nm{overflow:hidden;text-overflow:ellipsis;flex:1;min-width:0}.tn .tw{width:12px;color:var(--muted);flex:none;text-align:center}
.mini{display:flex;width:70px;height:8px;border-radius:2px;overflow:hidden;background:var(--line);flex:none}.mini i{height:100%}
.cnt{color:var(--muted);font-size:11.5px;min-width:56px;text-align:right;flex:none}
.tools{display:flex;gap:8px;flex-wrap:wrap;align-items:center;padding:8px 12px;border-bottom:1px solid var(--line)}
input[type=search]{flex:1;min-width:160px;padding:6px 8px;border:1px solid var(--line);border-radius:4px;background:var(--bg);color:var(--ink);font:inherit}
select,.btn{padding:5px 8px;border:1px solid var(--line);border-radius:4px;background:var(--bg);color:var(--ink);font:inherit;font-size:13px}
.btn{cursor:pointer}
table{width:100%;border-collapse:collapse}th,td{text-align:left;padding:5px 10px;border-bottom:1px solid var(--line);vertical-align:top}
th{font-size:12px;color:var(--muted);font-weight:600;position:sticky;top:0;background:var(--surface)}
tbody tr.fn{cursor:pointer}tbody tr.fn:hover{background:var(--hover)}tbody tr.open{background:var(--hover)}
td code,.code{font:12.5px ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
.pill{display:inline-flex;align-items:center;gap:5px;font-size:12px;white-space:nowrap}
.why{color:var(--muted);font-size:12.5px}
.fd{color:var(--find);font-weight:600;font-size:12px;white-space:nowrap}
.detail td{background:var(--bg);padding:12px 14px}
.detail h4{margin:10px 0 4px;font-size:12.5px}.detail h4:first-child{margin-top:0}
.links{display:flex;flex-direction:column;gap:2px}.links a{color:var(--accent);cursor:pointer;text-decoration:none}
.links a:hover{text-decoration:underline}.links .q{color:var(--muted);font-size:12px}
.flow{display:flex;flex-wrap:wrap;align-items:stretch;row-gap:8px;margin:6px 0}
.fseg{display:flex;align-items:stretch}
.node{background:var(--surface);border:1px solid var(--line);border-top:4px solid var(--rc,var(--line));border-radius:6px;padding:6px 8px;font-size:12.5px;max-width:240px;min-width:120px}
.node b{display:block;overflow-wrap:anywhere}.node span{display:block;color:var(--muted);font-size:11.5px;overflow-wrap:anywhere}
.node.cur{box-shadow:0 0 0 2px var(--accent)}
.edge{width:84px;display:flex;flex-direction:column;justify-content:center;padding:0 4px}
.arr{height:2px;background:var(--ink);position:relative;margin-right:6px}
.arr::after{content:"";position:absolute;right:-7px;top:-5px;border:6px solid transparent;border-left:8px solid var(--ink);border-right:0}
.dash .arr{background:repeating-linear-gradient(90deg,var(--muted) 0 6px,transparent 6px 10px)}.dash .arr::after{border-left-color:var(--muted)}
.el{font-size:11px;color:var(--muted);text-align:center;margin-top:3px;line-height:1.25}
@media(max-width:700px){.flow,.fseg{flex-direction:column}.node{max-width:none}.edge{width:auto;min-height:36px;flex-direction:row;align-items:center;gap:8px;padding-left:16px}
.arr{width:2px;height:26px;margin:0}.arr::after{right:-5px;top:auto;bottom:-7px;border:6px solid transparent;border-top:8px solid var(--ink);border-bottom:0}
.dash .arr{background:repeating-linear-gradient(180deg,var(--muted) 0 6px,transparent 6px 10px)}.dash .arr::after{border-top-color:var(--muted);border-left-color:transparent}.el{text-align:left;margin:0}}
.more{padding:10px;text-align:center}.empty{padding:20px;color:var(--muted)}
footer{color:var(--muted);font-size:12px;padding:0 20px 24px}
.view{padding:0 20px 30px}.fgs{width:100%;display:flex;flex-direction:column;gap:4px;margin-top:4px}
.fg{display:flex;flex-wrap:wrap;gap:5px;align-items:center}.fgl{font-size:12px;font-weight:600;min-width:110px;color:var(--muted)}
.sft th[data-sort]{cursor:pointer;user-select:none}.sft th[aria-sort=ascending]::after{content:" ▲"}.sft th[aria-sort=descending]::after{content:" ▼"}.note code{overflow-wrap:anywhere}
.chip.tg[aria-pressed=false]{opacity:1}.chip.tg[aria-pressed=true]{background:var(--ink);color:var(--surface);border-color:var(--ink)}
.au+.why,td .why{overflow-wrap:anywhere}.sk{display:inline-block;font-size:11.5px;padding:1px 6px;border-radius:3px;background:var(--ink);color:var(--surface);white-space:nowrap;margin:1px 0}
#codepane{position:fixed;right:0;top:0;bottom:0;width:min(860px,100vw);z-index:60;background:var(--surface);border-left:1px solid var(--line);box-shadow:-8px 0 24px rgba(0,0,0,.18);display:flex;flex-direction:column}
#codepane[hidden]{display:none}.cph{display:flex;justify-content:space-between;gap:10px;align-items:flex-start;padding:10px 14px;border-bottom:1px solid var(--line)}
#cpbody{overflow:auto;flex:1;font:12.5px/1.5 ui-monospace,Menlo,Consolas,monospace;padding:6px 0;tab-size:4}
.cl{display:flex;white-space:pre;min-width:max-content}.cl .cn{flex:none;width:52px;text-align:right;padding-right:12px;color:var(--muted);user-select:none}
.cl.in{background:color-mix(in srgb,var(--accent) 9%,transparent)}.cl.cur{background:color-mix(in srgb,var(--accent) 22%,transparent)}
.cl.hit{background:color-mix(in srgb,#e0a100 30%,transparent)}.cl .sk{margin-left:14px;font-size:11px;align-self:center}
a[data-code],.cdl{cursor:pointer;color:var(--accent)}
.chk{display:inline-flex;gap:5px;align-items:center;font-size:13px}
.trn{margin-left:calc(var(--d,0)*20px);padding:3px 0;display:flex;flex-wrap:wrap;gap:4px 8px;align-items:baseline;border-left:1px solid var(--line);padding-left:6px}
.trt{width:22px;height:22px;border:1px solid var(--line);background:var(--surface);color:var(--ink);border-radius:4px;cursor:pointer;line-height:1;padding:0}.trn .why{display:inline}.trt:disabled{opacity:.35;cursor:default}
.trn a{cursor:pointer;color:var(--accent);font-weight:600}.trpath a{cursor:pointer;color:var(--accent)}.trpath{display:flex;flex-wrap:wrap;gap:4px 6px;align-items:center;margin:6px 0}
.trh{display:grid;grid-template-columns:1fr 1fr;gap:18px}@media(max-width:900px){.trh{grid-template-columns:1fr}}
.sk.mb{background:transparent;color:var(--muted);border:1px dashed var(--muted)}.mth{font:600 12px ui-monospace,Menlo,monospace}
.au{font-size:12px;font-weight:600;white-space:nowrap}.au-none{color:var(--s-no_caller)}.au-check{color:var(--s-reached)}.au-public{color:var(--s-not_reached)}
.mini-t{width:auto;margin-top:4px}.mini-t td,.mini-t th{padding:3px 8px;font-size:12.5px}.snip{display:inline-block;max-width:520px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;vertical-align:bottom}
.chg{font-size:11.5px;color:var(--accent);font-weight:600;white-space:nowrap}
@media(max-width:700px){.sft thead{display:none}.sft tr.fn{display:block;border-bottom:1px solid var(--line);padding:4px 0}.sft tr.fn td{display:block;border:0;padding:2px 12px}}
.mfilter{display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin:8px 0;font-size:13px}.mfilter b{margin-right:4px}
#mq{flex:1;min-width:220px;max-width:460px;padding:6px 8px;border:1px solid var(--line);border-radius:4px;background:var(--surface);color:var(--ink);font:inherit}
.mchip{display:inline-flex;align-items:center;gap:4px;border:1px solid var(--line);border-radius:14px;padding:2px 4px 2px 10px;background:var(--surface);font-size:12.5px}
.mchip.x{border-style:dashed;color:var(--muted)}.mchip.x code{text-decoration:line-through}
.mchip button{border:0;background:none;color:var(--muted);cursor:pointer;font:inherit;padding:0 4px;border-radius:50%}.mchip button:hover{color:var(--ink);background:var(--hover)}
.tn .ta{display:none;border:1px solid var(--line);background:var(--bg);color:var(--ink);font:inherit;font-size:11px;padding:0 5px;border-radius:3px;cursor:pointer}
.tn:hover .ta,.tn:focus-within .ta,.tn.sel .ta{display:inline-block}
@media(hover:none){.tn .ta{display:inline-block}}
.tabs{display:flex;gap:0;margin:12px 0 2px}.tabs button{border:1px solid var(--line);background:var(--surface);color:var(--ink);
padding:6px 16px;font:inherit;font-size:13px;cursor:pointer}.tabs button:first-child{border-radius:5px 0 0 5px}
.tabs button:last-child{border-radius:0 5px 5px 0;border-left:0}.tabs button[aria-pressed=true]{background:var(--ink);color:var(--surface);border-color:var(--ink)}
#gview{padding:0 20px 30px}#gview .panel{position:relative}
.gtools{display:flex;flex-wrap:wrap;gap:8px;align-items:center;padding:8px 12px;border-bottom:1px solid var(--line)}
.seg button{border:1px solid var(--line);background:var(--bg);color:var(--ink);padding:5px 10px;font:inherit;font-size:13px;cursor:pointer}
.seg button+button{border-left:0}.seg button[aria-pressed=true]{background:var(--hover);box-shadow:inset 0 -2px var(--accent)}
.glegend{display:flex;flex-wrap:wrap;gap:10px;padding:6px 12px;font-size:12px;color:var(--muted);border-bottom:1px solid var(--line)}
.glegend span{display:inline-flex;align-items:center;gap:5px}
#gwrap{position:relative;height:72vh;min-height:380px;overflow:hidden;touch-action:none}
#gc{display:block;width:100%;height:100%;cursor:grab}#gc.drag{cursor:grabbing}
#ginfo{position:absolute;right:12px;bottom:12px;width:min(340px,calc(100% - 24px));background:var(--surface);border:1px solid var(--line);
border-radius:6px;padding:10px 12px;font-size:13px;box-shadow:0 4px 14px rgba(0,0,0,.12)}#ginfo[hidden]{display:none}
#ginfo h3{margin:0 0 4px;font-size:14px;overflow-wrap:anywhere}#ginfo .code{overflow-wrap:anywhere}#ginfo .acts{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px}
#ghint{position:absolute;left:8px;bottom:8px;font-size:12px;color:var(--muted);pointer-events:none;background:var(--surface);padding:2px 6px;border-radius:4px;opacity:.92}
@media(max-width:700px){#gwrap{height:62vh}#ginfo{position:static;width:auto;margin:10px;box-shadow:none}}
button:focus-visible,.tn:focus-visible,tr:focus-visible,a:focus-visible,input:focus-visible,select:focus-visible{outline:2px solid var(--accent);outline-offset:1px}
</style></head><body>
<header><h1>__TITLE__<small>reachmap __VERSION__</small></h1><div class="meta" id="meta"></div>
<div class="bar" id="bar" role="img"></div><div class="legend" id="legend"></div><div id="notes"></div>
<div class="mfilter" role="group" aria-label="Filter by module"><b>Modules</b>
<input type="text" id="mq" list="mlist" placeholder="folder, file or pattern, e.g. lessons/sqlinjection or *Controller.java" aria-label="Module, file or pattern">
<datalist id="mlist"></datalist><button class="btn" id="minc">Only these</button><button class="btn" id="mexc">Hide these</button>
<span id="mchips"></span><button class="btn" id="mclr" hidden>Clear module filter</button></div>
<div id="epsbar" class="note" hidden style="border-left-color:var(--s-entry)"><span id="epstext"></span> <button class="btn" id="epsoff">Show all code again</button></div>
<div class="tabs" role="group" aria-label="View"><button id="tlist" aria-pressed="true">Functions</button><button id="tgraph" aria-pressed="false">Graph</button><button id="tsurf" aria-pressed="false">Attack surface</button><button id="thot" aria-pressed="false">Hotspots</button><button id="ttrace" aria-pressed="false">Trace</button></div></header>
<section id="sfview" class="view" hidden><div class="panel"><h2>Attack surface <span class="why" id="sfcount"></span></h2>
<div class="tools"><div id="sfsum" style="width:100%"></div>
<input type="search" id="sfq" placeholder="Search path, handler or how it is checked" aria-label="Search endpoints"><button class="btn" id="sfcsv">Export CSV</button>
<select id="sfsort" aria-label="Sort endpoints"><option value="path:1">by path</option><option value="access:1">no check first</option><option value="sinks:1">most dangerous calls first</option><option value="method:1">by method</option><option value="handler:1">by handler</option><option value="reach:1">reaches most code first</option></select>
<button class="btn" id="sfuse">Use these in the graph and the function list</button>
<div id="sffil" class="fgs" role="group" aria-label="Filter endpoints"></div></div>
<div style="overflow:auto"><table class="sft"><thead><tr><th data-sort="method" tabindex="0">Method</th><th data-sort="path" tabindex="0">Path</th><th data-sort="handler" tabindex="0">Handler</th><th data-sort="access" tabindex="0">Access check</th><th data-sort="sinks" tabindex="0">Dangerous calls reached</th></tr></thead><tbody id="sfrows"></tbody></table></div>
<p class="why" style="padding:0 12px 12px">Access checks are read from annotations, route middleware and the first lines of the handler: a reading of the code, not a test.
Dangerous calls are found by pattern (SQL, operating system command, file access, deserialization, XML parser, outgoing request, redirect, code evaluation) and reached through the call map; a pale badge means the way there uses a link matched by name only. Neither proves a vulnerability.</p></div></section>
<aside id="codepane" hidden role="dialog" aria-label="Source code"><div class="cph"><div><b id="cptitle"></b><div class="why code" id="cpsub"></div></div>
<span><button class="btn" id="cpjump">To the function</button> <button class="btn" id="cpcopy">Copy path</button> <button class="btn" id="cpclose">Close</button></span></div><div id="cpbody"></div></aside>
<section id="trview" class="view" hidden><div class="panel"><h2>Trace a function <span class="why">who calls it, and what it calls</span></h2>
<div class="tools"><input type="search" id="trq" placeholder="Function or file name, then Enter" aria-label="Find a function to trace" autocomplete="off">
<button class="btn" id="trback" disabled>Back</button>
<label class="chk"><input type="checkbox" id="trtests"> callers from tests</label>
<label class="chk"><input type="checkbox" id="trloaded"> "module is loaded" links</label></div>
<div id="trhits" style="padding:0 12px"></div><div id="trbody" style="padding:6px 12px 14px"><p class="why">Pick a function above, or press <b>Trace</b> on any function in the list, the graph or the attack surface.</p></div></div></section>
<section id="hsview" class="view" hidden><div class="panel"><h2>Hotspots: functions many entry points pass through</h2>
<div style="overflow:auto"><table><thead><tr><th>Function</th><th>Entry points</th><th>Callers</th><th>Dangerous calls inside</th><th>Status</th><th></th></tr></thead><tbody id="hsrows"></tbody></table></div>
<p class="why" style="padding:0 12px">A flaw here affects every entry point that passes through. Central checks and data access usually show up at the top.</p></div>
<div class="panel" style="margin-top:14px"><h2>Delete candidates: not reached and unchanged for <select id="dcage" aria-label="Age"><option value="6">6 months</option><option value="12" selected>12 months</option><option value="24">2 years</option><option value="60">5 years</option></select></h2>
<div id="dcnote" style="padding:6px 12px"></div><div style="overflow:auto"><table><thead><tr><th>Function</th><th>Status</th><th>File last changed</th><th>Commits</th></tr></thead><tbody id="dcrows"></tbody></table></div></div></section>
<section id="gview" hidden><div class="panel">
<div class="gtools"><span class="seg" role="group" aria-label="Graph"><button id="gmod" aria-pressed="true">Map</button><button id="glay" aria-pressed="false">Layers</button><button id="gloc" aria-pressed="false">Around a function</button></span>
<label class="why" id="ghopsl" hidden>depth <select id="ghops"><option>1</option><option selected>2</option><option>3</option></select></label>
<span id="gfold"><button class="btn" id="gexpall">Expand all</button> <button class="btn" id="gcolall">Folders only</button></span>
<label class="why"><input type="checkbox" id="gnp" checked> hide tests, docs and vendor</label>
<label class="why" id="gisol"><input type="checkbox" id="giso"> hide points without links</label>
<label class="why"><input type="checkbox" id="gweak"> show links matched by name only</label>
<label class="why" id="gnbl" title="Only with a module filter"><input type="checkbox" id="gnb" checked> with linked files outside the filter</label>
<label class="why" id="gfindl" hidden><input type="checkbox" id="gfind"> only CodeRaster findings and their neighbours</label>
<input type="search" id="gq" placeholder="Find in graph" aria-label="Find in graph" style="max-width:220px">
<button class="btn" id="gfit">Fit</button><button class="btn" id="gpng">PNG</button><button class="btn" id="gsvg">SVG</button></div>
<div class="glegend" id="glegend"></div>
<div id="gwrap"><canvas id="gc" role="img" aria-label="Graph of folders, files and their calls. The list view shows the same data as text."></canvas>
<div id="ghint"></div></div>
<div id="ginfo" hidden></div>
</div></section>
<main><section class="panel"><h2>Folders and files <span class="cnt" style="min-width:0">not reached / all</span></h2><div id="tree" role="tree"></div></section>
<section class="panel"><h2><span id="scope">All functions</span><button class="btn" id="clr" hidden>Show all</button></h2>
<div class="tools"><input type="search" id="q" placeholder="Search function or file" aria-label="Search">
<select id="sort" aria-label="Sort"><option value="path">by file and line</option><option value="status">by status</option><option value="callers">by number of callers</option><option value="via">by entry points passing through</option><option value="age">by last change, oldest first</option></select>
<label class="why"><input type="checkbox" id="files"> show file-level code</label><button class="btn" id="lcsv">Export CSV</button>
<span id="cfgbox" hidden class="why">Config from this report: <b id="cfgn">0</b> rule(s) <button class="btn" id="cfgdl">Download reachmap.cfg</button> <button class="btn" id="cfgclr">Clear</button></span></div>
<div style="overflow:auto"><table><thead><tr><th>Function</th><th>Status</th><th>Why</th></tr></thead><tbody id="rows"></tbody></table></div>
<div class="more" id="more"></div></section></main>
<footer>Found by text search (Python: by its parser). Calls through interfaces, reflection or injection by type are only seen when the
function's name appears. A dashed link was matched by name only, because the same name is defined in several places.
"No caller found" is a lead to check, not proof that the code is unused.</footer>
<script id="data" type="application/json">__DATA__</script>
<script>
(()=>{
const D=JSON.parse(document.getElementById('data').textContent),L=__LABELS__,N=D.nodes;
const SK=__SINKS__,SKO=Object.keys(SK);
const ORDER=Object.keys(L),PROBLEM=new Set(['dead_branch','not_reached','tests_only','referenced','no_caller']);
const $=s=>document.querySelector(s),esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const col=s=>`var(--s-${s})`;
let on=new Set(ORDER),scope='',q='',limit=200,openId=null,showFiles=false,onlyChanged=false,onlySinks=false;
let EPS=null;            // null = off; otherwise {ids: node ids reached from the filtered endpoints, n, files}
const st=D.stats.summary;let bs=st.by_status;
// ---- module filter: "only these" and "hide these" patterns; kept in the address (#m=...) so a filtered view can be shared
const MF={inc:[],exc:[]};
function mre(p){p=p.trim().replace(/^\.?\//,'').replace(/\/$/,'');if(!p)return null;
 const g=p.replace(/[.+^${}()|[\]\\]/g,'\\$&').replace(/\*\*/g,'\u0000').replace(/\*/g,'[^/]*').replace(/\?/g,'[^/]').replace(/\u0000/g,'.*');
 try{return new RegExp('(^|/)'+g+'(/|$)','i');}catch(e){return null;}}
let MRX={inc:[],exc:[]};
function inScope(path){if(MRX.exc.some(r=>r.test(path)))return false;return !MRX.inc.length||MRX.inc.some(r=>r.test(path));}
function mfChanged(){MRX={inc:MF.inc.map(mre).filter(Boolean),exc:MF.exc.map(mre).filter(Boolean)};
 if(MF.inc.length||MF.exc.length)HS.set('m',JSON.stringify(MF));else HS.delete('m');saveHash();
 $('#mchips').innerHTML=[...MF.inc.map((p,i)=>`<span class="mchip"><span>only</span><code>${esc(p)}</code><button aria-label="Remove ${esc(p)}" data-mrm="inc:${i}">×</button></span>`),
  ...MF.exc.map((p,i)=>`<span class="mchip x"><span>hide</span><code>${esc(p)}</code><button aria-label="Remove ${esc(p)}" data-mrm="exc:${i}">×</button></span>`)].join('');
 $('#mclr').hidden=!(MF.inc.length||MF.exc.length);
 bs={};for(const f of N)if(f.kind==='function'&&inScope(f.path))bs[f.status]=(bs[f.status]||0)+1;
 drawBar();if(typeof legend==='function'){legend();rebuildTree();tree();limit=200;rows();}
 if(typeof GV!=='undefined'&&GV.built&&!$('#gview').hidden){GV.expInit=false;build();gLegend();}else if(typeof GV!=='undefined')GV.expInit=false;}
let HS=new URLSearchParams();try{HS=new URLSearchParams(location.hash.slice(1));}catch(e){}
function saveHash(){try{const h=HS.toString();history.replaceState(null,'',location.pathname+location.search+(h?'#'+h:''));}catch(e){}}
try{const v0=HS.get('m');if(v0){const v=JSON.parse(v0);MF.inc=(v.inc||[]).map(String);MF.exc=(v.exc||[]).map(String);}}catch(e){}
function addPat(kind){const v=$('#mq').value.trim();if(!v)return;for(const p of v.split(',').map(x=>x.trim()).filter(Boolean))if(!MF[kind].includes(p))MF[kind].push(p);$('#mq').value='';mfChanged();}
$('#minc').onclick=()=>addPat('inc');$('#mexc').onclick=()=>addPat('exc');
$('#mq').onkeydown=e=>{if(e.key==='Enter'){e.preventDefault();addPat(e.shiftKey?'exc':'inc');}};
$('#mchips').addEventListener('click',ev=>{const b=ev.target.closest('[data-mrm]');if(!b)return;const [k,i]=b.dataset.mrm.split(':');MF[k].splice(+i,1);mfChanged();});
$('#mclr').onclick=()=>{MF.inc=[];MF.exc=[];mfChanged();};
$('#mlist').innerHTML=[...new Set(N.filter(f=>f.kind==='file'&&f.code).flatMap(f=>{const p=f.path.split('/');return p.slice(0,-1).map((_,i)=>p.slice(0,i+1).join('/')+'/');}))].sort().slice(0,3000).map(d=>`<option value="${esc(d)}">`).join('');
$('#meta').textContent=`${st.files} files, ${st.functions} functions (${st.production_functions} in production code), ${D.generated}`;
function drawBar(){const total=ORDER.reduce((a,s)=>a+(bs[s]||0),0)||1;
 $('#bar').innerHTML=ORDER.filter(s=>bs[s]).map(s=>`<i style="width:${100*bs[s]/total}%;background:${col(s)}" title="${esc(L[s])}: ${bs[s]}"></i>`).join('');
 $('#bar').setAttribute('aria-label',ORDER.filter(s=>bs[s]).map(s=>`${L[s]} ${bs[s]}`).join(', '));}
drawBar();
function legend(){$('#legend').innerHTML=ORDER.filter(s=>bs[s]||!on.has(s)&&st.by_status[s]).map(s=>`<button class="chip" data-s="${s}" aria-pressed="${on.has(s)}"><span class="sw" style="background:${col(s)}"></span>${esc(L[s])} <b>${bs[s]||0}</b></button>`).join('')
 +`<button class="chip" id="onlyp" aria-pressed="true">Only problems</button><button class="chip" id="all" aria-pressed="true">All</button>`
 +`<button class="chip tg" id="onlysk" aria-pressed="${onlySinks}">With dangerous calls</button>`
 +(D.diff?`<button class="chip tg" id="onlych" aria-pressed="${onlyChanged}">Changed since last run</button>`:'');}
legend();
$('#legend').addEventListener('click',ev=>{const b=ev.target.closest('.chip');if(!b)return;
 if(b.id==='onlych'){onlyChanged=!onlyChanged;legend();limit=200;rows();return;}
 if(b.id==='onlysk'){onlySinks=!onlySinks;legend();limit=200;rows();if(typeof GV!=='undefined'&&GV.built&&!$('#gview').hidden){GV.expInit=false;build();}return;}
 if(b.id==='onlyp')on=new Set([...PROBLEM]);else if(b.id==='all')on=new Set(ORDER);
 else{const s=b.dataset.s;on.has(s)?on.delete(s):on.add(s);}legend();limit=200;rows();
 if(typeof GV!=='undefined'&&GV.built&&!$('#gview').hidden){GV.expInit=false;build();}});
const notes=[];
if(st.folders_without_entry.length)notes.push(`<div class="note"><b>Nothing in these folders is reached.</b> If they are used, an entry point is probably missing (add it to the config file):<ul>${st.folders_without_entry.slice(0,8).map(d=>`<li><code>${esc(d)}/</code></li>`).join('')}</ul></div>`);
if(st.edges_by_name_only)notes.push(`<div class="note" style="border-left-color:var(--s-maybe)">${st.edges_by_name_only} of ${st.edges} links are by name only; they are dashed in the paths.</div>`);
if(D.diff){const x=D.diff;notes.push(`<div class="note" style="border-left-color:var(--accent)"><b>Since the previous run (${esc(x.previous_generated)}):</b> ${x.new} new and ${x.removed} removed functions, ${x.now_reached} now reached, ${x.no_longer_reached} no longer reached. Endpoints: ${x.endpoints_new.length} new, ${x.endpoints_removed.length} removed, ${x.auth_changed.length} with a changed access check.${x.endpoints_new.length?`<ul>${x.endpoints_new.slice(0,8).map(e=>`<li><code>${esc(e)}</code> new</li>`).join('')}${x.auth_changed.slice(0,8).map(e=>`<li><code>${esc(e)}</code></li>`).join('')}</ul>`:''}</div>`);}
if(D.stats.findings)notes.push(`<div class="note" style="border-left-color:var(--find)"><b>CodeRaster findings on the map:</b> ${Object.entries(D.stats.findings).map(([k,v])=>esc(k)+' ('+v+')').join('; ')}</div>`);
$('#notes').innerHTML=notes.join('');
// tree
let T={kids:{},n:{},files:{}};
function rebuildTree(){T={kids:{},n:{},files:{}};
for(const f of N){if(f.kind==='file'&&!f.code)continue;if(!inScope(f.path))continue;const parts=f.path.split('/');let t=T;
 for(const p of parts.slice(0,-1)){t=t.kids[p]=t.kids[p]||{kids:{},n:{},files:{}};}
 if(f.kind==='file'){t.files[f.path]=t.files[f.path]||{n:{}};continue;}
 const fl=t.files[f.path]=t.files[f.path]||{n:{}};fl.n[f.status]=(fl.n[f.status]||0)+1;}
function agg(t){const n={};for(const k in t.kids){const c=agg(t.kids[k]);for(const s in c)n[s]=(n[s]||0)+c[s];}
 for(const p in t.files)for(const s in t.files[p].n)n[s]=(n[s]||0)+t.files[p].n[s];t.n=n;return n;}
agg(T);}
rebuildTree();
const mini=n=>{const tot=ORDER.reduce((a,s)=>a+(n[s]||0),0)||1;return `<span class="mini" aria-hidden="true">${ORDER.filter(s=>n[s]).map(s=>`<i style="width:${100*n[s]/tot}%;background:${col(s)}"></i>`).join('')}</span>`};
const bad=n=>[...PROBLEM].reduce((a,s)=>a+(n[s]||0),0),all=n=>ORDER.filter(s=>s!=='non_production').reduce((a,s)=>a+(n[s]||0),0);
const openDirs=new Set(['']);
(function autoOpen(t,p){const ks=Object.keys(t.kids).filter(k=>all(t.kids[k].n));if(ks.length===1&&!Object.keys(t.files).length){const q=p?p+'/'+ks[0]:ks[0];openDirs.add(q);autoOpen(t.kids[ks[0]],q);}})
 ((()=>{const ks=Object.keys(T.kids).filter(k=>all(T.kids[k].n));return ks.length===1?{kids:{[ks[0]]:T.kids[ks[0]]},files:{}}:{kids:{},files:{}}})(),'');
function tree(){const out=[];
 function rec(t,path,d){const ks=Object.keys(t.kids).sort();for(const k of ks){const p=path?path+'/'+k:k,c=t.kids[k],o=openDirs.has(p);
  out.push(`<div class="tn${scope===p+'/'?' sel':''}" role="treeitem" aria-expanded="${o}" tabindex="0" data-dir="${esc(p)}" style="--d:${d}"><span class="tw">${o?'▾':'▸'}</span><span class="nm">${esc(k)}/</span><button class="ta" data-only="${esc(p)}/" title="Show only this module">only</button><button class="ta" data-hide="${esc(p)}/" title="Hide this module">hide</button>${mini(c.n)}<span class="cnt">${bad(c.n)} / ${all(c.n)}</span></div>`);
  if(o)rec(c,p,d+1);}
  for(const fp of Object.keys(t.files).sort()){const c=t.files[fp];
  out.push(`<div class="tn${scope===fp?' sel':''}" role="treeitem" tabindex="0" data-file="${esc(fp)}" style="--d:${d}"><span class="tw"></span><span class="nm">${esc(fp.split('/').pop())}</span>${mini(c.n)}<span class="cnt">${bad(c.n)} / ${all(c.n)}</span></div>`);}}
 rec(T,'',0);$('#tree').innerHTML=out.join('');}
tree();
$('#tree').addEventListener('click',ev=>{const a=ev.target.closest('[data-only],[data-hide]');
 if(a){ev.stopPropagation();const k=a.dataset.only?'inc':'exc',v=a.dataset.only||a.dataset.hide;if(!MF[k].includes(v))MF[k].push(v);mfChanged();return;}
 const n=ev.target.closest('.tn');if(!n)return;
 if(n.dataset.dir!==undefined){const p=n.dataset.dir;if(ev.target.closest('.tw')||scope===p+'/'){openDirs.has(p)?openDirs.delete(p):openDirs.add(p);}else{openDirs.add(p);scope=p+'/';}}
 else scope=n.dataset.file;limit=200;tree();rows();});
$('#tree').addEventListener('keydown',ev=>{if(ev.key==='Enter'||ev.key===' '){ev.preventDefault();ev.target.click();}});
$('#clr').onclick=()=>{scope='';tree();rows();};
$('#q').oninput=e=>{q=e.target.value.toLowerCase();limit=200;rows();};
$('#sort').onchange=()=>rows();$('#files').onchange=e=>{showFiles=e.target.checked;rows();};
const pill=s=>`<span class="pill"><span class="sw" style="background:${col(s)}"></span>${esc(L[s]||s)}</span>`;
const where=f=>`${f.path.split('/').pop()}:${f.line}`;
function visible(){let r=N.filter(f=>(f.kind==='function'||showFiles||(q&&f.kind==='file'))&&on.has(f.status)&&inScope(f.path)&&(!onlyChanged||f.change)&&(!onlySinks||f.sinks.length)&&(!EPS||EPS.ids.has(f.id)));
 if(scope)r=r.filter(f=>scope.endsWith('/')?f.path.startsWith(scope):f.path===scope);
 if(q)r=r.filter(f=>(f.qual+' '+f.path).toLowerCase().includes(q));
 const by=$('#sort').value;
 r.sort(by==='status'?(a,b)=>ORDER.indexOf(a.status)-ORDER.indexOf(b.status)||a.path.localeCompare(b.path)||a.line-b.line
  :by==='callers'?(a,b)=>b.n_callers-a.n_callers:by==='via'?(a,b)=>b.via_entries-a.via_entries
  :by==='age'?(a,b)=>(a.changed||9e9)-(b.changed||9e9)||a.path.localeCompare(b.path):(a,b)=>a.path.localeCompare(b.path)||a.line-b.line);return r;}
function rows(){const r=visible();$('#scope').textContent=scope?scope:'All functions';$('#clr').hidden=!scope;
 $('#rows').innerHTML=r.length?r.slice(0,limit).map(f=>`<tr class="fn${openId===f.id?' open':''}" tabindex="0" data-id="${f.id}"><td><code>${esc(f.qual)}</code>${f.findings.length?` <span class="fd" title="CodeRaster findings">● ${f.findings.length} finding${f.findings.length>1?'s':''}</span>`:''}${f.sinks.length?' '+[...new Set(f.sinks.map(s=>s.kind))].map(k=>`<span class="sk" title="dangerous call: ${esc(SK[k])}">${esc(k)}</span>`).join(' '):''}${f.change?` <span class="chg">${esc(f.change)}</span>`:''}<div class="why">${esc(where(f))}</div></td><td>${pill(f.status)}</td><td class="why">${esc(f.reason)}</td></tr>`+(openId===f.id?`<tr class="detail"><td colspan="3">${detail(f)}</td></tr>`:'')).join('')
  :`<tr><td colspan="3" class="empty">Nothing matches. Change the filters above or pick another folder.</td></tr>`;
 $('#more').innerHTML=r.length>limit?`<button class="btn" id="mo">Show ${Math.min(500,r.length-limit)} more of ${r.length-limit}</button>`:(r.length?`<span class="why">${r.length} shown</span>`:'');
 const mo=$('#mo');if(mo)mo.onclick=()=>{limit+=500;rows();};}
function chain(f){if(!['reached','maybe','via_framework'].includes(f.status))return [];const out=[];let c=f,seen=new Set();
 while(c&&!seen.has(c.id)&&out.length<30){seen.add(c.id);out.push({id:c.id,how:c.pred_how,sure:c.pred_sure});c=c.pred>=0?N[c.pred]:null;}return out.reverse();}
function flow(f){const ch=chain(f);if(!ch.length)return '';
 const parts=ch.map((c,i)=>{const n=N[c.id];const node=`<div class="node${n.id===f.id?' cur':''}" style="--rc:${col(n.status)}"><b>${esc(n.qual)}</b><span>${esc(where(n))}</span>${i===0?`<span>${esc(n.entry||n.framework)}</span>`:''}</div>`;
  if(i===0)return node;return `<div class="fseg"><div class="edge${c.sure?'':' dash'}"><span class="arr"></span><span class="el">${esc(c.how)}${c.sure?'':' (by name only)'}</span></div>${node}</div>`;});
 return `<h4>Why it is alive: path from ${f.status==='via_framework'?'framework code':'an entry point'}</h4><div class="flow" role="list">${parts.join('')}</div>`;}
function lst(items,kind){if(!items.length)return '<span class="why">none</span>';
 return `<div class="links">${items.slice(0,40).map(c=>{const n=N[c.id];return `<div><a data-go="${n.id}">${esc(n.kind==='file'?n.path:n.qual)}</a> <span class="q">${esc(where(n))}, ${esc(c.how)}${c.sure?'':', by name only'}${kind==='in'&&c.at?' at '+esc(c.at):''}</span> ${pill(n.status)}</div>`}).join('')}${items.length>40?`<span class="why">and ${items.length-40} more</span>`:''}</div>`;}
function detail(f){let h=`<h4>Status</h4><p>${pill(f.status)} ${esc(f.reason)} <button class="btn" data-graph="${f.id}">Show in graph</button> <button class="btn" data-trace="${f.id}">Trace</button> <button class="btn" data-code="${f.id}">Show code</button> <button class="btn" data-follow="${f.id}" title="Graph, Layers: this file and the files linked to it">Follow file in layers</button></p>`;
 if(f.kind==='function'&&FI[f.path]&&FI[f.path].fid!=null)h+=`<p class="why">File: <a data-go="${FI[f.path].fid}" style="cursor:pointer;color:var(--accent)">${esc(f.path)}</a> (select it to see the file itself and what it loads)</p>`;
 if(f.change)h+=`<p class="chg">Since the last run: ${esc(f.change)}</p>`;
 h+=`<p class="why">Mark for the config file: <button class="btn" data-cfg="entry">entry point</button> <button class="btn" data-cfg="framework">framework code</button> <button class="btn" data-cfg="ignore">ignore</button></p>`;
 if(f.sinks.length)h+=`<h4>Dangerous calls inside</h4><div class="links">${f.sinks.map(s=>`<div><span class="sk">${esc(s.kind)}</span> line ${s.line}: <code class="snip">${esc(s.code)}</code></div>`).join('')}</div>`;
 if(f.via_entries)h+=`<p class="why">${f.via_entries} entry point(s) reach this function.</p>`;
 if(f.changed)h+=`<p class="why">File last changed ${new Date(f.changed*1000).toISOString().slice(0,10)}, ${f.commits} commit(s).</p>`;
 if(f.dead_root>=0){const r=N[f.dead_root];h+=`<p class="why">Top of this unreached branch: <a class="links" data-go="${r.id}" style="color:var(--accent);cursor:pointer">${esc(r.qual)}</a>. Check that one first.</p>`;}
 h+=flow(f);
 if(f.findings.length)h+=`<h4>CodeRaster findings</h4><div class="links">${f.findings.map(x=>`<div><span class="fd">${esc(x.status)} ${esc(x.severity)}</span> ${esc(x.rule)} at line ${x.line}</div>`).join('')}</div>`;
 h+=`<h4>Called from (${f.callers.length})</h4>${lst(f.callers,'in')}<h4>Calls (${f.callees.length})</h4>${lst(f.callees,'out')}`;
 h+=`<p class="why code">${esc(f.path)}:${f.line}-${f.end}</p>`;return h;}
$('#rows').addEventListener('click',ev=>{const tb=ev.target.closest('[data-trace]');if(tb){traceFn(+tb.dataset.trace);return;}const gb=ev.target.closest('[data-graph]');if(gb){showGraph('local',+gb.dataset.graph);return;}
 const cb=ev.target.closest('[data-cfg]');if(cb){cfgAdd(cb.dataset.cfg,N[openId]);cb.textContent='added';return;}
 const g=ev.target.closest('[data-go]');if(g){go(+g.dataset.go);return;}
 const tr=ev.target.closest('tr.fn');if(!tr)return;const id=+tr.dataset.id;openId=openId===id?null:id;rows();});
$('#rows').addEventListener('keydown',ev=>{if(ev.key==='Enter'&&ev.target.matches('tr.fn')){ev.preventDefault();ev.target.click();}});
function go(id){const f=N[id];openId=id;scope=f.path;on.add(f.status);if(f.kind==='file')showFiles=true;$('#files').checked=showFiles;q='';$('#q').value='';
 const parts=f.path.split('/');for(let i=1;i<parts.length;i++)openDirs.add(parts.slice(0,i).join('/'));legend();tree();rows();
 const tr=document.querySelector(`tr[data-id="${id}"]`);if(tr){tr.scrollIntoView({block:'center'});tr.focus();}}
rows();
// ======================= graph view: map (folders that open into files), layers, around a function =======================
const GV={target:null,mode:'map',focus:null,nodes:[],edges:[],adj:new Map(),by:new Map(),scale:1,tx:0,ty:0,alpha:0,hover:null,sel:null,find:'',raf:0,built:false,
 exp:new Set(),expInit:false,cols:[],heads:[],touched:false,layGroup:false};
const cv=$('#gc'),ctx=cv.getContext('2d'),RM=matchMedia('(prefers-reduced-motion: reduce)').matches;
const SEV=['info','low','medium','high','critical'];
// per file: function statuses, findings, depth from an entry point, framework
const FI={};
for(const f of N){const p=f.path,x=FI[p]=FI[p]||{n:{},nf:0,sev:-1,depth:1e9,fw:false,entry:false,code:false,np:false,fid:null,funcs:0,sk:0};
 x.sk+=f.status==='non_production'?0:f.sinks.length;
 if(f.kind==='file'){x.fid=f.id;x.code=f.code;x.np=f.status==='non_production';if(f.entry)x.entry=true;}
 else{x.n[f.status]=(x.n[f.status]||0)+1;if(f.status!=='non_production')x.funcs++;}
 if(f.status==='entry')x.entry=true;
 if(['entry','reached','maybe'].includes(f.status)&&f.depth>=0)x.depth=Math.min(x.depth,f.status==='entry'?0:f.depth);
 if(f.status==='framework'||f.status==='via_framework')x.fw=true;
 for(const k of f.findings){x.nf++;x.sev=Math.max(x.sev,SEV.indexOf(k.severity));}}
const HASF=Object.values(FI).some(x=>x.nf);$('#gfindl').hidden=!HASF;
const MOD={entry:['entry','Contains an entry point'],reached:['reached','All reached'],framework:['framework','Only framework code'],
 not_reached:['not_reached','Partly not reached'],no_caller:['no_caller','Nothing reached'],non_production:['non_production','Tests, docs, vendor'],
 referenced:['referenced','No functions (template, config, types)']};
function catOf(a){if(a.np)return 'non_production';const tot=all(a.n),b=bad(a.n);if(a.entry)return 'entry';
 if(!tot)return a.code?'referenced':'framework';if(!b)return (a.n.reached||a.n.maybe)?'reached':'framework';return b===tot?'no_caller':'not_reached';}
let CC={};function readColors(){const cs=getComputedStyle(document.documentElement);for(const s of ORDER)CC[s]=cs.getPropertyValue('--s-'+s).trim();
 for(const k of ['ink','muted','accent','find','line'])CC[k]=cs.getPropertyValue('--'+k).trim();CC.bg=cs.getPropertyValue('--surface').trim();}
readColors();matchMedia('(prefers-color-scheme: dark)').addEventListener('change',()=>{readColors();draw();});
function hash(s){let h=0;for(let i=0;i<s.length;i++)h=(h*31+s.charCodeAt(i))|0;return h;}
// ---- which files are shown, and as what: a file, or the folder it is folded into
function statusOk(p){const x=FI[p];if(onlySinks&&!x.sk)return false;if(EPS&&!EPS.files.has(p))return false;if(on.size===ORDER.length)return true;
 const ks=Object.keys(x.n);if(!ks.length)return on.has('referenced')||on.has('framework')||on.has('entry');return ks.some(s=>on.has(s));}
function shownFiles(){const hideNP=$('#gnp').checked;let ok=p=>inScope(p)&&statusOk(p);
 if((MF.inc.length||MF.exc.length)&&$('#gnb').checked){const near=new Set();
  for(const [a,b] of D.file_edges){const pa=N[a].path,pb=N[b].path;if(inScope(pa))near.add(pb);if(inScope(pb))near.add(pa);}ok=p=>inScope(p)||near.has(p);}
 return Object.entries(FI).filter(([p,x])=>x.fid!=null&&!(hideNP&&x.np)&&(x.code||x.funcs)&&ok(p)).map(([p])=>p);}
function dispKey(path){const parts=path.split('/');let d='';for(let i=0;i<parts.length-1;i++){d=d?d+'/'+parts[i]:parts[i];if(!GV.exp.has(d))return 'D:'+d;}return 'F:'+path;}
function initExp(){GV.exp=new Set();const files=shownFiles();
 for(let guard=0;guard<200;guard++){const groups=new Map();for(const p of files){const k=dispKey(p);groups.set(k,(groups.get(k)||0)+1);}
  if(groups.size>=40)break;let best=null,bn=0;for(const [k,n] of groups)if(k[0]==='D'&&n>bn){best=k;bn=n;}
  if(!best)break;const sub=new Set(files.filter(p=>dispKey(p)===best).map(p=>{GV.exp.add(best.slice(2));const k=dispKey(p);GV.exp.delete(best.slice(2));return k;}));
  if(groups.size-1+sub.size>90&&groups.size>8)break;GV.exp.add(best.slice(2));}
 GV.expInit=true;}
function buildMap(){if(!GV.expInit)initExp();const files=shownFiles(),groups=new Map(),of=new Map();
 const key=GV.mode==='layers'&&!GV.layGroup?(p=>'F:'+p):dispKey;
 for(const p of files){const k=key(p),x=FI[p];of.set(x.fid,k);let g=groups.get(k);
  if(!g){const isDir=k[0]==='D',path=k.slice(2);g={id:k,dir:isDir,path,label:isDir?path.split('/').pop()+'/':path.split('/').pop(),sub:path+(isDir?'/':''),
   n:{},nf:0,sev:-1,depth:1e9,fw:false,entry:false,code:false,np:true,files:[],funcs:0,grp:(isDir?path:path.split('/').slice(0,-1).join('/')).split('/').slice(0,3).join('/')};groups.set(k,g);}
  g.files.push(p);g.sk=(g.sk||0)+x.sk;for(const s in x.n)g.n[s]=(g.n[s]||0)+x.n[s];g.nf+=x.nf;g.sev=Math.max(g.sev,x.sev);g.depth=Math.min(g.depth,x.depth);
  g.fw=g.fw||x.fw;g.entry=g.entry||x.entry;g.code=g.code||x.code;g.np=g.np&&x.np;g.funcs+=x.funcs;}
 const weak=$('#gweak').checked,em=new Map();
 for(const [a,b,c,s] of D.file_edges){const ka=of.get(a),kb=of.get(b);if(!ka||!kb||ka===kb||!(s||weak))continue;const k=ka+'|'+kb;
  const e=em.get(k)||em.set(k,{a:ka,b:kb,c:0,sure:false}).get(k);e.c+=c;e.sure=e.sure||!!s;}
 let nodes=[...groups.values()],edges=[...em.values()];
 const seenL=new Map();for(const n of nodes)seenL.set(n.label,(seenL.get(n.label)||0)+1);       // two "source/" folders: say whose
 for(const n of nodes)if(seenL.get(n.label)>1){const parts=n.path.split('/');n.label=parts.slice(-2).join('/')+(n.dir?'/':'');}
 for(const n of nodes){n.cat=catOf(n);n.w=n.funcs+(n.n.non_production||0);n.r=Math.min(46,(n.dir?6:3)+Math.sqrt(n.w)*1.6);}
 return [nodes,edges];}
function buildLocal(id,hops){const seen=new Map([[id,0]]);let front=[id];
 for(let d=1;d<=hops;d++){const nx=[];for(const x of front){const f=N[x];for(const c of [...f.callers,...f.callees]){if(seen.size>=260)break;
   const t=N[c.id];if($('#gnp').checked&&t.status==='non_production'&&c.id!==id)continue;
   if(!inScope(t.path)||!on.has(t.status)&&on.size!==ORDER.length||EPS&&!EPS.ids.has(c.id)&&c.id!==id)continue;if(!seen.has(c.id)){seen.set(c.id,d);nx.push(c.id);}}}front=nx;}
 const path=GV.target!=null?bfsPath(id,GV.target):chain(N[id]);for(const c of path)if(!seen.has(c.id))seen.set(c.id,-1);
 const nodes=[...seen.keys()].map(i=>{const f=N[i];return {id:i,label:f.kind==='file'?f.path.split('/').pop():f.qual,sub:`${f.path}:${f.line}`,
  cat:f.status,w:f.n_callers,r:i===id||i===GV.target?9:3+Math.min(8,Math.sqrt(f.n_callers)*1.5),grp:f.path,nf:f.findings.length,sk:f.sinks.length,
  sev:Math.max(-1,...f.findings.map(k=>SEV.indexOf(k.severity)))};});
 const edges=[],has=new Set();for(const n of nodes)for(const c of N[n.id].callees)if(seen.has(c.id)){const k=n.id+'>'+c.id;if(!has.has(k)){has.add(k);edges.push({a:n.id,b:c.id,c:1,sure:c.sure});}}
 for(let i=1;i<path.length;i++){const a=path[i-1].id,b=path[i].id,k=a+'>'+b;const e=edges.find(x=>x.a===a&&x.b===b);
  if(e)e.path=true;else if(!has.has(k)){has.add(k);edges.push({a,b,c:1,sure:path[i].sure,path:true});}}
 for(const n of nodes)n.onpath=path.some(c=>c.id===n.id);return [nodes,edges];}
function postFilter(nodes,edges){
 if(GV.mode!=='local'&&$('#gfind').checked){const keep=new Set(nodes.filter(n=>n.nf).map(n=>n.id));
  for(const e of edges){if(keep.has(e.a))keep.add('~'+e.b);if(keep.has(e.b))keep.add('~'+e.a);}
  nodes=nodes.filter(n=>keep.has(n.id)||keep.has('~'+n.id));const ids=new Set(nodes.map(n=>n.id));edges=edges.filter(e=>ids.has(e.a)&&ids.has(e.b));}
 if(GV.mode!=='local'&&$('#giso').checked){const deg=new Set();for(const e of edges){deg.add(e.a);deg.add(e.b);}nodes=nodes.filter(n=>deg.has(n.id));}
 return [nodes,edges];}
// ---- layers: entry points left, then one column per call step, framework-only and never reached on the right
function layout(){const cols=new Map();const head=d=>d===0?'Entry points':d===1?'1 call further':`${d} calls further`;
 for(const n of GV.nodes){let c;if(n.depth<1e9)c=Math.min(n.depth,8);else if(n.fw||n.cat==='framework'||n.cat==='referenced')c=20;else c=30;
  n.col=c;(cols.get(c)||cols.set(c,[]).get(c)).push(n);}
 const keys=[...cols.keys()].sort((a,b)=>a-b);GV.cols=[];GV.heads=[];
 keys.forEach((c,i)=>{const list=cols.get(c).sort((a,b)=>a.sub.localeCompare(b.sub));let y=0,last=null;const x=i*290;
  GV.cols.push({x,label:c===20?'Only framework code':c===30?'Not reached from an entry point':c===8?'8+ calls further':head(c),n:list.length});
  for(const n of list){const fold=n.dir?n.path.split('/').slice(0,-1).join('/'):n.path.split('/').slice(0,-1).join('/');
   if(!GV.layGroup&&fold!==last){y+=last===null?6:22;GV.heads.push({x:x-18,y,t:(fold||'.')+'/'});y+=6;last=fold;}
   n.x=x;y+=n.r+9;n.y=y;y+=n.r+9;n.vx=n.vy=0;}});}
function gLegend(){const items=GV.mode==='local'?ORDER.filter(s=>GV.nodes.some(n=>n.cat===s)).map(s=>[s,L[s]]):Object.values(MOD);
 $('#glegend').innerHTML=items.map(([c,l])=>`<span><span class="sw" style="background:${col(c)};border-radius:50%"></span>${esc(l)}</span>`).join('')
  +(GV.mode!=='local'?`<span><span class="sw" style="background:transparent;border:2px solid var(--ink);border-radius:3px"></span>folder (double-click opens it)</span>`:'')
  +(HASF?`<span><span class="sw" style="background:transparent;border:2px solid var(--find);border-radius:50%"></span>CodeRaster finding</span>`:'')
  +`<span><span style="font-weight:700;color:var(--ink)">▲!</span> dangerous call inside (SQL, command, file …)</span>`
  +(GV.mode==='local'&&GV.target!=null?`<span><b>Blue: path from the endpoint to the dangerous call in ${esc(N[GV.target].qual)}.</b></span>`:'')
  +(GV.mode!=='local'&&(MF.inc.length||MF.exc.length)?`<span><span class="sw" style="background:var(--muted);opacity:.35;border-radius:50%"></span>pale: outside the module filter, linked to it</span>`:'')
  +`<span>Size: ${GV.mode==='local'?'number of callers':'number of functions'}. Dashed: matched by name only.${GV.mode==='local'?' Blue: path from the entry point.':''}</span>`;
 $('#ghint').textContent=GV.mode==='local'?'Drag, zoom, click for details. Double-click a point to center on it.'
  :GV.mode==='layers'?'Left to right: how many calls away from an entry point. Double-click a folder to open it.'
  :'Drag, zoom, click for details. Double-click a folder to open it, a file to see its functions.';}
function build(keep){const old=new Map(GV.nodes.map(n=>[n.id,n]));
 let [nodes,edges]=GV.mode==='local'?buildLocal(GV.focus,+$('#ghops').value):buildMap();[nodes,edges]=postFilter(nodes,edges);
 GV.nodes=nodes;GV.edges=edges;GV.by=new Map(nodes.map(n=>[n.id,n]));GV.adj=new Map(nodes.map(n=>[n.id,new Set()]));
 for(const e of edges){GV.adj.get(e.a).add(e.b);GV.adj.get(e.b).add(e.a);e.A=GV.by.get(e.a);e.B=GV.by.get(e.b);}
 GV.sel=GV.mode==='local'?GV.by.get(GV.focus):(GV.sel&&GV.by.get(GV.sel.id))||null;gLegend();info();
 if(GV.mode==='layers'){cancelAnimationFrame(GV.raf);GV.alpha=0;layout();if(!keep)fit();draw();return;}
 const R=Math.sqrt(nodes.length)*28;let fresh=0;
 for(const n of nodes){const o=old.get(n.id);n.fx=null;
  if(keep&&o&&o.x!=null&&GV.cols.length===0){n.x=o.x;n.y=o.y;n.vx=n.vy=0;continue;}
  const parent=keep&&[...old.values()].find(p=>p.dir&&n.sub.startsWith(p.sub));
  if(parent&&GV.cols.length===0){n.x=parent.x+(Math.random()-.5)*parent.r*2;n.y=parent.y+(Math.random()-.5)*parent.r*2;}
  else{const h=hash(n.grp),a=(h%360)/57.3,rr=R*(0.35+((h>>>9)%100)/160);n.x=Math.cos(a)*rr+(Math.random()-.5)*40;n.y=Math.sin(a)*rr+(Math.random()-.5)*40;fresh++;}
  n.vx=n.vy=0;}
 GV.cols=[];if(GV.mode==='local'){const c=GV.by.get(GV.focus);c.x=0;c.y=0;c.fx=0;c.fy=0;}
 GV.alpha=keep?0.5:1;if(!keep)GV.touched=false;
 if(RM){for(let i=0;i<300;i++)tick();if(!keep)fit();draw();}else{if(!keep)fit(true);loop();}}
function tick(){const ns=GV.nodes,a=GV.alpha,cell=140,grid=new Map();
 for(const n of ns){const k=Math.floor(n.x/cell)+','+Math.floor(n.y/cell);(grid.get(k)||grid.set(k,[]).get(k)).push(n);}
 const rep=GV.mode==='map'?2600:1500;
 for(const n of ns){const cx=Math.floor(n.x/cell),cy=Math.floor(n.y/cell);
  for(let i=-1;i<=1;i++)for(let j=-1;j<=1;j++){const b=grid.get((cx+i)+','+(cy+j));if(!b)continue;
   for(const m of b){if(m===n)continue;let dx=n.x-m.x,dy=n.y-m.y,d2=dx*dx+dy*dy;if(d2<1){dx=Math.random()-.5;dy=Math.random()-.5;d2=1;}
    if(d2>cell*cell)continue;const d=Math.sqrt(d2),over=n.r+m.r+6-d;let f=rep*a/d2;if(over>0)f+=over*0.3/d;n.vx+=dx*f;n.vy+=dy*f;}}}
 const L=GV.mode==='map'?70:80,K=GV.mode==='map'?0.025:0.04;
 for(const e of GV.edges){const A=e.A,B=e.B;let dx=B.x-A.x,dy=B.y-A.y,d=Math.sqrt(dx*dx+dy*dy)||1;
  const f=(d-L-A.r-B.r)*K*a/d,s=Math.min(1,0.4+Math.log(1+e.c)*0.2);A.vx+=dx*f*s;A.vy+=dy*f*s;B.vx-=dx*f*s;B.vy-=dy*f*s;}
 const grp=new Map();if(GV.mode==='map'){for(const n of ns){const g=grp.get(n.grp)||grp.set(n.grp,{x:0,y:0,k:0}).get(n.grp);g.x+=n.x;g.y+=n.y;g.k++;}}
 for(const n of ns){n.vx-=n.x*0.004*a;n.vy-=n.y*0.004*a;
  if(GV.mode==='map'){const g=grp.get(n.grp);if(g.k>1){n.vx+=(g.x/g.k-n.x)*0.012*a;n.vy+=(g.y/g.k-n.y)*0.012*a;}}
  if(n.fx!=null){n.x=n.fx;n.y=n.fy;n.vx=n.vy=0;continue;}n.vx*=0.55;n.vy*=0.55;n.x+=n.vx;n.y+=n.vy;}
 GV.alpha*=0.985;}
function loop(){cancelAnimationFrame(GV.raf);const step=()=>{const k=GV.nodes.length>800?1:3;for(let i=0;i<k&&GV.alpha>0.02;i++)tick();draw();
 if(GV.alpha>0.02)GV.raf=requestAnimationFrame(step);else if(!GV.touched){fit();draw();}};GV.raf=requestAnimationFrame(step);}
function size(){const r=cv.getBoundingClientRect(),dp=devicePixelRatio||1;cv.width=r.width*dp;cv.height=r.height*dp;return r;}
function fit(soft){const r=cv.getBoundingClientRect();if(!GV.nodes.length||!r.width)return;
 const xs=GV.nodes.map(n=>n.x).sort((a,b)=>a-b),ys=GV.nodes.map(n=>n.y).sort((a,b)=>a-b),k=GV.mode==='map'&&GV.nodes.length>40?Math.floor(GV.nodes.length*0.03):0;
 let x0=xs[k]-30,x1=xs[xs.length-1-k]+30,y0=ys[k]-30,y1=ys[ys.length-1-k]+30;
 if(GV.mode==='layers'){x0-=40;x1+=300;y0=-50;y1=Math.min(y1,y0+Math.max(700,r.height*1.2));}
 let s=Math.min(r.width/(x1-x0),r.height/(y1-y0),soft?1.2:2.5);if(GV.mode==='layers')s=Math.max(0.8,Math.min(1.1,r.width/(x1-x0)));GV.scale=s;GV.tx=GV.mode==='layers'?20-x0*s:r.width/2-(x0+x1)/2*s;GV.ty=GV.mode==='layers'?20-y0*s:r.height/2-(y0+y1)/2*s;}
function shape(n){ctx.beginPath();if(n.dir){const r=n.r,k=r*0.35;ctx.moveTo(n.x-r+k,n.y-r);ctx.arcTo(n.x+r,n.y-r,n.x+r,n.y+r,k);ctx.arcTo(n.x+r,n.y+r,n.x-r,n.y+r,k);
 ctx.arcTo(n.x-r,n.y+r,n.x-r,n.y-r,k);ctx.arcTo(n.x-r,n.y-r,n.x+r,n.y-r,k);ctx.closePath();}else ctx.arc(n.x,n.y,n.r,0,7);}
function draw(){const r=size(),dp=devicePixelRatio||1;ctx.setTransform(dp,0,0,dp,0,0);ctx.clearRect(0,0,r.width,r.height);
 ctx.translate(GV.tx,GV.ty);ctx.scale(GV.scale,GV.scale);const foc=GV.hover||(GV.mode!=='local'?GV.sel:null),nb=foc?GV.adj.get(foc.id):null,q=GV.find;
 if(GV.mode==='layers'){ctx.font=`600 ${13/GV.scale}px system-ui,sans-serif`;ctx.textAlign='left';ctx.textBaseline='alphabetic';
  for(const c of GV.cols){ctx.fillStyle=CC.ink;ctx.globalAlpha=1;ctx.fillText(`${c.label} (${c.n})`,c.x-20,-14/GV.scale*1.2);
   ctx.strokeStyle=CC.line;ctx.lineWidth=1/GV.scale;ctx.beginPath();ctx.moveTo(c.x-24,-6/GV.scale);ctx.lineTo(c.x-24,1e5);ctx.stroke();}
  ctx.font=`${11/GV.scale}px system-ui,sans-serif`;ctx.fillStyle=CC.muted;ctx.textBaseline='middle';
  for(const h of GV.heads){let t=h.t;while(t.length>6&&ctx.measureText(t).width>262)t='…'+t.slice(2);ctx.fillText(t,h.x,h.y);}}
 for(const e of GV.edges){const lit=foc?(e.A===foc||e.B===foc):(GV.mode==='local'&&e.path);
  ctx.globalAlpha=foc?(lit?0.9:0.05):(lit?0.9:GV.mode==='layers'?0.13:0.35);ctx.strokeStyle=lit?CC.accent:CC.muted;
  ctx.lineWidth=(lit?1.6:0.8+Math.min(2,Math.log(1+e.c)*0.35))/GV.scale*Math.min(GV.scale,1.5);
  ctx.setLineDash(e.sure?[]:[4/GV.scale,3/GV.scale]);ctx.beginPath();ctx.moveTo(e.A.x,e.A.y);
  if(GV.mode==='layers'){if(Math.abs(e.A.x-e.B.x)<1){const ox=e.A.x-40-Math.min(120,Math.abs(e.B.y-e.A.y)*0.15);ctx.bezierCurveTo(ox,e.A.y,ox,e.B.y,e.B.x,e.B.y);}
   else{const mx=(e.A.x+e.B.x)/2;ctx.bezierCurveTo(mx,e.A.y,mx,e.B.y,e.B.x,e.B.y);}}else ctx.lineTo(e.B.x,e.B.y);ctx.stroke();
  if((GV.mode==='local'&&(lit||!foc))||(GV.mode!=='local'&&lit)){const dx=e.B.x-e.A.x,dy=e.B.y-e.A.y,d=Math.hypot(dx,dy)||1;let ux=dx/d,uy=dy/d;if(GV.mode==='layers'){ux=Math.abs(dx)<1?1:Math.sign(dx);uy=0;}
   const tx=e.B.x-ux*(e.B.r+2),ty=e.B.y-uy*(e.B.r+2),h=7/GV.scale;ctx.setLineDash([]);ctx.fillStyle=lit?CC.accent:CC.muted;
   ctx.beginPath();ctx.moveTo(tx,ty);ctx.lineTo(tx-ux*h-uy*h*.6,ty-uy*h+ux*h*.6);ctx.lineTo(tx-ux*h+uy*h*.6,ty-uy*h-ux*h*.6);ctx.fill();}}
 ctx.setLineDash([]);
 for(const n of GV.nodes){const on=!foc||n===foc||nb.has(n.id),hit=q&&(n.sub.toLowerCase().includes(q)||n.label.toLowerCase().includes(q));
  const out=GV.mode!=='local'&&(MF.inc.length||MF.exc.length)&&!(n.files||[]).some(inScope);
  ctx.globalAlpha=(on?(q&&!hit?0.25:1):0.12)*(out?0.35:1);ctx.fillStyle=CC[n.cat]||CC.muted;shape(n);ctx.fill();
  if(n.dir){ctx.lineWidth=1.5/GV.scale;ctx.strokeStyle=CC.ink;ctx.stroke();}
  if(n.nf){ctx.lineWidth=3/GV.scale;ctx.strokeStyle=CC.find;ctx.beginPath();ctx.arc(n.x,n.y,n.r*(n.dir?1.45:1)+4/GV.scale,0,7);ctx.stroke();
   if(GV.scale>0.5||n===foc){ctx.fillStyle=CC.find;ctx.font=`700 ${10/GV.scale}px system-ui,sans-serif`;ctx.textAlign='left';ctx.textBaseline='bottom';
    ctx.fillText(String(n.nf),n.x+n.r*(n.dir?1.2:0.8)+3/GV.scale,n.y-n.r*0.6);}}
  if(n.sk){const s=Math.max(5,n.r*0.55)/1,sx=n.x-n.r*(n.dir?1.05:0.8)-2/GV.scale,sy=n.y-n.r*(n.dir?1.05:0.8)-2/GV.scale,h=Math.max(7/GV.scale,s*0.9);
   ctx.globalAlpha=Math.min(1,ctx.globalAlpha+0.2);ctx.fillStyle=CC.ink;ctx.beginPath();ctx.moveTo(sx,sy-h);ctx.lineTo(sx+h*0.9,sy+h*0.55);ctx.lineTo(sx-h*0.9,sy+h*0.55);ctx.closePath();ctx.fill();
   ctx.fillStyle=CC.bg;ctx.font=`700 ${h*0.9}px system-ui,sans-serif`;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText('!',sx,sy+h*0.12);}
  if(n===GV.sel||hit){ctx.lineWidth=2.5/GV.scale;ctx.strokeStyle=hit&&n!==GV.sel?CC.accent:CC.ink;shape(n);ctx.stroke();}}
 const fs=12/GV.scale;ctx.font=`${fs}px system-ui,sans-serif`;ctx.lineWidth=3/GV.scale;ctx.strokeStyle=CC.bg;ctx.fillStyle=CC.ink;
 const lay=GV.mode==='layers';ctx.textAlign=lay?'left':'center';ctx.textBaseline=lay?'middle':'top';
 const boxes=[],order=[...GV.nodes].sort((x,y)=>(y===foc)-(x===foc)||(y===GV.sel)-(x===GV.sel)||(y.dir?1:0)-(x.dir?1:0)||y.r-x.r);
 const few=(GV.mode==='local'&&GV.nodes.length<80)||(GV.mode==='map'&&GV.nodes.length<=90)||lay;
 for(const n of order){const hit=q&&(n.sub.toLowerCase().includes(q)||n.label.toLowerCase().includes(q));
  const show=n===foc||n===GV.sel||hit||(nb&&nb.has(n.id))||(!foc&&(few||n.onpath||n.dir||GV.scale*n.r>5));if(!show)continue;
  let t=n.label.length>40?n.label.slice(0,38)+'…':n.label;if(lay)while(t.length>4&&ctx.measureText(t).width>250-n.r)t=t.slice(0,-2)+'…';
  const w=ctx.measureText(t).width,h=fs*1.2;
  const x0=lay?n.x+n.r+5/GV.scale:n.x-w/2,y0=lay?n.y-h/2:n.y+n.r*(n.dir?1:1)+2/GV.scale;
  const must=n===foc||n===GV.sel||hit||(!foc&&n.onpath);if(!must&&boxes.some(b=>x0<b[2]&&x0+w>b[0]&&y0<b[3]&&y0+h>b[1]))continue;boxes.push([x0,y0,x0+w,y0+h]);
  ctx.globalAlpha=1;const tx=lay?x0:n.x,ty=lay?n.y:y0;ctx.strokeText(t,tx,ty);ctx.fillText(t,tx,ty);}
 ctx.globalAlpha=1;}
function at(mx,my){const x=(mx-GV.tx)/GV.scale,y=(my-GV.ty)/GV.scale;let best=null,bd=1e9;
 for(const n of GV.nodes){const d=Math.hypot(n.x-x,n.y-y);if(d<n.r*(n.dir?1.3:1)+6/GV.scale&&d<bd){bd=d;best=n;}}return best;}
function counts(n){return ORDER.filter(s=>n.n[s]).map(s=>`${pill(s)} ${n.n[s]}`).join('<br>')||'<span class="why">no functions</span>';}
function neighbours(n){const ids=[...(GV.adj.get(n.id)||[])].slice(0,12);if(!ids.length)return '';
 return `<p class="why" style="margin-bottom:2px">Linked with:</p><div class="links">${ids.map(i=>{const m=GV.by.get(i);return `<div><a data-pick="${esc(String(i))}">${esc(m.label)}</a></div>`}).join('')}${(GV.adj.get(n.id).size>12)?`<span class="why">and ${GV.adj.get(n.id).size-12} more</span>`:''}</div>`;}
function info(){const n=GV.sel,box=$('#ginfo');if(!n){box.hidden=true;return;}box.hidden=false;
 if(GV.mode!=='local'){const parent=n.path.split('/').slice(0,-1).join('/'),canFold=n.path.includes('/')&&GV.exp.has(parent);
  const fnd=n.nf?`<p><span class="fd">● ${n.nf} CodeRaster finding${n.nf>1?'s':''}, up to ${esc(SEV[n.sev]||'')}</span></p>`:'';
  const where=n.depth<1e9?(n.depth===0?'contains an entry point':`reached ${n.depth} call(s) after an entry point`):n.fw?'only framework code reaches it':'not reached from an entry point';
  box.innerHTML=`<h3>${esc(n.dir?n.path+'/':n.label)}</h3><div class="why code">${esc(n.dir?`${n.files.length} files`:n.path)}</div>
  <p>${esc(where)}</p>${fnd}<p>${counts(n)}</p>${neighbours(n)}
  <div class="acts">${n.dir?'<button class="btn" data-act="open">Open folder</button>':'<button class="btn" data-act="funcs">Functions around it</button>'}
  ${canFold?'<button class="btn" data-act="fold">Fold into '+esc(parent.split('/').pop())+'/</button>':''}${n.dir?'':`<button class="btn" data-code="${FI[n.path]?FI[n.path].fid:''}">Show code</button> `}<button class="btn" data-act="only">Only this module</button><button class="btn" data-act="hide">Hide</button><button class="btn" data-act="list">Open in list</button><button class="btn" data-act="close">Close</button></div>`;}
 else{const f=N[n.id];const fnd=f.findings.length?`<p>${f.findings.map(k=>`<span class="fd">● ${esc(k.status)} ${esc(k.severity)}</span> ${esc(k.rule)} line ${k.line}`).join('<br>')}</p>`:'';
  box.innerHTML=`<h3>${esc(f.kind==='file'?f.path:f.qual)}</h3><div class="why code">${esc(f.path)}:${f.line}</div>
  <p>${pill(f.status)}</p><p class="why">${esc(f.reason)}</p>${fnd}${neighbours(n)}
  <div class="acts">${n.id!==GV.focus?'<button class="btn" data-act="center">Center here</button>':''}<button class="btn" data-code="${f.id}">Show code</button><button class="btn" data-act="list">Open in list</button><button class="btn" data-act="close">Close</button></div>`;}}
function openFolder(n){GV.exp.add(n.path);GV.sel=null;build(true);}
function funcsOf(n){const p=n.path,f=N.find(x=>x.kind==='function'&&x.path===p&&x.status==='entry')||N.find(x=>x.kind==='function'&&x.path===p&&x.status!=='non_production')||N[FI[p].fid];showGraph('local',f.id);}
$('#ginfo').addEventListener('click',ev=>{if(ev.target.closest('[data-act="center"]'))GV.target=null;const pk=ev.target.closest('[data-pick]');if(pk){const k=pk.dataset.pick,m=GV.by.get(GV.mode==='local'?+k:k);
  if(m){const r=cv.getBoundingClientRect();GV.sel=m;info();GV.tx=r.width/2-m.x*GV.scale;GV.ty=r.height/2-m.y*GV.scale;draw();}return;}
 const b=ev.target.closest('[data-act]');if(!b||!GV.sel)return;const a=b.dataset.act,n=GV.sel;
 if(a==='close'){GV.sel=null;info();draw();}else if(a==='center'){showGraph('local',n.id);}else if(a==='open')openFolder(n);
 else if(a==='fold'){const parent=n.path.split('/').slice(0,-1).join('/');for(const d of [...GV.exp])if(d===parent||d.startsWith(parent+'/'))GV.exp.delete(d);GV.sel=null;build(true);}
 else if(a==='funcs')funcsOf(n);
 else if(a==='only'||a==='hide'){const k=a==='only'?'inc':'exc',v=n.dir?n.path+'/':n.path;if(!MF[k].includes(v))MF[k].push(v);GV.sel=null;mfChanged();}
 else if(a==='list'){view2('list');if(GV.mode!=='local'){scope=n.dir?n.path+'/':n.path;const p=n.path.split('/');for(let i=1;i<=p.length;i++)openDirs.add(p.slice(0,i).join('/'));tree();rows();}else go(n.id);}});
let drag=null;const pts=new Map();
cv.addEventListener('pointerdown',ev=>{cv.setPointerCapture(ev.pointerId);pts.set(ev.pointerId,{x:ev.offsetX,y:ev.offsetY});
 if(pts.size===2){drag={pinch:true,d:dist(),s:GV.scale};return;}const n=at(ev.offsetX,ev.offsetY);
 drag={n,x:ev.offsetX,y:ev.offsetY,tx:GV.tx,ty:GV.ty,moved:false};GV.touched=true;cv.classList.add('drag');if(n&&GV.mode!=='layers'){n.fx=n.x;n.fy=n.y;}});
function dist(){const [a,b]=[...pts.values()];return Math.hypot(a.x-b.x,a.y-b.y)||1;}
cv.addEventListener('pointermove',ev=>{if(pts.has(ev.pointerId))pts.set(ev.pointerId,{x:ev.offsetX,y:ev.offsetY});
 if(drag&&drag.pinch&&pts.size===2){const r=cv.getBoundingClientRect();zoomAt(r.width/2,r.height/2,drag.s*dist()/drag.d/GV.scale);return;}
 if(!drag){const h=at(ev.offsetX,ev.offsetY);if(h!==GV.hover){GV.hover=h;cv.style.cursor=h?'pointer':'grab';draw();}return;}
 const dx=ev.offsetX-drag.x,dy=ev.offsetY-drag.y;if(Math.abs(dx)+Math.abs(dy)>3)drag.moved=true;
 if(drag.n&&GV.mode!=='layers'){drag.n.fx=drag.n.x=(ev.offsetX-GV.tx)/GV.scale;drag.n.fy=drag.n.y=(ev.offsetY-GV.ty)/GV.scale;if(GV.alpha<0.15){GV.alpha=0.15;if(!RM)loop();}draw();}
 else{GV.tx=drag.tx+dx;GV.ty=drag.ty+dy;draw();}});
function up(ev){pts.delete(ev.pointerId);if(!drag)return;cv.classList.remove('drag');
 if(drag.n){if(!(GV.mode==='local'&&drag.n.id===GV.focus))drag.n.fx=null;if(!drag.moved){GV.sel=drag.n;info();}}
 else if(!drag.moved&&!drag.pinch){GV.sel=null;info();}drag=null;draw();}
cv.addEventListener('pointerup',up);cv.addEventListener('pointercancel',up);
cv.addEventListener('pointerleave',()=>{if(!drag&&GV.hover){GV.hover=null;draw();}});
function zoomAt(mx,my,k){const s=Math.max(0.03,Math.min(8,GV.scale*k));GV.tx=mx-(mx-GV.tx)*s/GV.scale;GV.ty=my-(my-GV.ty)*s/GV.scale;GV.scale=s;draw();}
cv.addEventListener('wheel',ev=>{ev.preventDefault();GV.touched=true;zoomAt(ev.offsetX,ev.offsetY,Math.exp(-ev.deltaY*0.0015));},{passive:false});
cv.addEventListener('dblclick',ev=>{const n=at(ev.offsetX,ev.offsetY);if(!n)return;GV.target=null;
 if(GV.mode==='local')showGraph('local',n.id);else if(n.dir)openFolder(n);else funcsOf(n);});
$('#gfit').onclick=()=>{fit();draw();};
$('#gq').oninput=e=>{GV.find=e.target.value.toLowerCase().trim();draw();};
$('#gq').onkeydown=e=>{if(e.key!=='Enter')return;const q=GV.find;const n=GV.nodes.find(n=>n.label.toLowerCase().includes(q)||n.sub.toLowerCase().includes(q));
 if(n){const r=cv.getBoundingClientRect();GV.sel=n;info();GV.scale=Math.max(GV.scale,1.2);GV.tx=r.width/2-n.x*GV.scale;GV.ty=r.height/2-n.y*GV.scale;draw();}};
$('#gnp').onchange=()=>{GV.expInit=false;build();};
$('#giso').onchange=$('#ghops').onchange=$('#gweak').onchange=$('#gfind').onchange=()=>build();
$('#gnb').onchange=()=>{GV.expInit=false;build();};
$('#gexpall').onclick=()=>{if(GV.mode==='layers'){GV.layGroup=false;build();return;}for(const p of shownFiles()){const parts=p.split('/');for(let i=1;i<parts.length;i++)GV.exp.add(parts.slice(0,i).join('/'));}build(GV.mode==='map');};
$('#gcolall').onclick=()=>{if(GV.mode==='layers'){GV.layGroup=true;if(!GV.expInit)initExp();build();return;}GV.exp=new Set();GV.expInit=true;const top=new Set(shownFiles().map(dispKey));
 if(top.size===1){initExp();}build();};
function setMode(m){GV.mode=m;$('#gexpall').textContent=m==='layers'?'Files':'Expand all';$('#gcolall').textContent=m==='layers'?'Folders':'Folders only';for(const [id,k] of [['#gmod','map'],['#glay','layers'],['#gloc','local']])$(id).setAttribute('aria-pressed',m===k);
 $('#ghopsl').hidden=m!=='local';$('#gisol').hidden=m==='local';$('#gfold').hidden=m==='local';$('#gfindl').hidden=!HASF||m==='local';}
$('#gmod').onclick=()=>{setMode('map');GV.sel=null;build();};
$('#glay').onclick=()=>{setMode('layers');GV.sel=null;build();};
$('#gloc').onclick=()=>{GV.target=null;if(GV.focus==null){const f=N.find(x=>x.kind==='function'&&x.status==='entry')||N.find(x=>x.kind==='function');if(!f)return;GV.focus=f.id;}showGraph('local',GV.focus);};
function view2(v){view(v);}
function showGraph(m,id,keep){if(!keep)GV.target=null;view2('graph');GV.built=true;if(id!=null)GV.focus=id;setMode(m);build();}
$('#tlist').onclick=()=>view('list');
if(MF.inc.length||MF.exc.length)mfChanged();
$('#tgraph').onclick=()=>{view2('graph');if(!GV.built){GV.built=true;setMode('map');build();}else{draw();if(GV.alpha>0.02&&!RM)loop();}};
// ======================= attack surface, hotspots, config from the report, exports =======================
const dl=(name,text,type)=>{const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([text],{type:type||'text/plain'}));a.download=name;document.body.appendChild(a);a.click();setTimeout(()=>{URL.revokeObjectURL(a.href);a.remove();},500);};
const csv=rows=>rows.map(r=>r.map(v=>{v=String(v??'');return /[",\n;]/.test(v)?'"'+v.replace(/"/g,'""')+'"':v;}).join(',')).join('\n');
const skBadges=(kinds,maybe)=>SKO.filter(k=>kinds[k]||(maybe&&maybe[k])).map(k=>`<span class="sk${kinds[k]?'':' mb'}" title="${esc(SK[k])}${kinds[k]?'':' (only through a link matched by name)'}">${esc(k)}${kinds[k]?' '+kinds[k]:''}</span>`).join(' ');
const AUTHL={check:'access check seen',public:'explicitly public',none:'no check seen'};
// ---- attack surface
const EP=D.endpoints||[];let EPopen=null;
// filter groups: values inside a group are OR, groups are AND; an empty group means "any"
const KINDL={http:'web endpoint',page:'page',job:'job / listener',program:'program start',middleware:'middleware',other:'other'};
const GROUPS=[
 {k:'acc',label:'Access check',val:e=>[e.auth.status],name:v=>AUTHL[v]||v,order:['none','public','check']},
 {k:'kind',label:'Kind',val:e=>[e.kind],name:v=>KINDL[v]||v,order:Object.keys(KINDL)},
 {k:'meth',label:'Method',val:e=>e.method.split('|'),name:v=>v,order:['GET','POST','PUT','PATCH','DELETE','ANY','HEAD','OPTIONS','JOB','RUN','MW']},
 {k:'sink',label:'Dangerous calls',val:e=>{const ks=Object.keys(e.sink_kinds);return ks.length?['any',...ks]:['none'];},name:v=>v==='any'?'any':v==='none'?'none':SK[v]||v,order:['any','none',...SKO]},
 {k:'cert',label:'Way there',val:e=>{const s=Object.keys(e.sink_kinds).length,m=Object.keys(e.sink_kinds_maybe||{}).length;return [s?'sure':m?'byname':'nothing'];},name:v=>({sure:'sure links',byname:'only by name',nothing:'no dangerous call'}[v]),order:['sure','byname','nothing']},
 {k:'fnd',label:'CodeRaster',val:e=>[e.findings?'yes':'no'],name:v=>v==='yes'?'with findings':'without findings',order:['yes','no'],only:()=>EP.some(e=>e.findings)},
];
let EPF={q:'',sort:'path',dir:1};for(const g of GROUPS)EPF[g.k]=new Set();EPF.kind=new Set(['http','page']);
const epBase=()=>EP.filter(e=>inScope(N[e.id].path)&&(!EPF.q||(e.method+' '+e.path+' '+N[e.id].qual+' '+N[e.id].path+' '+e.auth.how).toLowerCase().includes(EPF.q)));
const passes=(e,skip)=>GROUPS.every(g=>g.k===skip||!EPF[g.k].size||g.val(e).some(v=>EPF[g.k].has(v)));
function epVisible(){const r=epBase().filter(e=>passes(e));const k=EPF.sort,d=EPF.dir;
 const key={path:e=>e.path,method:e=>e.method,handler:e=>N[e.id].qual,access:e=>['none','public','check'].indexOf(e.auth.status),
  sinks:e=>-Object.values(e.sink_kinds).reduce((a,b)=>a+b,0),findings:e=>-e.findings,reach:e=>-e.reaches}[k]||(e=>e.path);
 return r.sort((a,b)=>{const x=key(a),y=key(b);return (x<y?-1:x>y?1:0)*d||a.path.localeCompare(b.path);});}
function sfFilters(){const base=epBase();
 $('#sffil').innerHTML=GROUPS.filter(g=>!g.only||g.only()).map(g=>{const cnt=new Map();for(const e of base)if(passes(e,g.k))for(const v of new Set(g.val(e)))cnt.set(v,(cnt.get(v)||0)+1);
  const vals=[...new Set([...g.order.filter(v=>cnt.has(v)||EPF[g.k].has(v)),...[...cnt.keys()].filter(v=>!g.order.includes(v))])];
  return `<div class="fg"><span class="fgl">${esc(g.label)}</span>${vals.map(v=>`<button class="chip tg" data-fg="${g.k}" data-v="${esc(v)}" aria-pressed="${EPF[g.k].has(v)}">${esc(g.name(v))} <b>${cnt.get(v)||0}</b></button>`).join('')}</div>`;}).join('')
  +`<button class="btn" id="sfreset">Reset filters</button>`;}
function sfSave(){try{const o={q:EPF.q,sort:EPF.sort,dir:EPF.dir};for(const g of GROUPS)o[g.k]=[...EPF[g.k]];HS.set('s',JSON.stringify(o));saveHash();}catch(e){}}
function sfLoad(){try{const v=HS.get('s');if(!v)return;const o=JSON.parse(v);for(const g of GROUPS)if(Array.isArray(o[g.k]))EPF[g.k]=new Set(o[g.k].map(String));
 EPF.q=String(o.q||'');EPF.sort=o.sort||'path';EPF.dir=o.dir===-1?-1:1;$('#sfq').value=EPF.q;}catch(e){}}
function surface(){const r=epVisible(),web=EP.filter(e=>['http','page'].includes(e.kind)&&inScope(N[e.id].path));
 const nochk=web.filter(e=>e.auth.status==='none').length,risky=web.filter(e=>e.auth.status==='none'&&Object.keys(e.sink_kinds).length).length;
 $('#sfsum').innerHTML=`<b>${web.length}</b> web endpoints and pages, <b>${nochk}</b> without a visible access check, <b>${risky}</b> of those reach a dangerous call.
  <button class="btn" id="sfquick">Show those ${risky}</button>`
  +(D.central_auth&&D.central_auth.length?`<div class="note" style="margin-top:8px">Access rules are also set centrally: ${D.central_auth.slice(0,3).map(x=>`<code>${esc(x)}</code>`).join(', ')}. They are not evaluated per endpoint here, so "no check seen" may still be protected there.</div>`:'');
 sfFilters();
 for(const th of document.querySelectorAll('.sft th[data-sort]'))th.setAttribute('aria-sort',th.dataset.sort===EPF.sort?(EPF.dir>0?'ascending':'descending'):'none');
 $('#sfrows').innerHTML=r.length?r.map(e=>{const f=N[e.id];return `<tr class="fn${EPopen===e.id?' open':''}" tabindex="0" data-ep="${e.id}"><td><span class="mth">${esc(e.method)}</span></td><td><code>${esc(e.path)}</code>${e.more?` <span class="why">+${e.more} more</span>`:''}</td>
  <td><code>${esc(f.qual)}</code><div class="why">${esc(where(f))}</div></td><td><span class="au au-${e.auth.status}">${esc(AUTHL[e.auth.status])}</span><div class="why">${esc(e.auth.how)}</div></td>
  <td>${skBadges(e.sink_kinds,e.sink_kinds_maybe)||'<span class="why">none</span>'}${e.findings?` <span class="fd">● ${e.findings}</span>`:''}</td></tr>`
  +(EPopen===e.id?`<tr class="detail"><td colspan="5">${epDetail(e)}</td></tr>`:'');}).join('')
  :`<tr><td colspan="5" class="empty">No endpoint matches. Change the filters or the module filter.</td></tr>`;
 $('#sfcount').textContent=`${r.length} of ${EP.length} shown`;
 $('#sfuse').textContent=`Use these ${r.length} in the graph and the function list`;
 const sv=EPF.sort+':'+EPF.dir;if([...$('#sfsort').options].some(o=>o.value===sv))$('#sfsort').value=sv;sfSave();}
$('#sffil').addEventListener('click',ev=>{if(ev.target.closest('#sfreset')){for(const g of GROUPS)EPF[g.k]=new Set();EPF.q='';$('#sfq').value='';surface();return;}
 const b=ev.target.closest('[data-fg]');if(!b)return;const s=EPF[b.dataset.fg],v=b.dataset.v;s.has(v)?s.delete(v):s.add(v);surface();});
$('#sfsum').addEventListener('click',ev=>{if(!ev.target.closest('#sfquick'))return;for(const g of GROUPS)EPF[g.k]=new Set();
 EPF.kind=new Set(['http','page']);EPF.acc=new Set(['none']);EPF.cert=new Set(['sure']);surface();});
document.querySelector('.sft thead').addEventListener('click',ev=>{const th=ev.target.closest('th[data-sort]');if(!th)return;const k=th.dataset.sort;
 if(EPF.sort===k)EPF.dir=-EPF.dir;else{EPF.sort=k;EPF.dir=1;}surface();});
// ---- "reached from the filtered endpoints": a scope for the function list and the graph
function reachOf(ids){const seen=new Set(ids),q=[...ids];while(q.length&&seen.size<60000){const x=q.shift();
 for(const c of N[x].callees){if(seen.has(c.id)||!c.sure)continue;const t=N[c.id];if(t.status==='non_production')continue;seen.add(c.id);q.push(c.id);}}return seen;}
function epScopeSet(on_){if(!on_){EPS=null;}else{const r=epVisible();EPS={ids:reachOf(r.map(e=>e.id)),n:r.length,files:null};
 EPS.files=new Set([...EPS.ids].map(i=>N[i].path));}
 $('#epsbar').hidden=!EPS;if(EPS)$('#epstext').textContent=`Showing only code reached through sure links from ${EPS.n} endpoint(s) of the attack-surface filter (${EPS.ids.size} functions and files).`;
 legend();limit=200;rows();if(GV.built){GV.expInit=false;if(!$('#gview').hidden)build();}}
$('#sfuse').onclick=()=>{epScopeSet(true);view('graph');if(!GV.built){GV.built=true;setMode('layers');build();}};
$('#epsoff').onclick=()=>epScopeSet(false);
$('#sfq').oninput=e=>{EPF.q=e.target.value.toLowerCase();surface();};
$('#sfsort').onchange=e=>{const [k,d]=e.target.value.split(':');EPF.sort=k;EPF.dir=+d;surface();};
sfLoad();
$('#sfcsv').onclick=()=>dl('reachmap-endpoints.csv',csv([['method','path','handler','file','line','access check','how','dangerous calls (sure)','dangerous calls (by name only)','findings','parameters'],
 ...epVisible().map(e=>{const f=N[e.id];return [e.method,e.path,f.qual,f.path,f.line,e.auth.status,e.auth.how,Object.entries(e.sink_kinds).map(([k,v])=>k+':'+v).join(' '),Object.entries(e.sink_kinds_maybe||{}).map(([k,v])=>k+':'+v).join(' '),e.findings,(e.params||[]).map(p=>p.in+':'+p.name).join(' ')];})]),'text/csv');
function epDetail(e){const f=N[e.id];let h=`<p>${pill(f.status)} ${esc(f.entry)} <button class="btn" data-go="${f.id}">Open in list</button> <button class="btn" data-graph="${f.id}">Show in graph</button> <button class="btn" data-trace="${f.id}">Trace</button> <button class="btn" data-code="${f.id}">Show code</button></p>`;
 h+=`<p class="why">Reaches ${e.reaches} function(s) through sure links.</p>`;
 if((e.params||[]).length)h+=`<h4>Parameters read in the handler</h4><p>${e.params.map(p=>`<span class="sk" title="${esc(p.in)}${p.line?' (line '+p.line+')':''}">${esc(p.in)}: ${esc(p.name)}</span>`).join(' ')}</p>`;
 else h+='<p class="why">No parameters read directly in the handler (it may read them in code it calls).</p>';
 if(e.sinks.length){h+=`<h4>Dangerous calls it can reach</h4><table class="mini-t"><tr><th>Kind</th><th>In</th><th>Code</th><th>Calls away</th><th></th></tr>${e.sinks.map(s=>{const t=N[s.id];
  return `<tr><td><span class="sk${s.sure?'':' mb'}">${esc(s.kind)}</span></td><td><a data-go="${t.id}">${esc(t.qual)}</a><div class="why"><a data-code="${t.id}" data-line="${s.line}">${esc(t.path.split('/').pop())}:${s.line}</a></div></td><td><code class="snip">${esc(s.code)}</code></td><td>${s.steps}${s.sure?'':' <span class="why">(by name)</span>'}</td><td><button class="btn" data-path="${e.id}:${t.id}">Path in graph</button></td></tr>`;}).join('')}</table>`;}
 else h+='<p class="why">No dangerous call found on the way (SQL, command, file, deserialization, XML, outgoing request, redirect, code evaluation).</p>';
 return h;}
$('#sfrows').addEventListener('click',ev=>{const tb=ev.target.closest('[data-trace]');if(tb){traceFn(+tb.dataset.trace);return;}const p=ev.target.closest('[data-path]');if(p){const [a,b]=p.dataset.path.split(':').map(Number);showPath(a,b);return;}
 const gb=ev.target.closest('[data-graph]');if(gb){showGraph('local',+gb.dataset.graph);return;}const g=ev.target.closest('[data-go]');if(g){view('list');go(+g.dataset.go);return;}
 const tr=ev.target.closest('tr[data-ep]');if(!tr)return;const id=+tr.dataset.ep;EPopen=EPopen===id?null:id;surface();});
$('#sfrows').addEventListener('keydown',ev=>{if(ev.key==='Enter'&&ev.target.matches('tr[data-ep]')){ev.preventDefault();ev.target.click();}});
// ---- hotspots and delete candidates
function hotspots(){const hs=(D.hotspots||[]).filter(h=>inScope(N[h.id].path));
 $('#hsrows').innerHTML=hs.length?hs.map(h=>{const f=N[h.id];return `<tr><td><a data-go="${f.id}">${esc(f.qual)}</a><div class="why">${esc(where(f))}</div></td><td><b>${h.via_entries}</b></td><td>${h.callers}</td><td>${h.sinks.map(k=>`<span class="sk">${esc(k)}</span>`).join(' ')||'<span class="why">none</span>'}</td><td>${pill(f.status)}</td><td><button class="btn" data-graph="${f.id}">Show in graph</button></td></tr>`;}).join('')
  :'<tr><td colspan="6" class="empty">No function is reached from several entry points (or the module filter hides them).</td></tr>';
 const G=D.git||{};const months=+$('#dcage').value;const lim=Date.now()/1000-months*30.4*86400;
 if(!G.available){$('#dcnote').innerHTML='<span class="why">No git history found for this folder, so file ages are not known.</span>';$('#dcrows').innerHTML='';return;}
 $('#dcnote').innerHTML=G.shallow?'<div class="note">This is a shallow git clone: the dates show the clone, not the real last change.</div>':'';
 const dc=N.filter(f=>f.kind==='function'&&['no_caller','not_reached','dead_branch','referenced'].includes(f.status)&&f.changed&&f.changed<lim&&inScope(f.path)).sort((a,b)=>a.changed-b.changed);
 $('#dcrows').innerHTML=dc.length?dc.slice(0,300).map(f=>`<tr><td><a data-go="${f.id}">${esc(f.qual)}</a><div class="why">${esc(where(f))}</div></td><td>${pill(f.status)}</td><td>${new Date(f.changed*1000).toISOString().slice(0,10)}</td><td>${f.commits}</td></tr>`).join('')
  :'<tr><td colspan="4" class="empty">Nothing unreached in files that old.</td></tr>';}
$('#hsview').addEventListener('click',ev=>{const gb=ev.target.closest('[data-graph]');if(gb){showGraph('local',+gb.dataset.graph);return;}const g=ev.target.closest('[data-go]');if(g){view('list');go(+g.dataset.go);}});
$('#dcage').onchange=hotspots;
// ---- config written from the report
let CFG=[];const CFK='reachmap-config:'+D.root;try{CFG=JSON.parse(localStorage.getItem(CFK)||'[]');}catch(e){}
function cfgSave(){try{localStorage.setItem(CFK,JSON.stringify(CFG));}catch(e){}$('#cfgbox').hidden=!CFG.length;$('#cfgn').textContent=CFG.length;}
function cfgAdd(kind,f){const pat=f.kind==='file'?f.path:`${f.path}:${f.qual}`;if(!CFG.some(c=>c.kind===kind&&c.pat===pat))CFG.push({kind,pat});cfgSave();}
$('#cfgdl').onclick=()=>dl('reachmap.cfg',`# reachmap config, written from the report of ${D.root} (${D.generated})\n# use: python3 reachmap.py PROJECT --config reachmap.cfg\n`+CFG.map(c=>`${c.kind} ${c.pat}`).join('\n')+'\n');
$('#cfgclr').onclick=()=>{CFG=[];cfgSave();};cfgSave();
// ---- list export
$('#lcsv').onclick=()=>dl('reachmap-functions.csv',csv([['function','file','line','status','reason','callers','entry points through it','dangerous calls','last change','findings'],
 ...visible().map(f=>[f.qual,f.path,f.line,f.status,f.reason,f.n_callers,f.via_entries,f.sinks.map(s=>s.kind).join(' '),f.changed?new Date(f.changed*1000).toISOString().slice(0,10):'',f.findings.length])]),'text/csv');
// ---- graph exports
$('#gpng').onclick=()=>{draw();cv.toBlob(b=>{const a=document.createElement('a');a.href=URL.createObjectURL(b);a.download='reachmap-graph.png';document.body.appendChild(a);a.click();setTimeout(()=>a.remove(),500);});};
$('#gsvg').onclick=()=>{const ns=GV.nodes;if(!ns.length)return;let x0=1e9,y0=1e9,x1=-1e9,y1=-1e9;for(const n of ns){x0=Math.min(x0,n.x-n.r-10);y0=Math.min(y0,n.y-n.r-10);x1=Math.max(x1,n.x+n.r+160);y1=Math.max(y1,n.y+n.r+24);}
 const e=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
 let o=`<svg xmlns="http://www.w3.org/2000/svg" viewBox="${x0} ${y0} ${x1-x0} ${y1-y0}" font-family="system-ui,sans-serif" font-size="11"><rect x="${x0}" y="${y0}" width="${x1-x0}" height="${y1-y0}" fill="${CC.bg}"/>`;
 for(const g of GV.edges)o+=`<line x1="${g.A.x.toFixed(1)}" y1="${g.A.y.toFixed(1)}" x2="${g.B.x.toFixed(1)}" y2="${g.B.y.toFixed(1)}" stroke="${g.path?CC.accent:CC.muted}" stroke-opacity="${g.path?0.9:0.35}"${g.sure?'':' stroke-dasharray="4 3"'}/>`;
 for(const n of ns){o+=n.dir?`<rect x="${(n.x-n.r).toFixed(1)}" y="${(n.y-n.r).toFixed(1)}" width="${2*n.r}" height="${2*n.r}" rx="${n.r*0.35}" fill="${CC[n.cat]}" stroke="${CC.ink}"/>`:`<circle cx="${n.x.toFixed(1)}" cy="${n.y.toFixed(1)}" r="${n.r}" fill="${CC[n.cat]}"/>`;
  if(n.nf)o+=`<circle cx="${n.x.toFixed(1)}" cy="${n.y.toFixed(1)}" r="${n.r*(n.dir?1.45:1)+4}" fill="none" stroke="${CC.find}" stroke-width="3"/>`;
  o+=`<text x="${n.x.toFixed(1)}" y="${(n.y+n.r+12).toFixed(1)}" text-anchor="middle" fill="${CC.ink}">${e(n.label)}</text>`;}
 dl('reachmap-graph.svg',o+'</svg>','image/svg+xml');};
// ---- path from an endpoint to a dangerous call, in the graph
function bfsPath(a,b){const prev=new Map([[a,null]]),q=[a];while(q.length&&prev.size<6000){const x=q.shift();if(x===b)break;
 for(const c of N[x].callees){if(!prev.has(c.id)){prev.set(c.id,{from:x,how:c.how,sure:c.sure});q.push(c.id);}}}
 if(!prev.has(b))return [];const out=[];let c=b;while(c!=null){const p=prev.get(c);out.push({id:c,how:p?p.how:'',sure:p?p.sure:true});c=p?p.from:null;}return out.reverse();}
function showPath(a,b){GV.target=b;$('#ghops').value='1';showGraph('local',a,true);}
// ---- views


// ---- code view: the source of a file, with the function and its dangerous calls marked
const SRC=__SRC__,SRCINFO=__SRCINFO__,SRCC={};
async function srcText(path){if(path in SRCC)return SRCC[path];const b=SRC[path];if(b==null)return null;
 try{const bin=Uint8Array.from(atob(b),c=>c.charCodeAt(0));const ds=new DecompressionStream('deflate');
  const t=await new Response(new Blob([bin]).stream().pipeThrough(ds)).text();return SRCC[path]=t;}catch(e){return SRCC[path]=null;}}
const CP={id:null,line:0};
async function openCode(id,line){const f=N[id];if(!f)return;CP.id=id;CP.line=line||f.line;const pane=$('#codepane');pane.hidden=false;
 $('#cptitle').textContent=f.kind==='file'?f.path.split('/').pop():f.qual;$('#cpsub').textContent=f.path+(f.kind==='file'?'':':'+f.line+'-'+f.end);
 $('#cpjump').hidden=f.kind==='file'&&!line;const body=$('#cpbody');body.textContent='Loading…';
 const t=await srcText(f.path);
 if(t==null){body.innerHTML=`<p class="why" style="padding:14px">${SRC[f.path]==null?(SRCINFO.mode==='none'?'This report was made without source code (--source none).':
  SRCINFO.mode==='production'&&f.status==='non_production'?'Tests, docs and vendored code are not included. Run with <code>--source all</code> to include them.':
  'This file is not included (too large or over the size budget).'):'The source could not be decoded in this browser.'}</p>`;return;}
 const lines=t.split('\n'),mark=new Map();for(const x of N)if(x.path===f.path)for(const k of x.sinks)mark.set(k.line,(mark.get(k.line)||'')+(mark.has(k.line)?', ':'')+k.kind);
 const lo=f.kind==='file'?0:f.line,hi=f.kind==='file'?0:f.end,hit=CP.line;
 body.innerHTML=lines.map((l,i)=>{const n=i+1,inn=lo&&n>=lo&&n<=hi;return `<div class="cl${inn?' in':''}${n===f.line&&lo?' cur':''}${n===hit&&n!==f.line?' hit':''}" id="cl${n}"><span class="cn">${n}</span><span>${esc(l)||' '}</span>${mark.has(n)?`<span class="sk" title="dangerous call">${esc(mark.get(n))}</span>`:''}</div>`;}).join('');
 const el=document.getElementById('cl'+Math.max(1,hit-3));if(el)body.scrollTop=el.offsetTop-body.offsetTop;}
$('#cpclose').onclick=()=>{$('#codepane').hidden=true;};
$('#cpcopy').onclick=()=>{const f=N[CP.id];if(f&&navigator.clipboard)navigator.clipboard.writeText(f.path+':'+(CP.line||f.line)).catch(()=>{});};
$('#cpjump').onclick=()=>{const el=document.getElementById('cl'+Math.max(1,(N[CP.id]||{line:1}).line-3));if(el)$('#cpbody').scrollTop=el.offsetTop-$('#cpbody').offsetTop;};
addEventListener('keydown',ev=>{if(ev.key==='Escape'&&!$('#codepane').hidden)$('#codepane').hidden=true;});
document.addEventListener('click',ev=>{const c=ev.target.closest('[data-code]');if(c){ev.preventDefault();openCode(+c.dataset.code,c.dataset.line?+c.dataset.line:0);}
 const fl=ev.target.closest('[data-follow]');if(fl){ev.preventDefault();followLayers(+fl.dataset.follow);}});
// ---- follow a file (or the file of a function) in the Layers graph: only that module plus the files linked to it
function followLayers(id){const f=N[id];if(!f)return;MF.inc=[f.path];MF.exc=[];$('#gnb').checked=true;
 view2('graph');GV.built=true;setMode('layers');mfChanged();GV.expInit=false;build();
 const n=GV.by.get('F:'+f.path);if(n){GV.sel=n;info();fit();draw();}}
// ---- Trace: follow one function up to the entry points that reach it and down to what it calls
const TR={id:null,hist:[],open:new Set(),tests:false,loaded:false,n:0};
function trKids(dir,id){const f=N[id],src=dir==='up'?f.callers:f.callees,out=[],idx=new Map();
 for(const c of src){if(!TR.loaded&&(c.kind==='loaded'||/module is loaded/.test(c.how||'')))continue;
  const t=N[c.id];if(!TR.tests&&t.status==='non_production')continue;
  if(idx.has(c.id)){idx.get(c.id).n++;continue;}const o={id:c.id,how:c.how,sure:c.sure,at:c.at||'',n:1};idx.set(c.id,o);out.push(o);}
 out.sort((a,b)=>(b.sure-a.sure)||N[a.id].qual.localeCompare(N[b.id].qual));return out;}
function trRow(dir,k,path,depth){if(TR.n++>1500)return '';const t=N[k.id],cyc=path.includes(k.id),key=dir+':'+path.concat(k.id).join('>');
 const kids=cyc?[]:trKids(dir,k.id),open=TR.open.has(key)&&kids.length>0;
 const kinds={};for(const x of t.sinks)kinds[x.kind]=1;
 let h=`<div class="trn" style="--d:${depth}"><button class="trt" data-tk="${key}" ${kids.length?'':'disabled'} aria-expanded="${open}" aria-label="${open?'Collapse':'Expand'}">${kids.length?(open?'▾':'▸'):'·'}</button>
  <a data-tf="${t.id}" tabindex="0">${esc(t.qual)}</a> ${pill(t.status)} <a data-code="${t.id}" title="Show code">{ }</a> <span class="why">${esc(where(t))}${k.at?', call at '+esc(k.at.split('/').pop()):''}${k.n>1?` (${k.n} places)`:''}${k.how?', '+esc(k.how):''}${k.sure?'':' (by name only)'}</span> ${skBadges(kinds)}
  ${cyc?'<span class="why">↻ already on this path</span>':''}${dir==='up'&&!kids.length&&t.status==='entry'?`<span class="why">entry point: ${esc(t.entry)}</span>`:''}</div>`;
 if(open)for(const c of kids.slice(0,60))h+=trRow(dir,c,path.concat(k.id),depth+1);
 if(open&&kids.length>60)h+=`<div class="trn why" style="--d:${depth+1}">+${kids.length-60} more, open the function itself to see them</div>`;
 return h;}
function trOpenAll(dir,id,max){const walk=(i,path,d)=>{if(d>max)return;for(const k of trKids(dir,i)){if(path.includes(k.id))continue;
  TR.open.add(dir+':'+path.concat(i,k.id).join('>'));if(TR.open.size<3000)walk(k.id,path.concat(i),d+1);}};
 TR.open=new Set([...TR.open].filter(x=>!x.startsWith(dir+':')));walk(id,[],1);}
function trRender(){const b=$('#trbody');if(TR.id==null)return;const f=N[TR.id];TR.n=0;
 const chain=[];let c=f,g=0;while(c&&g++<40){chain.unshift(c);c=c.pred>=0?N[c.pred]:null;if(c&&chain.includes(c))break;}
 const up=trKids('up',f.id),down=trKids('down',f.id);
 const sinks=f.sinks.length?`<p>${f.sinks.map(s=>`<span class="sk" title="line ${s.line}: ${esc(s.code)}">${esc(s.kind)}</span>`).join(' ')} <span class="why">dangerous calls inside this function</span></p>`:'';
 let h=`<h3 style="margin:6px 0"><code>${esc(f.qual)}</code> ${pill(f.status)}</h3><p class="why">${esc(f.path)}:${f.line}-${f.end}. ${esc(f.reason)}</p>${sinks}
  <p><button class="btn" data-go="${f.id}">Open in list</button> <button class="btn" data-graph="${f.id}">Show in graph</button> <button class="btn" data-code="${f.id}">Show code</button> <button class="btn" data-follow="${f.id}">Follow file in layers</button></p>`;
 if(chain.length>1)h+=`<h4>Shortest way from an entry point</h4><div class="trpath">${chain.map((x,i)=>`${i?'<span class="why">→</span>':''}<a data-tf="${x.id}" tabindex="0">${esc(x.name)}</a>`).join('')}</div>`;
 h+=`<div class="trh"><div><h4>Called from (${up.length}) <button class="btn" data-trx="up">Open 3 levels</button> <button class="btn" data-trx="upc">Close</button></h4>
  ${up.length?up.slice(0,60).map(k=>trRow('up',k,[f.id],0)).join(''):'<span class="why">Nothing calls it'+(TR.tests?'':' (callers from tests are hidden)')+'.</span>'}</div>
  <div><h4>Calls (${down.length}) <button class="btn" data-trx="down">Open 3 levels</button> <button class="btn" data-trx="downc">Close</button></h4>
  ${down.length?down.slice(0,60).map(k=>trRow('down',k,[f.id],0)).join(''):'<span class="why">It calls nothing that was found.</span>'}</div></div>`;
 if(TR.n>1500)h+='<p class="note">Showing the first 1500 rows. Close some branches or follow one function at a time.</p>';
 b.innerHTML=h;$('#trback').disabled=!TR.hist.length;}
function trFocus(id,push){if(push!==false&&TR.id!=null&&TR.id!==id)TR.hist.push(TR.id);TR.id=id;TR.open=new Set();
 for(const dir of ['up','down'])for(const k of trKids(dir,id))TR.open.add(dir+':'+[id,k.id].join('>'));
 HS.set('t',String(id));saveHash();$('#trhits').innerHTML='';trRender();}
function traceFn(id){view('trace');trFocus(id);}
function trSearch(){const q=$('#trq').value.trim().toLowerCase();const out=$('#trhits');if(!q){out.innerHTML='';return [];}
 const hits=N.filter(f=>f.kind==='function'&&(f.qual.toLowerCase().includes(q)||f.path.toLowerCase().includes(q))).sort((a,b)=>
  (a.status==='non_production')-(b.status==='non_production')||(a.name.toLowerCase()!==q)-(b.name.toLowerCase()!==q)||a.qual.length-b.qual.length).slice(0,25);
 out.innerHTML=hits.length?hits.map(f=>`<div><a data-tf="${f.id}" tabindex="0" style="cursor:pointer;color:var(--accent)">${esc(f.qual)}</a> ${pill(f.status)} <span class="why">${esc(where(f))}</span></div>`).join(''):'<span class="why">No function matches.</span>';return hits;}
$('#trq').oninput=trSearch;$('#trq').onkeydown=e=>{if(e.key==='Enter'){const h=trSearch();if(h.length)trFocus(h[0].id);}};
$('#trtests').onchange=e=>{TR.tests=e.target.checked;trRender();};$('#trloaded').onchange=e=>{TR.loaded=e.target.checked;trRender();};
$('#trback').onclick=()=>{if(TR.hist.length)trFocus(TR.hist.pop(),false);};
$('#trview').addEventListener('click',ev=>{const tf=ev.target.closest('[data-tf]');if(tf){trFocus(+tf.dataset.tf);return;}
 const tk=ev.target.closest('[data-tk]');if(tk&&!tk.disabled){const k=tk.dataset.tk;TR.open.has(k)?TR.open.delete(k):TR.open.add(k);trRender();return;}
 const x=ev.target.closest('[data-trx]');if(x){const v=x.dataset.trx;if(v.endsWith('c')){const d=v.slice(0,-1);TR.open=new Set([...TR.open].filter(y=>!y.startsWith(d+':')));}else trOpenAll(v,TR.id,3);trRender();return;}
 const gb=ev.target.closest('[data-graph]');if(gb){showGraph('local',+gb.dataset.graph);return;}const g=ev.target.closest('[data-go]');if(g){view('list');go(+g.dataset.go);}});
$('#trview').addEventListener('keydown',ev=>{if(ev.key==='Enter'&&ev.target.matches('a[data-tf]')){ev.preventDefault();ev.target.click();}});
function view(v){for(const [id,k] of [['#tlist','list'],['#tgraph','graph'],['#tsurf','surface'],['#thot','hot'],['#ttrace','trace']])$(id).setAttribute('aria-pressed',v===k);
 document.querySelector('main').hidden=v!=='list';$('#gview').hidden=v!=='graph';$('#sfview').hidden=v!=='surface';$('#hsview').hidden=v!=='hot';$('#trview').hidden=v!=='trace';if(v==='trace'&&TR.id==null){const t0=+HS.get('t');if(HS.get('t')&&N[t0])trFocus(t0,false);}
 if(v!=='graph')cancelAnimationFrame(GV.raf);if(v==='surface')surface();if(v==='hot')hotspots();}
$('#ttrace').onclick=()=>view('trace');$('#tsurf').onclick=()=>view('surface');$('#thot').onclick=()=>view('hot');
if(!EP.length)$('#tsurf').hidden=true;
addEventListener('resize',()=>{if(!$('#gview').hidden)draw();});
})();
</script></body></html>"""


# --------------------------------------------------------------------------------------------------------------
# Command line
# --------------------------------------------------------------------------------------------------------------
class Progress:
    def __init__(self, quiet: bool):
        self.on = not quiet and sys.stderr.isatty()
        self.last = 0.0

    def __call__(self, stage: str, i: int, n: int, item: str) -> None:
        if not self.on or (time.time() - self.last < 0.1 and i != n):
            return
        self.last = time.time()
        sys.stderr.write(f"\r\x1b[K{stage} {i}/{n} {item[-60:]}")
        sys.stderr.flush()

    def done(self) -> None:
        if self.on:
            sys.stderr.write("\r\x1b[K")


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="reachmap", description=__doc__.split("\n\n")[0])
    p.add_argument("path", help="project folder")
    p.add_argument("--out", help="report folder (default <data-dir>/runs/<timestamp>)")
    p.add_argument("--data-dir", default=default_data_dir(),
                   help="where reports go (default: reachmap-data next to the program folder, or $REACHMAP_DATA_DIR)")
    p.add_argument("--formats", default="html,json", help="comma list of html,json,sarif,openapi (default html,json)")
    p.add_argument("--fail-on", default="", metavar="RULES",
                   help="exit code 1 when one of these rules hits: " + ",".join(RULES) + " or all (for CI)")
    p.add_argument("--config", metavar="FILE",
                   help="extra entry points, framework code and names to ignore (default: .reachmap in the project, "
                        "only with --trust-project-config)")
    p.add_argument("--trust-project-config", action="store_true", help="use <path>/.reachmap if present")
    p.add_argument("--coderaster", metavar="JSON", help="mark findings from a CodeRaster report (coderaster.json)")
    p.add_argument("--exclude", action="append", default=[], metavar="GLOB", help="skip matching files (repeatable)")
    p.add_argument("--include-dir", action="append", default=[], metavar="NAME",
                   help="read a folder that is skipped by default (repeatable, e.g. vendor)")
    p.add_argument("--max-file-kb", type=int, default=MAX_BYTES // 1024, help="skip larger files (default 1024)")
    p.add_argument("--baseline", default="auto", metavar="FILE|auto|none",
                   help="earlier reachmap.json to compare with (default: the newest run of the same folder)")
    p.add_argument("--no-git", action="store_true", help="do not read file ages from git")
    p.add_argument("--trace", metavar="NAME", help="follow a function in the terminal: callers up to the entry points and "
                   "what it calls (name, qualified name or part of a path)")
    p.add_argument("--trace-depth", type=int, default=3, help="levels for --trace (default 3)")
    p.add_argument("--source", choices=("production", "all", "none"), default="production",
                   help="source code in the HTML report for the code view: production code (default), all files, or none "
                        "(smaller report)")
    p.add_argument("--quiet", "-q", action="store_true", help="no progress, only the summary")
    p.add_argument("--version", action="version", version=f"reachmap {VERSION}")
    a = p.parse_args(argv)
    if not os.path.isdir(a.path):
        print(f"not a folder: {a.path}", file=sys.stderr)
        return 2
    formats = [x.strip() for x in a.formats.split(",") if x.strip()]
    fail_on = [x.strip() for x in a.fail_on.split(",") if x.strip()]
    if "all" in fail_on:
        fail_on = list(RULES)
    if any(x not in RULES for x in fail_on):
        print("--fail-on takes: " + ", ".join(RULES) + ", all", file=sys.stderr)
        return 2
    if not formats or any(x not in ("html", "json", "sarif", "openapi") for x in formats):
        print("--formats takes html, json, sarif and/or openapi", file=sys.stderr)
        return 2
    cfg = Config()
    cfg_path = a.config or (os.path.join(a.path, ".reachmap") if a.trust_project_config else None)
    if cfg_path:
        try:
            cfg = load_config(cfg_path)
        except (OSError, ValueError) as exc:
            print(f"config: {exc}", file=sys.stderr)
            return 2
    elif os.path.isfile(os.path.join(a.path, ".reachmap")):
        print(f"note: ignoring {os.path.join(a.path, '.reachmap')} (use --trust-project-config or --config)",
              file=sys.stderr)
    t0 = time.time()
    root = os.path.abspath(a.path)
    skipped: dict = {}
    prog = Progress(a.quiet)
    out = a.out or os.path.join(a.data_dir, "runs", dt.datetime.now().strftime("%Y%m%d-%H%M%S"))
    files = list(discover(root, tuple(a.exclude), frozenset(a.include_dir), a.max_file_kb * 1024, skipped,
                          (out, a.data_dir)))
    if not any(f.kind == "code" for f in files):
        print(f"no source files found under {a.path}", file=sys.stderr)
        return 2
    g, stats = build(files, cfg, prog)
    prog.done()
    meta = {"generated": dt.datetime.now().strftime("%Y-%m-%d %H:%M"), "seconds": round(time.time() - t0, 1),
            "skipped": skipped, "minified": stats.get("minified", 0), "config": cfg_path or ""}
    if a.coderaster:
        try:
            meta["findings"] = attach_findings(g, a.coderaster)
        except (OSError, ValueError, KeyError) as exc:
            print(f"--coderaster: {exc}", file=sys.stderr)
            return 2
    surface = analyse_surface(g, files)
    git = attach_git(g, git_info(root)) if not a.no_git else {}
    meta["summary"] = summarize(g)
    if meta.get("findings"):
        meta["summary"]["findings"] = meta["findings"]
    doc = to_dict(g, root, meta)
    doc.update(surface)
    doc["hotspots"] = hotspots(g)
    doc["git"] = git
    meta["summary"]["surface"] = surface_summary(doc)
    meta["summary"]["git"] = git
    meta["summary"]["hotspots"] = [{"qual": g.nodes[h["id"]].qual, "where": f"{g.nodes[h['id']].path}:{g.nodes[h['id']].line}",
                                    "via_entries": h["via_entries"]} for h in doc["hotspots"][:10]]
    prev = None
    if a.baseline == "auto":
        prev = find_previous(os.path.join(a.data_dir, "runs"), root, out)
    elif a.baseline != "none":
        prev = a.baseline
    if prev:
        try:
            doc["diff"] = meta["summary"]["diff"] = compare_runs(doc, prev)
        except (OSError, ValueError, KeyError, TypeError) as exc:
            print(f"baseline {prev} could not be read: {exc}", file=sys.stderr)
            if a.baseline not in ("auto", "none"):
                return 2
    if a.trace:
        print(render_trace(doc, a.trace, a.trace_depth))
        return 0
    sources, source_info = pack_sources(files, a.source) if "html" in formats else ({}, {"mode": "none"})
    paths = write_reports(doc, out, formats, sources, source_info)
    color = sys.stdout.isatty() and not os.environ.get("NO_COLOR")
    print(render_terminal(meta["summary"], root, paths, time.time() - t0, color))
    if fail_on:
        hit = [h for h in rule_hits(doc) if h["rule"] in fail_on]
        for h in hit[:20]:
            print(f"  [{RULES[h['rule']][0]}] {h['path']}:{h['line']}  {h['text']}", file=sys.stderr)
        if len(hit) > 20:
            print(f"  ... and {len(hit) - 20} more", file=sys.stderr)
        if hit:
            print(f"--fail-on: {len(hit)} hit(s)", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
