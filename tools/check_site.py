"""Check the static site's document structure and local navigation."""
import json
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "site"
BASE = "https://tsuda-naoaki.github.io/lctr/"


class Document(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids = set()
        self.links = []
        self.meta = {}
        self.canonical = []
        self.alternates = {}
        self.h1 = 0
        self.lang = None
        self.schema = []
        self.script = None
        self.analytics_scripts = 0
        self.analytics_body = None

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if "id" in a:
            assert a["id"] not in self.ids, ("duplicate id", a["id"])
            self.ids.add(a["id"])
        if tag == "html":
            self.lang = a.get("lang")
        if tag == "h1":
            self.h1 += 1
        if tag == "meta" and "name" in a:
            self.meta[a["name"]] = a.get("content", "")
        if tag == "link" and a.get("rel") == "canonical":
            self.canonical.append(a["href"])
        if tag == "link" and a.get("rel") == "alternate":
            self.alternates[a.get("hreflang")] = a["href"]
        if tag in ("a", "link") and "href" in a:
            self.links.append(a["href"])
        if tag == "script":
            if a.get("type") == "application/ld+json":
                self.script = ""
            else:
                assert set(a) == {"type", "src", "data-cf-beacon"}, "Unexpected script attributes"
                assert a["type"] == "module", "Unexpected executable script"
                assert a["src"] == "https://static.cloudflareinsights.com/beacon.min.js", "Unexpected script source"
                assert json.loads(a["data-cf-beacon"]) == {"token": "c43e570c795049c6a075a033211dd8c2"}, "Unexpected analytics site"
                self.analytics_scripts += 1
                self.analytics_body = ""

    def handle_data(self, text):
        if self.script is not None:
            self.script += text
        elif self.analytics_body is not None:
            self.analytics_body += text

    def handle_endtag(self, tag):
        if tag == "script" and self.script is not None:
            self.schema.append(json.loads(self.script))
            self.script = None
        elif tag == "script" and self.analytics_body is not None:
            assert not self.analytics_body.strip(), "Unexpected inline script"
            self.analytics_body = None


docs = {}
for path in sorted(SITE.rglob("*.html")):
    doc = Document()
    doc.feed(path.read_text())
    assert doc.lang in ("ja", "en"), path
    assert doc.h1 == 1, (path, "expected one main heading")
    assert len(doc.canonical) == 1 and doc.canonical[0].startswith(BASE), path
    assert doc.meta.get("viewport"), path
    assert doc.meta.get("description"), path
    assert doc.analytics_scripts == 1, (path, "expected one Cloudflare analytics script")
    docs[path.resolve()] = doc

for path, doc in docs.items():
    for link in doc.links:
        parsed = urlsplit(link)
        if parsed.scheme == "mailto":
            assert "@" in parsed.path and not parsed.netloc, (path, link)
            continue
        if parsed.scheme or parsed.netloc:
            assert parsed.scheme == "https", (path, link)
            continue
        target = (path.parent / unquote(parsed.path)).resolve() if parsed.path else path
        assert target.is_relative_to(SITE.resolve()), (path, link)
        if target.is_dir():
            target /= "index.html"
        assert target.is_file(), ("broken local link", path, link)
        if parsed.fragment:
            assert target in docs and parsed.fragment in docs[target].ids, (path, link)

for filename, lang in (("index.html", "ja"), ("en.html", "en")):
    doc = docs[(SITE / filename).resolve()]
    assert doc.lang == lang
    assert set(doc.alternates) == {"ja", "en", "x-default"}
    assert doc.alternates["ja"] == BASE
    assert doc.alternates["en"] == BASE + "en.html"
    assert len(doc.schema) == 1
    article = doc.schema[0]
    assert article["@type"] == "ScholarlyArticle"
    assert article["inLanguage"] == lang
    assert article["headline"] == doc.meta["citation_title"]
    assert article["author"]["name"] == "Naoaki Tsuda"
    assert len(article["abstract"].split("\n\n")) == 11
    assert doc.meta["robots"] == "index,follow"

sitemap = ET.parse(SITE / "sitemap.xml")
urls = [item.text for item in sitemap.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}loc")]
assert set(urls) == {doc.canonical[0] for doc in docs.values()}
print(json.dumps({"status": "pass", "html_documents": len(docs), "local_links_checked": sum(len(d.links) for d in docs.values()), "abstract_paragraphs": {"ja": 11, "en": 11}, "sitemap_urls": len(urls), "analytics_scripts": sum(d.analytics_scripts for d in docs.values())}))
