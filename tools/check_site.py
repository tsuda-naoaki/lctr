"""Check the static site's document structure and local navigation."""
import json
import re
import struct
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
        self.ga4_scripts = 0
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
            elif a.get("src") in {"assets/analytics.js", "../assets/analytics.js", "../../assets/analytics.js"}:
                assert set(a) == {"defer", "src"}, "Unexpected GA4 loader attributes"
                self.ga4_scripts += 1
                self.links.append(a["src"])
                self.analytics_body = ""
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


verification = SITE / "googlef9fa91ecc9252ce3.html"
assert verification.is_file() and not verification.is_symlink(), verification
assert verification.read_bytes() == b"google-site-verification: googlef9fa91ecc9252ce3.html", verification

docs = {}
for path in sorted(SITE.rglob("*.html")):
    if path == verification:
        continue
    doc = Document()
    doc.feed(path.read_text())
    assert doc.lang in ("ja", "en"), path
    assert doc.h1 == 1, (path, "expected one main heading")
    assert len(doc.canonical) == 1 and doc.canonical[0].startswith(BASE), path
    assert doc.meta.get("viewport"), path
    assert doc.meta.get("description"), path
    assert doc.analytics_scripts == 1, (path, "expected one Cloudflare analytics script")
    assert doc.ga4_scripts == 1, (path, "expected one consent-controlled GA4 loader")
    assert {"analytics-privacy", "analytics-panel"} <= doc.ids, path
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
    assert re.fullmatch(r"\d{4}(?:/\d{2}/\d{2})?", doc.meta["citation_publication_date"])
    pdf_name = "lctr_main_jp.pdf" if lang == "ja" else "lctr_main_en.pdf"
    assert doc.meta["citation_pdf_url"] == BASE + pdf_name
    pdf = SITE / pdf_name
    assert pdf.is_file() and 0 < pdf.stat().st_size < 5_000_000
    assert pdf.read_bytes().startswith(b"%PDF-")
    assert pdf_name in doc.links, "The main PDF must also be visibly linked"
    assert article["encoding"]["contentUrl"] == doc.meta["citation_pdf_url"]
    assert article["encoding"]["inLanguage"] == lang


# Corpus numbering, visible metadata, and image dimensions must agree.
for filename in ("index.html", "en.html"):
    landing = (SITE / filename).read_text()
    visible_terms = [__import__("html").unescape(x) for x in re.findall(r'<li class="keyword">(.*?)</li>', landing)]
    assert visible_terms == docs[(SITE / filename).resolve()].schema[0]["keywords"]
    assert len(visible_terms) == len(set(visible_terms)), "Duplicate keyword"
    source = SITE / "sources" / filename
    text = source.read_text()
    numbers = [int(x) for x in re.findall(r'data-source-number="(\d+)"', text)]
    assert numbers == list(range(1, 73)), "Source numbering must be complete and ordered"
    items = docs[source.resolve()].schema[0]["mainEntity"]
    assert items["numberOfItems"] == len(numbers)
    assert [x["position"] for x in items["itemListElement"]] == numbers
    assert all(x["url"].endswith(f'#source-{n:02}') for n, x in zip(numbers, items["itemListElement"]))

images_checked = 0
for path in docs:
    for tag in re.findall(r'<img\s+[^>]+>', path.read_text()):
        attrs = dict(re.findall(r'([\w-]+)="([^"]*)"', tag))
        assert attrs.get("alt", "").strip(), (path, "Missing image description")
        image = (path.parent / attrs["src"]).resolve()
        assert image.is_relative_to(SITE.resolve()) and image.is_file()
        header = image.read_bytes()[:24]
        assert header[:8] == b"\x89PNG\r\n\x1a\n"
        assert struct.unpack(">II", header[16:24]) == (int(attrs["width"]), int(attrs["height"]))
        images_checked += 1
assert images_checked == 8

sitemap = ET.parse(SITE / "sitemap.xml")
urls = [item.text for item in sitemap.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}loc")]
assert set(urls) == {doc.canonical[0] for doc in docs.values()}
print(json.dumps({"status": "pass", "html_documents": len(docs), "local_links_checked": sum(len(d.links) for d in docs.values()), "abstract_paragraphs": {"ja": 11, "en": 11}, "sitemap_urls": len(urls), "source_entries_per_language": 72, "figure_images": images_checked, "cloudflare_scripts": sum(d.analytics_scripts for d in docs.values()), "ga4_loaders": sum(d.ga4_scripts for d in docs.values())}))
