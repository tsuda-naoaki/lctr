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
    def __init__(self, allow_create_time=False):
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
        self.allow_create_time = allow_create_time
        self.create_time_scripts = 0
        self.navs = []
        self.active_nav = None
        self.current_links = []
        self.details_depth = 0
        self.math_elements = 0
        self.math_inside_details = 0

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if "id" in a:
            assert a["id"] not in self.ids, ("duplicate id", a["id"])
            self.ids.add(a["id"])
        if tag == "html":
            self.lang = a.get("lang")
        if tag == "h1":
            self.h1 += 1
        if tag == "nav":
            assert self.active_nav is None, "Navigation landmarks must not be nested"
            self.active_nav = {"attrs": a, "links": []}
            self.navs.append(self.active_nav)
        if tag == "a":
            if self.active_nav is not None:
                self.active_nav["links"].append(a)
            if "aria-current" in a:
                self.current_links.append(a)
        if tag == "details":
            self.details_depth += 1
        if tag == "math":
            assert a.get("xmlns") == "http://www.w3.org/1998/Math/MathML", "Native MathML namespace required"
            self.math_elements += 1
            if self.details_depth:
                self.math_inside_details += 1
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
            elif self.allow_create_time and a.get("src") == "../assets/create-time.js":
                assert set(a) == {"defer", "src"}, "Unexpected create-time script attributes"
                self.create_time_scripts += 1
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
        if tag == "nav":
            self.active_nav = None
        if tag == "details":
            self.details_depth -= 1
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
    doc = Document(allow_create_time=path.parent == SITE / "create-time")
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


def local_target(path, link):
    parsed = urlsplit(link)
    target = (path.parent / unquote(parsed.path)).resolve() if parsed.path else path
    if target.is_dir():
        target /= "index.html"
    return target, unquote(parsed.fragment)


for path, doc in docs.items():
    for link in doc.links:
        parsed = urlsplit(link)
        if parsed.scheme == "mailto":
            assert "@" in parsed.path and not parsed.netloc, (path, link)
            continue
        if parsed.scheme or parsed.netloc:
            assert parsed.scheme == "https", (path, link)
            continue
        target, fragment = local_target(path, link)
        assert target.is_relative_to(SITE.resolve()), (path, link)
        assert target.is_file(), ("broken local link", path, link)
        if fragment:
            if target.suffix == ".pdf":
                assert re.fullmatch(r"page=[1-9][0-9]*", fragment), (path, "Invalid PDF page link", link)
            else:
                assert target in docs and fragment in docs[target].ids, (path, link)
    for link in doc.current_links:
        assert link.get("aria-current") == "page", (path, "Unexpected current-link value")
        assert "href" in link and local_target(path, link["href"]) == (path, ""), (path, "aria-current must identify the exact current page", link)

    # Every page provides the same visible routes; section anchors never mark a page current.
    filename = "en.html" if doc.lang == "en" else "index.html"
    home = (SITE / filename).resolve()
    expected_nav = [
        (home, ""),
        ((SITE / "create-time" / filename).resolve(), ""),
        ((SITE / "why-time-emergence-failed" / filename).resolve(), ""),
        ((SITE / "time-mysteries" / filename).resolve(), ""),
        ((SITE / "sources" / filename).resolve(), ""),
        (home, "figures"),
        (home, "verification"),
        ((SITE / "verification/law-candidate/index.html").resolve(), ""),
        (home, "materials-title"),
        ((SITE / "world-challenge" / filename).resolve(), ""),
    ]
    for class_name, expected in (("site-nav", expected_nav), ("site-footer-nav", [expected_nav[n] for n in (0, 1, 2, 3, 4, 7, 9)])):
        navs = [nav for nav in doc.navs if class_name in nav["attrs"].get("class", "").split()]
        assert len(navs) == 1, (path, "Expected one navigation landmark", class_name)
        nav = navs[0]
        assert nav["attrs"].get("aria-label"), (path, "Navigation needs an accessible name", class_name)
        assert "hidden" not in nav["attrs"], (path, "Site navigation must remain visible")
        assert all("href" in a and "hidden" not in a for a in nav["links"]), (path, class_name)
        assert [local_target(path, a["href"]) for a in nav["links"]] == expected, (path, "Incomplete or misordered site navigation", class_name)
        current = [a for a in nav["links"] if a.get("aria-current") == "page"]
        assert len(current) == 1, (path, "Navigation must mark the current page", class_name)
    assert re.search(r'<header class="masthead">.*?</header>\s*<nav class="site-nav"', path.read_text(), re.S), (path, "Site navigation must immediately follow the masthead")

# The bilingual page pairs point reciprocally to their own translations.
for directory in ("", "time-mysteries/", "sources/", "create-time/", "why-time-emergence-failed/", "world-challenge/"):
    expected_alternates = {"ja": BASE + directory, "en": BASE + directory + "en.html", "x-default": BASE + directory}
    for filename, lang in (("index.html", "ja"), ("en.html", "en")):
        path = (SITE / directory / filename).resolve()
        doc = docs[path]
        assert doc.lang == lang and doc.alternates == expected_alternates, (path, "Language alternates must be reciprocal")
        assert doc.canonical == [expected_alternates[lang]], (path, "Canonical URL must identify this language")
        language_navs = [nav for nav in doc.navs if nav["attrs"].get("aria-label") == "Language"]
        assert len(language_navs) == 1, (path, "Expected one language navigation")
        assert {local_target(path, a["href"]) for a in language_navs[0]["links"]} == {
            ((SITE / directory / "index.html").resolve(), ""),
            ((SITE / directory / "en.html").resolve(), ""),
        }, (path, "Visible language links must identify the paired translations")

for filename in ("index.html", "en.html"):
    path = (SITE / "create-time" / filename).resolve()
    doc = docs[path]
    assert doc.create_time_scripts == 0, (path, "Superseded comparison-only demonstration must not be loaded")
    assert doc.math_elements > 0, (path, "Educational equations must use native MathML")
    assert doc.math_inside_details == 0, (path, "Educational equations must be visible without expanding details")
    assert not any(name.startswith("citation_") for name in doc.meta), (path, "Educational pages must not claim paper citation metadata")
    assert {"time-representation", "continuum"} <= doc.ids, (path, "Educational cross-link anchors are required")

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
        expected_size = (int(attrs["width"]), int(attrs["height"]))
        if image.suffix.lower() == ".svg":
            vector = ET.parse(image).getroot()
            assert vector.tag == "{http://www.w3.org/2000/svg}svg"
            assert tuple(float(vector.get(k)) for k in ("width", "height")) == expected_size
            assert tuple(map(float, vector.get("viewBox").split())) == (0, 0, *expected_size)
            assert vector.find("{http://www.w3.org/2000/svg}title") is not None
            assert vector.find("{http://www.w3.org/2000/svg}desc") is not None
            for node in vector.iter():
                assert node.tag.rsplit("}", 1)[-1] not in {"script", "foreignObject"}
                for key, value in node.attrib.items():
                    assert not key.lower().startswith("on")
                    if key.rsplit("}", 1)[-1] in {"href", "src"}:
                        assert value.startswith("#"), "Diagram must be self-contained"
        else:
            header = image.read_bytes()[:24]
            assert header[:8] == b"\x89PNG\r\n\x1a\n"
            assert struct.unpack(">II", header[16:24]) == expected_size
        images_checked += 1
assert images_checked == 14

sitemap = ET.parse(SITE / "sitemap.xml")
urls = [item.text for item in sitemap.findall(".//{http://www.sitemaps.org/schemas/sitemap/0.9}loc")]
assert set(urls) == {doc.canonical[0] for doc in docs.values()}
print(json.dumps({"status": "pass", "html_documents": len(docs), "local_links_checked": sum(len(d.links) for d in docs.values()), "abstract_paragraphs": {"ja": 11, "en": 11}, "sitemap_urls": len(urls), "source_entries_per_language": 72, "figure_images": images_checked, "cloudflare_scripts": sum(d.analytics_scripts for d in docs.values()), "ga4_loaders": sum(d.ga4_scripts for d in docs.values())}))
