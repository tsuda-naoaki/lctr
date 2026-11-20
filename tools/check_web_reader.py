"""Validate the static v1.0.1 reader separately from the site landing pages."""
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


CHAPTERS = tuple(f"S{n}.html" for n in range(1, 9))
AUDITS = tuple(f"Sx3.SS2.SSS{n}.html" for n in range(1, 73))
CANONICAL = ("index.html", *CHAPTERS, *AUDITS)
SEARCH = "formula-search.html"
SHARED = ("contents.html", "supplement.html", "supplement-s1.html",
          "supplement-s2.html", "supplement-s3.html", "references.html",
          "verification-assets.html", SEARCH)
FORMULAS = {"ja": 20119, "en": 20012}
BASE = "https://tsuda-naoaki.github.io/lctr/full-text/"
INDEXABLE = {*CHAPTERS, *AUDITS, *SHARED} - {SEARCH}
CARD = re.compile(r'<li id="source-(\d{2})" data-source-number="(\d+)" class="source-card">'
                  r'\s*<h3><a href="([^"]+)">.*?</h3>.*?'
                  r'<p class="audit-location"><a href="([^"]+)">([^<]+)</a></p>.*?</li>', re.S)


class ReaderPage(HTMLParser):
    def __init__(self, path):
        super().__init__(convert_charrefs=True)
        self.path = path
        self.ids, self.links = set(), []
        self.lang, self.robots = "", set()
        self.canonical, self.alternates = [], []
        self.description = ""
        self.math = self.annotations = self.figures = 0
        self.feed(path.read_text(encoding="utf-8"))
        self.close()

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        ident = a.get("id")
        if ident:
            assert ident not in self.ids, (self.path, "duplicate reader ID", ident)
            self.ids.add(ident)
        if tag == "html":
            self.lang = a.get("lang")
        if tag == "meta" and a.get("name") == "robots":
            self.robots.update(a.get("content", "").replace(" ", "").split(","))
        if tag == "meta" and a.get("name") == "description":
            self.description = a.get("content", "")
        if tag == "link" and a.get("rel") == "canonical":
            self.canonical.append(a.get("href"))
        if tag == "link" and a.get("rel") == "alternate":
            self.alternates.append((a.get("hreflang"), a.get("href")))
        if tag == "math":
            self.math += 1
        if tag == "annotation" and a.get("encoding") == "application/x-tex":
            self.annotations += 1
        if tag == "img" and a.get("class") == "fixed-figure-art":
            self.figures += 1
        assert not any(key.startswith("on") for key in a), (self.path, "inline event handler")
        assert tag != "merror" and a.get("mathcolor") != "red", (self.path, "invalid math rendering")
        href = a.get("href") if tag in {"a", "link"} else a.get("src") if tag in {"script", "img"} else None
        if href:
            self.links.append(href)


def check_web_reader(site, shell_ids, reader_urls):
    site = site.resolve()
    root = site / "full-text"
    pages = {p: ReaderPage(p) for p in sorted(root.rglob("*.html"))}
    ids = {**shell_ids, **{p: doc.ids for p, doc in pages.items()}}

    def local_target(at, url):
        parts = urlsplit(url)
        if parts.scheme or parts.netloc:
            assert parts.scheme in {"https", "mailto", "data"}, (at, "unexpected link scheme")
            return False
        target = (at.parent / unquote(parts.path)).resolve() if parts.path else at
        if target.is_dir():
            target = target / "index.html"
        assert target.is_relative_to(site) and target.is_file(), (at, "missing reader link", url)
        if parts.fragment and target.suffix == ".html":
            assert unquote(parts.fragment) in ids.get(target, ()), (at, "missing reader anchor", url)
        return True

    report = {}
    observed_urls = set()
    for lang in ("ja", "en"):
        folder = root / lang
        docs = {p.name: doc for p, doc in pages.items() if p.parent == folder}
        assert len(docs) == 127 and set((*CANONICAL, *SHARED)) <= docs.keys(), (lang, "reader page coverage")
        assert all(d.lang == lang for d in docs.values()), (lang, "reader language")
        if reader_urls:
            for name, d in docs.items():
                if name in INDEXABLE:
                    url = f"{BASE}{lang}/{name}"
                    assert d.robots == {"index","follow"} and d.canonical == [url] and d.description, (lang, name)
                    assert d.alternates == [(alt, f"{BASE}{alt}/{name}") for alt in ("ja","en")], (lang, name)
                    observed_urls.add(url)
                elif name == "index.html":
                    assert d.robots == {"noindex","follow"} and d.canonical == [f"{BASE}{lang}/contents.html"]
                else:
                    assert d.robots == {"noindex","follow"} and not d.canonical and not d.alternates
        else:
            assert all("noindex" in d.robots for d in docs.values()), (lang, "private preview must not be indexed")
        math = sum(docs[n].math for n in CANONICAL)
        tex = sum(docs[n].annotations for n in CANONICAL)
        figures = sum(docs[n].figures for n in CANONICAL)
        assert math == tex == FORMULAS[lang] and figures == 32, (lang, math, tex, figures)

        listing = site / "sources" / ("index.html" if lang == "ja" else "en.html")
        source_html = listing.read_text(encoding="utf-8")
        cards = CARD.findall(source_html)
        assert len(cards) == 72 and 'class="source-full-text"' not in source_html
        other = "en" if lang == "ja" else "ja"
        for n, (card, number, title, supplement, label) in enumerate(cards, 1):
            expected = f"../full-text/{lang}/{AUDITS[n-1]}"
            assert (card, number, title, supplement) == (f"{n:02}", str(n), expected, expected)
            assert label == (f"補遺：資料 {n}" if lang == "ja" else f"Supplement: source {n}")
            assert f'href="#source-{n:02}"' in source_html
            page = folder / AUDITS[n-1]
            assert f'../{other}/{AUDITS[n-1]}' in docs[page.name].links
            assert f'ltx_tag_subsubsection">S.2.{n} </span>' in page.read_text(encoding="utf-8")
            assert local_target(listing, title) and local_target(listing, supplement)

        data = (folder / "formula-search-data.js").read_text(encoding="utf-8")
        rows = json.loads(data.split("globalThis.lctrPrivateFormulaData=", 1)[1].strip().removesuffix(";"))
        assert rows["language"] == lang and len(rows["rows"]) == math
        for row in rows["rows"]:
            assert row[-1] is None and all(local_target(folder / SEARCH, href) for href in row[:2])
        links = sum(local_target(doc.path, href) for doc in docs.values() for href in doc.links)
        report[lang] = {"html_pages": len(docs), "source_routes": len(cards), "math": math,
                        "figure_assets": figures, "local_links": links}
    assert len(pages) == sum(row["html_pages"] for row in report.values())
    assert observed_urls == reader_urls
    return report
