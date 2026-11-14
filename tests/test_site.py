import json
import tempfile
import unittest
from pathlib import Path
from xml.etree import ElementTree

from server.site import text, write_site

ROOT = Path(__file__).resolve().parents[1]


class SiteTests(unittest.TestCase):
    def test_static_pages_and_lazy_catalog(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "fonts").mkdir()
            (root / "node_modules/mathjax-full/es5/output/chtml/fonts/woff-v2").mkdir(
                parents=True
            )
            (root / "vendor").mkdir()
            (root / "vendor/fuse-7.5.0.min.cjs").write_text("")
            for name in ("logo.png", "mini-logo.png"):
                (root / name).write_bytes(b"")
            (root / "template.html").write_text(
                (ROOT / "server/template.html").read_text()
            )
            theorem = {
                "module": "LongTails.Theorems.Nested.Example",
                "statement": "Convergence spec budget",
                "formulaHtml": "<p>Budget: 42 calls.</p>",
                "referencesHtml": "",
            }
            setup = {
                "id": "Example",
                "filename": "Example.lean",
                "title": "Example.lean",
                "descriptionHtml": "<h2>Convex &amp; smooth</h2><p>Assumptions here.</p>",
                "theorems": [theorem],
                "contribution": 3,
            }
            rendered = {
                "css": "",
                "data": {
                    "repository_url": "https://github.com/owner/project",
                    "setups": [setup],
                    "template": "",
                    "nightlyHistory": [],
                },
            }
            target = write_site(root, rendered, "", "https://example.com/longtails/")
            homepage = target.read_text()
            self.assertIn('href="setups/Example/"', homepage)
            self.assertNotIn("__", homepage)
            result = (target.parent / "results/Nested/Example/index.html").read_text()
            self.assertIn("Assumptions here.", result)
            self.assertIn("42 calls", result)
            self.assertIn("not a proof of novelty", result)
            self.assertIn('href="../../../setups/Example/"', result)
            self.assertIn('href="../../../assets/site.css"', result)
            self.assertIn(
                'href="https://example.com/longtails/results/Nested/Example/"', result
            )
            catalog = json.loads((target.parent / "assets/catalog.json").read_text())
            self.assertNotIn("theorems", catalog["setups"][0])
            self.assertIn("42 calls", catalog["setups"][0]["searchText"])
            urls = ElementTree.parse(target.parent / "sitemap.xml").findall(".//{*}loc")
            self.assertEqual(len(urls), 3)
            self.assertTrue(
                all(
                    url.text.startswith("https://example.com/longtails/")
                    for url in urls
                )
            )
            self.assertTrue((target.parent / "data/Example.json").exists())
            rendered["data"]["setups"] = []
            write_site(root, rendered, "")
            self.assertFalse((target.parent / "data/Example.json").exists())
            self.assertFalse(
                (target.parent / "results/Nested/Example/index.html").exists()
            )

    def test_math_search_text(self):
        self.assertEqual(
            text(
                '<span data-tex="x &lt; y"><mjx-container>duplicate</mjx-container></span>'
            ),
            "x < y",
        )


if __name__ == "__main__":
    unittest.main()
