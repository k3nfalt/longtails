import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from server.site import search_text, write_site
from server.Theorems.create_theorem_description import extract_theorems

ROOT = Path(__file__).resolve().parents[1]


class TheoremDescriptionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        names = ("DistributedBatchedSgd", "GdConvex")
        subprocess.run(
            [
                "lake",
                "build",
                "BudgetLatex",
                *[f"LongTails.Theorems.{n}" for n in names],
            ],
            cwd=ROOT,
            check=True,
            capture_output=True,
        )
        cls.rows = {
            row["module"].split(".")[-1]: row
            for row in extract_theorems(
                [ROOT / f"LongTails/Theorems/{name}.lean" for name in names]
            )
        }

    def test_scalar_time_and_oracle_call_budgets(self):
        timed = self.rows["DistributedBatchedSgd"]
        self.assertEqual(timed["kind"], "timed")
        self.assertEqual(timed["budgets"], [timed["budget"]])
        self.assertNotIn("oracle", timed["budget"])
        latex = timed["budget"]["latex"]
        self.assertIn(r"\inf", latex)
        self.assertIn(r"\sum", latex)
        self.assertIn("64", latex)
        self.assertNotIn("clockBits", latex)
        ordinary = self.rows["GdConvex"]
        self.assertEqual(ordinary["kind"], "upper")
        self.assertEqual(ordinary["budget"]["oracle"], 0)

    def test_timed_website(self):
        timed = self.rows["DistributedBatchedSgd"].copy()
        self.assertIn("Elapsed-time upper bound", search_text(timed))
        legacy = {key: value for key, value in timed.items() if key != "kind"}
        self.assertIn("Elapsed-time upper bound", search_text(legacy))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path in (
                "fonts",
                "node_modules/mathjax-full/es5/output/chtml/fonts/woff-v2",
                "vendor",
            ):
                (root / path).mkdir(parents=True)
            for path in ("logo.png", "mini-logo.png", "vendor/fuse-7.5.0.min.cjs"):
                (root / path).touch()
            shutil.copyfile(ROOT / "server/template.html", root / "template.html")
            data = {
                "repository_url": "https://github.com/k3nfalt/longtails",
                "template": "oracle template",
                "distributedTemplate": "distributed template",
                "setups": [
                    {
                        "id": "DistributedSmoothNonconvex",
                        "filename": "DistributedSmoothNonconvex.lean",
                        "title": "Distributed smooth nonconvex",
                        "descriptionHtml": "<p>Distributed gradients.</p>",
                        "contribution": None,
                        "theorems": [timed],
                    }
                ],
            }
            write_site(root, {"data": data, "css": ""}, "")
            page = root / "public/results/DistributedBatchedSgd/index.html"
            self.assertIn("Proved elapsed-time upper bound", page.read_text())
            catalog = json.loads((root / "public/assets/catalog.json").read_text())
            self.assertIn(
                "elapsed-time upper bound", catalog["setups"][0]["searchText"]
            )
            self.assertEqual(catalog["distributedTemplate"], "distributed template")


if __name__ == "__main__":
    unittest.main()
