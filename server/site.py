import json
import re
import shutil
from html import escape, unescape
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit


class Text(HTMLParser):
    def __init__(self, html):
        super().__init__()
        self.parts = []
        self.feed(html)

    def handle_data(self, data):
        self.parts.append(data)

    def __str__(self):
        return " ".join(" ".join(self.parts).split())


def text(html):
    html = re.sub(
        r'data-tex="([^"]*)"[^>]*>',
        lambda match: ">" + escape(unescape(match[1])),
        html,
    )
    html = re.sub(r"<mjx-container\b.*?</mjx-container>", "", html, flags=re.S)
    return str(Text(html))


def title(html, fallback):
    match = re.search(r"<h[1-6]\b[^>]*>(.*?)</h[1-6]>", html or "", re.S)
    return text(match[1]) if match else re.sub(r"(?<=[a-z])(?=[A-Z])", " ", fallback)


def search_text(value, key=""):
    if isinstance(value, dict):
        return " ".join(search_text(item, key) for key, item in value.items())
    if isinstance(value, list):
        return " ".join(search_text(item) for item in value)
    if value is None:
        return ""
    if key.endswith("Html"):
        return text(value)
    return str(value)


def write_site(root, rendered, fonts, site_url=None):
    data = rendered["data"]
    repository = data["repository_url"]
    owner, name = urlsplit(repository).path.strip("/").split("/")
    site_url = (site_url or f"https://{owner}.github.io/{name}/").rstrip("/") + "/"
    parsed = urlsplit(site_url)
    if (
        parsed.scheme not in ("http", "https")
        or not parsed.hostname
        or parsed.query
        or parsed.fragment
    ):
        raise ValueError(
            "site-url must be an absolute HTTP(S) URL without query or fragment"
        )
    output = root / "public"
    output.mkdir(exist_ok=True)
    assets = output / "assets"
    assets.mkdir(exist_ok=True)
    shutil.copytree(root / "fonts", assets / "fonts", dirs_exist_ok=True)
    shutil.copytree(
        root / "node_modules/mathjax-full/es5/output/chtml/fonts/woff-v2",
        assets / "mathjax-fonts",
        dirs_exist_ok=True,
    )
    for filename in ("logo.png", "mini-logo.png"):
        shutil.copyfile(root / filename, assets / filename)
    template = (root / "template.html").read_text()
    css = re.search(r"<style>(.*?)</style>", template, re.S)[1]
    css = css.replace("__FONT_FACES__", fonts).replace("__MATH_CSS__", rendered["css"])
    (assets / "site.css").write_text(
        "\n".join(line.rstrip() for line in css.splitlines()) + "\n"
    )
    template = re.sub(
        r"<style>.*?</style>",
        '<link rel="stylesheet" href="assets/site.css">',
        template,
        flags=re.S,
    )
    template = template.replace("__PROJECT_NAME__", "LongTails")
    template = template.replace("__REPOSITORY_URL__", escape(repository, quote=True))
    urls = []
    generated = set()

    def write(path, content):
        if path.endswith((".html", ".js")):
            content = "\n".join(line.rstrip() for line in content.splitlines()) + "\n"
        if path.endswith(".html") and len(content.encode()) >= 2_000_000:
            raise ValueError(f"HTML exceeds crawler size budget: {path}")
        target = output / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8")
        generated.add(target)
        if path.endswith(".html"):
            urls.append(site_url + path.removesuffix("index.html"))

    def page(path, heading, description, body):
        prefix = "../" * (len(Path(path).parts) - 1)
        canonical = escape(site_url + path.removesuffix("index.html"), quote=True)
        write(
            path,
            f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="referrer" content="no-referrer">
<title>{escape(heading)} — LongTails</title>
<meta name="description" content="{escape(description[:300], quote=True)}">
<link rel="canonical" href="{canonical}">
<link rel="stylesheet" href="{prefix}assets/site.css">
<link rel="icon" href="{prefix}assets/mini-logo.png">
</head><body><header class="shell site-header"><a class="title-link" href="{prefix}">LongTails</a></header>
<main class="shell detail"><a class="back" href="{prefix}">← All setups</a>
<article><div class="card-body"><h1>{escape(heading)}</h1>{body}</div></article></main></body></html>''',
        )

    def proof_link(theorem):
        url = repository + "/blob/main/" + theorem["module"].replace(".", "/") + ".lean"
        return f'<a href="{escape(url, quote=True)}">Lean proof</a>'

    directory = []
    summaries = []
    for setup in data["setups"]:
        setup_title = title(setup["descriptionHtml"], setup["id"])
        setup["url"] = f"setups/{setup['id']}/"
        description = text(setup["descriptionHtml"])
        links = []
        for theorem in setup["theorems"]:
            module = (
                theorem["module"].removeprefix("LongTails.Theorems.").replace(".", "/")
            )
            theorem["url"] = f"results/{module}/"
            theorem_title = title(theorem.get("formulaHtml"), module.split("/")[-1])
            references = theorem.get("referencesHtml")
            if not references:
                references = (
                    "<p>References have not been researched yet.</p>"
                    if references is None
                    else "<p>No qualifying prior reference verified; this is not a proof of novelty.</p>"
                )
            statement = escape(theorem["statement"])
            prefix = "../" * (len(Path(theorem["url"]).parts))
            body = f'<p><a href="{prefix}{setup["url"]}">{escape(setup_title)}</a> · {proof_link(theorem)}</p>'
            body += '<div class="description">' + setup["descriptionHtml"] + "</div>"
            body += '<section class="budgets"><h2>Proved result</h2>'
            body += (
                theorem.get("formulaHtml")
                or "<p>See the formal statement and Lean proof for the budget.</p>"
            )
            body += f"<pre><code>{statement}</code></pre>"
            if not theorem.get("formulaHtml"):
                for budget in theorem.get("budgets", [theorem.get("budget", {})]):
                    body += (
                        "<pre><code>"
                        + escape(budget.get("value", ""))
                        + "</code></pre>"
                    )
            body += "</section>"
            body += (
                '<section class="previous-results"><h2>Relevant previous results</h2>'
                + references
                + "</section>"
            )
            if setup.get("stale"):
                body = (
                    "<p>Descriptions may be stale. Consult the linked Lean sources.</p>"
                    + body
                )
            page(
                theorem["url"] + "index.html",
                theorem_title + " — " + setup_title,
                theorem_title + ". " + description,
                body,
            )
            links.append(
                f'<li><a href="../../{theorem["url"]}">{escape(theorem_title)}</a> · {proof_link(theorem)}</li>'
            )
        body = (
            '<div class="description">'
            + setup["descriptionHtml"]
            + "</div><h2>Results</h2><ul>"
            + "".join(links)
            + "</ul>"
        )
        if setup.get("stale"):
            body = (
                "<p>Descriptions may be stale. Consult the linked Lean sources.</p>"
                + body
            )
        body += (
            '<div class="comparison-scroll">'
            + (setup.get("comparisonHtml") or "")
            + "</div>"
        )
        body += f'<p><a href="{escape(repository)}/blob/main/LongTails/Setups/{setup["filename"]}">Lean setup</a></p>'
        page(setup["url"] + "index.html", setup_title, description, body)
        directory.append(f'<li><a href="{setup["url"]}">{escape(setup_title)}</a></li>')
        write(f"data/{setup['id']}.json", json.dumps(setup, ensure_ascii=False))
        formula_text = " ".join(
            text(row.get("formulaHtml") or "") for row in setup["theorems"]
        )
        summaries.append(
            {
                "id": setup["id"],
                "title": setup["title"],
                "contribution": setup["contribution"],
                "formulaLength": len(re.sub(r"\s", "", formula_text)) or 1_000_000,
                "searchText": " ".join(
                    dict.fromkeys(search_text(setup).replace("_", " ").lower().split())
                ),
            }
        )
    index = {**data, "setups": summaries}
    write("assets/catalog.json", json.dumps(index, ensure_ascii=False))
    fallback = (
        '<nav aria-label="Browse all setups"><ul>' + "".join(directory) + "</ul></nav>"
    )
    template = template.replace("__STATIC_CATALOG__", fallback)
    template = template.replace("__SITE_URL__", escape(site_url, quote=True))
    scripts = re.findall(r"<script>(.*?)</script>", template, re.S)
    script = "\n".join(scripts).replace(
        "__FUSE_JS__", (root / "vendor/fuse-7.5.0.min.cjs").read_text()
    )
    write("assets/catalog.js", script)
    template = re.sub(r"<script>.*?</script>", "", template, flags=re.S)
    template = template.replace(
        "</body>", '<script src="assets/catalog.js"></script>\n</body>'
    )
    write("index.html", template)
    write(
        "sitemap.xml",
        '<?xml version="1.0" encoding="UTF-8"?><urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'
        + "".join(f"<url><loc>{escape(url)}</loc></url>" for url in urls)
        + "</urlset>",
    )
    for directory in ("setups", "results", "data"):
        for path in (output / directory).rglob("*"):
            if path.is_file() and path not in generated:
                path.unlink()
    return output / "index.html"
