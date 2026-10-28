"""Run output routing; copied library modules retain their original identities."""

from .common import require

CATEGORIES = ("Algorithms", "Setups", "Proofs", "Theorems")


def in_category(path, category):
    return path.startswith((f"outputs/{category}/", f"LongTails/{category}/"))


def setup_module(name):
    return name.startswith(("outputs.Setups.", "LongTails.Setups."))


def adapt_metadata(source):
    for category, variable in (("Theorems", "moduleName"), ("Setups", "setupModule")):
        old = f"(`LongTails.{category}).isPrefixOf {variable}"
        require(source.count(old) == 1, "Unsupported native metadata routing: " + old)
        source = source.replace(
            old, f"({old} || (`outputs.{category}).isPrefixOf {variable})"
        )
    return source


def adapt_comparator(source):
    old = 'sorted((ROOT / "LongTails/Theorems").glob("*.lean"))'
    require(source.count(old) == 1, "Unsupported native Comparator routing")
    source = source.replace(
        old,
        'sorted([*(ROOT / "outputs/Theorems").glob("*.lean"), *(ROOT / "LongTails/Theorems").glob("*.lean")])',
    )
    return (
        source.replace(
            'ROOT / "LongTails/Theorems" / selected',
            'ROOT / "outputs/Theorems" / selected',
        )
        .replace(
            '.removeprefix("LongTails.Theorems.")',
            '.removeprefix("LongTails.Theorems.").removeprefix("outputs.Theorems.")',
        )
        .replace(
            "file in LongTails/Theorems",
            "file in outputs/Theorems or copied LongTails/Theorems",
        )
    )


def adapt_style_linter(source):
    old = "modulesNotUpperCamelCase opts allModuleNames"
    require(source.count(old) == 1, "Unsupported pinned style-linter module check")
    return source.replace(
        old,
        "modulesNotUpperCamelCase opts "
        "(allModuleNames.map fun n => n.replacePrefix `outputs `Outputs)",
    )
