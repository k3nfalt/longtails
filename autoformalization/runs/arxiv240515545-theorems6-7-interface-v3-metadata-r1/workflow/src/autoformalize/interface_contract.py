"""Bind the self-contained workflow instructions to the actual Lean interface."""

from .common import require


BEGIN = "<!-- BEGIN PINNED TEMPLATE -->\n```lean\n"
END = "\n```\n<!-- END PINNED TEMPLATE -->"


def validate_template_contract(contract, template):
    """Fail closed if the policy describes a different API than the run imports."""
    contract = contract.replace("\r\n", "\n")
    template = template.replace("\r\n", "\n").rstrip("\n")
    require(
        contract.count(BEGIN) == 1 and contract.count(END) == 1,
        "Explicit output contract must contain exactly one pinned Template.lean block",
    )
    before, embedded = contract.split(BEGIN, 1)
    require(END not in before, "Malformed pinned Template.lean block")
    embedded = embedded.split(END, 1)[0]
    require(
        embedded == template,
        "Explicit workflow Template.lean contract differs from the pinned project interface; "
        "update and review the workflow contract for new runs, never edit the project template to bypass this check",
    )
