import unittest

from infra.research_status import pane_state


class ResearchStatusTests(unittest.TestCase):
    def test_visible_status(self):
        error = (
            "■ stream disconnected before completion: Transport error:\n  network error"
        )
        cases = [
            (error + "\n\n› Ask Codex to do anything", "disconnected"),
            (error + "\n• Working (esc to interrupt)\n\n›", "working"),
            (error + "\n• Later message\n\n›", "unknown"),
            (
                "Would you like to run the following command?\n› 1. Yes",
                "waiting for input",
            ),
            ("Goal achieved in an earlier session.\n›", "unknown"),
            ("›\n  GPT · workspace\n  ← for agents · Goal achieved", "goal achieved"),
            ("›\n  Goal paused", "goal paused"),
            ("› Ask Codex to do anything", "unknown"),
            ("✔ Goal achieved\n✻ Brewed for 2m\n────\n❯\n────", "goal achieved"),
            ("✔ Goal achieved\n❯ new request\n● reply\n────\n❯", "unknown"),
            ("✔ Goal achieved\n────\n❯\n────\n⏵ esc to interrupt", "working"),
            (
                "❯ 1. Yes\n  2. No\nEnter to confirm · Esc to cancel",
                "waiting for input",
            ),
        ]
        cases.append(
            (
                "✻ Waiting for 1 background agent to finish\n2 background task updates waiting\n"
                "❯ 1. Stop and wait for limit to reset\nEnter to confirm · Esc to cancel",
                "working (background)",
            )
        )
        for screen, expected in cases:
            with self.subTest(screen=screen):
                self.assertEqual(pane_state(screen), expected)
