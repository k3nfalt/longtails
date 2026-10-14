#!/usr/bin/env python3
"""Run one command with a fresh auto-math-bot installation token.
Requires Python 3 and openssl; no pip packages or sudo.
Key defaults to ~/.config/auto-math-bot/private-key.pem.
Override with AUTO_MATH_BOT_KEY. Use an HTTPS Git remote.
Set AUTO_MATH_BOT_INSTALLATION_ID to the installation ID for k3nfalt.
Call this wrapper for EACH GitHub operation during long Codex runs.
This changes authentication, not OS isolation. Do not run commands that
dump their environment: it contains a secret token.
"""

import base64
import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path


def b64(data):
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode()


def installation_token():
    installation_id = os.environ.get("AUTO_MATH_BOT_INSTALLATION_ID", "")
    if (
        not installation_id.isascii()
        or not installation_id.isdecimal()
        or int(installation_id) <= 0
    ):
        raise ValueError("Set AUTO_MATH_BOT_INSTALLATION_ID to a positive integer.")
    key = Path(
        os.environ.get("AUTO_MATH_BOT_KEY", "~/.config/auto-math-bot/private-key.pem")
    ).expanduser()
    if not key.is_file():
        raise RuntimeError("Private key not found; set AUTO_MATH_BOT_KEY to its path.")
    now = int(time.time())
    header = b64(b'{"alg":"RS256","typ":"JWT"}')
    payload = b64(
        json.dumps(
            {
                "iss": "Iv23liYQZ9xS7rsf67Cf",
                "iat": now - 60,
                "exp": now + 540,
            }
        ).encode()
    )
    message = f"{header}.{payload}".encode()
    signed = subprocess.run(
        ["openssl", "dgst", "-sha256", "-sign", str(key)],
        input=message,
        capture_output=True,
        check=True,
    ).stdout
    jwt = message.decode() + "." + b64(signed)
    request = urllib.request.Request(
        f"https://api.github.com/app/installations/{installation_id}/access_tokens",
        data=json.dumps(
            {
                "repositories": ["longtails"],
                "permissions": {"contents": "write", "pull_requests": "write"},
            }
        ).encode(),
        headers={
            "Authorization": f"Bearer {jwt}",
            "Accept": "application/vnd.github+json",
            "Content-Type": "application/json",
            "User-Agent": "auto-math-bot-token-launcher",
        },
        method="POST",
    )
    # Pass the JWT through stdin, rather than exposing it in command arguments.
    curl_config = "\n".join(
        f"header = {json.dumps(f'{name}: {value}')}"
        for name, value in request.header_items()
    )

    result = subprocess.run(
        [
            "curl",
            "--config",
            "-",
            "--silent",
            "--show-error",
            "--fail-with-body",
            "--connect-timeout",
            "15",
            "--max-time",
            "60",
            *(
                ["--proxy", os.environ["PROXY_URL"], "--noproxy", ""]
                if os.environ.get("PROXY_URL")
                else ["--noproxy", "*"]
            ),
            "--request",
            "POST",
            "--data-binary",
            request.data.decode("utf-8"),
            request.full_url,
        ],
        input=curl_config + "\n",
        check=False,
        text=True,
        capture_output=True,
    )

    if result.returncode != 0:
        # Do not print stdout: a successful response contains a secret token.
        print(result.stderr.strip(), file=sys.stderr)
        raise RuntimeError(f"Token request via curl failed (exit {result.returncode}).")

    return json.loads(result.stdout)["token"]


def command_environment(token):
    env = os.environ.copy()
    env["GH_TOKEN"] = token
    env["GITHUB_TOKEN"] = token
    env["GIT_TERMINAL_PROMPT"] = "0"
    # Preserve existing runtime Git settings, then override authentication.
    count = int(env.get("GIT_CONFIG_COUNT", "0"))
    auth = base64.b64encode(f"x-access-token:{token}".encode()).decode()
    for key, value in [
        ("credential.helper", ""),
        ("http.https://github.com/.extraheader", ""),
        ("http.https://github.com/.extraheader", f"Authorization: Basic {auth}"),
    ]:
        env[f"GIT_CONFIG_KEY_{count}"] = key
        env[f"GIT_CONFIG_VALUE_{count}"] = value
        count += 1
    env["GIT_CONFIG_COUNT"] = str(count)
    return env


def main():
    command = sys.argv[1:]
    if command and command[0] == "--":
        command = command[1:]
    if not command or command == ["--help"]:
        print(__doc__)
        return 0 if command else 2
    try:
        env = command_environment(installation_token())
        return subprocess.call(command, env=env)
    except urllib.error.HTTPError as error:
        print(
            f"Token request failed: HTTP {error.code}. Check app installation, "
            "repository selection, and Contents/Pull requests write permissions.",
            file=sys.stderr,
        )
    except subprocess.CalledProcessError:
        print("Key signing failed. Check the PEM key and openssl.", file=sys.stderr)
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        print(
            f"Could not run bot command ({type(error).__name__}). "
            "Check the key path, dependencies, network, and command.",
            file=sys.stderr,
        )
    return 1


if __name__ == "__main__":
    sys.exit(main())
