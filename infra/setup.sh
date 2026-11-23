#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

if (( $# != 0 )); then
    printf 'Usage: %s\n' "$0" >&2
    exit 2
fi

packages=()
command -v cc >/dev/null && command -v make >/dev/null || packages+=(build-essential)
command -v curl >/dev/null || packages+=(curl)
command -v git >/dev/null || packages+=(git)
command -v python3 >/dev/null || packages+=(python3)
command -v pipx >/dev/null || packages+=(pipx)
command -v tar >/dev/null || packages+=(tar)
command -v zstd >/dev/null || packages+=(zstd)
command -v gh >/dev/null || packages+=(gh)
command -v openssl >/dev/null || packages+=(openssl)
[[ -s /etc/ssl/certs/ca-certificates.crt ]] || packages+=(ca-certificates)

if (( ${#packages[@]} )); then
    if ! command -v apt-get >/dev/null; then
        printf 'Install these system packages before retrying: %s\n' "${packages[*]}" >&2
        exit 1
    fi
    apt=(apt-get)
    if (( EUID != 0 )); then
        if ! command -v sudo >/dev/null; then
            printf 'Installing system packages requires root or sudo: %s\n' "${packages[*]}" >&2
            exit 1
        fi
        apt=(sudo apt-get)
    fi
    "${apt[@]}" update
    "${apt[@]}" install -y "${packages[@]}"
fi

installer_dir=$(mktemp -d)
trap 'rm -rf -- "$installer_dir"' EXIT
elan_bin="${ELAN_HOME:-$HOME/.elan}/bin"
if [[ ! -x "$elan_bin/elan" ]]; then
    if [[ "$(uname -s):$(uname -m)" != Linux:x86_64 ]]; then
        printf 'Automatic Elan installation requires x86-64 Linux. Install Elan and rerun this script.\n' >&2
        exit 1
    fi
    curl --fail --silent --show-error --location \
        'https://github.com/leanprover/elan/releases/download/v4.2.2/elan-x86_64-unknown-linux-gnu.tar.gz' \
        --output "$installer_dir/elan.tar.gz"
    tar -xzf "$installer_dir/elan.tar.gz" -C "$installer_dir" elan-init
    "$installer_dir/elan-init" -y --default-toolchain none --no-modify-path
fi
export PATH="$elan_bin:$PATH"

ruff_version=0.17.0
export PATH="$HOME/.local/bin:$PATH"
if [[ "$(ruff --version 2>/dev/null || true)" != "ruff $ruff_version" ]]; then
    PIPX_BIN_DIR="$HOME/.local/bin" pipx install --force "ruff==$ruff_version"
fi
ruff --version

if ! command -v codex >/dev/null; then
    curl --fail --silent --show-error --location \
        'https://github.com/openai/codex/releases/latest/download/install.sh' \
        --output "$installer_dir/codex-install.sh"
    CODEX_NON_INTERACTIVE=1 CODEX_INSTALLER_USE_RELEASES_OPENAI_COM=0 \
        sh "$installer_dir/codex-install.sh"
fi
codex --version

toolchain=$(<lean-toolchain)
"$elan_bin/elan" toolchain install "$toolchain"
lake --version
lake exe cache get

bash_login="$HOME/.profile"
for profile in "$HOME/.bash_profile" "$HOME/.bash_login"; do
    if [[ -r "$profile" ]]; then
        bash_login="$profile"
        break
    fi
done
zsh_dir="${ZDOTDIR:-$HOME}"
path_line='case ":$PATH:" in *":${ELAN_HOME:-$HOME/.elan}/bin:"*) ;; *) export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH" ;; esac'
for profile in "$bash_login" "$HOME/.bashrc" "$zsh_dir/.zprofile" "$zsh_dir/.zshrc"; do
    for line in "$path_line" 'case ":$PATH:" in *":$HOME/.local/bin:"*) ;; *) export PATH="$HOME/.local/bin:$PATH" ;; esac'; do
        if ! grep -Fxq -- "$line" "$profile" 2>/dev/null; then
            printf '\n%s\n' "$line" >> "$profile"
        fi
    done
done

printf 'LongTails dependencies are installed. Open a new shell and run ./build.sh --cache to build from the latest compatible nightly.\n'
