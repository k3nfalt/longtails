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
command -v tar >/dev/null || packages+=(tar)
command -v zstd >/dev/null || packages+=(zstd)
command -v openssl >/dev/null || packages+=(openssl)
[[ -s /etc/ssl/certs/ca-certificates.crt ]] || packages+=(ca-certificates)

if (( ${#packages[@]} )); then
    if (( EUID != 0 )) || ! command -v apt-get >/dev/null; then
        printf 'Install these system packages before retrying: %s\n' "${packages[*]}" >&2
        exit 1
    fi
    apt-get update
    apt-get install -y "${packages[@]}"
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

export PATH="$HOME/.local/bin:$PATH"
mkdir -p "$HOME/.local/bin"
if ! command -v gh >/dev/null; then
    case "$(uname -s):$(uname -m)" in
        Linux:x86_64) gh_arch=amd64 ;;
        Linux:aarch64) gh_arch=arm64 ;;
        *) printf 'Install GitHub CLI for this platform and rerun setup.\n' >&2; exit 1 ;;
    esac
    gh_package="gh_2.105.0_linux_$gh_arch"
    curl -fsSL "https://github.com/cli/cli/releases/download/v2.105.0/$gh_package.tar.gz" \
        -o "$installer_dir/gh.tar.gz"
    tar -xzf "$installer_dir/gh.tar.gz" -C "$installer_dir" "$gh_package/bin/gh"
    install -m 755 "$installer_dir/$gh_package/bin/gh" "$HOME/.local/bin/gh"
fi

ruff_version=0.17.0
if [[ "$(ruff --version 2>/dev/null || true)" != "ruff $ruff_version" ]]; then
    curl -fsSL "https://github.com/astral-sh/ruff/releases/download/$ruff_version/ruff-installer.sh" \
        -o "$installer_dir/ruff-install.sh"
    RUFF_UNMANAGED_INSTALL="$HOME/.local/bin" sh "$installer_dir/ruff-install.sh"
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
