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

elan_bin="${ELAN_HOME:-$HOME/.elan}/bin"
if [[ ! -x "$elan_bin/elan" ]]; then
    if [[ "$(uname -s):$(uname -m)" != Linux:x86_64 ]]; then
        printf 'Automatic Elan installation requires x86-64 Linux. Install Elan and rerun this script.\n' >&2
        exit 1
    fi
    installer_dir=$(mktemp -d)
    trap 'rm -rf -- "$installer_dir"' EXIT
    curl --fail --silent --show-error --location \
        'https://github.com/leanprover/elan/releases/download/v4.2.2/elan-x86_64-unknown-linux-gnu.tar.gz' \
        --output "$installer_dir/elan.tar.gz"
    tar -xzf "$installer_dir/elan.tar.gz" -C "$installer_dir" elan-init
    "$installer_dir/elan-init" -y --default-toolchain none --no-modify-path
fi
export PATH="$elan_bin:$PATH"

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
    if ! grep -Fxq -- "$path_line" "$profile" 2>/dev/null; then
        printf '\n%s\n' "$path_line" >> "$profile"
    fi
done

printf 'LongTails dependencies are installed. Open a new shell and run ./build.sh to build the project.\n'
