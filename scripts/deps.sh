#!/bin/sh
# Builds the native dependencies from pinned releases into deps/install:
# SDL3 (window, input) and ThorVG (vector drawing, its C API). Needs git,
# a C/C++ compiler, CMake, Meson and Ninja. Run from the repository root.
set -eu

SDL_TAG=release-3.4.18
THORVG_TAG=v1.1.3

root=$(pwd)
src=$root/deps/src
out=$root/deps/install
mkdir -p "$src" "$out"

fetch() { # name url tag
  if [ ! -d "$src/$1" ]; then
    git clone --depth 1 --branch "$3" "$2" "$src/$1"
  fi
}

fetch SDL https://github.com/libsdl-org/SDL.git "$SDL_TAG"
fetch thorvg https://github.com/thorvg/thorvg.git "$THORVG_TAG"

cmake -S "$src/SDL" -B "$src/SDL/build" -G Ninja \
  -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$out" -DCMAKE_INSTALL_LIBDIR=lib \
  -DSDL_SHARED=ON -DSDL_STATIC=OFF -DSDL_TEST_LIBRARY=OFF -DSDL_EXAMPLES=OFF
cmake --build "$src/SDL/build"
cmake --install "$src/SDL/build"

meson setup "$src/thorvg/build" "$src/thorvg" --reconfigure --buildtype=release \
  --prefix="$out" --libdir=lib -Ddefault_library=shared \
  -Dengines=sw -Dloaders=svg,ttf -Dbindings=capi -Dtools= -Dexamples=false -Dtests=false
ninja -C "$src/thorvg/build" install
