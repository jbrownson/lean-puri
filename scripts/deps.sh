#!/bin/sh
# Builds native dependencies from pinned releases into deps/install. `lake
# build` runs this itself when it needs to, so there's no need to run it by
# hand. Run from the repository root.
#
#   scripts/deps.sh             both
#   scripts/deps.sh sdl         SDL3 (window, input): needs CMake and SDL's
#                               build dependencies. Not needed if the system
#                               has SDL3 3.2 or later, which lake uses.
#   scripts/deps.sh thorvg      ThorVG (vector drawing, its C API): needs
#                               Meson and Ninja.
#
# Both need git and a C/C++ compiler.
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

sdl() {
  fetch SDL https://github.com/libsdl-org/SDL.git "$SDL_TAG"
  cmake -S "$src/SDL" -B "$src/SDL/build" -G Ninja \
    -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$out" -DCMAKE_INSTALL_LIBDIR=lib \
    -DSDL_SHARED=ON -DSDL_STATIC=OFF -DSDL_TEST_LIBRARY=OFF -DSDL_EXAMPLES=OFF
  cmake --build "$src/SDL/build"
  cmake --install "$src/SDL/build"
}

thorvg() {
  fetch thorvg https://github.com/thorvg/thorvg.git "$THORVG_TAG"
  meson setup "$src/thorvg/build" "$src/thorvg" --reconfigure --buildtype=release \
    --prefix="$out" --libdir=lib -Ddefault_library=shared \
    -Dengines=cpu -Dloaders=svg,ttf -Dbindings=capi -Dtools= -Dtests=false -Dextra=
  ninja -C "$src/thorvg/build" install
}

for what in ${*:-sdl thorvg}; do
  case $what in
    sdl) sdl ;;
    thorvg) thorvg ;;
    *) echo "deps.sh: no dependency called $what (sdl, thorvg)" >&2; exit 2 ;;
  esac
done
