import Lake
open Lake DSL System

/-! `lake build` checks the proofs and builds the demo and the benchmark,
getting the native dependencies itself:

- SDL3 (the window, input): the system's, if `pkg-config` finds version 3.2
  or later; otherwise built once from its pinned release into deps/.
- ThorVG (drawing): always built once from its pinned release into deps/.
  Few systems package it, and we need its C API and TTF loader.

Building them is scripts/deps.sh. It needs git, a C/C++ compiler, Meson and
Ninja, and for SDL3, CMake and SDL's build dependencies. -/

package «lean-puri» where
  moreLinkArgs := #[
    -- The libraries in deps/ are found from the executables in .lake/build/bin.
    "-Wl,-rpath,$ORIGIN/../../../deps/install/lib",
    -- Lean links against its own C library; system libraries may expect a
    -- newer one, which they find at run time.
    "-Wl,--allow-shlib-undefined"]

/-- A dependency's shared library in deps/install/lib, built from its pinned
release by scripts/deps.sh unless it is there already. -/
def pinned (pkg : Package) (name file : String) : JobM FilePath := do
  let lib := pkg.dir / "deps" / "install" / "lib" / file
  unless (← lib.pathExists) do
    logInfo s!"building {name} into deps/ (once; it takes a few minutes)"
    proc (quiet := true) { cmd := "sh", args := #["scripts/deps.sh", name], cwd := pkg.dir }
  setTrace (← computeTrace lib)
  return lib

/-- SDL3's shared library: the system's, if `pkg-config` finds version 3.2 or
later, or else the pinned release's. -/
target sdl3 pkg : FilePath := Job.async (caption := "SDL3") do
  if (← testProc { cmd := "pkg-config", args := #["--atleast-version=3.2.0", "sdl3"] }) then
    if let some dir ← captureProc? { cmd := "pkg-config", args := #["--variable=libdir", "sdl3"] } then
      let lib := FilePath.mk dir / "libSDL3.so"
      if (← lib.pathExists) then
        setTrace (← computeTrace lib)
        return lib
  pinned pkg "sdl" "libSDL3.so"

/-- ThorVG's shared library, from the pinned release. -/
target thorvg pkg : FilePath := Job.async (caption := "ThorVG") do
  pinned pkg "thorvg" "libthorvg-1.so"

/-- The bridge between Lean and the native libraries (native/platform.c). -/
target platform.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "platform.c")
  let libs := (← sdl3.fetch).zipWith (·, ·) (← thorvg.fetch)
  libs.bindM fun (sdl, _) => do
    let deps := pkg.dir / "deps" / "install"
    -- SDL3's headers: beside the pinned library, or where pkg-config says.
    let sdlFlags ←
      if sdl.toString.startsWith deps.toString then
        pure #["-I", (deps / "include").toString]
      else
        let flags := (← captureProc? { cmd := "pkg-config", args := #["--cflags", "sdl3"] }).getD ""
        pure (flags.splitOn " " |>.filter (· ≠ "") |>.toArray)
    let includes := #["-I", (← getLeanIncludeDir).toString, "-I", (deps / "include" / "thorvg-1").toString]
    buildO (pkg.buildDir / "native" / "platform.o") src (includes ++ sdlFlags) #["-fPIC", "-O2"] "cc"

target libplatform pkg : FilePath := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "platform") #[← platform.o.fetch]

lean_lib Puri

/-- The long list that the demo shows and the benchmark measures. -/
lean_lib Example

@[default_target]
lean_exe demo where
  root := `Demo
  moreLinkObjs := #[libplatform, sdl3, thorvg]

/-- Measures the incremental view against drawing the whole window, with no
display: see scripts/bench.sh. -/
@[default_target]
lean_exe bench where
  root := `Bench
  moreLinkObjs := #[libplatform, sdl3, thorvg]
