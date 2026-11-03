import Lake
open Lake DSL System

/-! `lake build` checks the proofs and builds the demo and the benchmark,
with two native libraries:

- SDL3 (the window, input), 3.2 or later, from the system, found with
  `pkg-config`.
- ThorVG (drawing), built here from a pinned release by its own Meson build,
  once. Few systems package a recent ThorVG with its C API, and how fast it
  draws text is what the benchmark measures. Needs git, Meson, Ninja and a
  C++ compiler. -/

package «lean-puri» where
  moreLinkArgs := #[
    -- ThorVG is found from the executables in .lake/build/bin.
    "-Wl,-rpath,$ORIGIN/../thorvg/install/lib",
    -- Lean links against its own C library; system libraries may expect a
    -- newer one, which they find at run time.
    "-Wl,--allow-shlib-undefined"]

/-- The path of a system library's shared library, found with `pkg-config`:
`lib<name>.so` in its `libdir`, where `<name>` is from its `-l` flag. Lean's
linker doesn't search the system's library directories, so it is given the
file itself. -/
def systemLib (module atLeast hint : String) : JobM FilePath := do
  let pc (args : Array String) := captureProc? { cmd := "pkg-config", args := args.push module }
  if (← testProc { cmd := "pkg-config", args := #[s!"--atleast-version={atLeast}", module] }) then
    if let (some dir, some l) := (← pc #["--variable=libdir"], ← pc #["--libs-only-l"]) then
      let lib := FilePath.mk dir / s!"lib{(l.drop 2).toString}.so"
      if (← lib.pathExists) then
        setTrace (← computeTrace lib)
        return lib
  error s!"pkg-config found no {module} {atLeast} or later: {hint}"

target sdl3 : FilePath := Job.async (caption := "SDL3") do
  systemLib "sdl3" "3.2.0" "install SDL3's development package (on Arch, sdl3)"

/-- The ThorVG release built here. -/
def thorvgTag := "v1.1.3"

/-- ThorVG, fetched at `thorvgTag` and built into .lake/build/thorvg, unless
it is there already: the path of its shared library. -/
target thorvg pkg : FilePath := Job.async (caption := "ThorVG") do
  let dir := pkg.buildDir / "thorvg"
  let lib := dir / "install" / "lib" / "libthorvg-1.so"
  unless (← lib.pathExists) do
    logInfo s!"building ThorVG {thorvgTag} (once)"
    if (← (dir / "build").pathExists) then IO.FS.removeDirAll (dir / "build")
    unless (← (dir / "src").pathExists) do
      proc (quiet := true) { cmd := "git", args := #["clone", "--depth", "1", "--branch", thorvgTag,
        "https://github.com/thorvg/thorvg.git", (dir / "src").toString] }
    proc (quiet := true) { cmd := "meson", args := #["setup", (dir / "build").toString, (dir / "src").toString,
      "--buildtype=release", s!"--prefix={dir / "install"}", "--libdir=lib", "-Ddefault_library=shared",
      "-Dengines=cpu", "-Dloaders=svg,ttf", "-Dbindings=capi", "-Dtools=", "-Dtests=false", "-Dextra="] }
    proc (quiet := true) { cmd := "ninja", args := #["-C", (dir / "build").toString, "install"] }
  setTrace (← computeTrace lib)
  return lib

/-- The bridge between Lean and the native libraries (native/platform.c). -/
target platform.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "platform.c")
  let libs := (← sdl3.fetch).zipWith (·, ·) (← thorvg.fetch)
  libs.bindM fun (_, tvg) => do
    let sdlFlags := (← captureProc? { cmd := "pkg-config", args := #["--cflags", "sdl3"] }).getD ""
    let tvgInclude := tvg.parent.bind (·.parent) |>.getD "." |>.join "include" |>.join "thorvg-1"
    let flags := #["-I", (← getLeanIncludeDir).toString, "-I", tvgInclude.toString] ++
      (sdlFlags.splitOn " " |>.filter (· ≠ "") |>.toArray)
    buildO (pkg.buildDir / "native" / "platform.o") src flags #["-fPIC", "-O2"] "cc"

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
