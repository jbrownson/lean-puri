import Lake
open Lake DSL System

/-! `lake build` checks the proofs and builds the demo and the benchmark. The
native libraries come from the system, found with `pkg-config`: SDL3 (the
window, input), 3.2 or later, and ThorVG (drawing), 1.1 or later, built with
its C API (`-Dbindings=capi`) and TTF loader (`-Dloaders=ttf`). -/

package «lean-puri» where
  -- Lean links against its own C library; system libraries may expect a
  -- newer one, which they find at run time.
  moreLinkArgs := #["-Wl,--allow-shlib-undefined"]

/-- A system library found with `pkg-config`: the path of its shared library,
`lib<name>.so` in its `libdir`, where `<name>` is from its `-l` flag. -/
def systemLib (modules : List String) (atLeast hint : String) : JobM FilePath := do
  let pc (args : Array String) := captureProc? { cmd := "pkg-config", args }
  for m in modules do
    if (← testProc { cmd := "pkg-config", args := #[s!"--atleast-version={atLeast}", m] }) then
      if let (some dir, some l) := (← pc #["--variable=libdir", m], ← pc #["--libs-only-l", m]) then
        let lib := FilePath.mk dir / s!"lib{(l.drop 2).toString}.so"
        if (← lib.pathExists) then
          setTrace (← computeTrace lib)
          return lib
  error s!"pkg-config found no {modules.head!} {atLeast} or later: {hint}"

target sdl3 : FilePath := Job.async (caption := "SDL3") do
  systemLib ["sdl3"] "3.2.0" "install SDL3's development package (on Arch, sdl3)"

target thorvg : FilePath := Job.async (caption := "ThorVG") do
  systemLib ["thorvg-1", "thorvg"] "1.1.0"
    "install ThorVG, built with its C API and TTF loader (on Arch, the AUR's thorvg)"

/-- The compiler flags of `pkg-config` modules. -/
def cflags (modules : Array String) : JobM (Array String) := do
  let flags := (← captureProc? { cmd := "pkg-config", args := #["--cflags"] ++ modules }).getD ""
  return flags.splitOn " " |>.filter (· ≠ "") |>.toArray

/-- The bridge between Lean and the native libraries (native/platform.c). -/
target platform.o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "native" / "platform.c")
  let libs := (← sdl3.fetch).zipWith (·, ·) (← thorvg.fetch)
  libs.bindM fun (_, tvg) => do
    let tvgModule := if tvg.fileName == some "libthorvg-1.so" then "thorvg-1" else "thorvg"
    let flags := #["-I", (← getLeanIncludeDir).toString] ++ (← cflags #["sdl3", tvgModule])
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
