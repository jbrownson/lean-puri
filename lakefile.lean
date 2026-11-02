import Lake
open Lake DSL System

/-! The native dependencies (SDL3, ThorVG) are built by scripts/deps.sh into
deps/install; the bridge in native/ is compiled here and linked against them. -/

def depsDir (pkg : Package) : FilePath := pkg.dir / "deps" / "install"

package «lean-puri» where
  moreLinkArgs := #[
    "-Ldeps/install/lib", "-lSDL3", "-lthorvg",
    "-Wl,-rpath,$ORIGIN/../../../deps/install/lib",
    "-Wl,--allow-shlib-undefined"]

lean_lib Puri

@[default_target]
lean_exe demo where
  root := `Demo

target platform.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "platform.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "platform.c"
  let deps := depsDir pkg
  let weakArgs := #["-I", (← getLeanIncludeDir).toString,
    "-I", (deps / "include").toString, "-I", (deps / "include" / "thorvg-1").toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

extern_lib libplatform pkg := do
  let o ← platform.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "platform") #[o]
