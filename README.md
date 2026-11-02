# lean-puri

Puri's change structures in Lean, with proved derivatives, and a window
drawn by ThorVG. The example is a long scrolling list whose drawing is kept
up to date from the list's edits and the scroll, instead of being laid out
and drawn again each frame.

## What's where

- `Puri/Change.lean`: edit and change structures, `Inc`, `Inc.ok`, `lift`,
  `whole`, `recompute`.
- `Puri/List.lean`: list edits, `patch`, `diff`, `dmap`, with proofs.
- `Puri/Drawing.lean`: drawings (rows placed at heights) and their edits:
  `translate`, `shift`, `insert`, `delete`, `update`. `diff` makes them a
  change structure.
- `Puri/Scroll.lean`: a list held split at the first row that shows, its
  edits (list edits and scrolling), and two outputs, each an `Inc` with its
  law: `view` (the drawing of the rows that show, `view_ok`) and `extent`
  (offset and height, for the scroll bar, `extent_ok`). The laws are at the
  end of the file. `draw_eq` says what the view is in terms of the whole
  list.
- `Puri/Axioms.lean`: `#guard_msgs` checks of every law's axioms, so
  `lake build` fails on a `sorry` or a new axiom.
- `Puri/Platform.lean`, `native/platform.c`: the SDL3 window, an offscreen
  target with no display, and `Rows`, retained rows whose operations are a
  drawing's edits.
- `Puri/Render.lean`: makes a drawing's edits to `Rows`.
- `Example.lean`: the 10,000-item list both programs use.
- `Demo.lean`: the window. `Bench.lean`: the measurements.

## Building

Needs git, a C/C++ compiler, CMake, Meson and Ninja, and SDL's build
dependencies (on Debian or Ubuntu: `libx11-dev libxext-dev libxcursor-dev
libxrandr-dev libxi-dev libxfixes-dev libxss-dev libxtst-dev
libxkbcommon-dev libwayland-dev wayland-protocols libegl-dev libgl-dev`).
Lean comes from [elan](https://github.com/leanprover/elan), at the version
in `lean-toolchain`.

```bash
scripts/deps.sh
```

```bash
lake build
```

`scripts/deps.sh` builds SDL3 and ThorVG into `deps/`. `lake build` checks
the proofs and builds `demo` and `bench`.

## The demo

Run it from the repository's root, so it finds the font:

```bash
.lake/build/bin/demo
```

- Wheel, arrow keys, Page Up/Down, Home/End: scroll.
- Click an item: open or close it. The items below it shift.
- Return or `n`: insert an item below the one under the pointer.
- Delete, Backspace or `d`: delete the item under the pointer.
- `w`: draw the whole window every frame instead, to compare.
- `a`: scroll by itself, to watch and time frames.
- `q` or Escape: quit.

Once a second, the title bar and standard output report the CPU work per
frame: from the events to the frame being ready, not counting the wait for
the display.

## Measuring

```bash
scripts/bench.sh
```

That checks both paths agree, frame by frame, then times 5 rounds of 600
frames through each. It needs no display. `scripts/bench.sh --callgrind`
also counts instructions per frame with valgrind, which is slow.
`.lake/build/bin/bench --sdl` also checks the window code with SDL's
offscreen video driver. `--scale 1` measures at one pixel per point.

## Results

On a 4-core cloud VM (Intel Xeon at 2.8 GHz), 2026-11-02: one script of
600 frames (scrolling at 4 to 22 points a frame, then up, a page, a jump to
the top, a fling at 60, and an open, insert and delete every 40 frames),
5 rounds, a 520 × 760-point window of 10,000 items. Cloud timings are
noisy, so the maxima mean little; the instruction counts (callgrind, 200
frames) don't vary.

Milliseconds per frame, median (90th percentile), at 2 pixels per point:

| | all frames | scrolling | jumps | edits |
|---|---|---|---|---|
| whole window | 17.3 (20.8) | 17.3 (20.9) | 15.7 | 17.3 (20.8) |
| incremental, less composite | 0.27 (1.87) | 0.011 (1.68) | 16.0 | 0.96 (4.35) |
| incremental: composite alone (CPU here) | 1.07 (1.75) | 1.05 (1.69) | 2.1 | 1.37 (2.06) |
| of which Lean (`view.df`, `extent.df`, `apply`) | 0.005 (0.009) | 0.005 (0.008) | 0.014 | 0.010 (0.013) |

Instructions per frame, median (90th percentile), at 2 pixels per point:

| | scrolling | jumps | edits |
|---|---|---|---|
| whole window | 79.1M (85.2M) | 79.1M | 77.8M (86.9M) |
| of which Lean (apply, draw, extent) | 1.29M | 1.30M | 1.29M |
| incremental: Lean | 8.0K (8.7K) | 18.7K | 12.8K (14.9K) |
| incremental: render edits | 1.7K (7.8M) | 79.9M | 8.2M (23.9M) |
| incremental: CPU composite | 4.6M | 4.6M | 4.6M |

At 1 pixel per point, drawing the whole window takes 7.3 ms (median) and
the incremental path 0.09 ms less composite, 0.31 ms with it.

The derivatives cost microseconds. What costs is drawing text: ThorVG takes
about 1.2 ms per row at 2 pixels per point (0.5 ms at 1), and the
incremental path still draws each row that enters (0.66 per frame here). A
jump draws every row, as drawing the whole window does. On a window, the
composite is GPU work; offscreen, the CPU copies about 6 MB per frame,
timed apart above.
