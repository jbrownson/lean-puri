// The platform bridge: an SDL3 window whose frames ThorVG draws on the CPU,
// or an offscreen target with the same drawing and no display.
//
// The window is a Lean external object. Coordinates crossing the bridge are
// logical points; the bridge scales drawing by the window's pixel density, so
// a 2x display gets sharp output. Events come back as flat UInt32 words, five
// per event, and Lean decodes them (Platform.lean), so policy stays in Lean.
//
// Two ways to draw:
//  - A frame: begin, add shapes and text, end. ThorVG draws the whole window
//    and the window shows it. Everything is drawn again each frame.
//  - Rows: a retained list of rows, each drawn once into its own pixels when
//    it enters or changes. Its operations are a drawing's edits
//    (Puri/Drawing.lean): translate, shift, insert, delete, update. Showing
//    the rows composites their pixels at their tops: on a window, as SDL
//    textures the GPU composites; offscreen, by copying on the CPU.

#include <lean/lean.h>
#define SDL_MAIN_HANDLED
#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <thorvg_capi.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(__has_include)
#if __has_include(<valgrind/callgrind.h>)
#include <valgrind/callgrind.h>
#endif
#endif
#ifndef CALLGRIND_ZERO_STATS
#define CALLGRIND_ZERO_STATS
#define CALLGRIND_DUMP_STATS_AT(s) ((void)(s))
#endif

typedef struct {
  SDL_Window* window;     // NULL offscreen
  SDL_Renderer* renderer;
  SDL_Texture* texture;   // a frame's pixels, on a window
  Tvg_Canvas canvas;
  Tvg_Paint root;         // this frame's scene, scaled from points to pixels
  uint32_t* pixels;       // a frame's pixels, or offscreen, what shows
  int pw, ph;             // the target's size in pixels
  float scale;            // offscreen: pixels per point
} PuriWindow;

static void window_finalize(void* p) {
  PuriWindow* w = p;
  if (w->canvas) tvg_canvas_destroy(w->canvas);
  if (w->texture) SDL_DestroyTexture(w->texture);
  if (w->renderer) SDL_DestroyRenderer(w->renderer);
  if (w->window) SDL_DestroyWindow(w->window);
  free(w->pixels);
  free(w);
}

static void no_foreach(void* p, b_lean_obj_arg f) {}

static lean_external_class* window_class = NULL;

static lean_obj_res io_error(const char* what) {
  char msg[512];
  snprintf(msg, sizeof msg, "%s: %s", what, SDL_GetError());
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res io_unit(void) { return lean_io_result_mk_ok(lean_box(0)); }

static PuriWindow* window_of(b_lean_obj_arg w) {
  return (PuriWindow*)lean_get_external_data(w);
}

static int engine_ready = 0, video_ready = 0;

static int ensure_engine(void) {
  if (!engine_ready) {
    if (tvg_engine_init(0) != TVG_RESULT_SUCCESS) return 0;
    window_class = lean_register_external_class(window_finalize, no_foreach);
    engine_ready = 1;
  }
  return 1;
}

static float scale_of(PuriWindow* w) {
  return w->window ? SDL_GetWindowPixelDensity(w->window) : w->scale;
}

// Matches the frame's pixels to the window's size, which may have changed.
// False if it couldn't.
static int fit_target(PuriWindow* w) {
  int pw = w->pw, ph = w->ph;
  if (w->window) SDL_GetWindowSizeInPixels(w->window, &pw, &ph);
  if (pw == w->pw && ph == w->ph && w->pixels != NULL) return 1;
  free(w->pixels);
  w->pw = pw; w->ph = ph;
  w->pixels = malloc((size_t)pw * ph * 4);
  if (!w->pixels) { w->pw = w->ph = 0; return 0; }
  if (w->window) {
    if (w->texture) SDL_DestroyTexture(w->texture);
    w->texture = SDL_CreateTexture(w->renderer, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STREAMING, pw, ph);
    if (!w->texture) return 0;
  }
  tvg_swcanvas_set_target(w->canvas, w->pixels, pw, pw, ph, TVG_COLORSPACE_ARGB8888);
  return 1;
}

LEAN_EXPORT lean_obj_res puri_window_open(b_lean_obj_arg title, uint32_t width, uint32_t height,
                                          lean_obj_arg world) {
  if (!video_ready) {
    SDL_SetMainReady();
    if (!SDL_Init(SDL_INIT_VIDEO)) return io_error("SDL_Init");
    video_ready = 1;
  }
  if (!ensure_engine()) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("tvg_engine_init failed")));
  }
  PuriWindow* w = calloc(1, sizeof *w);
  w->window = SDL_CreateWindow(lean_string_cstr(title), (int)width, (int)height,
                               SDL_WINDOW_RESIZABLE | SDL_WINDOW_HIGH_PIXEL_DENSITY);
  if (!w->window) { free(w); return io_error("SDL_CreateWindow"); }
  w->renderer = SDL_CreateRenderer(w->window, NULL);
  if (!w->renderer) { window_finalize(w); return io_error("SDL_CreateRenderer"); }
  SDL_SetRenderVSync(w->renderer, 1);
  w->canvas = tvg_swcanvas_create(TVG_ENGINE_OPTION_DEFAULT);
  SDL_StartTextInput(w->window);
  return lean_io_result_mk_ok(lean_alloc_external(window_class, w));
}

// A target with no display, width by height points at scale pixels per point.
LEAN_EXPORT lean_obj_res puri_offscreen_open(uint32_t width, uint32_t height, double scale, lean_obj_arg world) {
  if (!ensure_engine()) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("tvg_engine_init failed")));
  }
  PuriWindow* w = calloc(1, sizeof *w);
  w->scale = (float)scale;
  w->pw = (int)lroundf(width * w->scale);
  w->ph = (int)lroundf(height * w->scale);
  w->canvas = tvg_swcanvas_create(TVG_ENGINE_OPTION_DEFAULT);
  w->pixels = malloc((size_t)w->pw * w->ph * 4);
  tvg_swcanvas_set_target(w->canvas, w->pixels, w->pw, w->pw, w->ph, TVG_COLORSPACE_ARGB8888);
  return lean_io_result_mk_ok(lean_alloc_external(window_class, w));
}

// Points to pixels.
LEAN_EXPORT lean_obj_res puri_window_scale(b_lean_obj_arg win, lean_obj_arg world) {
  return lean_io_result_mk_ok(lean_box_float(scale_of(window_of(win))));
}

// The window's size in points, width in the high half, height in the low.
LEAN_EXPORT lean_obj_res puri_window_size(b_lean_obj_arg win, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  int width, height;
  if (w->window) SDL_GetWindowSize(w->window, &width, &height);
  else { width = (int)lroundf(w->pw / w->scale); height = (int)lroundf(w->ph / w->scale); }
  return lean_io_result_mk_ok(lean_box_uint64(((uint64_t)(uint32_t)width << 32) | (uint32_t)height));
}

LEAN_EXPORT lean_obj_res puri_window_set_title(b_lean_obj_arg win, b_lean_obj_arg title, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  if (w->window) SDL_SetWindowTitle(w->window, lean_string_cstr(title));
  return io_unit();
}

// Events
// ------
// Five words per event: kind, then four arguments (floats as their bits).

enum { EV_QUIT = 1, EV_MOVE, EV_DOWN, EV_UP, EV_KEY_DOWN, EV_KEY_UP, EV_TEXT, EV_RESIZED, EV_WHEEL, EV_EXPOSED, EV_LEAVE };

static uint32_t fbits(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }

static lean_object* push(lean_object* arr, uint32_t k, uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
  arr = lean_array_push(arr, lean_box_uint32(k));
  arr = lean_array_push(arr, lean_box_uint32(a));
  arr = lean_array_push(arr, lean_box_uint32(b));
  arr = lean_array_push(arr, lean_box_uint32(c));
  return lean_array_push(arr, lean_box_uint32(d));
}

// A resize, with the window's size in points.
static lean_object* push_size(lean_object* arr, SDL_WindowID id) {
  int w = 0, h = 0;
  SDL_Window* win = SDL_GetWindowFromID(id);
  if (win) SDL_GetWindowSize(win, &w, &h);
  return push(arr, EV_RESIZED, (uint32_t)w, (uint32_t)h, 0, 0);
}

static lean_object* encode(lean_object* arr, SDL_Event* e) {
  switch (e->type) {
    case SDL_EVENT_QUIT:
    case SDL_EVENT_WINDOW_CLOSE_REQUESTED:
      return push(arr, EV_QUIT, 0, 0, 0, 0);
    case SDL_EVENT_MOUSE_MOTION:
      return push(arr, EV_MOVE, fbits(e->motion.x), fbits(e->motion.y), 0, 0);
    case SDL_EVENT_MOUSE_BUTTON_DOWN:
      return push(arr, EV_DOWN, fbits(e->button.x), fbits(e->button.y), e->button.button, 0);
    case SDL_EVENT_MOUSE_BUTTON_UP:
      return push(arr, EV_UP, fbits(e->button.x), fbits(e->button.y), e->button.button, 0);
    case SDL_EVENT_KEY_DOWN:
      return push(arr, EV_KEY_DOWN, e->key.key, e->key.repeat, e->key.mod, 0);
    case SDL_EVENT_KEY_UP:
      return push(arr, EV_KEY_UP, e->key.key, 0, e->key.mod, 0);
    case SDL_EVENT_TEXT_INPUT: {
      // The text's UTF-8 bytes, four per word after a header with its length.
      size_t n = strlen(e->text.text);
      arr = push(arr, EV_TEXT, (uint32_t)n, 0, 0, 0);
      for (size_t i = 0; i < n; i += 4) {
        uint32_t word = 0;
        for (size_t j = 0; j < 4 && i + j < n; j++) word |= (uint32_t)(uint8_t)e->text.text[i + j] << (8 * j);
        arr = lean_array_push(arr, lean_box_uint32(word));
      }
      return arr;
    }
    case SDL_EVENT_WINDOW_RESIZED:
    case SDL_EVENT_WINDOW_PIXEL_SIZE_CHANGED:
    case SDL_EVENT_WINDOW_DISPLAY_SCALE_CHANGED:
      return push_size(arr, e->window.windowID);
    // The renderer lost its textures: everything retained must be drawn
    // again, as after a resize.
    case SDL_EVENT_RENDER_TARGETS_RESET:
    case SDL_EVENT_RENDER_DEVICE_RESET:
      return push_size(arr, e->render.windowID);
    case SDL_EVENT_WINDOW_MOUSE_LEAVE:
      return push(arr, EV_LEAVE, 0, 0, 0, 0);
    case SDL_EVENT_WINDOW_EXPOSED:
      return push(arr, EV_EXPOSED, 0, 0, 0, 0);
    case SDL_EVENT_MOUSE_WHEEL:
      return push(arr, EV_WHEEL, fbits(e->wheel.mouse_x), fbits(e->wheel.mouse_y), fbits(e->wheel.x), fbits(e->wheel.y));
    default:
      return arr;
  }
}

// Waits up to timeout_ms for events (a negative timeout waits without a
// deadline), then drains what has arrived.
LEAN_EXPORT lean_obj_res puri_window_wait(b_lean_obj_arg win, int32_t timeout_ms, lean_obj_arg world) {
  lean_object* arr = lean_mk_empty_array();
  SDL_Event e;
  if (SDL_WaitEventTimeout(&e, timeout_ms)) {
    arr = encode(arr, &e);
    while (SDL_PollEvent(&e)) arr = encode(arr, &e);
  }
  return lean_io_result_mk_ok(arr);
}

// Shapes
// ------

static void color(uint32_t rgba, uint8_t* r, uint8_t* g, uint8_t* b, uint8_t* a) {
  *r = rgba >> 24; *g = rgba >> 16; *b = rgba >> 8; *a = rgba;
}

// 0xRRGGBBAA as a premultiplied ARGB8888 pixel.
static uint32_t pixel(uint32_t rgba) {
  uint32_t r = rgba >> 24, g = (rgba >> 16) & 0xff, b = (rgba >> 8) & 0xff, a = rgba & 0xff;
  r = r * a / 255; g = g * a / 255; b = b * a / 255;
  return (a << 24) | (r << 16) | (g << 8) | b;
}

static void add_round_rect(Tvg_Paint scene, float x, float y, float wd, float ht, float rad, uint32_t rgba) {
  uint8_t r, g, b, a;
  color(rgba, &r, &g, &b, &a);
  Tvg_Paint s = tvg_shape_new();
  tvg_shape_append_rect(s, x, y, wd, ht, rad, rad, true);
  tvg_shape_set_fill_color(s, r, g, b, a);
  tvg_scene_add(scene, s);
}

static void add_text(Tvg_Paint scene, float x, float y, float size, uint32_t rgba, const char* str) {
  uint8_t r, g, b, a;
  color(rgba, &r, &g, &b, &a);
  Tvg_Paint t = tvg_text_new();
  tvg_text_set_font(t, NULL);
  tvg_text_set_size(t, size);
  tvg_text_set_text(t, str);
  tvg_text_set_color(t, r, g, b);
  tvg_paint_set_opacity(t, a);
  tvg_paint_translate(t, x, y);
  tvg_scene_add(scene, t);
}

// Frames
// ------

// Starts a frame at the window's current size, cleared to bg (0xRRGGBBAA).
LEAN_EXPORT lean_obj_res puri_frame_begin(b_lean_obj_arg win, uint32_t bg, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  if (!fit_target(w)) return io_error("the window's frame");
  tvg_canvas_remove(w->canvas, NULL);
  w->root = tvg_scene_new();
  float s = scale_of(w);
  tvg_paint_scale(w->root, s);
  add_round_rect(w->root, 0, 0, w->pw / s, w->ph / s, 0, bg);
  return io_unit();
}

// A rectangle with rounded corners of radius rad, in points.
LEAN_EXPORT lean_obj_res puri_fill_round_rect(b_lean_obj_arg win, double x, double y, double wd, double ht,
                                              double rad, uint32_t rgba, lean_obj_arg world) {
  add_round_rect(window_of(win)->root, (float)x, (float)y, (float)wd, (float)ht, (float)rad, rgba);
  return io_unit();
}

// A line of text with its top-left corner at (x, y), in points.
LEAN_EXPORT lean_obj_res puri_fill_text(b_lean_obj_arg win, double x, double y, double size, uint32_t rgba,
                                        b_lean_obj_arg str, lean_obj_arg world) {
  add_text(window_of(win)->root, (float)x, (float)y, (float)size, rgba, lean_string_cstr(str));
  return io_unit();
}

// Draws the frame, and on a window, hands it to the renderer; `show` shows it.
LEAN_EXPORT lean_obj_res puri_frame_end(b_lean_obj_arg win, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  tvg_canvas_add(w->canvas, w->root);
  tvg_canvas_update(w->canvas);
  tvg_canvas_draw(w->canvas, true);
  tvg_canvas_sync(w->canvas);
  if (w->window) {
    SDL_UpdateTexture(w->texture, NULL, w->pixels, w->pw * 4);
    SDL_RenderTexture(w->renderer, w->texture, NULL, NULL);
  }
  return io_unit();
}

// Shows what the renderer has, waiting for the display's next refresh.
LEAN_EXPORT lean_obj_res puri_window_show(b_lean_obj_arg win, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  if (w->window) SDL_RenderPresent(w->renderer);
  return io_unit();
}

LEAN_EXPORT lean_obj_res puri_font_load(b_lean_obj_arg path, lean_obj_arg world) {
  return lean_io_result_mk_ok(lean_box(tvg_font_load(lean_string_cstr(path)) == TVG_RESULT_SUCCESS));
}

// Rows
// ----

typedef struct {
  int32_t top;       // in points, before the rows' translation
  SDL_Texture* tex;  // on a window: the row's pixels
  uint32_t* px;      // offscreen: the row's pixels
  int pw, ph;        // the row's size in pixels
} Row;

typedef struct {
  lean_object* owner;  // the window, kept alive as long as these rows
  PuriWindow* win;
  Row* rows;
  size_t n, cap;
  int32_t base;        // added to every row's top: the translation
  uint32_t bg;
  Tvg_Canvas canvas;   // draws one row at a time
  Tvg_Paint pending;   // the row being painted, until it is inserted or updated
  int32_t pending_h;   // its height, in points
  uint32_t* scratch;   // on a window, pixels for drawing a row before upload
  size_t scratch_cap;
  uint64_t drawn;      // rows drawn so far
} PuriRows;

static void row_free(Row* r) {
  if (r->tex) SDL_DestroyTexture(r->tex);
  free(r->px);
  r->tex = NULL; r->px = NULL;
}

static void rows_finalize(void* p) {
  PuriRows* r = p;
  for (size_t i = 0; i < r->n; i++) row_free(&r->rows[i]);
  free(r->rows);
  if (r->pending) tvg_paint_rel(r->pending);
  if (r->canvas) tvg_canvas_destroy(r->canvas);
  free(r->scratch);
  lean_dec(r->owner);
  free(r);
}

static lean_external_class* rows_class = NULL;

static PuriRows* rows_of(b_lean_obj_arg r) { return (PuriRows*)lean_get_external_data(r); }

// Rows shown in a window, on a background of bg.
LEAN_EXPORT lean_obj_res puri_rows_new(b_lean_obj_arg win, uint32_t bg, lean_obj_arg world) {
  if (rows_class == NULL) rows_class = lean_register_external_class(rows_finalize, no_foreach);
  PuriRows* r = calloc(1, sizeof *r);
  lean_inc(win);
  r->owner = (lean_object*)win;
  r->win = window_of(win);
  r->bg = bg;
  r->canvas = tvg_swcanvas_create(TVG_ENGINE_OPTION_DEFAULT);
  return lean_io_result_mk_ok(lean_alloc_external(rows_class, r));
}

// Starts painting a row height points tall, on the background.
LEAN_EXPORT lean_obj_res puri_rows_begin(b_lean_obj_arg rows, uint32_t height, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  if (!fit_target(r->win)) return io_error("the window's frame");
  if (r->pending) tvg_paint_rel(r->pending);
  float s = scale_of(r->win);
  r->pending = tvg_scene_new();
  tvg_paint_scale(r->pending, s);
  r->pending_h = (int32_t)height;
  // The background covers every pixel of the row, which is ceil(height * s)
  // pixels tall, so at a fractional scale its last line isn't left clear.
  add_round_rect(r->pending, 0, 0, r->win->pw / s, ceilf(height * s) / s, 0, r->bg);
  return io_unit();
}

LEAN_EXPORT lean_obj_res puri_rows_fill_round_rect(b_lean_obj_arg rows, double x, double y, double wd, double ht,
                                                   double rad, uint32_t rgba, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  if (r->pending) add_round_rect(r->pending, (float)x, (float)y, (float)wd, (float)ht, (float)rad, rgba);
  return io_unit();
}

LEAN_EXPORT lean_obj_res puri_rows_fill_text(b_lean_obj_arg rows, double x, double y, double size, uint32_t rgba,
                                             b_lean_obj_arg str, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  if (r->pending) add_text(r->pending, (float)x, (float)y, (float)size, rgba, lean_string_cstr(str));
  return io_unit();
}

// Draws the pending row into its own pixels: a texture on a window, memory
// offscreen. The row keeps no top; the caller sets it. Sets *ok to 0 if the
// pixels couldn't be had.
static Row rows_draw(PuriRows* r, int* ok) {
  Row row = {0};
  *ok = 1;
  PuriWindow* w = r->win;
  int pw = w->pw;
  int ph = (int)ceilf(r->pending_h * scale_of(w));
  if (!r->pending || pw <= 0 || ph <= 0) {
    if (r->pending) tvg_paint_rel(r->pending);
    r->pending = NULL;
    return row;
  }
  size_t need = (size_t)pw * ph;
  uint32_t* px;
  if (w->window) {
    if (r->scratch_cap < need) {
      free(r->scratch);
      r->scratch = malloc(need * 4);
      r->scratch_cap = r->scratch ? need : 0;
    }
    px = r->scratch;
  } else {
    px = malloc(need * 4);
  }
  if (!px) {
    tvg_paint_rel(r->pending);
    r->pending = NULL;
    *ok = 0;
    return row;
  }
  tvg_swcanvas_set_target(r->canvas, px, pw, pw, ph, TVG_COLORSPACE_ARGB8888);
  tvg_canvas_add(r->canvas, r->pending);
  tvg_canvas_update(r->canvas);
  tvg_canvas_draw(r->canvas, true);
  tvg_canvas_sync(r->canvas);
  tvg_canvas_remove(r->canvas, NULL);
  r->pending = NULL;
  r->drawn++;
  row.pw = pw; row.ph = ph;
  if (w->window) {
    row.tex = SDL_CreateTexture(w->renderer, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STATIC, pw, ph);
    if (!row.tex) { *ok = 0; return row; }
    SDL_SetTextureBlendMode(row.tex, SDL_BLENDMODE_NONE);
    SDL_UpdateTexture(row.tex, NULL, px, pw * 4);
  } else {
    row.px = px;
  }
  return row;
}

// The pending row enters at position k with its top at top (points). Past
// the end, it is appended.
LEAN_EXPORT lean_obj_res puri_rows_insert(b_lean_obj_arg rows, uint32_t k, int32_t top, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  int ok;
  Row row = rows_draw(r, &ok);
  row.top = top - r->base;
  if (r->n == r->cap) {
    size_t cap = r->cap ? r->cap * 2 : 64;
    Row* rows2 = realloc(r->rows, cap * sizeof(Row));
    if (!rows2) { row_free(&row); return io_error("placing a row"); }
    r->rows = rows2;
    r->cap = cap;
  }
  size_t at = k < r->n ? k : r->n;
  memmove(&r->rows[at + 1], &r->rows[at], (r->n - at) * sizeof(Row));
  r->rows[at] = row;
  r->n++;
  // The row is placed even without its pixels, so positions stay right.
  return ok ? io_unit() : io_error("drawing a row");
}

// The row at position k becomes the pending row, keeping its top.
LEAN_EXPORT lean_obj_res puri_rows_update(b_lean_obj_arg rows, uint32_t k, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  if (k >= r->n) {
    if (r->pending) tvg_paint_rel(r->pending);
    r->pending = NULL;
    return io_unit();
  }
  int ok;
  Row row = rows_draw(r, &ok);
  row.top = r->rows[k].top;
  row_free(&r->rows[k]);
  r->rows[k] = row;
  return ok ? io_unit() : io_error("drawing a row");
}

// The row at position k leaves.
LEAN_EXPORT lean_obj_res puri_rows_delete(b_lean_obj_arg rows, uint32_t k, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  if (k < r->n) {
    row_free(&r->rows[k]);
    memmove(&r->rows[k], &r->rows[k + 1], (r->n - k - 1) * sizeof(Row));
    r->n--;
  }
  return io_unit();
}

// The rows from position k on move down by dy points.
LEAN_EXPORT lean_obj_res puri_rows_shift(b_lean_obj_arg rows, uint32_t k, int32_t dy, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  for (size_t i = k; i < r->n; i++) r->rows[i].top += dy;
  return io_unit();
}

// Every row moves down by dy points.
LEAN_EXPORT lean_obj_res puri_rows_translate(b_lean_obj_arg rows, int32_t dy, lean_obj_arg world) {
  rows_of(rows)->base += dy;
  return io_unit();
}

// Every row leaves.
LEAN_EXPORT lean_obj_res puri_rows_clear(b_lean_obj_arg rows, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  for (size_t i = 0; i < r->n; i++) row_free(&r->rows[i]);
  r->n = 0;
  r->base = 0;
  return io_unit();
}

// The rows' tops, in points, for checking them against the drawing.
LEAN_EXPORT lean_obj_res puri_rows_tops(b_lean_obj_arg rows, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  lean_object* arr = lean_mk_empty_array();
  for (size_t i = 0; i < r->n; i++) arr = lean_array_push(arr, lean_box_uint32((uint32_t)(r->base + r->rows[i].top)));
  return lean_io_result_mk_ok(arr);
}

// How many rows have been drawn into pixels so far.
LEAN_EXPORT lean_obj_res puri_rows_drawn(b_lean_obj_arg rows, lean_obj_arg world) {
  return lean_io_result_mk_ok(lean_box_uint64(rows_of(rows)->drawn));
}

static void fill_px(PuriWindow* w, int x0, int y0, int x1, int y1, uint32_t p) {
  if (x0 < 0) x0 = 0;
  if (y0 < 0) y0 = 0;
  if (x1 > w->pw) x1 = w->pw;
  if (y1 > w->ph) y1 = w->ph;
  for (int y = y0; y < y1; y++) {
    uint32_t* line = w->pixels + (size_t)y * w->pw;
    for (int x = x0; x < x1; x++) line[x] = p;
  }
}

// Composites the rows at their tops on the background, and a bar (the scroll
// bar's thumb, in points) over them, for `show` to show.
LEAN_EXPORT lean_obj_res puri_rows_compose(b_lean_obj_arg rows, double bx, double by, double bw, double bh,
                                           uint32_t bar, lean_obj_arg world) {
  PuriRows* r = rows_of(rows);
  PuriWindow* w = r->win;
  float s = scale_of(w);
  if (w->window) {
    if (!fit_target(w)) return io_error("the window's frame");
    uint8_t cr, cg, cb, ca;
    color(r->bg, &cr, &cg, &cb, &ca);
    SDL_SetRenderDrawColor(w->renderer, cr, cg, cb, ca);
    SDL_RenderClear(w->renderer);
    for (size_t i = 0; i < r->n; i++) {
      Row* row = &r->rows[i];
      if (!row->tex) continue;
      SDL_FRect dst = {0, (float)lroundf((r->base + row->top) * s), (float)row->pw, (float)row->ph};
      if (dst.y + dst.h <= 0 || dst.y >= w->ph) continue;
      SDL_RenderTexture(w->renderer, row->tex, NULL, &dst);
    }
    color(bar, &cr, &cg, &cb, &ca);
    SDL_SetRenderDrawColor(w->renderer, cr, cg, cb, ca);
    SDL_FRect thumb = {(float)lround(bx * s), (float)lround(by * s), (float)lround(bw * s), (float)lround(bh * s)};
    SDL_RenderFillRect(w->renderer, &thumb);
  } else {
    fill_px(w, 0, 0, w->pw, w->ph, pixel(r->bg));
    for (size_t i = 0; i < r->n; i++) {
      Row* row = &r->rows[i];
      if (!row->px) continue;
      int y0 = (int)lroundf((r->base + row->top) * s);
      int from = y0 < 0 ? -y0 : 0;
      int to = y0 + row->ph > w->ph ? w->ph - y0 : row->ph;
      int width = row->pw < w->pw ? row->pw : w->pw;
      for (int y = from; y < to; y++)
        memcpy(w->pixels + (size_t)(y0 + y) * w->pw, row->px + (size_t)y * row->pw, (size_t)width * 4);
    }
    fill_px(w, (int)lround(bx * s), (int)lround(by * s), (int)lround((bx + bw) * s), (int)lround((by + bh) * s),
            pixel(bar));
  }
  return io_unit();
}

// Checking and measuring
// ----------------------

// How two offscreen targets' last frames differ: the largest difference in
// any channel of any pixel (0 to 255) in the top byte, and how many pixels
// differ in the rest; or 2^64 - 1 if their sizes differ.
LEAN_EXPORT lean_obj_res puri_window_diff(b_lean_obj_arg a, b_lean_obj_arg b, lean_obj_arg world) {
  PuriWindow* x = window_of(a);
  PuriWindow* y = window_of(b);
  if (x->pw != y->pw || x->ph != y->ph) return lean_io_result_mk_ok(lean_box_uint64(UINT64_MAX));
  uint64_t n = 0, most = 0;
  size_t count = (size_t)x->pw * x->ph;
  for (size_t i = 0; i < count; i++) {
    uint32_t p = x->pixels[i], q = y->pixels[i];
    if (p == q) continue;
    n++;
    for (int c = 0; c < 32; c += 8) {
      int d = (int)((p >> c) & 0xff) - (int)((q >> c) & 0xff);
      if (d < 0) d = -d;
      if ((uint64_t)d > most) most = d;
    }
  }
  return lean_io_result_mk_ok(lean_box_uint64((most << 56) | n));
}

// Writes an offscreen target's last frame as a binary PPM.
LEAN_EXPORT lean_obj_res puri_window_save_ppm(b_lean_obj_arg win, b_lean_obj_arg path, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  FILE* f = fopen(lean_string_cstr(path), "wb");
  if (!f) return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("can't write the image")));
  fprintf(f, "P6\n%d %d\n255\n", w->pw, w->ph);
  for (size_t i = 0; i < (size_t)w->pw * w->ph; i++) {
    uint32_t p = w->pixels[i];
    unsigned char rgb[3] = {(unsigned char)(p >> 16), (unsigned char)(p >> 8), (unsigned char)p};
    fwrite(rgb, 1, 3, f);
  }
  fclose(f);
  return io_unit();
}

// Under callgrind, zeroes its counts, and dumps them as a part named name.
// Without valgrind, these do nothing.
LEAN_EXPORT lean_obj_res puri_callgrind_zero(lean_obj_arg world) {
  CALLGRIND_ZERO_STATS;
  return io_unit();
}

LEAN_EXPORT lean_obj_res puri_callgrind_dump(b_lean_obj_arg name, lean_obj_arg world) {
  CALLGRIND_DUMP_STATS_AT(lean_string_cstr(name));
  return io_unit();
}

// The monotonic clock in nanoseconds, read after x has been computed: taking
// x keeps the compiler from moving x's computation past the reading.
LEAN_EXPORT lean_obj_res puri_clock_after(b_lean_obj_arg x, lean_obj_arg world) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec));
}

// For checking the window code with no display: makes the next window use
// SDL's offscreen video driver and its software renderer.
LEAN_EXPORT lean_obj_res puri_use_offscreen_video(lean_obj_arg world) {
  SDL_SetHint(SDL_HINT_VIDEO_DRIVER, "offscreen");
  SDL_SetHint(SDL_HINT_RENDER_DRIVER, "software");
  return io_unit();
}

// Reads back what a window's renderer holds, before `show`, into the window's
// frame pixels, so `diff` can compare it with an offscreen target's.
LEAN_EXPORT lean_obj_res puri_window_read_back(b_lean_obj_arg win, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  if (!w->window) return io_unit();
  if (!fit_target(w)) return io_error("the window's frame");
  SDL_Surface* s = SDL_RenderReadPixels(w->renderer, NULL);
  if (!s) return io_error("SDL_RenderReadPixels");
  SDL_Surface* c = SDL_ConvertSurface(s, SDL_PIXELFORMAT_ARGB8888);
  SDL_DestroySurface(s);
  if (!c) return io_error("SDL_ConvertSurface");
  int h = c->h < w->ph ? c->h : w->ph;
  int wd = c->w < w->pw ? c->w : w->pw;
  for (int y = 0; y < h; y++) memcpy(w->pixels + (size_t)y * w->pw, (uint8_t*)c->pixels + (size_t)y * c->pitch, (size_t)wd * 4);
  SDL_DestroySurface(c);
  return io_unit();
}
