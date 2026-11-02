// The platform bridge: an SDL3 window whose frames ThorVG draws on the CPU.
//
// The window is a Lean external object. Coordinates crossing the bridge are
// logical points; the bridge scales drawing by the window's pixel density, so
// a 2x display gets sharp output. Events come back as flat UInt32 words, five
// per event, and Lean decodes them (Platform.lean), so policy stays in Lean.

#include <lean/lean.h>
#include <SDL3/SDL.h>
#include <thorvg_capi.h>
#include <string.h>

typedef struct {
  SDL_Window* window;
  SDL_Renderer* renderer;
  SDL_Texture* texture;
  Tvg_Canvas canvas;
  Tvg_Paint root;     // this frame's scene, scaled from points to pixels
  uint32_t* pixels;
  int pw, ph;         // the target's size in pixels
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

static void window_foreach(void* p, b_lean_obj_arg f) {}

static lean_external_class* window_class = NULL;

static lean_obj_res io_error(const char* what) {
  char msg[512];
  snprintf(msg, sizeof msg, "%s: %s", what, SDL_GetError());
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static PuriWindow* window_of(b_lean_obj_arg w) {
  return (PuriWindow*)lean_get_external_data(w);
}

LEAN_EXPORT lean_obj_res puri_window_open(b_lean_obj_arg title, uint32_t width, uint32_t height,
                                          lean_obj_arg world) {
  if (window_class == NULL) {
    SDL_SetMainReady();
    if (!SDL_Init(SDL_INIT_VIDEO)) return io_error("SDL_Init");
    if (tvg_engine_init(0) != TVG_RESULT_SUCCESS) {
      return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("tvg_engine_init failed")));
    }
    window_class = lean_register_external_class(window_finalize, window_foreach);
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

// Points to pixels.
LEAN_EXPORT lean_obj_res puri_window_scale(b_lean_obj_arg win, lean_obj_arg world) {
  return lean_io_result_mk_ok(lean_box_float(SDL_GetWindowPixelDensity(window_of(win)->window)));
}

// Events
// ------
// Five words per event: kind, then four arguments (floats as their bits).

enum { EV_QUIT = 1, EV_MOVE, EV_DOWN, EV_UP, EV_KEY_DOWN, EV_KEY_UP, EV_TEXT, EV_RESIZED, EV_WHEEL, EV_EXPOSED };

static uint32_t fbits(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }

static lean_object* push(lean_object* arr, uint32_t k, uint32_t a, uint32_t b, uint32_t c, uint32_t d) {
  arr = lean_array_push(arr, lean_box_uint32(k));
  arr = lean_array_push(arr, lean_box_uint32(a));
  arr = lean_array_push(arr, lean_box_uint32(b));
  arr = lean_array_push(arr, lean_box_uint32(c));
  return lean_array_push(arr, lean_box_uint32(d));
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
    case SDL_EVENT_WINDOW_DISPLAY_SCALE_CHANGED: {
      int w, h;
      SDL_GetWindowSize(SDL_GetWindowFromID(e->window.windowID), &w, &h);
      return push(arr, EV_RESIZED, (uint32_t)w, (uint32_t)h, 0, 0);
    }
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

// Drawing
// -------

static void color(uint32_t rgba, uint8_t* r, uint8_t* g, uint8_t* b, uint8_t* a) {
  *r = rgba >> 24; *g = rgba >> 16; *b = rgba >> 8; *a = rgba;
}

// Starts a frame at the window's current size, cleared to bg (0xRRGGBBAA).
LEAN_EXPORT lean_obj_res puri_frame_begin(b_lean_obj_arg win, uint32_t bg, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  int pw, ph;
  SDL_GetWindowSizeInPixels(w->window, &pw, &ph);
  if (pw != w->pw || ph != w->ph || w->pixels == NULL) {
    free(w->pixels);
    if (w->texture) SDL_DestroyTexture(w->texture);
    w->pw = pw; w->ph = ph;
    w->pixels = malloc((size_t)pw * ph * 4);
    w->texture = SDL_CreateTexture(w->renderer, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STREAMING, pw, ph);
    tvg_swcanvas_set_target(w->canvas, w->pixels, pw, pw, ph, TVG_COLORSPACE_ARGB8888);
  }
  tvg_canvas_remove(w->canvas, NULL);
  w->root = tvg_scene_new();
  tvg_paint_scale(w->root, SDL_GetWindowPixelDensity(w->window));
  uint8_t r, g, b, a;
  color(bg, &r, &g, &b, &a);
  Tvg_Paint back = tvg_shape_new();
  tvg_shape_append_rect(back, 0, 0, (float)pw, (float)ph, 0, 0, true);
  tvg_shape_set_fill_color(back, r, g, b, a);
  tvg_scene_add(w->root, back);
  return lean_io_result_mk_ok(lean_box(0));
}

// A rectangle with rounded corners of radius rad, in points.
LEAN_EXPORT lean_obj_res puri_fill_round_rect(b_lean_obj_arg win, double x, double y, double wd, double ht,
                                              double rad, uint32_t rgba, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  uint8_t r, g, b, a;
  color(rgba, &r, &g, &b, &a);
  Tvg_Paint s = tvg_shape_new();
  tvg_shape_append_rect(s, (float)x, (float)y, (float)wd, (float)ht, (float)rad, (float)rad, true);
  tvg_shape_set_fill_color(s, r, g, b, a);
  tvg_scene_add(w->root, s);
  return lean_io_result_mk_ok(lean_box(0));
}

// A line of text with its top-left corner at (x, y), in points.
LEAN_EXPORT lean_obj_res puri_fill_text(b_lean_obj_arg win, double x, double y, double size, uint32_t rgba,
                                        b_lean_obj_arg str, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  uint8_t r, g, b, a;
  color(rgba, &r, &g, &b, &a);
  Tvg_Paint t = tvg_text_new();
  tvg_text_set_font(t, NULL);
  tvg_text_set_size(t, (float)size);
  tvg_text_set_text(t, lean_string_cstr(str));
  tvg_text_set_color(t, r, g, b);
  tvg_paint_set_opacity(t, a);
  tvg_paint_translate(t, (float)x, (float)y);
  tvg_scene_add(w->root, t);
  return lean_io_result_mk_ok(lean_box(0));
}

// Draws the frame and shows it.
LEAN_EXPORT lean_obj_res puri_frame_present(b_lean_obj_arg win, lean_obj_arg world) {
  PuriWindow* w = window_of(win);
  tvg_canvas_add(w->canvas, w->root);
  tvg_canvas_update(w->canvas);
  tvg_canvas_draw(w->canvas, true);
  tvg_canvas_sync(w->canvas);
  SDL_UpdateTexture(w->texture, NULL, w->pixels, w->pw * 4);
  SDL_RenderTexture(w->renderer, w->texture, NULL, NULL);
  SDL_RenderPresent(w->renderer);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res puri_font_load(b_lean_obj_arg path, lean_obj_arg world) {
  return lean_io_result_mk_ok(lean_box(tvg_font_load(lean_string_cstr(path)) == TVG_RESULT_SUCCESS));
}
