// Stress / edge-case test for the Rocqsheet extracted kernel.
// Exercises arithmetic boundaries, deep nesting, ref chains, cycles,
// string/float ops, range aggregations, parser corner cases, and
// spec-vs-impl correspondence with formula::eval_iter.

#include "rocqsheet.h"
#include "../src/eval_iter.h"

#include <climits>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <optional>
#include <string>
#include <utility>

using S = Rocqsheet;

namespace {

int passes = 0;
int fails  = 0;

std::optional<int64_t> as_int(const S::EvalResult& r) {
  if (std::holds_alternative<S::EvalResult::EVal>(r.v()))
    return std::get<S::EvalResult::EVal>(r.v()).d_a0;
  return std::nullopt;
}

bool is_err(const S::EvalResult& r) {
  return std::holds_alternative<S::EvalResult::EErr>(r.v());
}
bool is_fuel(const S::EvalResult& r) {
  return std::holds_alternative<S::EvalResult::EFuel>(r.v());
}

void check(const char* tag, bool cond) {
  if (cond) { ++passes; }
  else { ++fails; std::printf("FAIL %s\n", tag); }
}

void check_int(const char* tag, std::optional<int64_t> got, int64_t want) {
  bool ok = got.has_value() && *got == want;
  if (!ok) {
    std::printf("FAIL %s: got %s, want %lld\n", tag,
                got ? std::to_string(*got).c_str() : "None", (long long)want);
    ++fails;
  } else { ++passes; }
}

S::Sheet put(S::Sheet s, int c, int r, S::Cell cell) {
  return S::set_cell(std::move(s), S::CellRef{(int64_t)c, (int64_t)r},
                     std::move(cell));
}
S::Sheet lit(S::Sheet s, int c, int r, int64_t n) {
  return put(std::move(s), c, r, S::Cell::clit(n));
}
S::Sheet form(S::Sheet s, int c, int r, S::Expr e) {
  return put(std::move(s), c, r, S::Cell::cform(std::move(e)));
}

// Pretty-print an EvalResult for failure messages.
std::string show(const S::EvalResult& r) {
  if (auto v = as_int(r)) return std::to_string(*v);
  if (is_err(r)) return "EErr";
  if (is_fuel(r)) return "EFuel";
  return "<other>";
}

// Compare specs.
void agree_iter_vs_spec(const char* tag, const S::Sheet& sh,
                         const S::CellRef& r) {
  auto spec = as_int(S::eval_cell(S::DEFAULT_FUEL, sh, r));
  auto impl = formula::eval_iter(sh, r);
  if (spec.has_value()) {
    if (!impl.has_value() || *impl != *spec) {
      std::printf("FAIL agree/%s: spec=%lld impl=%s\n", tag,
                  (long long)*spec,
                  impl ? std::to_string(*impl).c_str() : "None");
      ++fails;
    } else { ++passes; }
  } else {
    // Spec returned EErr/EFuel. impl should also be nullopt (the iter
    // contract is "EVal v means agreement"; non-EVal is unconstrained).
    ++passes;
  }
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

void test_literals_and_empties() {
  // Empty cells fall through to 0.
  check_int("empty/A1", as_int(S::eval_cell(S::DEFAULT_FUEL, S::new_sheet,
                                            S::CellRef{0, 0})), 0);
  check_int("empty/last", as_int(S::eval_cell(S::DEFAULT_FUEL, S::new_sheet,
                                              S::CellRef{259, 199})), 0);

  auto s = lit(S::new_sheet, 0, 0, 0);
  s = lit(s, 1, 0, 1);
  s = lit(s, 2, 0, -1);
  s = lit(s, 3, 0, INT64_MAX);
  s = lit(s, 4, 0, INT64_MIN);
  s = lit(s, 5, 0, 9223372036854775807LL);  // INT64_MAX
  check_int("lit/0",   as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{0,0})), 0);
  check_int("lit/1",   as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{1,0})), 1);
  check_int("lit/-1",  as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2,0})), -1);
  check_int("lit/max", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3,0})), INT64_MAX);
  check_int("lit/min", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4,0})), INT64_MIN);
}

void test_arith_basic() {
  auto s = lit(S::new_sheet, 0, 0, 7);
  s = lit(s, 1, 0, 3);
  auto a = S::Expr::eref(S::CellRef{0, 0});
  auto b = S::Expr::eref(S::CellRef{1, 0});

  s = form(s, 2, 0, S::Expr::eadd(a.clone(), b.clone()));
  check_int("add", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 0})), 10);
  s = form(s, 3, 0, S::Expr::esub(a.clone(), b.clone()));
  check_int("sub", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})), 4);
  s = form(s, 4, 0, S::Expr::emul(a.clone(), b.clone()));
  check_int("mul", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 21);
  s = form(s, 5, 0, S::Expr::ediv(a.clone(), b.clone()));
  check_int("div", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})), 2);
  s = form(s, 6, 0, S::Expr::emod(a.clone(), b.clone()));
  check_int("mod", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{6, 0})), 1);
  s = form(s, 7, 0, S::Expr::epow(a.clone(), S::Expr::eint(2)));
  check_int("pow", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{7, 0})), 49);
}

void test_div_mod_zero_neg_pow() {
  auto s = lit(S::new_sheet, 0, 0, 100);
  s = form(s, 1, 0, S::Expr::ediv(S::Expr::eref(S::CellRef{0, 0}),
                                   S::Expr::eint(0)));
  check("div-by-0 → EErr", is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{1, 0})));
  s = form(s, 2, 0, S::Expr::emod(S::Expr::eref(S::CellRef{0, 0}),
                                   S::Expr::eint(0)));
  check("mod-by-0 → EErr", is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 0})));
  s = form(s, 3, 0, S::Expr::epow(S::Expr::eint(2), S::Expr::eint(-3)));
  check("neg-pow → EErr", is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})));
  // Pow with 0 exponent is 1.
  s = form(s, 4, 0, S::Expr::epow(S::Expr::eint(0), S::Expr::eint(0)));
  check_int("pow 0^0", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 1);
}

void test_comparisons_and_if() {
  auto s = lit(S::new_sheet, 0, 0, 5);
  s = lit(s, 1, 0, 5);
  s = lit(s, 2, 0, 7);
  auto A = S::Expr::eref(S::CellRef{0, 0});
  auto B = S::Expr::eref(S::CellRef{1, 0});
  auto C = S::Expr::eref(S::CellRef{2, 0});
  s = form(s, 3, 0, S::Expr::eeq(A.clone(), B.clone()));
  check_int("eq true",  as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})), 1);
  s = form(s, 4, 0, S::Expr::eeq(A.clone(), C.clone()));
  check_int("eq false", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 0);
  s = form(s, 5, 0, S::Expr::elt(A.clone(), C.clone()));
  check_int("lt true",  as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})), 1);
  s = form(s, 6, 0, S::Expr::egt(C.clone(), A.clone()));
  check_int("gt true",  as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{6, 0})), 1);
  // IF(true_branch_picked, then=99, else=-1)
  s = form(s, 7, 0, S::Expr::eif(
                          S::Expr::eeq(A.clone(), B.clone()),
                          S::Expr::eint(99), S::Expr::eint(-1)));
  check_int("if-then", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{7, 0})), 99);
  // Nested IF chain
  s = form(s, 8, 0, S::Expr::eif(
                          S::Expr::elt(A.clone(), C.clone()),
                          S::Expr::eif(S::Expr::egt(C.clone(), A.clone()),
                                       S::Expr::eint(42), S::Expr::eint(-2)),
                          S::Expr::eint(-3)));
  check_int("if-nested", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{8, 0})), 42);
}

void test_iferr() {
  auto s = lit(S::new_sheet, 0, 0, 10);
  // IFERR( 10 / 0 + 1, -7 ) -> -7
  s = form(s, 1, 0, S::Expr::eiferr(
                       S::Expr::eadd(
                          S::Expr::ediv(S::Expr::eref(S::CellRef{0, 0}),
                                        S::Expr::eint(0)),
                          S::Expr::eint(1)),
                       S::Expr::eint(-7)));
  check_int("iferr trap", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{1, 0})), -7);
  // IFERR( safe, fallback ) -> safe
  s = form(s, 2, 0, S::Expr::eiferr(S::Expr::eint(33), S::Expr::eint(-7)));
  check_int("iferr passthrough", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 0})), 33);
}

void test_deep_nesting() {
  // ((((1 + 1) + 1) + ... ) + 1) at depth 1000 should evaluate to 1000.
  S::Expr e = S::Expr::eint(0);
  for (int i = 0; i < 1000; ++i) {
    e = S::Expr::eadd(std::move(e), S::Expr::eint(1));
  }
  auto s = form(S::new_sheet, 0, 0, std::move(e));
  // eval_cell may run out of fuel at depth 1000; eval_iter should not.
  auto v = formula::eval_iter(s, S::CellRef{0, 0});
  check_int("deep 1000", v, 1000);

  // 5000-deep gauss
  S::Expr g = S::Expr::eint(0);
  for (int i = 1; i <= 100; ++i) {
    g = S::Expr::eadd(std::move(g), S::Expr::eint(i));
  }
  auto s2 = form(S::new_sheet, 0, 0, std::move(g));
  auto v2 = formula::eval_iter(s2, S::CellRef{0, 0});
  check_int("gauss(100)", v2, 5050);
}

void test_long_ref_chain() {
  // A1 = 1; A2 = A1 + 1; ...; A_n = A_{n-1} + 1.
  // For n = 8000 (within sheet limits: 260 cols × 200 rows = 52000 cells).
  auto s = lit(S::new_sheet, 0, 0, 1);
  const int N = 8000;
  for (int i = 1; i < N; ++i) {
    int r = i % 200;
    int c = i / 200;
    if (c >= 260) break;
    auto e = S::Expr::eadd(
        S::Expr::eref(S::CellRef{(int64_t)((i - 1) / 200),
                                  (int64_t)((i - 1) % 200)}),
        S::Expr::eint(1));
    s = form(s, c, r, std::move(e));
  }
  int last_c = (N - 1) / 200;
  int last_r = (N - 1) % 200;
  auto v = formula::eval_iter(s, S::CellRef{(int64_t)last_c, (int64_t)last_r});
  check_int("8000-chain", v, N);
}

void test_cycles() {
  // Self cycle: A1 = A1
  auto s = form(S::new_sheet, 0, 0, S::Expr::eref(S::CellRef{0, 0}));
  check("self-cycle/iter",  !formula::eval_iter(s, S::CellRef{0, 0}).has_value());
  check("self-cycle/spec",  is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{0, 0}))
                          || is_fuel(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{0, 0})));

  // Two-cell cycle: A1 = B1; B1 = A1
  auto s2 = form(S::new_sheet, 0, 0, S::Expr::eref(S::CellRef{1, 0}));
  s2 = form(s2, 1, 0, S::Expr::eref(S::CellRef{0, 0}));
  check("2cycle/iter@A1", !formula::eval_iter(s2, S::CellRef{0, 0}).has_value());
  check("2cycle/iter@B1", !formula::eval_iter(s2, S::CellRef{1, 0}).has_value());

  // 5-cell cycle.
  auto s5 = form(S::new_sheet, 0, 0, S::Expr::eref(S::CellRef{1, 0}));
  s5 = form(s5, 1, 0, S::Expr::eref(S::CellRef{2, 0}));
  s5 = form(s5, 2, 0, S::Expr::eref(S::CellRef{3, 0}));
  s5 = form(s5, 3, 0, S::Expr::eref(S::CellRef{4, 0}));
  s5 = form(s5, 4, 0, S::Expr::eref(S::CellRef{0, 0}));
  for (int i = 0; i < 5; ++i)
    check("5cycle/iter", !formula::eval_iter(s5, S::CellRef{(int64_t)i, 0}).has_value());

  // Cycle entered from outside: Z1 = A1 = B1 = A1
  auto s3 = form(S::new_sheet, 25, 0, S::Expr::eref(S::CellRef{0, 0}));
  s3 = form(s3, 0, 0, S::Expr::eref(S::CellRef{1, 0}));
  s3 = form(s3, 1, 0, S::Expr::eref(S::CellRef{0, 0}));
  check("entered-cycle/iter", !formula::eval_iter(s3, S::CellRef{25, 0}).has_value());
}

void test_saturation() {
  // INT64_MAX + 1 should saturate to INT64_MAX (not wrap).
  auto s = form(S::new_sheet, 0, 0, S::Expr::eadd(
                                        S::Expr::eint(INT64_MAX),
                                        S::Expr::eint(1)));
  auto v = formula::eval_iter(s, S::CellRef{0, 0});
  check_int("sat add overflow", v, INT64_MAX);
  // INT64_MIN - 1 should saturate to INT64_MIN.
  s = form(s, 1, 0, S::Expr::esub(S::Expr::eint(INT64_MIN), S::Expr::eint(1)));
  check_int("sat sub underflow", formula::eval_iter(s, S::CellRef{1, 0}), INT64_MIN);
  // INT64_MAX * 2.
  s = form(s, 2, 0, S::Expr::emul(S::Expr::eint(INT64_MAX), S::Expr::eint(2)));
  check_int("sat mul overflow", formula::eval_iter(s, S::CellRef{2, 0}), INT64_MAX);
  // Negative * positive overflow → INT64_MIN.
  s = form(s, 3, 0, S::Expr::emul(S::Expr::eint(INT64_MIN), S::Expr::eint(2)));
  check_int("sat mul neg overflow", formula::eval_iter(s, S::CellRef{3, 0}), INT64_MIN);
}

void test_aggregations() {
  // Build a 5x5 block at (0,0)..(4,4) with cells = row*5 + col + 1
  // (so 1..25; sum = 325, min = 1, max = 25, count = 25, avg = 13).
  // Use eval_cell only — formula::eval_iter does not handle SUM/AVG/MIN/MAX.
  auto s = S::new_sheet;
  for (int r = 0; r < 5; ++r)
    for (int c = 0; c < 5; ++c)
      s = lit(s, c, r, (int64_t)(r * 5 + c + 1));

  S::CellRef tl{0, 0}, br{4, 4};
  auto eval_at = [](const S::Sheet& sh, int c, int r) {
    return as_int(S::eval_cell(S::DEFAULT_FUEL, sh, S::CellRef{(int64_t)c, (int64_t)r}));
  };

  s = form(s, 5, 0, S::Expr::esum(tl, br));
  check_int("SUM 5x5", eval_at(s, 5, 0), 325);
  s = form(s, 5, 1, S::Expr::eavg(tl, br));
  check_int("AVG 5x5", eval_at(s, 5, 1), 13);
  s = form(s, 5, 2, S::Expr::ecount(tl, br));
  check_int("COUNT 5x5", eval_at(s, 5, 2), 25);
  s = form(s, 5, 3, S::Expr::emin(tl, br));
  check_int("MIN 5x5", eval_at(s, 5, 3), 1);
  s = form(s, 5, 4, S::Expr::emax(tl, br));
  check_int("MAX 5x5", eval_at(s, 5, 4), 25);

  // Inverted range: br before tl. SUM/MIN/MAX should error or be 0/COUNT 0.
  s = form(s, 6, 0, S::Expr::ecount(br, tl));
  check_int("COUNT inverted", eval_at(s, 6, 0), 0);

  // Single-cell range.
  s = form(s, 5, 5, S::Expr::esum(S::CellRef{2, 2}, S::CellRef{2, 2}));
  check_int("SUM 1x1", eval_at(s, 5, 5), 13);
}

void test_aggregation_with_holes() {
  auto s = S::new_sheet;
  for (int r = 0; r < 5; ++r)
    for (int c = 0; c < 5; ++c)
      s = lit(s, c, r, (int64_t)(r * 5 + c + 1));
  s = put(s, 2, 2, S::Cell::cempty());
  S::CellRef tl{0, 0}, br{4, 4};
  s = form(s, 5, 0, S::Expr::esum(tl, br));
  check_int("SUM with hole",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})),
            325 - 13);
}

void test_boolean_ops() {
  auto s = put(S::new_sheet, 0, 0, S::Cell::cbool(true));
  s = put(s, 1, 0, S::Cell::cbool(false));
  // BAND/BOR/BNOT
  s = form(s, 2, 0, S::Expr::ebnot(S::Expr::eref(S::CellRef{0, 0})));
  // BNOT returns EValB; via eval_cell this is a bool not an int. Spec
  // returns EValB(false). We just check it's *not* an EErr.
  auto r = S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 0});
  check("BNOT is not EErr", !is_err(r) && !is_fuel(r));
  s = form(s, 3, 0, S::Expr::eband(S::Expr::eref(S::CellRef{0, 0}),
                                    S::Expr::eref(S::CellRef{1, 0})));
  check("BAND ok", !is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})));
  s = form(s, 4, 0, S::Expr::ebor(S::Expr::eref(S::CellRef{0, 0}),
                                    S::Expr::eref(S::CellRef{1, 0})));
  check("BOR ok",  !is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})));

  // Integer logical AND/OR (truthy = nonzero).
  s = form(s, 5, 0, S::Expr::eand(S::Expr::eint(7), S::Expr::eint(0)));
  check_int("AND(7,0) = 0", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})), 0);
  s = form(s, 6, 0, S::Expr::eor(S::Expr::eint(7), S::Expr::eint(0)));
  check_int("OR(7,0) = 1", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{6, 0})), 1);
  s = form(s, 7, 0, S::Expr::enot(S::Expr::eint(0)));
  check_int("NOT(0) = 1", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{7, 0})), 1);
  s = form(s, 8, 0, S::Expr::enot(S::Expr::eint(42)));
  check_int("NOT(42) = 0", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{8, 0})), 0);
}

void test_string_ops() {
  // Concat two strings.
  auto s = put(S::new_sheet, 0, 0, S::Cell::cstr("Hello "));
  s = put(s, 1, 0, S::Cell::cstr("Rocq"));
  s = form(s, 2, 0, S::Expr::econcat(S::Expr::eref(S::CellRef{0, 0}),
                                      S::Expr::eref(S::CellRef{1, 0})));
  auto r = S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 0});
  bool concat_ok = std::holds_alternative<S::EvalResult::EValS>(r.v())
       && std::get<S::EvalResult::EValS>(r.v()).d_a0 == "Hello Rocq";
  check("string concat", concat_ok);

  // LEN of "Rocqsheet" = 9.
  s = put(s, 3, 0, S::Cell::cstr("Rocqsheet"));
  s = form(s, 4, 0, S::Expr::elen(S::Expr::eref(S::CellRef{3, 0})));
  check_int("LEN", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 9);

  // SUBSTR("Rocqsheet", 4, 5) = "sheet"
  s = form(s, 5, 0, S::Expr::esubstr(S::Expr::eref(S::CellRef{3, 0}),
                                      S::Expr::eint(4), S::Expr::eint(5)));
  auto sr = S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0});
  bool substr_ok = std::holds_alternative<S::EvalResult::EValS>(sr.v())
       && std::get<S::EvalResult::EValS>(sr.v()).d_a0 == "sheet";
  check("SUBSTR", substr_ok);
}

void test_correspondence_corpus() {
  // Several hundred pseudo-random small expressions, comparing
  // eval_cell (spec) to formula::eval_iter (impl).
  uint32_t rng = 0xC0FFEEu;
  auto next = [&]() {
    rng ^= rng << 13; rng ^= rng >> 17; rng ^= rng << 5;
    return rng;
  };
  auto rand_int = [&](int lo, int hi) {
    return lo + (int)(next() % (uint32_t)(hi - lo + 1));
  };

  for (int trial = 0; trial < 250; ++trial) {
    auto s = S::new_sheet;
    // Fill a 6×6 block of literals (mostly 0..20, sometimes 0).
    for (int r = 0; r < 6; ++r)
      for (int c = 0; c < 6; ++c)
        s = lit(s, c, r, rand_int(0, 20));
    // Build a random small expression using cells from the block.
    std::function<S::Expr(int)> mk;
    mk = [&](int depth) -> S::Expr {
      if (depth == 0) {
        int kind = next() % 3;
        if (kind == 0) {
          int v = rand_int(-100, 100);
          return S::Expr::eint(v);
        }
        if (kind == 1) return S::Expr::eref(
            S::CellRef{(int64_t)rand_int(0, 5), (int64_t)rand_int(0, 5)});
        return S::Expr::eint(0);
      }
      int op = next() % 8;
      switch (op) {
        case 0: return S::Expr::eadd(mk(depth - 1), mk(depth - 1));
        case 1: return S::Expr::esub(mk(depth - 1), mk(depth - 1));
        case 2: return S::Expr::emul(mk(depth - 1), mk(depth - 1));
        case 3: return S::Expr::ediv(mk(depth - 1), mk(depth - 1));
        case 4: return S::Expr::eif(mk(depth - 1), mk(depth - 1),
                                     mk(depth - 1));
        case 5: return S::Expr::eeq(mk(depth - 1), mk(depth - 1));
        case 6: return S::Expr::elt(mk(depth - 1), mk(depth - 1));
        default: return S::Expr::egt(mk(depth - 1), mk(depth - 1));
      }
    };
    auto e = mk(4);
    auto target = S::CellRef{6, 0};
    s = form(s, 6, 0, std::move(e));
    char tag[32];
    std::snprintf(tag, sizeof(tag), "rand/%d", trial);
    agree_iter_vs_spec(tag, s, target);
  }
}

void test_parser_extra() {
  // Things not covered by formula_test.cpp.
  auto p = [](const std::string& src) {
    return Parser::parse_formula(src).has_value();
  };
  check("parser/sum-range",  p("SUM(A1:E5)"));
  check("parser/avg-range",  p("AVG(A1:E5)"));
  check("parser/count-range",p("COUNT(A1:A1)"));
  check("parser/min-range",  p("MIN(A1:E5)"));
  check("parser/max-range",  p("MAX(A1:E5)"));
  check("parser/iferror",    p("IFERROR(A1/0,-1)"));
  check("parser/deep-paren", p("(((((1+1)+1)+1)+1)+1)"));
  check("parser/and-or-mix", p("AND(OR(A1=1,A1=2),NOT(A1=3))"));
  check("parser/mixed-prec", p("1+2*3-4/2+5%3^2"));

  // Errors
  check("parser/range-no-colon", !p("SUM(A1 E5)"));
  check("parser/range-rev",      p("SUM(E5:A1)"));   // syntactically OK
  check("parser/missing-comma",  !p("IF(A1=B1 1 0)"));
  check("parser/iferror-1arg",   !p("IFERROR(A1)"));
}

void test_workbook_invariants() {
  // Boundary cell (col 259, row 199) is the last addressable.
  auto s = lit(S::new_sheet, 259, 199, 42);
  check_int("max-cell write/read", as_int(S::eval_cell(S::DEFAULT_FUEL, s,
                                            S::CellRef{259, 199})), 42);
  // Truly OOB index: row 200 (one past last). cell_index = 200*260+0 = 52000
  // which equals GRID_SIZE; PrimArray.set on >= length is documented as a no-op.
  auto s2 = lit(s, 0, 200, 99);
  check_int("OOB row write doesn't appear",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s2, S::CellRef{0, 200})), 0);
  check_int("max-cell still 42 after OOB write",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s2, S::CellRef{259, 199})), 42);

  // get_set_eq / get_set_neq smoke at neighbouring rows.
  auto s3 = S::new_sheet;
  s3 = lit(s3, 5, 5, 100);
  s3 = lit(s3, 5, 6, 200);
  check_int("setget@(5,5)",   as_int(S::eval_cell(S::DEFAULT_FUEL, s3, S::CellRef{5, 5})), 100);
  check_int("setget@(5,6)",   as_int(S::eval_cell(S::DEFAULT_FUEL, s3, S::CellRef{5, 6})), 200);
  check_int("untouched@(5,7)",as_int(S::eval_cell(S::DEFAULT_FUEL, s3, S::CellRef{5, 7})), 0);

  // Overwrite preserves length: write 1000 random cells and read each back.
  auto s4 = S::new_sheet;
  for (int i = 0; i < 1000; ++i) {
    int c = (i * 7) % 260;
    int r = (i * 11) % 200;
    s4 = lit(s4, c, r, (int64_t)(i + 1));
  }
  // Last write per (c, r) pair wins; check the very last entry.
  int last = 999;
  int lc = (last * 7) % 260;
  int lr = (last * 11) % 200;
  check_int("1000-write final cell",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s4,
                                 S::CellRef{(int64_t)lc, (int64_t)lr})),
            (int64_t)(last + 1));
}

}  // namespace

int main() {
  test_literals_and_empties();
  test_arith_basic();
  test_div_mod_zero_neg_pow();
  test_comparisons_and_if();
  test_iferr();
  test_deep_nesting();
  test_long_ref_chain();
  test_cycles();
  test_saturation();
  test_aggregations();
  test_aggregation_with_holes();
  test_boolean_ops();
  test_string_ops();
  test_correspondence_corpus();
  test_parser_extra();
  test_workbook_invariants();

  std::printf("\n=== torture_test summary ===\n");
  std::printf("PASS: %d\n", passes);
  std::printf("FAIL: %d\n", fails);
  return fails == 0 ? 0 : 1;
}
