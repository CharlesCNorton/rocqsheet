// Stress / edge-case test for the Rocqsheet extracted kernel.
// Exercises arithmetic boundaries, deep nesting, ref chains, cycles,
// string/float ops, range aggregations, parser corner cases, and
// spec-vs-impl correspondence with formula::eval_iter.

#include "rocqsheet.h"
#include "../src/eval_iter.h"
#include "../src/number_format_helpers.h"

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
  // 2^-3 = 1/8 as a float (EFVal 0.125); 0^-3 stays EErr.
  s = form(s, 3, 0, S::Expr::epow(S::Expr::eint(2), S::Expr::eint(-3)));
  {
    auto r = S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0});
    bool ok = std::holds_alternative<S::EvalResult::EFVal>(r.v()) &&
              std::get<S::EvalResult::EFVal>(r.v()).d_a0 == 0.125;
    check("neg-pow → EFVal 1/8", ok);
  }
  s = form(s, 5, 0, S::Expr::epow(S::Expr::eint(0), S::Expr::eint(-3)));
  check("0^neg → EErr", is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})));
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

// COUNT counts numeric cells, COUNTA counts non-empty
// cells, RANGE_SIZE keeps the original rectangle cardinality.
void test_count_counta() {
  // A1=1, B1=2.5f, C1="x", D1=TRUE, E1 empty, F1==A1+1, G1==1/0.
  auto s = lit(S::new_sheet, 0, 0, 1);
  s = put(s, 1, 0, S::Cell::cfloat(2.5));
  s = put(s, 2, 0, S::Cell::cstr("x"));
  s = put(s, 3, 0, S::Cell::cbool(true));
  s = form(s, 5, 0, S::Expr::eadd(S::Expr::eref(S::CellRef{0, 0}),
                                  S::Expr::eint(1)));
  s = form(s, 6, 0, S::Expr::ediv(S::Expr::eint(1), S::Expr::eint(0)));
  S::CellRef tl{0, 0}, br{6, 0};
  // Numeric: A1 lit, B1 float, F1 numeric formula.
  s = form(s, 0, 1, S::Expr::ecountn(tl, br));
  check_int("COUNT numeric",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{0, 1})), 3);
  // Non-empty: everything but E1 (errors count as occupied).
  s = form(s, 1, 1, S::Expr::ecounta(tl, br));
  check_int("COUNTA non-empty",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{1, 1})), 6);
  // Rectangle cardinality is unchanged under the RANGE_SIZE spelling.
  s = form(s, 2, 1, S::Expr::ecount(tl, br));
  check_int("RANGE_SIZE",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 1})), 7);
  // The Excel-mismatch the TODO called out: COUNT over an
  // empty 5x6 range is 0, not 30.
  S::CellRef etl{0, 19}, ebr{4, 24};
  s = form(s, 3, 1, S::Expr::ecountn(etl, ebr));
  check_int("COUNT empty-range",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 1})), 0);
  s = form(s, 4, 1, S::Expr::ecount(etl, ebr));
  check_int("RANGE_SIZE 5x6",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 1})), 30);
  // COUNTA sees through to formula cells that reference the counted
  // range without double-counting: inverted rectangle is 0.
  s = form(s, 5, 1, S::Expr::ecounta(br, tl));
  check_int("COUNTA inverted",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 1})), 0);
}

// SUMIF / COUNTIF / AVERAGEIF with a CmpOp-against-literal
// predicate and an offset aggregation range.
void test_if_aggregates() {
  // Criteria column A rows 1-5; data column C rows 1-5.
  auto s = S::new_sheet;
  const int64_t crit[5] = {1, 5, 10, -3, 7};
  const int64_t data[5] = {100, 200, 300, 400, 500};
  for (int r = 0; r < 5; ++r) {
    s = lit(s, 0, r, crit[r]);
    s = lit(s, 2, r, data[r]);
  }
  S::CellRef tl{0, 0}, br{0, 4}, sumtl{2, 0};
  s = form(s, 4, 0, S::Expr::ecountif(tl, br, S::CmpOp::e_CMPGT, 4));
  check_int("COUNTIF >4",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 3);
  s = form(s, 4, 1, S::Expr::esumif(tl, br, S::CmpOp::e_CMPGT, 4, sumtl));
  check_int("SUMIF >4",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 1})), 1000);
  s = form(s, 4, 2, S::Expr::eavgif(tl, br, S::CmpOp::e_CMPLT, 8, sumtl));
  check_int("AVERAGEIF <8",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 2})), 300);
  s = form(s, 4, 3, S::Expr::ecountif(tl, br, S::CmpOp::e_CMPEQ, -3));
  check_int("COUNTIF =-3",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 3})), 1);
  // No criteria match: AVERAGEIF divides by zero matches → EErr.
  s = form(s, 4, 4, S::Expr::eavgif(tl, br, S::CmpOp::e_CMPGT, 1000, sumtl));
  check("AVERAGEIF no-match → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 4})));
}

// VAR / VARP / STDEV / STDEVP over integer cells.  The
// classic dataset 2,4,4,4,5,5,7,9: n=8, mean 5, population variance
// 4, population stdev 2.  Sample variance 32/7 truncates to 4.
void test_var_stdev() {
  auto s = S::new_sheet;
  const int64_t xs[8] = {2, 4, 4, 4, 5, 5, 7, 9};
  for (int r = 0; r < 8; ++r) s = lit(s, 0, r, xs[r]);
  // A string and an empty cell inside the rectangle are skipped.
  s = put(s, 1, 0, S::Cell::cstr("note"));
  S::CellRef tl{0, 0}, br{1, 7};
  s = form(s, 3, 0, S::Expr::evarpop(tl, br));
  check_int("VARP", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})), 4);
  s = form(s, 3, 1, S::Expr::estdevpop(tl, br));
  check_int("STDEVP", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 1})), 2);
  s = form(s, 3, 2, S::Expr::evarsamp(tl, br));
  check_int("VAR", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 2})), 4);
  s = form(s, 3, 3, S::Expr::estdevsamp(tl, br));
  check_int("STDEV", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 3})), 2);
  // Sample variance over a single cell divides by zero -> EErr.
  s = form(s, 3, 4, S::Expr::evarsamp(S::CellRef{0, 0}, S::CellRef{0, 0}));
  check("VAR single-cell → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 4})));
  // Population variance over an empty range -> EErr.
  s = form(s, 3, 5, S::Expr::evarpop(S::CellRef{0, 19}, S::CellRef{4, 24}));
  check("VARP empty-range → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 5})));
}

// CSV import through the extracted scanner and its iterative
// C++ driver.
void test_csv_import() {
  auto sh = Csv::csv_import("7,hi\n\"a,b\",-3\n", S::new_sheet,
                            S::CellRef{1, 1});
  auto c00 = S::get_cell(sh, S::CellRef{1, 1});
  check("csv lit", std::holds_alternative<S::Cell::CLit>(c00.v()) &&
                       std::get<S::Cell::CLit>(c00.v()).d_a0 == 7);
  auto c10 = S::get_cell(sh, S::CellRef{2, 1});
  check("csv str", std::holds_alternative<S::Cell::CStr>(c10.v()) &&
                       std::get<S::Cell::CStr>(c10.v()).d_a0 == "hi");
  auto c01 = S::get_cell(sh, S::CellRef{1, 2});
  check("csv quoted comma",
        std::holds_alternative<S::Cell::CStr>(c01.v()) &&
            std::get<S::Cell::CStr>(c01.v()).d_a0 == "a,b");
  auto c11 = S::get_cell(sh, S::CellRef{2, 2});
  check("csv negative",
        std::holds_alternative<S::Cell::CLit>(c11.v()) &&
            std::get<S::Cell::CLit>(c11.v()).d_a0 == -3);
  // CRLF rows and the trailing field without a final newline.
  auto crlf = Csv::csv_import("1\r\n2", S::new_sheet, S::CellRef{0, 0});
  auto r1 = S::get_cell(crlf, S::CellRef{0, 1});
  check("csv crlf + trailing",
        std::holds_alternative<S::Cell::CLit>(r1.v()) &&
            std::get<S::Cell::CLit>(r1.v()).d_a0 == 2);
  // A ~120KB input exercises the iterative driver; per-character
  // extracted recursion would overflow the stack here.
  std::string big;
  for (int i = 0; i < 60000; ++i) big += "1,";
  big += "9\n";
  auto wide = Csv::csv_import(big, S::new_sheet, S::CellRef{0, 0});
  auto last = S::get_cell(wide, S::CellRef{259, 0});
  check("csv 120KB survives",
        std::holds_alternative<S::Cell::CLit>(last.v()));
}

// UPPER / LOWER / TRIM / FIND / REPLACE.
void test_string_funcs() {
  auto s = put(S::new_sheet, 0, 0, S::Cell::cstr("  Hello, World  "));
  auto str_at = [&](const S::Sheet& sh, int c, int r) {
    auto v = S::eval_cell(S::DEFAULT_FUEL, sh, S::CellRef{c, r});
    return std::holds_alternative<S::EvalResult::EValS>(v.v())
               ? std::get<S::EvalResult::EValS>(v.v()).d_a0
               : std::string("<not-a-string>");
  };
  s = form(s, 1, 0, S::Expr::eupper(S::Expr::estr("aB3z")));
  check("UPPER", str_at(s, 1, 0) == "AB3Z");
  s = form(s, 2, 0, S::Expr::elower(S::Expr::estr("AbC!")));
  check("LOWER", str_at(s, 2, 0) == "abc!");
  s = form(s, 3, 0, S::Expr::etrim(S::Expr::eref(S::CellRef{0, 0})));
  check("TRIM", str_at(s, 3, 0) == "Hello, World");
  s = form(s, 4, 0, S::Expr::efind(S::Expr::estr("lo"),
                                   S::Expr::estr("hello")));
  check_int("FIND hit",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 4);
  s = form(s, 5, 0, S::Expr::efind(S::Expr::estr("xy"),
                                   S::Expr::estr("hello")));
  check("FIND miss → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})));
  s = form(s, 6, 0, S::Expr::ereplaces(S::Expr::estr("abcdef"),
                                       S::Expr::eint(2), S::Expr::eint(3),
                                       S::Expr::estr("XY")));
  check("REPLACE", str_at(s, 6, 0) == "aXYef");
  // Regression: an out-of-range SUBSTR must clamp (the raw substr
  // mapping threw std::out_of_range and aborted the process).
  s = form(s, 7, 0, S::Expr::esubstr(S::Expr::estr("x"), S::Expr::eint(5),
                                     S::Expr::eint(1)));
  check("SUBSTR OOB clamps", str_at(s, 7, 0) == "");
}

// MEDIAN / MODE / RANK / PERCENTILE / NPV.
void test_order_stats_npv() {
  auto s = S::new_sheet;
  const int64_t xs[5] = {9, 1, 5, 7, 5};
  for (int r = 0; r < 5; ++r) s = lit(s, 0, r, xs[r]);
  // A skipped string cell inside the rectangle.
  s = put(s, 1, 0, S::Cell::cstr("n/a"));
  S::CellRef tl{0, 0}, br{1, 4};
  s = form(s, 3, 0, S::Expr::emedian(tl, br));
  check_int("MEDIAN", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})), 5);
  s = form(s, 3, 1, S::Expr::emodev(tl, br));
  check_int("MODE", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 1})), 5);
  s = form(s, 3, 2, S::Expr::erank(S::Expr::eint(5), tl, br));
  check_int("RANK", as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 2})), 3);
  s = form(s, 3, 3, S::Expr::epercentile(S::Expr::eint(100), tl, br));
  check_int("PERCENTILE 100",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 3})), 9);
  s = form(s, 3, 4, S::Expr::enpvz(S::Expr::eint(1), tl, br));
  check_int("NPV d=1 sums",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 4})), 27);
  // Empty range -> EErr; NPV with d < 1 -> EErr.
  s = form(s, 4, 0, S::Expr::emedian(S::CellRef{0, 19}, S::CellRef{4, 24}));
  check("MEDIAN empty → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})));
  s = form(s, 4, 1, S::Expr::enpvz(S::Expr::eint(0), tl, br));
  check("NPV d=0 → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 1})));
}

// VLOOKUP / HLOOKUP / MATCH / INDEX (exact match).
void test_lookups() {
  // Key column A: 10, 20, 30; value column B: 100, 200, 300; C: text.
  auto s = S::new_sheet;
  for (int r = 0; r < 3; ++r) {
    s = lit(s, 0, r, 10 * (r + 1));
    s = lit(s, 1, r, 100 * (r + 1));
  }
  s = put(s, 2, 1, S::Cell::cstr("twenty"));
  S::CellRef tl{0, 0}, br{2, 2};
  s = form(s, 4, 0, S::Expr::evlookup(S::Expr::eint(20), tl, br,
                                      S::Expr::eint(2)));
  check_int("VLOOKUP hit",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 200);
  s = form(s, 4, 1, S::Expr::evlookup(S::Expr::eint(99), tl, br,
                                      S::Expr::eint(2)));
  check("VLOOKUP miss → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 1})));
  s = form(s, 4, 2, S::Expr::evlookup(S::Expr::eint(20), tl, br,
                                      S::Expr::eint(9)));
  check("VLOOKUP col OOB → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 2})));
  // VLOOKUP returning a string cell passes the type through.
  s = form(s, 4, 3, S::Expr::evlookup(S::Expr::eint(20), tl, br,
                                      S::Expr::eint(3)));
  {
    auto v = S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 3});
    check("VLOOKUP string result",
          std::holds_alternative<S::EvalResult::EValS>(v.v()) &&
              std::get<S::EvalResult::EValS>(v.v()).d_a0 == "twenty");
  }
  s = form(s, 4, 4, S::Expr::ematchv(S::Expr::eint(30), tl, br));
  check_int("MATCH",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 4})), 3);
  s = form(s, 4, 5, S::Expr::eindex(tl, br, S::Expr::eint(2),
                                    S::Expr::eint(2)));
  check_int("INDEX",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 5})), 200);
  // HLOOKUP over the transposed layout: keys in row 5.
  for (int c = 0; c < 3; ++c) {
    s = lit(s, c, 5, 10 * (c + 1));
    s = lit(s, c, 6, 1000 * (c + 1));
  }
  s = form(s, 4, 6, S::Expr::ehlookup(S::Expr::eint(30),
                                      S::CellRef{0, 5}, S::CellRef{2, 6},
                                      S::Expr::eint(2)));
  check_int("HLOOKUP",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 6})), 3000);
  // Approximate (sorted-range) mode: key 25 selects the row of 20.
  s = form(s, 5, 0, S::Expr::evlookupa(S::Expr::eint(25), tl, br,
                                       S::Expr::eint(2)));
  check_int("VLOOKUP approx",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})), 200);
  // An exact key still hits its own row.
  s = form(s, 5, 1, S::Expr::evlookupa(S::Expr::eint(30), tl, br,
                                       S::Expr::eint(2)));
  check_int("VLOOKUP approx exact key",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 1})), 300);
  // Every key above x misses.
  s = form(s, 5, 2, S::Expr::evlookupa(S::Expr::eint(5), tl, br,
                                       S::Expr::eint(2)));
  check("VLOOKUP approx all-above → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 2})));
  s = form(s, 5, 3, S::Expr::ematcha(S::Expr::eint(25), tl,
                                     S::CellRef{0, 2}));
  check_int("MATCH approx",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 3})), 2);
  s = form(s, 5, 4, S::Expr::ehlookupa(S::Expr::eint(25),
                                       S::CellRef{0, 5}, S::CellRef{2, 6},
                                       S::Expr::eint(2)));
  check_int("HLOOKUP approx",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 4})), 2000);
}

// numeric strings coerce in integer contexts.
void test_string_coercion() {
  auto s = put(S::new_sheet, 0, 0, S::Cell::cstr("5"));
  s = put(s, 1, 0, S::Cell::cstr("x"));
  s = form(s, 2, 0, S::Expr::eadd(S::Expr::eref(S::CellRef{0, 0}),
                                  S::Expr::eint(2)));
  check_int("\"5\"+2",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 0})), 7);
  s = form(s, 3, 0, S::Expr::emul(S::Expr::estr("-3"), S::Expr::estr("4")));
  check_int("\"-3\"*\"4\"",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})), -12);
  s = form(s, 4, 0, S::Expr::eadd(S::Expr::eref(S::CellRef{1, 0}),
                                  S::Expr::eint(2)));
  check("\"x\"+2 → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})));
}

// CDate cells, DATE / WEEKDAY / EDATE / EOMONTH, and
// the floored-division extraction fix.
void test_dates() {
  auto s = put(S::new_sheet, 0, 0, S::Cell::cdate(20608));  // 2026-06-04
  s = form(s, 1, 0, S::Expr::eadd(S::Expr::eref(S::CellRef{0, 0}),
                                  S::Expr::eint(1)));
  check_int("date + 1",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{1, 0})), 20609);
  s = form(s, 2, 0, S::Expr::edate3(S::Expr::eint(2026), S::Expr::eint(6),
                                    S::Expr::eint(4)));
  check_int("DATE(2026,6,4)",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{2, 0})), 20608);
  s = form(s, 3, 0, S::Expr::eweekdayf(S::Expr::eint(20608)));
  check_int("WEEKDAY",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{3, 0})), 4);
  s = form(s, 4, 0, S::Expr::eedatef(S::Expr::eint(20608),
                                     S::Expr::eint(-2)));
  check_int("EDATE -2",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{4, 0})), 20547);
  s = form(s, 5, 0, S::Expr::eeomonthf(S::Expr::eint(20608),
                                       S::Expr::eint(0)));
  check_int("EOMONTH",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{5, 0})), 20634);
  // Floored division now matches the Coq spec on negatives.
  s = form(s, 6, 0, S::Expr::ediv(S::Expr::eint(-7), S::Expr::eint(2)));
  check_int("floored div",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{6, 0})), -4);
  s = form(s, 7, 0, S::Expr::emod(S::Expr::eint(-7), S::Expr::eint(2)));
  check_int("floored mod",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{7, 0})), 1);
  agree_iter_vs_spec("floored-div", s, S::CellRef{6, 0});
  agree_iter_vs_spec("floored-mod", s, S::CellRef{7, 0});
  // DATEDIF in days, months, years; reversed interval errors.
  auto d0 = S::Expr::edate3(S::Expr::eint(2000), S::Expr::eint(6),
                            S::Expr::eint(4));
  auto d1 = S::Expr::edate3(S::Expr::eint(2026), S::Expr::eint(6),
                            S::Expr::eint(4));
  s = form(s, 8, 0, S::Expr::edatedif(d0, d1, S::Expr::eint(2)));
  check_int("DATEDIF years",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{8, 0})), 26);
  s = form(s, 9, 0, S::Expr::edatedif(d0, d1, S::Expr::eint(1)));
  check_int("DATEDIF months",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{9, 0})), 312);
  s = form(s, 10, 0, S::Expr::edatedif(S::Expr::eint(0), S::Expr::eint(45),
                                       S::Expr::eint(0)));
  check_int("DATEDIF days",
            as_int(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{10, 0})), 45);
  s = form(s, 11, 0, S::Expr::edatedif(d1, d0, S::Expr::eint(0)));
  check("DATEDIF reversed → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{11, 0})));
  s = form(s, 12, 0, S::Expr::edatedif(d0, d1, S::Expr::eint(7)));
  check("DATEDIF bad unit → EErr",
        is_err(S::eval_cell(S::DEFAULT_FUEL, s, S::CellRef{12, 0})));
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

// The NFDate display branch mirrors the proven Coq renderer: the
// helper's hand-transcribed civil-from-days must agree with the
// extracted date_to_string everywhere we probe, including the epoch
// and pre-epoch days.
void test_nfdate_format() {
  const NumberFormat date_fmt{NumberFormat::NFDate{}};
  for (int64_t z : {int64_t(20608), int64_t(0), int64_t(-1),
                    int64_t(-719162), int64_t(11111), int64_t(45000)}) {
    const std::string tag =
        "NFDate matches date_to_string @" + std::to_string(z);
    check(tag.c_str(),
          number_format_helpers::format_z(z, date_fmt) ==
              S::date_to_string(z));
  }
  check("NFDate literal render",
        number_format_helpers::format_z(int64_t(20608), date_fmt) ==
            "2026-06-04");
  check("NFDate float truncates",
        number_format_helpers::format_float(20608.7, date_fmt) ==
            "2026-06-04");
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
  test_count_counta();
  test_if_aggregates();
  test_var_stdev();
  test_csv_import();
  test_string_funcs();
  test_order_stats_npv();
  test_lookups();
  test_string_coercion();
  test_dates();
  test_nfdate_format();
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
