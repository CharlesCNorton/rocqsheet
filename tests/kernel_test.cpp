// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Runtime tests over the Rocqsheet kernel.  These complement the
// Rocq-side theorems by exercising the actual C++ extraction at
// runtime, including a deep-chain stress test that the recursive
// extracted [eval_cell] cannot survive.

#include "rocqsheet.h"
#include "../src/eval_iter.h"

#include <cstdint>
#include <cstdio>
#include <string>

namespace {

int failures = 0;

void check(const char* tag, std::optional<int64_t> got, int64_t want) {
  if (!got || *got != want) {
    std::printf("FAIL %s: got %s, want %lld\n", tag,
        got ? std::to_string(*got).c_str() : "None", (long long)want);
    ++failures;
  }
}
void check_none(const char* tag, std::optional<int64_t> got) {
  if (got) {
    std::printf("FAIL %s: got %lld, want None\n", tag, (long long)*got);
    ++failures;
  }
}

}  // namespace

using S = Rocqsheet;

int main() {
  // The closed Rocq smoke value: A1=2, B1=3, C1=(A1+B1)*7 = 35.
  check("smoke", S::smoke, 35);

  // A1=10, B1=3.  Exercise all four operators plus a unary-negation form.
  const auto a1 = S::CellRef{0, 0};
  const auto b1 = S::CellRef{1, 0};
  const auto c1 = S::CellRef{2, 0};
  auto sh = S::set_cell(S::new_sheet, a1, S::Cell::clit(10));
  sh = S::set_cell(sh, b1, S::Cell::clit(3));

  auto eval_with = [&](S::Expr e) {
    auto local = S::set_cell(sh, c1, S::Cell::cform(std::move(e)));
    return formula::eval_iter(local, c1);
  };

  check("add", eval_with(S::Expr::eadd(S::Expr::eref(a1), S::Expr::eref(b1))), 13);
  check("sub", eval_with(S::Expr::esub(S::Expr::eref(a1), S::Expr::eref(b1))),  7);
  check("mul", eval_with(S::Expr::emul(S::Expr::eref(a1), S::Expr::eref(b1))), 30);
  check("div", eval_with(S::Expr::ediv(S::Expr::eref(a1), S::Expr::eref(b1))),  3);
  check_none("div-by-zero",
      eval_with(S::Expr::ediv(S::Expr::eref(a1), S::Expr::eint(0))));

  // Empty cell evaluates as 0.
  check("empty-cell", formula::eval_iter(S::new_sheet, S::CellRef{5, 5}), 0);

  // Multi-letter columns: AA = 26, BA = 52, CZ = 103.
  {
    auto aa1 = S::CellRef{26, 0};
    auto ba1 = S::CellRef{52, 0};
    auto cz1 = S::CellRef{103, 0};
    auto wide = S::set_cell(S::new_sheet, aa1, S::Cell::clit(100));
    wide = S::set_cell(wide, ba1, S::Cell::clit(200));
    wide = S::set_cell(wide, cz1, S::Cell::clit(700));
    auto sum_expr = S::Expr::eadd(
        S::Expr::eadd(S::Expr::eref(aa1), S::Expr::eref(ba1)),
        S::Expr::eref(cz1));
    wide = S::set_cell(wide, c1, S::Cell::cform(std::move(sum_expr)));
    check("multi-letter sum", formula::eval_iter(wide, c1), 1000);
  }

  // Dependency chain: A1=1, A2=A1+1, ..., A50=A49+1.
  {
    auto chain = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(1));
    for (int r = 1; r < 50; ++r) {
      auto e = S::Expr::eadd(
          S::Expr::eref(S::CellRef{0, r - 1}),
          S::Expr::eint(1));
      chain = S::set_cell(chain, S::CellRef{0, r},
                          S::Cell::cform(std::move(e)));
    }
    check("50-chain", formula::eval_iter(chain, S::CellRef{0, 49}), 50);
  }

  // Two-cell cycle: A1 <-> B1 returns None on either entry point.
  {
    auto cyc = S::set_cell(S::new_sheet, a1,
        S::Cell::cform(S::Expr::eref(b1)));
    cyc = S::set_cell(cyc, b1, S::Cell::cform(S::Expr::eref(a1)));
    check_none("cycle@A1", formula::eval_iter(cyc, a1));
    check_none("cycle@B1", formula::eval_iter(cyc, b1));
  }

  // IF / comparison operators.
  {
    auto sh2 = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(7));
    sh2 = S::set_cell(sh2, S::CellRef{1, 0}, S::Cell::clit(7));
    sh2 = S::set_cell(sh2, S::CellRef{2, 0}, S::Cell::clit(3));
    auto eA = S::CellRef{4, 0};

    auto with_if = [&](S::Expr e) {
      auto local = S::set_cell(sh2, eA, S::Cell::cform(std::move(e)));
      return formula::eval_iter(local, eA);
    };

    auto refA = S::CellRef{0, 0}, refB = S::CellRef{1, 0}, refC = S::CellRef{2, 0};
    // A==B (7==7) is true: IF picks the then-branch (1).
    check("if-true",
          with_if(S::Expr::eif(
              S::Expr::eeq(S::Expr::eref(refA), S::Expr::eref(refB)),
              S::Expr::eint(1),
              S::Expr::eint(0))),
          1);
    // A==C (7==3) is false: IF picks else (0).
    check("if-false",
          with_if(S::Expr::eif(
              S::Expr::eeq(S::Expr::eref(refA), S::Expr::eref(refC)),
              S::Expr::eint(1),
              S::Expr::eint(0))),
          0);
    // C<A (3<7) is true: pick then.
    check("lt-true",
          with_if(S::Expr::eif(
              S::Expr::elt(S::Expr::eref(refC), S::Expr::eref(refA)),
              S::Expr::eint(99),
              S::Expr::eint(-1))),
          99);
    // A>C (7>3) is true.
    check("gt-true",
          with_if(S::Expr::eif(
              S::Expr::egt(S::Expr::eref(refA), S::Expr::eref(refC)),
              S::Expr::eint(11),
              S::Expr::eint(22))),
          11);
    // Comparison alone returns 1/0.
    check("eq-as-value",
          with_if(S::Expr::eeq(S::Expr::eref(refA), S::Expr::eref(refB))),
          1);
    check("lt-as-value",
          with_if(S::Expr::elt(S::Expr::eref(refA), S::Expr::eref(refC))),
          0);
  }

  // Stress: a 9000-deep ref chain that the recursive extracted
  // eval_cell would segfault on (each call burns C++ stack), but
  // eval_iter handles via its heap continuation stack.
  {
    auto big = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(1));
    int prev_c = 0, prev_r = 0;
    int last_c = 0, last_r = 0;
    int total = 1;
    for (int i = 1; i < 9000; ++i) {
      int r = i % static_cast<int>(S::NUM_ROWS);
      int c = i / static_cast<int>(S::NUM_ROWS);
      if (c >= static_cast<int>(S::NUM_COLS)) break;
      auto e = S::Expr::eadd(
          S::Expr::eref(S::CellRef{prev_c, prev_r}),
          S::Expr::eint(1));
      big = S::set_cell(big, S::CellRef{c, r},
                        S::Cell::cform(std::move(e)));
      prev_c = c; prev_r = r;
      last_c = c; last_r = r;
      total = i + 1;
    }
    auto v = formula::eval_iter(big, S::CellRef{last_c, last_r});
    check("9000-deep chain", v, total);
  }

  // Empirical correspondence between the Rocq-extracted eval_cell
  // (recursive, fuel-bounded; the spec) and formula::eval_iter
  // (iterative, hand-coded; the implementation).  For every input
  // where the recursive version terminates within fuel, the
  // iterative version must produce the same answer.
  {
    auto agree = [&](const char* tag, const S::Sheet& sh, const S::CellRef& r) {
      auto spec = S::eval_cell(S::DEFAULT_FUEL, sh, r);
      auto impl = formula::eval_iter(sh, r);
      // Where the spec returns Some, the impl must agree.
      // Where the spec returns None, the impl is allowed to return
      // either Some (if eval_cell ran out of fuel rather than
      // hitting a cycle/divzero) or the same None.  The kernel test
      // above already covers the cases where both should be None.
      if (spec.has_value()) {
        if (!impl.has_value() || *impl != *spec) {
          std::printf("FAIL correspondence/%s: spec=%lld impl=%s\n", tag,
                      (long long)*spec,
                      impl ? std::to_string(*impl).c_str() : "None");
          ++failures;
        }
      }
    };

    // Empty / literal / formula in all three positions.
    agree("empty", S::new_sheet, S::CellRef{0, 0});
    auto sh = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(42));
    agree("lit", sh, S::CellRef{0, 0});
    sh = S::set_cell(sh, S::CellRef{1, 0},
        S::Cell::cform(S::Expr::eint(7)));
    agree("eint-form", sh, S::CellRef{1, 0});

    // All four operators on a few literal pairs.
    auto with = [&](S::Expr e) {
      auto local = S::set_cell(sh, S::CellRef{2, 0}, S::Cell::cform(std::move(e)));
      agree("op", local, S::CellRef{2, 0});
    };
    with(S::Expr::eadd(S::Expr::eint(11), S::Expr::eint(31)));
    with(S::Expr::esub(S::Expr::eint(99), S::Expr::eint(40)));
    with(S::Expr::emul(S::Expr::eint(7), S::Expr::eint(13)));
    with(S::Expr::ediv(S::Expr::eint(50), S::Expr::eint(3)));

    // A short reference chain that fits in DEFAULT_FUEL.
    {
      auto chain = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(1));
      for (int r = 1; r < 30; ++r) {
        chain = S::set_cell(chain, S::CellRef{0, r}, S::Cell::cform(
            S::Expr::eadd(S::Expr::eref(S::CellRef{0, r - 1}),
                          S::Expr::eint(1))));
      }
      agree("chain-29", chain, S::CellRef{0, 29});
    }

    // Mixed operators with refs.
    {
      auto m = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(10));
      m = S::set_cell(m, S::CellRef{1, 0}, S::Cell::clit(3));
      m = S::set_cell(m, S::CellRef{2, 0}, S::Cell::cform(
          S::Expr::emul(
              S::Expr::eadd(S::Expr::eref(S::CellRef{0, 0}),
                            S::Expr::eref(S::CellRef{1, 0})),
              S::Expr::esub(S::Expr::eref(S::CellRef{0, 0}),
                            S::Expr::eref(S::CellRef{1, 0})))));
      agree("(A+B)*(A-B)", m, S::CellRef{2, 0});
    }

    // IF / comparison correspondence.
    auto sh3 = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(7));
    sh3 = S::set_cell(sh3, S::CellRef{1, 0}, S::Cell::clit(3));
    auto put_form = [&](S::Expr e) {
      auto local = S::set_cell(sh3, S::CellRef{2, 0},
          S::Cell::cform(std::move(e)));
      agree("if-cmp", local, S::CellRef{2, 0});
    };
    put_form(S::Expr::eeq(S::Expr::eint(7), S::Expr::eint(7)));
    put_form(S::Expr::eeq(S::Expr::eref(S::CellRef{0, 0}),
                            S::Expr::eref(S::CellRef{1, 0})));
    put_form(S::Expr::elt(S::Expr::eref(S::CellRef{1, 0}),
                            S::Expr::eref(S::CellRef{0, 0})));
    put_form(S::Expr::egt(S::Expr::eref(S::CellRef{1, 0}),
                            S::Expr::eref(S::CellRef{0, 0})));
    put_form(S::Expr::eif(
        S::Expr::elt(S::Expr::eref(S::CellRef{1, 0}),
                     S::Expr::eref(S::CellRef{0, 0})),
        S::Expr::eref(S::CellRef{0, 0}),
        S::Expr::eref(S::CellRef{1, 0})));
    put_form(S::Expr::eif(S::Expr::eint(0),
                            S::Expr::eint(99),
                            S::Expr::eint(-1)));
  }

  if (failures == 0) std::printf("OK (all kernel cases pass)\n");
  else std::printf("FAILED (%d)\n", failures);
  return failures;
}
