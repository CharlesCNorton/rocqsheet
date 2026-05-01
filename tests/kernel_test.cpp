// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Runtime tests over the Crane-extracted Rocqsheet kernel.  These
// complement the Rocq-side theorems by exercising the actual C++
// extraction at runtime.

#include "rocqsheet.h"

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
    return S::eval_cell(S::DEFAULT_FUEL, local, c1);
  };

  check("add", eval_with(S::Expr::eadd(S::Expr::eref(a1), S::Expr::eref(b1))), 13);
  check("sub", eval_with(S::Expr::esub(S::Expr::eref(a1), S::Expr::eref(b1))),  7);
  check("mul", eval_with(S::Expr::emul(S::Expr::eref(a1), S::Expr::eref(b1))), 30);
  check("div", eval_with(S::Expr::ediv(S::Expr::eref(a1), S::Expr::eref(b1))),  3);
  check_none("div-by-zero",
      eval_with(S::Expr::ediv(S::Expr::eref(a1), S::Expr::eint(0))));

  // Empty cell evaluates as 0.
  check("empty-cell", S::eval_cell(S::DEFAULT_FUEL, S::new_sheet, S::CellRef{5, 5}), 0);

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
    check("multi-letter sum",
        S::eval_cell(S::DEFAULT_FUEL, wide, c1), 1000);
  }

  // Dependency chain: A1=1, A2=A1+1, ..., A50=A49+1.  The visited-set
  // distinguishes this legitimate chain from a cycle.
  {
    auto chain = S::set_cell(S::new_sheet, S::CellRef{0, 0}, S::Cell::clit(1));
    for (int r = 1; r < 50; ++r) {
      auto e = S::Expr::eadd(
          S::Expr::eref(S::CellRef{0, r - 1}),
          S::Expr::eint(1));
      chain = S::set_cell(chain, S::CellRef{0, r},
                          S::Cell::cform(std::move(e)));
    }
    check("50-chain", S::eval_cell(S::DEFAULT_FUEL, chain, S::CellRef{0, 49}), 50);
    check_none("low-fuel",
        S::eval_cell(5, chain, S::CellRef{0, 49}));
  }

  // Two-cell cycle: A1 <-> B1 returns None on either entry point.
  {
    auto cyc = S::set_cell(S::new_sheet, a1,
        S::Cell::cform(S::Expr::eref(b1)));
    cyc = S::set_cell(cyc, b1, S::Cell::cform(S::Expr::eref(a1)));
    check_none("cycle@A1", S::eval_cell(S::DEFAULT_FUEL, cyc, a1));
    check_none("cycle@B1", S::eval_cell(S::DEFAULT_FUEL, cyc, b1));
  }

  if (failures == 0) std::printf("OK (all kernel cases pass)\n");
  else std::printf("FAILED (%d)\n", failures);
  return failures;
}
