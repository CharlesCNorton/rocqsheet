// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.

#include "eval_iter.h"

#include <climits>
#include <memory>
#include <utility>
#include <vector>

namespace formula {
namespace {

using Sheet = Rocqsheet::Sheet;
using Cell = Rocqsheet::Cell;
using Expr = Rocqsheet::Expr;
using CellRef = Rocqsheet::CellRef;

bool ref_eq(const CellRef& a, const CellRef& b) {
  return a.ref_col == b.ref_col && a.ref_row == b.ref_row;
}

bool mem_ref(const CellRef& r, const std::vector<CellRef>& visited) {
  for (const auto& v : visited) {
    if (ref_eq(v, r)) return true;
  }
  return false;
}

// Saturating int64 arithmetic mirroring the Z.add/sub/mul overrides
// in theories/Rocqsheet.v.
int64_t sat_add(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_add_overflow(a, b, &r)) return a < 0 ? INT64_MIN : INT64_MAX;
  return r;
}
int64_t sat_sub(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_sub_overflow(a, b, &r)) return a < 0 ? INT64_MIN : INT64_MAX;
  return r;
}
int64_t sat_mul(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_mul_overflow(a, b, &r)) {
    return ((a < 0) != (b < 0)) ? INT64_MIN : INT64_MAX;
  }
  return r;
}

enum class Op { Add, Sub, Mul, Div };

struct Cont {
  enum class Kind { EvalRight, CombineLeft };
  Kind kind;
  Op op;
  std::vector<CellRef> visited;
  const Expr* right_expr = nullptr;
  int64_t val_left = 0;
};

}  // namespace

std::optional<int64_t> eval_iter(const Sheet& sheet, const CellRef& root_ref) {
  // get_cell returns a Cell by value; we need to keep every CForm Cell
  // we ever follow alive for the lifetime of the loop, because cur_e
  // is a pointer into one of them.  unique_ptr storage gives stable
  // addresses across vector growth.
  std::vector<std::unique_ptr<Cell>> owned;

  auto root_cell = Rocqsheet::get_cell(sheet, root_ref);
  if (std::holds_alternative<Cell::CEmpty>(root_cell.v())) return int64_t(0);
  if (std::holds_alternative<Cell::CLit>(root_cell.v())) {
    return std::get<Cell::CLit>(root_cell.v()).d_a0;
  }
  owned.push_back(std::make_unique<Cell>(std::move(root_cell)));
  const Expr* cur_e = &std::get<Cell::CForm>(owned.back()->v()).d_a0;

  std::vector<Cont> stack;
  std::vector<CellRef> visited;
  visited.push_back(root_ref);

  bool have_val = false;
  std::optional<int64_t> cur_val;

  while (true) {
    if (!have_val) {
      const auto& v = cur_e->v();
      if (std::holds_alternative<Expr::EInt>(v)) {
        cur_val = std::get<Expr::EInt>(v).d_a0;
        have_val = true;
      } else if (std::holds_alternative<Expr::ERef>(v)) {
        const auto& r = std::get<Expr::ERef>(v).d_a0;
        if (mem_ref(r, visited)) {
          cur_val = std::nullopt;
          have_val = true;
        } else {
          auto target_cell = Rocqsheet::get_cell(sheet, r);
          const auto& tv = target_cell.v();
          if (std::holds_alternative<Cell::CEmpty>(tv)) {
            cur_val = int64_t(0);
            have_val = true;
          } else if (std::holds_alternative<Cell::CLit>(tv)) {
            cur_val = std::get<Cell::CLit>(tv).d_a0;
            have_val = true;
          } else {
            owned.push_back(std::make_unique<Cell>(std::move(target_cell)));
            visited.push_back(r);
            cur_e = &std::get<Cell::CForm>(owned.back()->v()).d_a0;
            // have_val remains false
          }
        }
      } else {
        Op op;
        const Expr* a;
        const Expr* b;
        if (std::holds_alternative<Expr::EAdd>(v)) {
          op = Op::Add;
          a = std::get<Expr::EAdd>(v).d_a0.get();
          b = std::get<Expr::EAdd>(v).d_a1.get();
        } else if (std::holds_alternative<Expr::ESub>(v)) {
          op = Op::Sub;
          a = std::get<Expr::ESub>(v).d_a0.get();
          b = std::get<Expr::ESub>(v).d_a1.get();
        } else if (std::holds_alternative<Expr::EMul>(v)) {
          op = Op::Mul;
          a = std::get<Expr::EMul>(v).d_a0.get();
          b = std::get<Expr::EMul>(v).d_a1.get();
        } else {
          op = Op::Div;
          a = std::get<Expr::EDiv>(v).d_a0.get();
          b = std::get<Expr::EDiv>(v).d_a1.get();
        }
        Cont k;
        k.kind = Cont::Kind::EvalRight;
        k.op = op;
        k.visited = visited;
        k.right_expr = b;
        stack.push_back(std::move(k));
        cur_e = a;
        // have_val remains false
      }
    } else {
      if (!cur_val.has_value()) {
        // Failure propagates: drop the pending continuation stack.
        return std::nullopt;
      }
      if (stack.empty()) {
        return cur_val;
      }
      Cont top = std::move(stack.back());
      stack.pop_back();
      if (top.kind == Cont::Kind::EvalRight) {
        Cont next;
        next.kind = Cont::Kind::CombineLeft;
        next.op = top.op;
        next.val_left = *cur_val;
        stack.push_back(std::move(next));
        visited = std::move(top.visited);
        cur_e = top.right_expr;
        have_val = false;
      } else {
        int64_t l = top.val_left;
        int64_t r = *cur_val;
        switch (top.op) {
          case Op::Add: cur_val = sat_add(l, r); break;
          case Op::Sub: cur_val = sat_sub(l, r); break;
          case Op::Mul: cur_val = sat_mul(l, r); break;
          case Op::Div:
            if (r == 0) {
              cur_val = std::nullopt;
            } else {
              cur_val = l / r;
            }
            break;
        }
      }
    }
  }
}

}  // namespace formula
