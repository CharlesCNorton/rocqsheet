// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.

#include "eval_iter.h"

#include <climits>
#include <cstddef>
#include <functional>
#include <memory>
#include <unordered_set>
#include <utility>
#include <vector>

namespace formula {
namespace {

using Sheet = Rocqsheet::Sheet;
using Cell = Rocqsheet::Cell;
using Expr = Rocqsheet::Expr;
using CellRef = Rocqsheet::CellRef;

struct CellRefHash {
  std::size_t operator()(const CellRef& r) const noexcept {
    // The grid is small; mix col/row into a single key.
    return std::hash<int64_t>{}(r.ref_col * 1'000'003LL + r.ref_row);
  }
};
struct CellRefEq {
  bool operator()(const CellRef& a, const CellRef& b) const noexcept {
    return a.ref_col == b.ref_col && a.ref_row == b.ref_row;
  }
};
using VisitedSet = std::unordered_set<CellRef, CellRefHash, CellRefEq>;

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

enum class Op { Add, Sub, Mul, Div, Eq, Lt, Gt };

struct Cont {
  enum class Kind { EvalRight, CombineLeft, IfChoose };
  Kind kind;
  Op op;
  VisitedSet visited;
  // Used by EvalRight (right_expr) and IfChoose (then_expr/else_expr).
  const Expr* right_expr = nullptr;
  const Expr* else_expr = nullptr;
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
  VisitedSet visited;
  visited.insert(root_ref);

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
        if (visited.count(r)) {
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
            visited.insert(r);
            cur_e = &std::get<Cell::CForm>(owned.back()->v()).d_a0;
          }
        }
      } else if (std::holds_alternative<Expr::EIf>(v)) {
        const auto& [c_p, t_p, e_p] = std::get<Expr::EIf>(v);
        Cont k;
        k.kind = Cont::Kind::IfChoose;
        k.visited = visited;
        k.right_expr = t_p.get();    // "then" branch
        k.else_expr = e_p.get();
        stack.push_back(std::move(k));
        cur_e = c_p.get();
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
        } else if (std::holds_alternative<Expr::EDiv>(v)) {
          op = Op::Div;
          a = std::get<Expr::EDiv>(v).d_a0.get();
          b = std::get<Expr::EDiv>(v).d_a1.get();
        } else if (std::holds_alternative<Expr::EEq>(v)) {
          op = Op::Eq;
          a = std::get<Expr::EEq>(v).d_a0.get();
          b = std::get<Expr::EEq>(v).d_a1.get();
        } else if (std::holds_alternative<Expr::ELt>(v)) {
          op = Op::Lt;
          a = std::get<Expr::ELt>(v).d_a0.get();
          b = std::get<Expr::ELt>(v).d_a1.get();
        } else {
          op = Op::Gt;
          a = std::get<Expr::EGt>(v).d_a0.get();
          b = std::get<Expr::EGt>(v).d_a1.get();
        }
        Cont k;
        k.kind = Cont::Kind::EvalRight;
        k.op = op;
        k.visited = visited;
        k.right_expr = b;
        stack.push_back(std::move(k));
        cur_e = a;
      }
    } else {
      if (!cur_val.has_value()) {
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
      } else if (top.kind == Cont::Kind::IfChoose) {
        // cur_val is the cond.  Nonzero -> then; zero -> else.
        cur_e = (*cur_val != 0) ? top.right_expr : top.else_expr;
        visited = std::move(top.visited);
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
          case Op::Eq: cur_val = (l == r) ? int64_t(1) : int64_t(0); break;
          case Op::Lt: cur_val = (l <  r) ? int64_t(1) : int64_t(0); break;
          case Op::Gt: cur_val = (l >  r) ? int64_t(1) : int64_t(0); break;
        }
      }
    }
  }
}

}  // namespace formula
