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
    return std::hash<int64_t>{}(r.ref_col * 1'000'003LL + r.ref_row);
  }
};
struct CellRefEq {
  bool operator()(const CellRef& a, const CellRef& b) const noexcept {
    return a.ref_col == b.ref_col && a.ref_row == b.ref_row;
  }
};
using VisitedSet = std::unordered_set<CellRef, CellRefHash, CellRefEq>;

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
int64_t int_pow(int64_t base, int64_t exp) {
  if (exp < 0) return 0;
  int64_t r = 1;
  for (int64_t i = 0; i < exp; ++i) r = sat_mul(r, base);
  return r;
}

enum class Op {
  Add, Sub, Mul, Div, Eq, Lt, Gt, Mod, Pow, And, Or
};

struct Cont {
  enum class Kind { EvalRight, CombineLeft, IfChoose, NotFinish, IfErrFallback };
  Kind kind;
  Op op;
  VisitedSet visited;
  const Expr* right_expr = nullptr;
  const Expr* else_expr = nullptr;
  int64_t val_left = 0;
};

// Forward declaration so the range-aggregation helpers can recurse.
std::optional<int64_t> eval_iter_impl(const Sheet& sheet, const CellRef& root,
                                       VisitedSet visited);

// Walk a (tl, br) rectangle invoking [f] on each in-range cell's value.
// [f] receives (col, row, opt) where opt is nullopt when the cell does not
// reduce to an integer (empty cells contribute 0; non-int cells contribute
// nullopt and the aggregator chooses the policy).
template <typename F>
void walk_range(const Sheet& sheet, const CellRef& tl, const CellRef& br,
                const VisitedSet& visited, F&& f) {
  int64_t lc = tl.ref_col, hc = br.ref_col;
  int64_t lr = tl.ref_row, hr = br.ref_row;
  if (hc < lc || hr < lr) return;
  for (int64_t r = lr; r <= hr; ++r) {
    for (int64_t c = lc; c <= hc; ++c) {
      CellRef ref{c, r};
      auto cell = Rocqsheet::get_cell(sheet, ref);
      const auto& cv = cell.v();
      std::optional<int64_t> v;
      if (std::holds_alternative<Cell::CEmpty>(cv)) {
        v = int64_t(0);
      } else if (std::holds_alternative<Cell::CLit>(cv)) {
        v = std::get<Cell::CLit>(cv).d_a0;
      } else if (std::holds_alternative<Cell::CForm>(cv)) {
        if (visited.count(ref)) {
          v = std::nullopt;
        } else {
          VisitedSet sub = visited;
          sub.insert(ref);
          v = eval_iter_impl(sheet, ref, std::move(sub));
        }
      } else {
        v = std::nullopt;  // CFloat / CStr / CBool not representable
      }
      f(c, r, v);
    }
  }
}

// Aggregation helpers.  Each returns nullopt on any failure (range
// inversion, non-integer cell, deep-cycle).
std::optional<int64_t> agg_sum(const Sheet& sheet, const CellRef& tl,
                                const CellRef& br, const VisitedSet& visited) {
  if (br.ref_col < tl.ref_col || br.ref_row < tl.ref_row) return std::nullopt;
  int64_t acc = 0;
  bool ok = true;
  walk_range(sheet, tl, br, visited, [&](int64_t, int64_t, auto v) {
    if (!ok) return;
    if (!v.has_value()) { ok = false; return; }
    acc = sat_add(acc, *v);
  });
  if (!ok) return std::nullopt;
  return acc;
}
std::optional<int64_t> agg_count(const CellRef& tl, const CellRef& br) {
  if (br.ref_col < tl.ref_col || br.ref_row < tl.ref_row) return int64_t(0);
  int64_t cols = br.ref_col - tl.ref_col + 1;
  int64_t rows = br.ref_row - tl.ref_row + 1;
  return cols * rows;
}
std::optional<int64_t> agg_avg(const Sheet& sheet, const CellRef& tl,
                                const CellRef& br, const VisitedSet& visited) {
  auto s = agg_sum(sheet, tl, br, visited);
  auto n = agg_count(tl, br);
  if (!s.has_value() || !n.has_value() || *n == 0) return std::nullopt;
  return *s / *n;
}
std::optional<int64_t> agg_min(const Sheet& sheet, const CellRef& tl,
                                const CellRef& br, const VisitedSet& visited) {
  if (br.ref_col < tl.ref_col || br.ref_row < tl.ref_row) return std::nullopt;
  std::optional<int64_t> best;
  bool ok = true;
  walk_range(sheet, tl, br, visited, [&](int64_t, int64_t, auto v) {
    if (!ok) return;
    if (!v.has_value()) { ok = false; return; }
    if (!best.has_value() || *v < *best) best = *v;
  });
  if (!ok) return std::nullopt;
  return best;
}
std::optional<int64_t> agg_max(const Sheet& sheet, const CellRef& tl,
                                const CellRef& br, const VisitedSet& visited) {
  if (br.ref_col < tl.ref_col || br.ref_row < tl.ref_row) return std::nullopt;
  std::optional<int64_t> best;
  bool ok = true;
  walk_range(sheet, tl, br, visited, [&](int64_t, int64_t, auto v) {
    if (!ok) return;
    if (!v.has_value()) { ok = false; return; }
    if (!best.has_value() || *v > *best) best = *v;
  });
  if (!ok) return std::nullopt;
  return best;
}

// Fold a binary integer operator at the combine site.
std::optional<int64_t> apply_binop(Op op, int64_t l, int64_t r) {
  switch (op) {
    case Op::Add: return sat_add(l, r);
    case Op::Sub: return sat_sub(l, r);
    case Op::Mul: return sat_mul(l, r);
    case Op::Div: return r == 0 ? std::optional<int64_t>{} : std::optional<int64_t>{l / r};
    case Op::Mod: return r == 0 ? std::optional<int64_t>{} : std::optional<int64_t>{l % r};
    case Op::Pow: return r < 0  ? std::optional<int64_t>{} : std::optional<int64_t>{int_pow(l, r)};
    case Op::Eq:  return int64_t(l == r);
    case Op::Lt:  return int64_t(l <  r);
    case Op::Gt:  return int64_t(l >  r);
    case Op::And: return int64_t((l != 0) && (r != 0));
    case Op::Or:  return int64_t((l != 0) || (r != 0));
  }
  return std::nullopt;
}

}  // namespace

// The core iterative evaluator.  Public eval_iter delegates here with a
// fresh VisitedSet seeded with [root_ref].
namespace {

std::optional<int64_t> eval_iter_impl(const Sheet& sheet,
                                       const CellRef& root_ref,
                                       VisitedSet visited) {
  std::vector<std::unique_ptr<Cell>> owned;

  auto root_cell = Rocqsheet::get_cell(sheet, root_ref);
  if (std::holds_alternative<Cell::CEmpty>(root_cell.v())) return int64_t(0);
  if (std::holds_alternative<Cell::CLit>(root_cell.v())) {
    return std::get<Cell::CLit>(root_cell.v()).d_a0;
  }
  if (!std::holds_alternative<Cell::CForm>(root_cell.v())) {
    return std::nullopt;  // CFloat / CStr / CBool
  }
  owned.push_back(std::make_unique<Cell>(std::move(root_cell)));
  const Expr* cur_e = &std::get<Cell::CForm>(owned.back()->v()).d_a0;

  std::vector<Cont> stack;
  bool have_val = false;
  std::optional<int64_t> cur_val;

  while (true) {
    if (!have_val) {
      const auto& v = cur_e->v();

      if (std::holds_alternative<Expr::EInt>(v)) {
        cur_val = std::get<Expr::EInt>(v).d_a0;
        have_val = true;
        continue;
      }

      if (std::holds_alternative<Expr::ERef>(v)) {
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
          } else if (std::holds_alternative<Cell::CForm>(tv)) {
            owned.push_back(std::make_unique<Cell>(std::move(target_cell)));
            visited.insert(r);
            cur_e = &std::get<Cell::CForm>(owned.back()->v()).d_a0;
          } else {
            // CFloat / CStr / CBool
            cur_val = std::nullopt;
            have_val = true;
          }
        }
        continue;
      }

      if (std::holds_alternative<Expr::EIf>(v)) {
        const auto& alt = std::get<Expr::EIf>(v);
        Cont k;
        k.kind = Cont::Kind::IfChoose;
        k.visited = visited;
        k.right_expr = alt.d_a1.get();   // then
        k.else_expr  = alt.d_a2.get();
        stack.push_back(std::move(k));
        cur_e = alt.d_a0.get();
        continue;
      }

      // Unary integer-returning operators.
      if (std::holds_alternative<Expr::ENot>(v)) {
        const auto& alt = std::get<Expr::ENot>(v);
        Cont k;
        k.kind = Cont::Kind::NotFinish;
        k.visited = visited;
        stack.push_back(std::move(k));
        cur_e = alt.d_a0.get();
        continue;
      }

      // EIfErr a fb — evaluate a, on nullopt fall through to fb.
      if (std::holds_alternative<Expr::EIfErr>(v)) {
        const auto& alt = std::get<Expr::EIfErr>(v);
        Cont k;
        k.kind = Cont::Kind::IfErrFallback;
        k.visited = visited;
        k.right_expr = alt.d_a1.get();
        stack.push_back(std::move(k));
        cur_e = alt.d_a0.get();
        continue;
      }

      // Range aggregations — handled inline (no continuation needed).
      if (std::holds_alternative<Expr::ESum>(v)) {
        const auto& alt = std::get<Expr::ESum>(v);
        cur_val = agg_sum(sheet, alt.d_a0, alt.d_a1, visited);
        have_val = true;
        continue;
      }
      if (std::holds_alternative<Expr::EAvg>(v)) {
        const auto& alt = std::get<Expr::EAvg>(v);
        cur_val = agg_avg(sheet, alt.d_a0, alt.d_a1, visited);
        have_val = true;
        continue;
      }
      if (std::holds_alternative<Expr::ECount>(v)) {
        const auto& alt = std::get<Expr::ECount>(v);
        cur_val = agg_count(alt.d_a0, alt.d_a1);
        have_val = true;
        continue;
      }
      if (std::holds_alternative<Expr::EMin>(v)) {
        const auto& alt = std::get<Expr::EMin>(v);
        cur_val = agg_min(sheet, alt.d_a0, alt.d_a1, visited);
        have_val = true;
        continue;
      }
      if (std::holds_alternative<Expr::EMax>(v)) {
        const auto& alt = std::get<Expr::EMax>(v);
        cur_val = agg_max(sheet, alt.d_a0, alt.d_a1, visited);
        have_val = true;
        continue;
      }

      // Float/string/bool constructors don't have integer projections;
      // match the spec's eval_cell which returns EFVal/EValS/EValB and
      // therefore projects to nullopt under formula::eval_iter's contract.
      if (std::holds_alternative<Expr::EFloat>(v)
          || std::holds_alternative<Expr::EFAdd>(v)
          || std::holds_alternative<Expr::EFSub>(v)
          || std::holds_alternative<Expr::EFMul>(v)
          || std::holds_alternative<Expr::EFDiv>(v)
          || std::holds_alternative<Expr::EStr>(v)
          || std::holds_alternative<Expr::EConcat>(v)
          || std::holds_alternative<Expr::ESubstr>(v)
          || std::holds_alternative<Expr::EBool>(v)
          || std::holds_alternative<Expr::EBNot>(v)
          || std::holds_alternative<Expr::EBAnd>(v)
          || std::holds_alternative<Expr::EBOr>(v)) {
        cur_val = std::nullopt;
        have_val = true;
        continue;
      }

      // ELen — string length is integer-valued in spec, but we don't
      // carry string values through eval_iter.  Return nullopt rather
      // than throw; the grid renderer uses eval_cell for strings.
      if (std::holds_alternative<Expr::ELen>(v)) {
        cur_val = std::nullopt;
        have_val = true;
        continue;
      }

      // Binary integer-returning operators.
      Op op = Op::Add;
      const Expr* a = nullptr;
      const Expr* b = nullptr;
      bool matched = true;
      if      (std::holds_alternative<Expr::EAdd>(v)) { op = Op::Add; const auto& x = std::get<Expr::EAdd>(v); a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::ESub>(v)) { op = Op::Sub; const auto& x = std::get<Expr::ESub>(v); a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EMul>(v)) { op = Op::Mul; const auto& x = std::get<Expr::EMul>(v); a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EDiv>(v)) { op = Op::Div; const auto& x = std::get<Expr::EDiv>(v); a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EEq>(v))  { op = Op::Eq;  const auto& x = std::get<Expr::EEq>(v);  a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::ELt>(v))  { op = Op::Lt;  const auto& x = std::get<Expr::ELt>(v);  a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EGt>(v))  { op = Op::Gt;  const auto& x = std::get<Expr::EGt>(v);  a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EMod>(v)) { op = Op::Mod; const auto& x = std::get<Expr::EMod>(v); a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EPow>(v)) { op = Op::Pow; const auto& x = std::get<Expr::EPow>(v); a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EAnd>(v)) { op = Op::And; const auto& x = std::get<Expr::EAnd>(v); a = x.d_a0.get(); b = x.d_a1.get(); }
      else if (std::holds_alternative<Expr::EOr>(v))  { op = Op::Or;  const auto& x = std::get<Expr::EOr>(v);  a = x.d_a0.get(); b = x.d_a1.get(); }
      else                                             { matched = false; }

      if (matched) {
        Cont k;
        k.kind = Cont::Kind::EvalRight;
        k.op = op;
        k.visited = visited;
        k.right_expr = b;
        stack.push_back(std::move(k));
        cur_e = a;
        continue;
      }

      // Catch-all safety net — a future Expr constructor that this
      // dispatch hasn't been taught about projects to nullopt instead
      // of throwing std::bad_variant_access.
      cur_val = std::nullopt;
      have_val = true;
    } else {
      if (stack.empty()) {
        return cur_val;
      }
      Cont top = std::move(stack.back());
      stack.pop_back();

      switch (top.kind) {
        case Cont::Kind::EvalRight: {
          if (!cur_val.has_value()) {
            // Short-circuit: error in left propagates without evaluating right.
            // Push back a no-op CombineLeft frame produces nullopt anyway,
            // but we can simply return early since stack/visited are now
            // unwound by the outer loop.
            return std::nullopt;
          }
          Cont next;
          next.kind = Cont::Kind::CombineLeft;
          next.op = top.op;
          next.val_left = *cur_val;
          stack.push_back(std::move(next));
          visited = std::move(top.visited);
          cur_e = top.right_expr;
          have_val = false;
          break;
        }
        case Cont::Kind::CombineLeft: {
          if (!cur_val.has_value()) return std::nullopt;
          cur_val = apply_binop(top.op, top.val_left, *cur_val);
          // have_val stays true; cur_val may be nullopt for div/mod-zero.
          break;
        }
        case Cont::Kind::IfChoose: {
          if (!cur_val.has_value()) return std::nullopt;
          cur_e = (*cur_val != 0) ? top.right_expr : top.else_expr;
          visited = std::move(top.visited);
          have_val = false;
          break;
        }
        case Cont::Kind::NotFinish: {
          if (!cur_val.has_value()) return std::nullopt;
          cur_val = int64_t(*cur_val == 0 ? 1 : 0);
          break;
        }
        case Cont::Kind::IfErrFallback: {
          if (cur_val.has_value()) break;       // a succeeded → keep its value
          // a errored → evaluate the fallback expression instead.
          visited = std::move(top.visited);
          cur_e = top.right_expr;
          have_val = false;
          break;
        }
      }
    }
  }
}

}  // namespace

std::optional<int64_t> eval_iter(const Sheet& sheet, const CellRef& root_ref) {
  VisitedSet v;
  v.insert(root_ref);
  return eval_iter_impl(sheet, root_ref, std::move(v));
}

}  // namespace formula
