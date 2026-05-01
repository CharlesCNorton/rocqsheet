// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Runtime tests over the extracted Rocq formula parser.

#include "rocqsheet.h"

#include <cstdint>
#include <cstdio>
#include <optional>
#include <string>

namespace {

int failures = 0;

void want_ok(const char* tag, const std::string& src) {
  if (!Parser::parse_formula(src).has_value()) {
    std::printf("FAIL parse(%s) [%s]\n", src.c_str(), tag);
    ++failures;
  }
}
void want_fail(const char* tag, const std::string& src) {
  if (Parser::parse_formula(src).has_value()) {
    std::printf("FAIL reject(%s) [%s]\n", src.c_str(), tag);
    ++failures;
  }
}
void want_int(const char* tag, const std::string& src, int64_t expected) {
  auto got = Parser::parse_int_literal(src);
  if (!got.has_value() || *got != expected) {
    std::printf("FAIL int(%s) [%s] got %s want %lld\n",
                src.c_str(), tag,
                got ? std::to_string(*got).c_str() : "None",
                (long long)expected);
    ++failures;
  }
}
void want_int_fail(const char* tag, const std::string& src) {
  auto got = Parser::parse_int_literal(src);
  if (got.has_value()) {
    std::printf("FAIL int_reject(%s) [%s] got %lld\n",
                src.c_str(), tag, (long long)*got);
    ++failures;
  }
}

}  // namespace

int main() {
  want_ok("single", "A1");
  want_ok("single", "Z100");
  want_ok("lower", "a1");
  want_ok("multi", "AA1");
  want_ok("multi", "BA1");
  want_ok("multi", "CZ1");
  want_ok("multi-lower", "cz100");
  want_ok("multi-mixed", "aA1");
  want_ok("add", "1+2");
  want_ok("prec", "1+2*3");
  want_ok("paren", "(1+2)*3");
  want_ok("deep-paren", "((((1))))");
  want_ok("unary", "-1");
  want_ok("unary-deep", "---5");
  want_ok("unary-mid", "1+-1");
  want_ok("ws", "  A1  +  B2  ");

  want_fail("row-oob", "A201");
  want_fail("col-oob", "JA1");
  want_fail("col-far-oob", "ZZ1");
  want_fail("row-zero", "A0");
  want_fail("empty", "");
  want_fail("3-letter", "AAA1");
  want_fail("trailing-op", "1+");
  want_fail("double-op", "1++1");
  want_fail("bare-letter", "A");
  want_fail("decimal", "1.5");
  want_fail("hex", "0x10");
  want_fail("paren-only", "(");
  want_fail("close-only", ")");
  want_fail("unbalanced", "(1+2");
  want_fail("extra-close", "1+2)");
  want_fail("ws-only", " ");

  want_ok("just-under-max", "9223372036854775807");
  want_fail("over-max", "9223372036854775808");
  want_fail("way-over-max", "9999999999999999999");

  want_int("zero", "0", 0);
  want_int("neg", "-42", -42);
  want_int("ws", "  17  ", 17);
  want_int_fail("mixed", "12 abc");
  want_int_fail("over", "9999999999999999999");

  want_ok("eq",          "A1=B1");
  want_ok("lt",          "A1<B1");
  want_ok("gt",          "A1>B1");
  want_ok("eq-num",      "5=5");
  want_ok("if-simple",   "IF(A1=B1,A1,B1)");
  want_ok("if-lower",    "if(A1=B1,A1,B1)");
  want_ok("if-arith",    "IF(A1+1=B1*2,1,0)");
  want_ok("if-nested",   "IF(A1<B1,IF(B1<C1,1,2),3)");
  want_ok("eq-then-arith", "1+(A1=B1)");
  want_fail("if-too-few",  "IF(A1,B1)");
  want_fail("if-no-paren", "IF A1,B1,C1");
  want_fail("if-bare",     "IF");
  want_fail("eq-trailing", "A1=");

  if (failures == 0) std::printf("OK (all parser cases pass)\n");
  else std::printf("FAILED (%d)\n", failures);
  return failures;
}
