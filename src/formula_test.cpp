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

  want_ok("mod",         "10%3");
  want_ok("mod-prec",    "1+10%3");
  want_ok("pow",         "2^10");
  want_ok("pow-mix",     "2^3*4");
  want_fail("mod-trail", "10%");
  want_fail("pow-trail", "2^");

  want_ok("not",         "NOT(0)");
  want_ok("not-lower",   "not(A1)");
  want_ok("and",         "AND(A1,B1)");
  want_ok("or",          "OR(A1,B1)");
  want_ok("not-nested",  "NOT(AND(A1,B1))");
  want_fail("not-bare",  "NOT");
  want_fail("not-noargs","NOT()");
  want_fail("and-1arg",  "AND(A1)");

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

  // date functions.
  want_ok("date3",     "DATE(2026,6,4)");
  want_ok("weekday",   "WEEKDAY(A1)");
  want_ok("edate",     "EDATE(A1,1)");
  want_ok("eomonth",   "EOMONTH(A1,0)");
  want_ok("date-expr", "DATE(2026,B1,4)");
  want_ok("datedif",   "DATEDIF(A1,B1,2)");
  want_ok("datedif-expr", "DATEDIF(DATE(2000,6,4),DATE(2026,6,4),0)");
  want_fail("date-2arg",   "DATE(2026,6)");
  want_fail("edate-1arg",  "EDATE(A1)");
  want_fail("datedif-2arg", "DATEDIF(A1,B1)");

  // exact-match lookups.
  want_ok("vlookup",      "VLOOKUP(20,A1:C3,2)");
  want_ok("hlookup",      "HLOOKUP(20,A1:C3,2)");
  want_ok("match",        "MATCH(30,A1:A5)");
  want_ok("index",        "INDEX(A1:C3,2,2)");
  want_ok("vlookup-expr", "VLOOKUP(B1+1,A1:C3,2)");
  want_fail("vlookup-2arg", "VLOOKUP(20,A1:C3)");
  want_fail("index-1arg",   "INDEX(A1:C3,2)");
  want_fail("match-norange","MATCH(30)");

  // approximate-match modes via the literal fourth / third argument.
  want_ok("vlookup-approx",  "VLOOKUP(25,A1:C3,2,1)");
  want_ok("vlookup-exact4",  "VLOOKUP(25,A1:C3,2,0)");
  want_ok("vlookup-true",    "VLOOKUP(25,A1:C3,2,TRUE)");
  want_ok("vlookup-false",   "VLOOKUP(25,A1:C3,2,FALSE)");
  want_ok("hlookup-approx",  "HLOOKUP(25,A1:C3,2,1)");
  want_ok("match-approx",    "MATCH(25,A1:A5,1)");
  want_ok("match-exact3",    "MATCH(25,A1:A5,0)");
  want_fail("vlookup-badmode", "VLOOKUP(25,A1:C3,2,7)");
  want_fail("match-badmode",   "MATCH(25,A1:A5,9)");

  // order statistics and NPV.
  want_ok("median",       "MEDIAN(A1:A5)");
  want_ok("mode",         "MODE(A1:A5)");
  want_ok("rank",         "RANK(5,A1:A5)");
  want_ok("rank-expr",    "RANK(B1+1,A1:A5)");
  want_ok("percentile",   "PERCENTILE(A1:A5,50)");
  want_ok("npv",          "NPV(2,A1:A5)");
  want_fail("median-noargs", "MEDIAN()");
  want_fail("rank-norange",  "RANK(5)");
  want_fail("npv-norange",   "NPV(2)");

  // string operators.
  want_ok("upper",        "UPPER(\"x\")");
  want_ok("lower",        "LOWER(A1)");
  want_ok("trim",         "TRIM(\" x \")");
  want_ok("upper-nested", "UPPER(LOWER(A1))");
  want_ok("find",         "FIND(\"a\",A1)");
  want_ok("replace4",     "REPLACE(A1,2,3,\"Z\")");
  want_fail("upper-noargs", "UPPER()");
  want_fail("find-1arg",    "FIND(A1)");
  want_fail("replace-3arg", "REPLACE(A1,2,3)");

  // variance / standard deviation.
  want_ok("var",       "VAR(A1:A8)");
  want_ok("varp",      "VARP(A1:A8)");
  want_ok("stdev",     "STDEV(A1:A8)");
  want_ok("stdevp",    "STDEVP(A1:A8)");
  want_ok("var-lower", "var(A1:A8)");
  want_fail("var-bare",   "VAR");
  want_fail("var-noargs", "VAR()");

  // IF-aggregates.
  want_ok("sumif",          "SUMIF(A1:A5,>4,C1)");
  want_ok("countif",        "COUNTIF(A1:A5,=3)");
  want_ok("countif-neg",    "COUNTIF(A1:A5,<-3)");
  want_ok("averageif",      "AVERAGEIF(A1:A5,<8,C1)");
  want_ok("sumif-lower",    "sumif(A1:A5,>4,C1)");
  want_fail("sumif-nopred", "SUMIF(A1:A5,C1)");
  want_fail("countif-noargs", "COUNTIF()");
  want_fail("averageif-norange", "AVERAGEIF(A1,>4,C1)");

  // counting aggregates.
  want_ok("count",        "COUNT(A1:B2)");
  want_ok("counta",       "COUNTA(A1:B2)");
  want_ok("range-size",   "RANGE_SIZE(A1:B2)");
  want_fail("count-bare", "COUNT");
  want_fail("counta-noargs", "COUNTA()");

  // float / string / bool literals.
  want_ok("float",           "1.5");
  want_ok("float-pi",        "3.14");
  want_ok("float-zero-frac", "2.0");
  want_ok("neg-float",       "-2.5");
  want_ok("float-arith",     "1.5+2.5");
  want_fail("trailing-dot",  "1.");
  want_fail("bare-dot",      ".5");
  want_ok("true",            "TRUE");
  want_ok("false",           "FALSE");
  want_ok("true-lower",      "true");
  want_ok("false-mixed",     "False");
  want_fail("true-suffix",   "TRUEX");
  want_fail("false-suffix",  "FALSE1");
  want_ok("string",          "\"hello\"");
  want_ok("string-empty",    "\"\"");
  want_ok("string-spaces",   "\"two words\"");
  want_ok("string-concat-shape", "IF(A1,\"yes\",\"no\")");
  want_fail("string-unterminated", "\"abc");

  if (failures == 0) std::printf("OK (all parser cases pass)\n");
  else std::printf("FAILED (%d)\n", failures);
  return failures;
}
