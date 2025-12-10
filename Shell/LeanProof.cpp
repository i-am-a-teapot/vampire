/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LeanProof.cpp
 * Routines for producing a Lean proof script from a Vampire proof
 */

#include <array>
#include <unordered_set>
#include <algorithm>

#include "Debug/Assertion.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/Superposition.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Exception.hpp"
#include "LeanProof.hpp"

#include "Inferences/ALASCA/BinInf.hpp"
#include "Inferences/ALASCA/FourierMotzkin.hpp"
#include "Inferences/ALASCA/Superposition.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Lib/SharedSet.hpp"
#include "Saturation/Splitter.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

using namespace Kernel;
using Indexing::Splitter;
using SortMap = DHMap<unsigned, TermList>;

// get first N parents of a unit
template <unsigned N, typename T>
std::array<T *, N> getParents(T *unit)
{
  std::array<T *, N> parents;
  UnitIterator it = unit->getParents();
  for (unsigned i = 0; i < N; i++) {
    ALWAYS(it.hasNext())
    parents[i] = static_cast<T *>(it.next());
  }
  ALWAYS(!it.hasNext())
  return parents;
}

template <bool real>
struct SMTNumeral {
  const IntegerConstantType &constant;
};

template <bool real>
static std::ostream &operator<<(std::ostream &out, SMTNumeral<real> num)
{
  if (num.constant.sign() == Sign::Neg)
    return out << "(- " << num.constant.abs() << (real ? ".0" : "") << ")";
  else
    return out << num.constant << (real ? ".0" : "");
}

struct Escaped {
  const char *name;
};

static std::ostream &operator<<(std::ostream &out, Escaped escaped)
{
  out << "_";
  for (const char *c = escaped.name; *c; c++)
    if (*c == '_')
      out << '+';
    else
      out << *c;
  return out ;
}

struct FunctionName {
  FunctionName(Signature::Symbol *symbol) : symbol(symbol) {}
  FunctionName(Term *t) : FunctionName(env.signature->getFunction(t->functor())) {}
  Signature::Symbol *symbol;
};

bool isInfix(const Signature::InterpretedSymbol *sym)
{
  switch (sym->getInterpretation()) {
    case Theory::EQUAL:
    case Theory::INT_GREATER:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_LESS:
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_DIVIDES:
    case Theory::RAT_GREATER:
    case Theory::RAT_GREATER_EQUAL:
    case Theory::RAT_LESS:
    case Theory::RAT_LESS_EQUAL:
    case Theory::REAL_GREATER:
    case Theory::REAL_GREATER_EQUAL:
    case Theory::REAL_LESS:
    case Theory::REAL_LESS_EQUAL:
    case Theory::INT_PLUS:
    case Theory::RAT_PLUS:
    case Theory::REAL_PLUS:
    case Theory::INT_MINUS:
    case Theory::RAT_MINUS:
    case Theory::REAL_MINUS:
    case Theory::INT_MULTIPLY:
    case Theory::RAT_MULTIPLY:
    case Theory::REAL_MULTIPLY:
    case Theory::INT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT:
    case Theory::REAL_QUOTIENT:
    case Theory::INT_QUOTIENT_T:
    case Theory::INT_QUOTIENT_F:
    case Theory::RAT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT_T:
    case Theory::RAT_QUOTIENT_F:
    case Theory::REAL_QUOTIENT_E:
    case Theory::REAL_QUOTIENT_T:
    case Theory::REAL_QUOTIENT_F:
    case Theory::INT_REMAINDER_E:
    case Theory::INT_REMAINDER_T:
    case Theory::INT_REMAINDER_F:
    case Theory::RAT_REMAINDER_E:
    case Theory::RAT_REMAINDER_T:
    case Theory::RAT_REMAINDER_F:
    case Theory::REAL_REMAINDER_E:
    case Theory::REAL_REMAINDER_T:
    case Theory::REAL_REMAINDER_F:
      return true;
    case Theory::INT_IS_INT:
    case Theory::INT_IS_RAT:
    case Theory::INT_IS_REAL:
    case Theory::RAT_IS_INT:
    case Theory::RAT_IS_RAT:
    case Theory::RAT_IS_REAL:
    case Theory::REAL_IS_INT:
    case Theory::REAL_IS_RAT:
    case Theory::REAL_IS_REAL:
    case Theory::INT_SUCCESSOR:
    case Theory::INT_UNARY_MINUS:
    case Theory::RAT_UNARY_MINUS:
    case Theory::REAL_UNARY_MINUS:
    case Theory::INT_TRUNCATE:
    case Theory::RAT_TRUNCATE:
    case Theory::REAL_TRUNCATE:
    case Theory::INT_ROUND:
    case Theory::RAT_ROUND:
    case Theory::REAL_ROUND:
    case Theory::INT_ABS:
    case Theory::RAT_TO_INT:
    case Theory::REAL_TO_INT:
    case Theory::INT_TO_RAT:
    case Theory::INT_TO_REAL:
    case Theory::INT_TO_INT:
    case Theory::RAT_TO_RAT:
    case Theory::RAT_TO_REAL:
    case Theory::REAL_TO_RAT:
    case Theory::REAL_TO_REAL:
    case Theory::RAT_FLOOR:
    case Theory::REAL_FLOOR:
    case Theory::RAT_CEILING:
    case Theory::REAL_CEILING:
    case Theory::INT_FLOOR:
    case Theory::INT_CEILING:
    case Theory::ARRAY_SELECT:
    case Theory::ARRAY_BOOL_SELECT:
    case Theory::ARRAY_STORE:
    case Theory::INVALID_INTERPRETATION:
      return false;
  }
  return false;
}

static std::ostream &operator<<(std::ostream &out, FunctionName name)
{
  auto f = name.symbol;
  if (!f->interpreted())
    return out << Escaped{f->name().c_str()};
  if (f->integerConstant())
    return out << SMTNumeral<false>{f->integerValue()};
  if (f->rationalConstant() || f->realConstant()) {
    auto rat = f->rationalConstant() ? f->rationalValue() : f->realValue();
    return out << "(" << SMTNumeral<true>{rat.numerator()} << '/' << SMTNumeral<true>{rat.denominator()} << ")";
  }
  auto *interpreted = static_cast<Signature::InterpretedSymbol *>(f);
  switch (interpreted->getInterpretation()) {
    case Theory::EQUAL:
    case Theory::INT_IS_INT:
    case Theory::INT_IS_RAT:
    case Theory::INT_IS_REAL:
    case Theory::INT_GREATER:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_LESS:
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_DIVIDES:
    case Theory::RAT_IS_INT:
    case Theory::RAT_IS_RAT:
    case Theory::RAT_IS_REAL:
    case Theory::RAT_GREATER:
    case Theory::RAT_GREATER_EQUAL:
    case Theory::RAT_LESS:
    case Theory::RAT_LESS_EQUAL:
    case Theory::REAL_IS_INT:
    case Theory::REAL_IS_RAT:
    case Theory::REAL_IS_REAL:
    case Theory::REAL_GREATER:
    case Theory::REAL_GREATER_EQUAL:
    case Theory::REAL_LESS:
    case Theory::REAL_LESS_EQUAL:
      // should be predicates, not functions
      ASSERTION_VIOLATION
    case Theory::INT_SUCCESSOR:
      NOT_IMPLEMENTED;
    case Theory::INT_UNARY_MINUS:
    case Theory::RAT_UNARY_MINUS:
    case Theory::REAL_UNARY_MINUS:
      return out << '-';
    case Theory::INT_PLUS:
    case Theory::RAT_PLUS:
    case Theory::REAL_PLUS:
      return out << '+';
    case Theory::INT_MINUS:
    case Theory::RAT_MINUS:
    case Theory::REAL_MINUS:
      return out << '-';
    case Theory::INT_MULTIPLY:
    case Theory::RAT_MULTIPLY:
    case Theory::REAL_MULTIPLY:
      return out << '*';
    case Theory::INT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT:
    case Theory::REAL_QUOTIENT:
      return out << '/';
    case Theory::INT_QUOTIENT_T:
    case Theory::INT_QUOTIENT_F:
    case Theory::RAT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT_T:
    case Theory::RAT_QUOTIENT_F:
    case Theory::REAL_QUOTIENT_E:
    case Theory::REAL_QUOTIENT_T:
    case Theory::REAL_QUOTIENT_F:
      NOT_IMPLEMENTED;
    case Theory::INT_REMAINDER_E:
      return out << "mod";
    case Theory::INT_REMAINDER_T:
    case Theory::INT_REMAINDER_F:
    case Theory::RAT_REMAINDER_E:
    case Theory::RAT_REMAINDER_T:
    case Theory::RAT_REMAINDER_F:
    case Theory::REAL_REMAINDER_E:
    case Theory::REAL_REMAINDER_T:
    case Theory::REAL_REMAINDER_F:
      NOT_IMPLEMENTED;
    case Theory::INT_TRUNCATE:
    case Theory::RAT_TRUNCATE:
    case Theory::REAL_TRUNCATE:
      NOT_IMPLEMENTED;
    case Theory::INT_ROUND:
    case Theory::RAT_ROUND:
    case Theory::REAL_ROUND:
      NOT_IMPLEMENTED;
    case Theory::INT_ABS:
      NOT_IMPLEMENTED;
    case Theory::RAT_TO_INT:
    case Theory::REAL_TO_INT:
      return out << "to_int";
    case Theory::INT_TO_RAT:
    case Theory::INT_TO_REAL:
      return out << "to_real";
    // should be handled specially at the term level
    case Theory::INT_TO_INT:
    case Theory::RAT_TO_RAT:
    case Theory::RAT_TO_REAL:
    case Theory::REAL_TO_RAT:
    case Theory::REAL_TO_REAL:
    case Theory::RAT_FLOOR:
    case Theory::REAL_FLOOR:
    case Theory::RAT_CEILING:
    case Theory::REAL_CEILING:
      ASSERTION_VIOLATION
    // weird, not sure what these would do
    case Theory::INT_FLOOR:
    case Theory::INT_CEILING:
      ASSERTION_VIOLATION
    case Theory::ARRAY_SELECT:
    case Theory::ARRAY_BOOL_SELECT:
    case Theory::ARRAY_STORE:
      NOT_IMPLEMENTED;
    case Theory::INVALID_INTERPRETATION:
      ASSERTION_VIOLATION
  }
  return out;
}

struct PredicateName {
  PredicateName(Signature::Symbol *symbol) : symbol(symbol) {}
  PredicateName(Literal *l) : PredicateName(env.signature->getPredicate(l->functor())) {}
  Signature::Symbol *symbol;
};

static std::ostream &operator<<(std::ostream &out, PredicateName name)
{
  auto p = name.symbol;
  if (!p->interpreted())
    return out << Escaped{p->name().c_str()};
  auto *interpreted = static_cast<Signature::InterpretedSymbol *>(p);
  switch (interpreted->getInterpretation()) {
    case Theory::EQUAL:
      return out << '=';
    case Theory::RAT_IS_INT:
    case Theory::REAL_IS_INT:
      return out << "is_int";
    case Theory::REAL_IS_RAT:
      return out << "is_rat";
    case Theory::INT_IS_INT:
    case Theory::INT_IS_RAT:
    case Theory::RAT_IS_RAT:
    case Theory::INT_IS_REAL:
    case Theory::RAT_IS_REAL:
    case Theory::REAL_IS_REAL:
      // should be special-cased at the term level
      ASSERTION_VIOLATION
    case Theory::INT_GREATER:
    case Theory::RAT_GREATER:
    case Theory::REAL_GREATER:
      return out << '>';
    case Theory::INT_GREATER_EQUAL:
    case Theory::RAT_GREATER_EQUAL:
    case Theory::REAL_GREATER_EQUAL:
      return out << ">=";
    case Theory::INT_LESS:
    case Theory::RAT_LESS:
    case Theory::REAL_LESS:
      return out << '<';
    case Theory::INT_LESS_EQUAL:
    case Theory::RAT_LESS_EQUAL:
    case Theory::REAL_LESS_EQUAL:
      return out << "<=";
    case Theory::INT_DIVIDES:
      NOT_IMPLEMENTED;

    case Theory::INT_SUCCESSOR:
    case Theory::INT_UNARY_MINUS:
    case Theory::INT_PLUS:
    case Theory::INT_MINUS:
    case Theory::INT_MULTIPLY:
    case Theory::INT_QUOTIENT_E:
    case Theory::INT_QUOTIENT_T:
    case Theory::INT_QUOTIENT_F:
    case Theory::INT_REMAINDER_E:
    case Theory::INT_REMAINDER_T:
    case Theory::INT_REMAINDER_F:
    case Theory::INT_FLOOR:
    case Theory::INT_CEILING:
    case Theory::INT_TRUNCATE:
    case Theory::INT_ROUND:
    case Theory::INT_ABS:
    case Theory::RAT_UNARY_MINUS:
    case Theory::RAT_PLUS:
    case Theory::RAT_MINUS:
    case Theory::RAT_MULTIPLY:
    case Theory::RAT_QUOTIENT:
    case Theory::RAT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT_T:
    case Theory::RAT_QUOTIENT_F:
    case Theory::RAT_REMAINDER_E:
    case Theory::RAT_REMAINDER_T:
    case Theory::RAT_REMAINDER_F:
    case Theory::RAT_FLOOR:
    case Theory::RAT_CEILING:
    case Theory::RAT_TRUNCATE:
    case Theory::RAT_ROUND:
    case Theory::REAL_UNARY_MINUS:
    case Theory::REAL_PLUS:
    case Theory::REAL_MINUS:
    case Theory::REAL_MULTIPLY:
    case Theory::REAL_QUOTIENT:
    case Theory::REAL_QUOTIENT_E:
    case Theory::REAL_QUOTIENT_T:
    case Theory::REAL_QUOTIENT_F:
    case Theory::REAL_REMAINDER_E:
    case Theory::REAL_REMAINDER_T:
    case Theory::REAL_REMAINDER_F:
    case Theory::REAL_FLOOR:
    case Theory::REAL_CEILING:
    case Theory::REAL_TRUNCATE:
    case Theory::REAL_ROUND:
    case Theory::INT_TO_INT:
    case Theory::INT_TO_RAT:
    case Theory::INT_TO_REAL:
    case Theory::RAT_TO_INT:
    case Theory::RAT_TO_RAT:
    case Theory::RAT_TO_REAL:
    case Theory::REAL_TO_INT:
    case Theory::REAL_TO_RAT:
    case Theory::REAL_TO_REAL:
    case Theory::ARRAY_SELECT:
    case Theory::ARRAY_BOOL_SELECT:
    case Theory::ARRAY_STORE:
      // should be predicates, not functions
      ASSERTION_VIOLATION
    case Theory::INVALID_INTERPRETATION:
      ASSERTION_VIOLATION
  }
  return out;
}

struct Blank {};
static std::ostream &operator<<(std::ostream &out, Blank) { return out; }
struct Inhabit {};
static std::ostream &operator<<(std::ostream &out, Inhabit) { return out << "inhabit_"; }

template <typename Prefix = Blank>
struct SortName {
  SortName(unsigned functor) : functor(functor) {}
  SortName(AtomicSort *s) : functor(s->functor()) {}
  unsigned functor;
};

template <typename Prefix>
static std::ostream &operator<<(std::ostream &out, SortName<Prefix> name)
{
  Prefix prefix;
  switch (name.functor) {
    case Signature::DEFAULT_SORT_CON:
      return out << prefix << "iota";
    case Signature::BOOL_SRT_CON:
      return out << prefix << "Bool";
    case Signature::INTEGER_SRT_CON:
      return out << prefix << "Int";
    // SMT-LIB doesn't have rationals
    case Signature::RATIONAL_SRT_CON:
    case Signature::REAL_SRT_CON:
      return out << prefix << "Real";
  }
  return out << '|' << prefix << '_' << env.signature->getTypeCon(name.functor)->name() << '|';
}

struct Args {
  TermList *start;
  SortMap &conclSorts;
  SortMap &otherSorts;
};

void printArgs(std::ostream &out, Args args, bool recurse = false)
{
  if (args.start->isEmpty())
    return;
  TermList *current = args.start;
  if (current->isVar()) {
    unsigned var = current->var();
    if (args.conclSorts.findPtr(var)) {
        out << "v" << var;
    }
    else {
      out << SortName<Inhabit>(static_cast<AtomicSort *>(args.otherSorts.get(var).term()));
    }
    return;
  }
  bool printed = false;
  if (current->isTerm()) {
    Term *term = current->term();
    FunctionName name(term);
    if (term->arity()) {
      if (name.symbol->interpreted()) {
        auto interpreted = static_cast<Signature::InterpretedSymbol *>(name.symbol);
        if (isInfix(interpreted) && term->arity() == 2) {
          current = term->termArgs();
          out << "(";
          printArgs(out, Args{current, args.conclSorts, args.otherSorts}, recurse);
          out << name;
          printArgs(out, Args{current->next(), args.conclSorts, args.otherSorts}, recurse);
          out << ")";
          printed = true;
        }
      }
      else if (name.symbol->linMul()) {
        out << "(";
        if (auto attempt = env.signature->tryLinMul<IntegerConstantType>(term->functor()); attempt.isSome()) {
          auto factor = SMTNumeral<false>{attempt.unwrap()};
          out << factor << "*";
        }
        else if (auto attempt = env.signature->tryLinMul<RationalConstantType>(term->functor()); attempt.isSome()) {
          auto factor = attempt.unwrap();
          out << "( " << SMTNumeral<true>{factor.numerator()} << "/" << SMTNumeral<true>{factor.denominator()} << ")";
        }
        else if (auto attempt = env.signature->tryLinMul<RealConstantType>(term->functor()); attempt.isSome()) {
          auto factor = attempt.unwrap();
          out << "( " << SMTNumeral<true>{factor.numerator()} << "/" << SMTNumeral<true>{factor.denominator()} << ")";
        }
        else
          ASSERTION_VIOLATION
        printArgs(out, Args{term->termArgs(), args.conclSorts, args.otherSorts}, recurse);
        out << ")";
        printed = true;
      }
    }
    if (!printed) {
      current = term->termArgs();
      out << "(" << name << " ";
      while (!current->isEmpty()) {
        printArgs(out, Args{current, args.conclSorts, args.otherSorts}, recurse);
        current = current->next();
        out << (current->isEmpty() ? "" : " ");
      }
      out << ")";
    }
  }
  else {
    out << "missing term implementation for Lean output" << std::endl;
    ASSERTION_VIOLATION
  }
}

static std::ostream &operator<<(std::ostream &out, Args args)
{
  printArgs(out, args, true);
  return out;
}

struct Lit {
  Literal *literal;
  SortMap &conclSorts;
  SortMap &otherSorts;
};

void printLiteral(std::ostream &out, Lit lit)
{
  Literal *literal = lit.literal;
  PredicateName name(literal);
  if (!literal->polarity())
    out << "(¬";
  if (literal->arity())
    out << "(";
  if (name.symbol->interpreted()) {
    auto interpreted = static_cast<Signature::InterpretedSymbol *>(name.symbol);
    switch (interpreted->getInterpretation()) {
      case Theory::INT_IS_INT:
      case Theory::INT_IS_RAT:
      case Theory::INT_IS_REAL:
      case Theory::RAT_IS_RAT:
      case Theory::RAT_IS_REAL:
      case Theory::REAL_IS_REAL:
        out << "true";
      default:
        break;
    }
    if (isInfix(interpreted) && literal->arity() == 2) {
      TermList *current = literal->args();
      printArgs(out, Args{current, lit.conclSorts, lit.otherSorts}, false);
      out << name;
      printArgs(out, Args{current->next(), lit.conclSorts, lit.otherSorts}, true);
    }
    else {
      out << name;
      printArgs(out, Args{literal->args(), lit.conclSorts, lit.otherSorts}, true);
    }
  }
  else {
    printArgs(out, Args{literal->args(), lit.conclSorts, lit.otherSorts}, true);
  }
  if (literal->arity())
    out << ")";
  if (!literal->polarity())
    out << ")";
}

static std::ostream &operator<<(std::ostream &out, Lit lit)
{
  printLiteral(out, lit);
  return out;
}

struct Sort {
  TermList sort;
};

static std::ostream &operator<<(std::ostream &out, Sort print)
{
  AtomicSort *sort = static_cast<AtomicSort *>(print.sort.term());
  // don't support type constructors yet
  ASS_EQ(sort->arity(), 0)
  return out << SortName(sort);
}

template <bool flip = false>
struct Split {
  unsigned level;
  Split(unsigned level) : level(level) {}
};

template <bool flip>
static std::ostream &operator<<(std::ostream &out, Split<flip> split)
{
  SATLiteral sat = Splitter::getLiteralFromName(split.level);
  return out
      << (flip == sat.positive() ? "(¬ " : "")
      << "sp" << sat.var()
      << (flip == sat.positive() ? ")" : "");
}

struct Identity {
  Literal *operator()(Literal *l) { return l; }
  TermList operator()(unsigned int var){ return TermList::var(var); }
};

struct DoSubst {
  Substitution &subst;
  DoSubst(Substitution &subst) : subst(subst) {}
  Literal *operator()(Literal *l) { return SubstHelper::apply(l, subst); }
  TermList operator()(unsigned int var){ return subst.apply(var); }
};

template <unsigned bank>
struct DoRobSubst {
  const RobSubstitution &subst;
  DoRobSubst(const RobSubstitution &subst) : subst(subst) {}
  Literal *operator()(Literal *l) { return subst.apply(l, bank); }
  TermList operator()(unsigned int var){ return subst.apply(TermList::var(var),bank); }
};

void outputSortsWithQuantor(std::ostream &out, SortMap &sorts, std::string quantor = "∀")
{
  if(sorts.isEmpty())
    return;
  auto it = sorts.items();
  std::map<TermList, std::vector<unsigned>> varsBySort;
  while (it.hasNext()) {
    auto [var, sort] = it.next();
    varsBySort[sort].push_back(var);
  }
  bool first = true;
  for (auto &[sort, vars] : varsBySort) {
    std::sort(vars.begin(), vars.end());
    if (!first)
      out << ", ";
    out << quantor;
    for (unsigned var : vars) {
      out << " v" << var;
    }
    out << " : " << Sort{sort};
  }
  out << ", ";
}

void printFormula(std::ostream &out, Formula *f, SortMap &conclSorts, SortMap &otherSorts)
{
  switch (f->connective()) {
    case LITERAL:
      printLiteral(out, Lit{f->literal(), conclSorts, otherSorts});
      break;
    case AND: {
      out << "(";
      Kernel::FormulaList* reversedList = FormulaList::reverse(FormulaList::copy(f->args()));
      auto args = reversedList->iter();
      while (args.hasNext()) {
        printFormula(out, args.next(), conclSorts, otherSorts);
        if (args.hasNext())
          out << " ∧ ";
      }
      FormulaList::destroy(reversedList);
      out << ")";
    } break;
    case OR: {
      out << "( ";
      auto reversedList =  FormulaList::reverse(FormulaList::copy(f->args()));
      //auto args = f->args()->iter();
      auto args = reversedList->iter();
      while (args.hasNext()) {
        printFormula(out, args.next(), conclSorts, otherSorts);
        if (args.hasNext())
          out << " ∨ ";
      }
      FormulaList::destroy(reversedList);
      out << ")";
    } break;
    case IMP:
      out << "(";
      printFormula(out, f->left(), conclSorts, otherSorts);
      out << " → ";
      printFormula(out, f->right(), conclSorts, otherSorts);
      out << ")";
      break;
    case IFF:
      out << "(";
      printFormula(out, f->left(), conclSorts, otherSorts);
      out << " ↔ ";
      printFormula(out, f->right(), conclSorts, otherSorts);
      out << ")";
      break;
    case XOR:
      out << "¬(";
      printFormula(out, f->left(), conclSorts, otherSorts);
      out << " ↔ ";
      printFormula(out, f->right(), conclSorts, otherSorts);
      out << ")";
      break;
    case NOT:
      out << "(¬";
      printFormula(out, f->uarg(), conclSorts, otherSorts);
      out << ")";
      break;
    case FORALL: {
      VList::Iterator vs(f->vars());
      SList::Iterator ss(f->sorts());
      SortMap map;
      while(ss.hasNext() && vs.hasNext()) {
        auto sort = ss.next();
        auto var = vs.next();
        map.insert(var, sort);
      }
      outputSortsWithQuantor(out, map, "∀");
      printFormula(out, f->qarg(), conclSorts, otherSorts);
    } break;
    case EXISTS: {
      VList::Iterator vs(f->vars());
      SList::Iterator ss(f->sorts());
      SortMap map;
      while(ss.hasNext() && vs.hasNext()) {
        auto sort = ss.next();
        auto var = vs.next();
        map.insert(var, sort);
      }
      outputSortsWithQuantor(out, map, "∃");
      printFormula(out, f->qarg(), conclSorts, otherSorts);
    } break;
    case BOOL_TERM:
      out << "missing bool term implementation for Lean output" << std::endl;
      ASSERTION_VIOLATION
      break;
    case TRUE:
      out << "true";
      break;
    case FALSE:
      out << "⊥";
      break;
    default:
      ASSERTION_VIOLATION
  }
}



template <typename Transform = Identity>
static void outputPremise(std::ostream &out, SortMap &conclSorts, Clause *cl, Transform transform = Transform{}, bool useConclSorts = false)
{
  out << " (";
  bool first = true;
  SortMap sorts;
  SortHelper::collectVariableSorts(cl, sorts);
  outputSortsWithQuantor(out, sorts);
  for (Literal *l : *cl) {
    if (!first)
      out << " ∨ ";
    l = transform(l);
    if(useConclSorts)
      out << Lit{l, conclSorts, sorts};
    else
      out << Lit{l, sorts, sorts};
    first = false;
  }
  out << ")";
}

static void outputPremiseFormula(std::ostream &out, SortMap &conclSorts, Formula *f, bool useConclSorts = false)
{
  out << " (";
  bool first = true;
  SortMap sorts;
  SortHelper::collectVariableSorts(f, sorts);
  if (useConclSorts)
    printFormula(out, f, conclSorts, sorts);
  else
    printFormula(out, f, sorts, sorts);
  out << ")";
}

static void outputConclusion(std::ostream &out, SortMap &conclSorts, Clause *cl)
{
  if(cl->isEmpty()) {
    out << "⊥";
    return;
  }
  bool first = true;
  out << "(";
  SortMap otherSorts;
  SortHelper::collectVariableSorts(cl, otherSorts);
  outputSortsWithQuantor(out, conclSorts);
  for (Literal *l : *cl) {
    if (!first) {
      out << " ∨ ";
    }
    printLiteral(out, Lit{l, conclSorts, otherSorts});
    first = false;
  }
  out << ")";
}
template <typename Transform = Identity>
static void outputVariables(std::ostream &out, VirtualIterator<unsigned int> const &iterator , SortMap &conclSorts, SortMap &varSorts, Transform trans=Transform{}){
  Kernel::VStack vars = Stack<unsigned>::fromIterator(iterator);
  vars.sort();
  for (auto var: vars) {
    TermList translatedTerm = trans(var);
    SortMap newVarSorts;
    if(translatedTerm.isVar())
    {
      newVarSorts.insert(translatedTerm.var(), varSorts.get(var));
    }
    else if(translatedTerm.isTerm())
    {
      SortHelper::collectVariableSorts(translatedTerm.term(), newVarSorts);
    } else {
      ASSERTION_VIOLATION
    }
    out << Args{&translatedTerm, conclSorts, newVarSorts} << " ";
  }
}

static void axiom(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  outputConclusion(out, conclSorts, concl->asClause());
}

static void trivial(std::ostream &out, SortMap &conclSorts, Clause *concl, std::string tactic = "aesop")
{
  UnitIterator parents = concl->getParents();
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    ASS(parent->isClause())
    outputPremise(out, conclSorts, parent->asClause());
    out << " → ";
  }
  outputConclusion(out, conclSorts, concl->asClause());
  out << " := by\n  " << tactic << "\n";
}

static void resolution(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  const auto &br = env.proofExtra.get<Inferences::BinaryResolutionExtra>(concl);

  auto uwa = AbstractingUnifier::empty(AbstractionOracle(env.options->unificationWithAbstraction()));
  Literal *selectedLeft = br.selectedLiteral.selectedLiteral;
  Literal *selectedRight = br.otherLiteral;
  for (unsigned i = 0; i < selectedLeft->arity(); i++)
    ALWAYS(uwa.unify((*selectedLeft)[i], 0, (*selectedRight)[i], 1))
  ASS_NEQ(selectedLeft->polarity(), selectedRight->polarity())
  RobSubstitution &subst = uwa.subs();
  /*for (unsigned i = 0; i < left->length(); i++)
   if ((*left)[i] != selectedLeft)
      subst.apply((*left)[i], 0);
  for (unsigned i = 0; i < right->length(); i++)
  if ((*right)[i] != selectedRight)
      subst.apply((*right)[i], 1);
  */
  outputPremise(out, conclSorts, left->asClause());
  out << " → ";
  outputPremise(out, conclSorts, right->asClause());
  out << " → ";
  outputConclusion(out, conclSorts, concl->asClause());
  out << " := by";
  out << "\n  intros h1 h2 ";
  outputVariables(out, conclSorts.domain(), conclSorts, conclSorts);
  out << "\n  have l := (h1 ";
  SortMap varSorts;
  SortHelper::collectVariableSorts(left,varSorts);
  outputVariables(out, left->getVariableIterator(), conclSorts, varSorts, DoRobSubst<0>(subst));
  out << ")\n  have r := (h2 ";
  varSorts.reset();
  SortHelper::collectVariableSorts(right,varSorts);
  outputVariables(out,right->getVariableIterator(),conclSorts, varSorts,DoRobSubst<1>(subst));
  out << ")\n  exact resolve l r\n";
}

static void subsumptionResolution(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  auto sr = env.proofExtra.get<Inferences::LiteralInferenceExtra>(concl);
  Literal *m = sr.selectedLiteral;

  // reconstruct match by calling into the SATSR code
  SATSubsumption::SATSubsumptionAndResolution satSR;
  ALWAYS(satSR.checkSubsumptionResolutionWithLiteral(right, left, left->getLiteralPosition(m)))
  auto subst = satSR.getBindingsForSubsumptionResolutionWithLiteral();
  SortMap sorts;
  SortHelper::collectVariableSorts(left, sorts);
  outputPremise(out, sorts, left->asClause(), Identity(), true);
  out << " → ";
  sorts = SortMap();
  SortHelper::collectVariableSorts(right, sorts);
  outputPremise(out, sorts, right->asClause(), Identity(), true);
  out << " → ";
  outputConclusion(out, conclSorts, concl->asClause());

  out << " := by\n  intros h1 h2 ";
  outputVariables(out, conclSorts.domain(), conclSorts, conclSorts);
  out << "\n  have l := (h1 ";
  sorts = SortMap();
  SortHelper::collectVariableSorts(left, sorts);
  outputVariables(out, left->getVariableIterator(), conclSorts, sorts);
  out << ")\n  have r := (h2 ";
  outputVariables(out, right->getVariableIterator(), conclSorts, sorts, DoSubst(subst));
  out << ")\n  exact resolve l r\n";
}

static void factoring(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [premise] = getParents<1>(concl);
  const auto &fact = env.proofExtra.get<Inferences::FactoringExtra>(concl);

  RobSubstitution subst;
  Literal *selected = fact.selectedLiteral.selectedLiteral;
  Literal *other = fact.otherLiteral;
  ASS_EQ(selected->polarity(), other->polarity())
  ASS_EQ(selected->functor(), other->functor())
  ALWAYS(subst.unify(TermList(selected), 0, TermList(other), 0));

  for (unsigned i = 0; i < premise->length(); i++)
    if ((*premise)[i] != other)
      subst.apply((*premise)[i], 0);

  outputPremise(out, conclSorts, premise->asClause());
  out << " → ";
  outputConclusion(out, conclSorts, concl->asClause());
}

static void equalityResolution(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [premise] = getParents<1>(concl);
  const auto &res = env.proofExtra.get<Inferences::EqualityResolutionExtra>(concl);

  RobSubstitution subst;
  Literal *selected = res.selectedLiteral;
  ASS(selected->isEquality())
  ASS(selected->isNegative())
  TermList s = selected->termArg(0), t = selected->termArg(1);
  ALWAYS(subst.unify(s, 0, t, 0));
  for (unsigned i = 0; i < premise->length(); i++)
    if ((*premise)[i] != selected)
      subst.apply((*premise)[i], 0);

  outputPremise(out, conclSorts, premise->asClause());
  out << " → ";
  outputConclusion(out, conclSorts, concl->asClause());
}

static void superposition(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  auto sup = env.proofExtra.get<Inferences::SuperpositionExtra>(concl);

  // compute unifier for selected literals

  RobSubstitution subst;
  Literal *leftSelected = sup.selected.selectedLiteral.selectedLiteral;
  Literal *rightSelected = sup.selected.otherLiteral;
  TermList from = sup.rewrite.lhs;
  TermList to = EqHelper::getOtherEqualitySide(rightSelected, from);
  TermList target = sup.rewrite.rewritten;
  ASS(rightSelected->isEquality())
  ASS(rightSelected->isPositive())
  ASS(rightSelected->termArg(0) == from || rightSelected->termArg(1) == from)
  ALWAYS(subst.unify(target, 0, from, 1))

  subst.apply(to, 1);
  subst.apply(leftSelected, 0);
  subst.apply(target, 0);
  subst.apply(from, 1);
  /*
  for (unsigned i = 0; i < left->length(); i++)
    if ((*left)[i] != leftSelected)
      subst.apply((*left)[i], 0);
  for (unsigned i = 0; i < right->length(); i++)
    if ((*right)[i] != rightSelected)
      subst.apply((*right)[i], 1);
  */
  outputPremise(out, conclSorts, left->asClause());
  out << " → ";
  outputPremise(out, conclSorts, right->asClause());
  out << " → ";
  outputConclusion(out, conclSorts, concl->asClause());
  out << " := by\n  intros h1 h2 ";
  outputVariables(out, conclSorts.domain(), conclSorts, conclSorts);
  out << "\n  have l := (h1 ";
  SortMap varSorts;
  SortHelper::collectVariableSorts(left, varSorts);
  outputVariables(out, left->getVariableIterator(), conclSorts, varSorts, DoRobSubst<0>(subst));
  out << ")\n  have r := (h2 ";
  varSorts.reset();
  SortHelper::collectVariableSorts(right, varSorts);
  outputVariables(out, right->getVariableIterator(), conclSorts, varSorts, DoRobSubst<1>(subst));
  out << ")\n  first | exact superpose l r | exact superpose r l\n";
}

// check whether `demodulator` l = r rewrites left-to-right in the context of C[t] -> C[s]
// TODO copied from Dedukti, merge at some point
static bool isL2RDemodulatorFor(Literal *demodulator, Clause *rewritten, TermList target, Clause *result)
{
  ASS(demodulator->isEquality())
  ASS(demodulator->isPositive())

  // TODO this is waaay overkill, but it's very hard to work out which way a demodulator was used
  // consult MH about how best to do this
  Substitution subst;
  if (!MatchingUtils::matchTerms(demodulator->termArg(0), target, subst))
    return false;
  TermList rhsSubst = SubstHelper::apply(demodulator->termArg(1), subst);

  for (Literal *l : rewritten->iterLits())
    if (!result->contains(l) && !result->contains(EqHelper::replace(l, target, rhsSubst)))
      return false;

  return true;
}

static void demodulation(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  auto rw = env.proofExtra.get<Inferences::RewriteInferenceExtra>(concl);

  Substitution subst;
  Literal *rightLit = (*right)[0];
  TermList target = rw.rewritten;
  TermList from = rightLit->termArg(!isL2RDemodulatorFor(rightLit, left, target, concl));
  ASS(rightLit->isEquality())
  ASS(rightLit->isPositive())
  ASS(rightLit->termArg(0) == from || rightLit->termArg(1) == from)
  ALWAYS(MatchingUtils::matchTerms(from, target, subst))

  outputPremise(out, conclSorts, left->asClause());
  out << " → ";
  outputPremise(out, conclSorts, right->asClause());
  out << " → ";
  outputConclusion(out, conclSorts, concl->asClause());

  out << " := by\n  intros h1 h2 ";
  outputVariables(out, conclSorts.domain(), conclSorts, conclSorts);
  out << "\n  have l := (h1 ";
  SortMap varSorts;
  SortHelper::collectVariableSorts(left, varSorts);
  outputVariables(out, left->getVariableIterator(), conclSorts, varSorts);
  out << ")\n  have r := (h2 ";
  varSorts.reset();
  SortHelper::collectVariableSorts(right, varSorts);
  outputVariables(out, right->getVariableIterator(), conclSorts, varSorts, DoSubst(subst));
  out << ")\n  first | exact superpose l r | exact superpose r l\n";

}

static void splitClause(std::ostream &out, SortMap &conclSorts, Unit *concl)
{
  ASS(conclSorts.isEmpty())

  SATClause *sat = env.proofExtra.get<Indexing::SATClauseExtra>(concl).clause;
  std::unordered_set<unsigned> seen;
  for (SATLiteral l : sat->iter())
    if (seen.insert(l.var()).second)
      out << "(declare-const sp" << l.var() << " Bool)\n";

  auto parents = concl->getParents();
  ALWAYS(parents.hasNext())
  Clause *split = parents.next()->asClause();
  outputPremise(out, conclSorts, split);
  for (Unit *u : iterTraits(parents)) {
    Clause *component = env.proofExtra.get<Indexing::SplitDefinitionExtra>(u).component;
    SortMap otherSorts;
    SortHelper::collectVariableSorts(component, otherSorts);
    out << "(assert (= " << Split{component->splits()->sval()} << " (or";
    for (Literal *l : *component)
      out << ' ' << Lit{l, conclSorts, otherSorts};
    out << ")))\n";
  }

  for (SATLiteral l : sat->iter())
    out
        << "(assert "
        << (l.positive() ? "(¬ " : "")
        << "sp" << l.var()
        << (l.positive() ? ")" : "")
        << ")\n";
}

static void satRefutation(std::ostream &out, SortMap &conclSorts, Unit *concl)
{
  std::unordered_set<unsigned> seen;
  for (Unit *u : iterTraits(concl->getParents()))
    for (SATLiteral l : env.proofExtra.get<Indexing::SATClauseExtra>(u).clause->iter())
      if (seen.insert(l.var()).second)
        out << "(declare-const sp" << l.var() << " Bool)\n";

  for (Unit *u : iterTraits(concl->getParents())) {
    out << "(assert (or";
    for (SATLiteral l : env.proofExtra.get<Indexing::SATClauseExtra>(u).clause->iter())
      out
          << ' ' << (l.positive() ? "" : "(¬ ")
          << "sp" << l.var()
          << (l.positive() ? "" : ")");
    out << "))\n";
  }
}

template <class Rule>
static void alascaBinInf(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  const auto &fm = env.proofExtra.get<ALASCA::BinInfExtra<Rule>>(concl);

  auto uwa = AbstractingUnifier::empty(AbstractionOracle(env.options->unificationWithAbstraction()));
  ALWAYS(uwa.unify(fm.left.key(), 0, fm.right.key(), 1))
  RobSubstitution &subst = uwa.subs();

  subst.apply(fm.left.literal(), 0);
  subst.apply(fm.right.literal(), 1);
  for (unsigned i = 0; i < left->length(); i++)
    subst.apply((*left)[i], 0);
  for (unsigned i = 0; i < right->length(); i++)
    subst.apply((*right)[i], 1);

  outputPremise(out, conclSorts, left->asClause(), DoRobSubst<0>(subst));
  outputPremise(out, conclSorts, right->asClause(), DoRobSubst<1>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void outputSplits(std::ostream &out, Unit *u)
{
  if (!u->isClause())
    return;
  Clause *cl = u->asClause();
  if (!cl->splits())
    return;
  SplitSet &clSplits = *cl->splits();

  std::unordered_set<unsigned> splits;
  for (unsigned i = 0; i < clSplits.size(); i++)
    splits.insert(clSplits[i]);

  UnitIterator parents = u->getParents();
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    if (!parent->isClause())
      continue;
    Clause *cl = parent->asClause();
    if (!cl->splits())
      continue;
    SplitSet &clSplits = *cl->splits();
    for (unsigned i = 0; i < clSplits.size(); i++)
      splits.insert(clSplits[i]);
  }

  for (unsigned split : splits)
    out << "(declare-const sp" << Splitter::getLiteralFromName(split).var() << " Bool)\n";
}

static void normalForm(std::ostream &out, SortMap &conclSorts, Unit *u, Kernel::InferenceRule rule)
{
  UnitIterator parents = u->getParents();
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    SortMap map;
    SortHelper::collectVariableSorts(parent, map);
    out << "(";
    printFormula(out, parent->getFormula(), conclSorts, map);
    out << ")";
    out << " → ";
  }
  auto formula = u->getFormula();
  SortMap otherSorts;
  SortHelper::collectVariableSorts(u, otherSorts);
  out << "(";
  printFormula(out, formula, conclSorts, otherSorts);
  out << ")";
  out << ":= by grind\n";
  // This should be nicer in the future depending on InferenceRule
}

static void collectUninterpretedSymbols(TermList *terms, std::set<Signature::Symbol*> &symbols) {
  while(!terms->isEmpty()) {
    if (!terms->isTerm()) {
      terms = terms->next();
      continue;
    }
    FunctionName funcName(terms->term());
    if (!funcName.symbol->interpreted()) {
      symbols.insert(funcName.symbol);
    }
    TermList* termArgs = terms->term()->termArgs();
    collectUninterpretedSymbols(termArgs, symbols);
    terms = terms->next();
  }
}


static void collectUninterpretedSymbols(Formula *f, std::set<Signature::Symbol*> &symbols) {
  switch(f->connective()) {
    case LITERAL: {
      Literal * lit = f->literal();
      PredicateName name(lit);
      if (!name.symbol->interpreted()) {
        symbols.insert(name.symbol);
      }
      collectUninterpretedSymbols(lit->args(), symbols);
      break;
    }
    case AND:
    case OR: {
      auto args = f->args()->iter();
      while(args.hasNext()) {
        collectUninterpretedSymbols(args.next(), symbols);
      }
      break;
    }
    case IMP:
    case IFF:
    case XOR: {
      collectUninterpretedSymbols(f->left(), symbols);
      collectUninterpretedSymbols(f->right(), symbols);
      break;
    }
    case NOT: {
      collectUninterpretedSymbols(f->uarg(), symbols);
      break;
    }
    case FORALL:
    case EXISTS: {
      collectUninterpretedSymbols(f->qarg(), symbols);
      break;
    }
    case BOOL_TERM:
      // TODO
      ASSERTION_VIOLATION
      break;
    case TRUE:
    case FALSE:
      break;
    default:
      ASSERTION_VIOLATION
  }
}

static void skolemize(std::ostream &out, SortMap &conclSorts, Unit *u)
{
  UnitIterator parents = u->getParents();
  //The first parent is the original formula
  Unit *parent = parents.next();
  std::set<Signature::Symbol *> parentSymbols;
  collectUninterpretedSymbols(parent->getFormula(), parentSymbols);
  //The second parent is the choice axiom
  ASS(parents.hasNext());
  Unit *choiceAxiom = parents.next();
  //we need to determine the skolem constants/functions introduced
  std::set<Signature::Symbol *> choiceSymbols;
  collectUninterpretedSymbols(choiceAxiom->getFormula(), choiceSymbols);
  

  //There should be one new symbol in the difference of sets
  std::set<Signature::Symbol*> diff;
  std::set_difference(choiceSymbols.begin(), choiceSymbols.end(), 
                      parentSymbols.begin(), parentSymbols.end(), 
                      std::inserter(diff, diff.begin()));
      
  out << " rcases step" << parent->number() << " with ⟨ ";
  for ( auto var: diff){
    out << FunctionName(var) << " ,"; 
  }
  out << " step" << u->number() << "⟩\n";
  out << " rw [eq_comm] at step" << u->number() << "\n";
}
/*
static void choiceAxiom(std::ostream &out, SortMap &conclSorts, Unit *u)
{
  UnitIterator parents = u->getParents();
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    outputPremiseFormula(out, conclSorts, parent->getFormula());
    out << " → ";
  }
  auto formula = u->getFormula();
  SortMap otherSorts;
  SortHelper::collectVariableSorts(u, otherSorts);
  out << "(";
  printFormula(out, formula, conclSorts, otherSorts);
  out << ")";
  out << ":= by\n intro h\n";
  out << " obtain ⟨f, hf⟩ := h \n";
  out << " simp_all\n";
}*/

static void evaluation(std::ostream &out, SortMap &conclSorts, Unit *u)
{
  UnitIterator parents = u->getParents();
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    SortMap map;
    SortHelper::collectVariableSorts(parent, map);
    out << "(";
    printFormula(out, parent->getFormula(), conclSorts, map);
    out << ")";
    out << " → ";
  }
  auto formula = u->getFormula();
  SortMap otherSorts;
  SortHelper::collectVariableSorts(u, otherSorts);
  out << "(";
  printFormula(out, formula, conclSorts, otherSorts);
  out << ")";
  out << ":= by\n  intros h ";
  outputVariables(out, conclSorts.domain(), conclSorts, conclSorts);
  out << "\n  have h1 := h ";
  outputVariables(out, otherSorts.domain(), otherSorts, otherSorts);
  out << "\n  norm_num1\n";
  out << "  norm_num1 at h\n";
  out << "  simp_all\n";
}

namespace Shell {
namespace LeanProof {

bool isUncheckedStep(InferenceRule rule) {
  return
      // can't check the input
      rule == InferenceRule::INPUT
      // can't check distinctness axioms
      || rule == InferenceRule::DISTINCTNESS_AXIOM
      // can't check definition introduction
      || rule == InferenceRule::AVATAR_DEFINITION || rule == InferenceRule::AVATAR_COMPONENT
      // nothing to check here
      || rule == InferenceRule::AVATAR_CONTRADICTION_CLAUSE;
}

void outputCombinedProofHeader(std::ostream &out, Kernel::UnitList *inputs){
  out << "have fullProof : ";
  auto iter = inputs->iter();
  while(iter.hasNext()){
    Unit* input = iter.next();
    SortMap sorts;
    SortHelper::collectVariableSorts(input, sorts);
    out << "(";
    outputPremiseFormula(out, sorts, input->getFormula());
    out << ") → ";
  }
  out << "⊥ := by\n";
  out << "  intros ";
  iter = inputs->iter();
  while(iter.hasNext()){
    Unit* input = iter.next();
    out << "inf_s" << input->number() << " ";
  }
  out << "\n";
}

void outputProofInputs(std::ostream &out, Kernel::UnitList *inputs){
  auto iter = inputs->iter();
  out << "theorem proof : ";
   while(iter.hasNext()){
    Unit* input = iter.next();
    SortMap sorts;
    SortHelper::collectVariableSorts(input, sorts);
    out << "(";
    outputPremiseFormula(out, sorts, input->getFormula());
    out << ")";
    if(iter.hasNext()){
      out << " → ";
    } 
  }

  //check if proof has a conjecture input
  bool hasConjecture = false;
  iter = inputs->iter();
  while(iter.hasNext()){
    Unit* input = iter.next();
    if(input->inputType() == UnitInputType::CONJECTURE){
      hasConjecture = true;
      break;
    }
  }
  if(!hasConjecture){
    out << " → False";
  }
  out << " := by\n intros ";
  Unit* input;
  iter = inputs->iter();
  while(iter.hasNext()){
    input = iter.next();
    if(input->inputType() != UnitInputType::CONJECTURE){
      out << "step" << input->number() << " ";
    } else {
      break;
    }
  }
  out << "\n";
}

bool isAxiom(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::THA_COMMUTATIVITY:
    case InferenceRule::THA_ASSOCIATIVITY:
    case InferenceRule::THA_RIGHT_IDENTITY:
    case InferenceRule::THA_LEFT_IDENTITY:
    case InferenceRule::THA_INVERSE_OP_OP_INVERSES:
    case InferenceRule::THA_INVERSE_OP_UNIT:
    case InferenceRule::THA_INVERSE_ASSOC:
    case InferenceRule::THA_NONREFLEX:
    case InferenceRule::THA_TRANSITIVITY:
    case InferenceRule::THA_ORDER_TOTALITY:
    case InferenceRule::THA_ORDER_MONOTONICITY:
    case InferenceRule::THA_ALASCA:
    case InferenceRule::THA_PLUS_ONE_GREATER:
    case InferenceRule::THA_ORDER_PLUS_ONE_DICHOTOMY:
    case InferenceRule::THA_MINUS_MINUS_X:
    case InferenceRule::THA_TIMES_ZERO:
    case InferenceRule::THA_DISTRIBUTIVITY:
    case InferenceRule::THA_DIVISIBILITY:
    case InferenceRule::THA_MODULO_MULTIPLY:
    case InferenceRule::THA_MODULO_POSITIVE:
    case InferenceRule::THA_MODULO_SMALL:
    case InferenceRule::THA_DIVIDES_MULTIPLY:
    case InferenceRule::THA_NONDIVIDES_SKOLEM:
    case InferenceRule::THA_ABS_EQUALS:
    case InferenceRule::THA_ABS_MINUS_EQUALS:
    case InferenceRule::THA_QUOTIENT_NON_ZERO:
    case InferenceRule::THA_QUOTIENT_MULTIPLY:
    case InferenceRule::THA_EXTRA_INTEGER_ORDERING:
    case InferenceRule::THA_FLOOR_SMALL:
    case InferenceRule::THA_FLOOR_BIG:
    case InferenceRule::THA_CEILING_BIG:
    case InferenceRule::THA_CEILING_SMALL:
    case InferenceRule::THA_TRUNC1:
    case InferenceRule::THA_TRUNC2:
    case InferenceRule::THA_TRUNC3:
    case InferenceRule::THA_TRUNC4:
    case InferenceRule::THA_ARRAY_EXTENSIONALITY:
    case InferenceRule::THA_BOOLEAN_ARRAY_EXTENSIONALITY:
    case InferenceRule::THA_BOOLEAN_ARRAY_WRITE1:
    case InferenceRule::THA_BOOLEAN_ARRAY_WRITE2:
    case InferenceRule::THA_ARRAY_WRITE1:
    case InferenceRule::THA_ARRAY_WRITE2:
    case InferenceRule::TERM_ALGEBRA_ACYCLICITY_AXIOM:
    case InferenceRule::TERM_ALGEBRA_DIRECT_SUBTERMS_AXIOM:
    case InferenceRule::TERM_ALGEBRA_SUBTERMS_TRANSITIVE_AXIOM:
    case InferenceRule::TERM_ALGEBRA_DISCRIMINATION_AXIOM:
    case InferenceRule::TERM_ALGEBRA_DISTINCTNESS_AXIOM:
    case InferenceRule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM:
    case InferenceRule::TERM_ALGEBRA_INJECTIVITY_AXIOM:
    case InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE:
    case InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE:
      return true;
    default:
      return false;
  }
}

void outputStepIfAxiom(std::ostream &out, Unit *u){
  InferenceRule rule = u->inference().rule();
  if (!isAxiom(rule))
    return;

  out << "\n-- step " << u->number() << " " << ruleName(rule) << "\n";

  bool sorry = false;
  SortMap conclSorts;
  SortHelper::collectVariableSorts(u, conclSorts);
  out << "axiom step" << u->number() << " : ";
  axiom(out, conclSorts, u->asClause());
  out << "\n";
} 


void outputStep(std::ostream &out, Unit *u)
{
  InferenceRule rule = u->inference().rule();
  if (isUncheckedStep(rule))
    return;
   if(isAxiom(rule)) {
    // axioms are handled elsewhere
    return;
  }
  out << "\n-- step " << u->number() << " " << ruleName(rule) << "\n";

  bool sorry = false;
  SortMap conclSorts;
  SortHelper::collectVariableSorts(u, conclSorts);

 

  switch (rule) {
    case InferenceRule::EVALUATION:
      out << " have inf_s" << u->number() << " : ";
      evaluation(out, conclSorts, u);
      break;
    case InferenceRule::NEGATED_CONJECTURE:
      out << " by_contra step" << u->number() << "\n"; 
      break;
    case InferenceRule::TRIVIAL_INEQUALITY_REMOVAL:
      out << " have inf_s" << u->number() << " : ";
      trivial(out, conclSorts, u->asClause(),
        "intro h1\n  repeat rewrite [neg_eq_false] at h1\n  repeat rewrite [or_false] at h1\n  exact h1");
      break;
    case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    case InferenceRule::ALASCA_NORMALIZATION:
      out << " have inf_s" << u->number() << " : ";
      trivial(out, conclSorts, u->asClause());
      break;
    case InferenceRule::RESOLUTION:
      out << " have inf_s" << u->number() << " : ";
      resolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    case InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
      out << " have inf_s" << u->number() << " : ";
      subsumptionResolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::FACTORING:
      out << " have inf_s" << u->number() << " : ";
      factoring(out, conclSorts, u->asClause());
      break;
    case InferenceRule::EQUALITY_RESOLUTION:
      out << " have inf_s" << u->number() << " : ";
      equalityResolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::SUPERPOSITION:
      out << " have inf_s" << u->number() << " : ";
      superposition(out, conclSorts, u->asClause());
      break;
    case InferenceRule::FORWARD_DEMODULATION:
    case InferenceRule::BACKWARD_DEMODULATION:
      out << " have inf_s" << u->number() << " : ";
      demodulation(out, conclSorts, u->asClause());
      break;
    case InferenceRule::AVATAR_SPLIT_CLAUSE:
      // splitClause(out, conclSorts, u);
      // break;
    case InferenceRule::AVATAR_REFUTATION:
      // satRefutation(out, conclSorts, u);
      // break;
    case InferenceRule::ALASCA_FOURIER_MOTZKIN:
      // alascaBinInf<ALASCA::FourierMotzkinConf>(out, conclSorts, u->asClause());
      // break;
    case InferenceRule::ALASCA_SUPERPOSITION:
      // alascaBinInf<ALASCA::SuperpositionConf>(out, conclSorts, u->asClause());
      // break;
    case InferenceRule::NNF:
    case InferenceRule::ENNF:
    case InferenceRule::FLATTEN:
    case InferenceRule::CLAUSIFY:
    case InferenceRule::THEORY_NORMALIZATION:
      out << " have inf_s" << u->number() << " : ";
      normalForm(out, conclSorts, u, rule);
      break;
    case InferenceRule::SKOLEMIZE:
      skolemize(out, conclSorts, u);
      break;
    default:
      sorry = true;
      //out << "(echo \"sorry: " << ruleName(rule) << "\")\n";
  }
  if (rule != InferenceRule::SKOLEMIZE && rule != InferenceRule::NEGATED_CONJECTURE && !sorry){
    out << " have step" << u->number() << " := inf_s" << u->number();
    for (auto parents = u->getParents(); parents.hasNext(); ) {
      Unit *parent = parents.next();
      out << " step" << parent->number();
    }
    out << "\n";
  }
}

void outputLeanPreamble(std::ostream &out)
{
  out << "-- Lean proof output generated by Vampire\n"
  "import Mathlib.Order.Basic\n"
  "import Mathlib.Data.Real.Basic\n"
  "import Lean\n"
  "import LeanTest.Superposition\n"
  "open Lean Elab Tactic Meta\n"
  "universe u\n"
  "set_option linter.style.longLine false\n"
  "def inhabit_Int : Int := default\n"
  "def inhabit_Real : Real := default\n"
  "def inhabit_Bool : Bool := default\n"
  "inductive iota where\n"
  "| mk\n"
  "deriving Inhabited\n\n";
  ;
  Signature &sig = *env.signature;
  for(unsigned i = Signature::FIRST_USER_CON; i < sig.typeCons(); i++) {
  //  out << "(declare-sort " << SortName(i);
  //#if VDEBUG
  //  Signature::Symbol *type = sig.getTypeCon(i);
  //  OperatorType *typeType = type->typeConType();
  //  // we don't support polymorphism yet
  //  ASS_EQ(typeType->numTypeArguments(), 0)
  //#endif
    out << "def " << SortName<Inhabit>(i) << " : " << SortName(i) << " := default\n";
  }

  for(unsigned i = 0; i < sig.functions(); i++) {
    Signature::Symbol *fun = sig.getFunction(i);
    if(fun->interpreted() || fun->linMul())
      continue;

    out << "variable (" << FunctionName(fun);
    OperatorType *type = fun->fnType();
    TermList range = type->result();

    // we don't support polymorphism yet
    ASS_EQ(type->numTypeArguments(), 0)
    out << " : (";
    for (unsigned i = 0; i < type->arity(); i++)
      out << (i == 0 ? "" : " → ") << Sort {type->arg(i)};
    if(type->arity() > 0){
      out << " → ";
    }
    out << Sort {range} << ") )\n";
  }

  /*for(unsigned i = 1; i < sig.predicates(); i++) {
    Signature::Symbol *pred = sig.getPredicate(i);
    if(pred->interpreted())
      continue;

    out << "def " << PredicateName(pred);
    OperatorType *type = pred->predType();

    // we don't support polymorphism yet
    ASS_EQ(type->numTypeArguments(), 0)
    out << " : (";
    for (unsigned i = 0; i < type->arity(); i++)
      out << (i == 0 ? "" : " ") << Sort {type->arg(i)};
    out << ") Bool)\n";
  }*/
}
} // namespace LeanProof
} // namespace Shell