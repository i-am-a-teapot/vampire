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

#include <iosfwd>
#include <set>
#include <unordered_set>
#include "Forwards.hpp"
#include "Kernel/InferenceStore.hpp"

namespace Shell {
namespace LeanProof {

bool isUncheckedStep(InferenceRule rule);
void outputLeanPreamble(std::ostream &out);
void outputCombinedProofHeader(std::ostream &out, Kernel::UnitList *inputs);
void outputProofInputs(std::ostream &out, Kernel::UnitList *inputs);



template<typename Compare>
void outputCombinationStep(std::ostream &out, const std::set<Kernel::Unit *, Compare> &proof){
  std::unordered_set<unsigned> takenSteps;
  uint lastStepNumber = 0;
  for (Unit* u : proof){
    if(isUncheckedStep(u->inference().rule()))
      continue;
    out << "have h" << u->number() << " := step" << u->number() << " ";
    takenSteps.insert(u->number());
    for (Unit *parent : iterTraits(u->getParents())) {
      if(takenSteps.find(parent->number()) == takenSteps.end()) {
        out << "step" << parent->number() << " ";
      } else {
        out << "h" << parent->number() << " ";
      }
    }
    out << " \n";
    lastStepNumber = u->number();
  }
  out << "exact h" << lastStepNumber << "\n";
}

void outputStep(std::ostream &out, Kernel::Unit *u);
void outputStepIfAxiom(std::ostream &out, Unit *u);

}
}
