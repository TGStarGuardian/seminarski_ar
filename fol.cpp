#include "fol.hpp"

shared_ptr<TermDatabase> TermDatabase::_term_database = nullptr;
shared_ptr<FormulaDatabase> FormulaDatabase::_formula_database = nullptr;
Formula parsed_formula = nullptr;
