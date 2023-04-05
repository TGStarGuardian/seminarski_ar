#include "fol.hpp"
#include <string>
#include <vector>
#include <list>
#include <set>

extern int yyparse();

/* Ovaj pokazivac ce nakon parsiranja dobiti vrednost 
   adrese parsirane formule. */
extern Formula parsed_formula;

using atomic_pointer = std::shared_ptr<const Atom>;

typedef struct Literal {
	Formula a;
	bool isNeg;
} Literal;

typedef struct Quant {
	std::string var;
	bool type;
} Quant;

inline
std::string print_neg(bool x) {
	return (x)? "~": "";
}

using Clause = std::vector<Literal>;

int i = 0;

void get_vars_from_term(std::set<Term>& vars, Term term) {
	BaseTerm::Type type = term->getType();
	switch(type) {
		case BaseTerm::TT_VARIABLE:
			vars.insert(TermDatabase::getTermDatabase().makeVariableTerm(term->getVariable()));
			return;
		case BaseTerm::TT_FUNCTION:
			for(Term t : term->getOperands()) {
				get_vars_from_term(vars, t);
			}
			return;
	}
}

void get_vars(std::set<Term>& vars, std::vector<Term> terms) {
	for(Term term : terms) {
		get_vars_from_term(vars, term);
	}
}

Formula tseitin_helper(const Formula&, std::vector<Clause>&, std::list<Quant>&);

void tseitin(const Formula &f, std::vector<Clause> &CNF, std::list<Quant>& quants) {
	Formula t = tseitin_helper(f, CNF, quants);
	
	// ono sto je ostalo od formule treba staviti u KNF
	CNF.push_back({Literal{t, false}});

	return;
}


Formula tseitin_helper(const Formula &f, std::vector<Clause> &CNF, std::list<Quant>& quants) {
	BaseFormula::Type type = f->getType();
	std::cout << type << '\n';
	Formula a;
	atomic_pointer t, t1, t2;
	std::vector<Term> terms;
	std::vector<Term> vars;
	std::set<Term> s;
	Term v;
	switch(type) {
		case BaseFormula::T_TRUE:
		case BaseFormula::T_FALSE:
		case BaseFormula::T_ATOM:
			// ne radimo nista kad je atom ili const u pitanju
			return f;
		case BaseFormula::T_NOT:
			// ulazimo u potformule i radimo transformaciju
			t = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand(), CNF, quants));
			// sada je umesto f->getOperand() tu formula xi
			// ~xi <=> xi+1
			// prebacujemo to u KNF
			// (~xi => xi+1) & (xi+1 => ~xi)
			// (xi | xi+1) & (~xi+1 | ~xi)
			terms.insert(terms.end(), t->getOperands().begin(), t->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			a = FormulaDatabase::getFormulaDatabase().makeAtom("x" + to_string(++i), vars);
			CNF.push_back({Literal{a, false}, Literal{t, false}});
			CNF.push_back({Literal{a, true}, Literal{t, true}});
			// vracamo xi+1
			return a;
		case BaseFormula::T_AND:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			a = FormulaDatabase::getFormulaDatabase().makeAtom("x" + to_string(++i), vars);
			// operand1 --> a, operand2 --> b
			// f --> xi+1
			// xi+1 <=> (a & b)
			// (~xi+1 | (a & b)) & (~(a & b) | xi+1)
			// (~xi+1 | a) & (~xi+1 | b) & (~a | ~b | xi+1)
			CNF.push_back({Literal{t1, false}, Literal{a, true}});
			CNF.push_back({Literal{t2, false}, Literal{a, true}});
			CNF.push_back({Literal{t1, true}, Literal{t2, true}, Literal{a, false}});
			return a;
		case BaseFormula::T_OR:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			a = FormulaDatabase::getFormulaDatabase().makeAtom("x" + to_string(++i), vars);
			// xi+1 <=> (a | b)
			// (~xi+1 | a | b) & (xi+1 | (~a & ~b))
			// (~xi+1 | a | b) & (xi+1 | ~a) & (xi+1 | ~b)
			CNF.push_back({Literal{t1, true}, Literal{a, false}});
			CNF.push_back({Literal{t2, true}, Literal{a, false}});
			CNF.push_back({Literal{t1, false}, Literal{t2, false}, Literal{a, true}});
			return a;
		case BaseFormula::T_IMP:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			a = FormulaDatabase::getFormulaDatabase().makeAtom("x" + to_string(++i), vars);
			// xi+1 <=> (a -> b)
			// (xi+1) <=> (~a | b)
			// (~xi+1 | ~a | b) & (xi+1 | a) & (xi+1 | ~b)
			CNF.push_back({Literal{t1, false}, Literal{a, false}});
			CNF.push_back({Literal{t2, true}, Literal{a, false}});
			CNF.push_back({Literal{t1, true}, Literal{t2, false}, Literal{a, true}});
			return a;
		case BaseFormula::T_IFF:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			a = FormulaDatabase::getFormulaDatabase().makeAtom("x" + to_string(++i), vars);
			// xi+1 <=> (a <=> b)
			// xi+1 <=> (~a | b) & (~b | a)
			// pravimo tablicu
			// xi+1  a   b    r
			//   0   0   0    1
			//   0   0   1    1
			//   0   1   0    1
			//   0   1   1    0
			//   1   0   0    0
			//   1   0   1    0
			//   1   1   0    0
			//   1   1   1    1
			// DNF od !F: (~xi+1 & a & b) | (xi+1 & ~a & ~b) | (xi+1 & ~a & b) | (xi+1 & a & ~b)
			// KNF od F: (xi+1 | ~a | ~b) & (~xi+1 | a | b) & (~xi+1 | a | ~b) & (~xi+1 | ~a | b)
			CNF.push_back({Literal{a, false}, Literal{t1, true}, Literal{t2, true}});
			CNF.push_back({Literal{a, true}, Literal{t1, false}, Literal{t2, false}});
			CNF.push_back({Literal{a, true}, Literal{t1, false}, Literal{t2, true}});
			CNF.push_back({Literal{a, true}, Literal{t1, true}, Literal{t2, false}});
			return a;
			
		case BaseFormula::T_FORALL:
			t = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand(), CNF, quants));
			v = TermDatabase::getTermDatabase().makeVariableTerm(f->getVariable());
			terms.insert(terms.end(), t->getOperands().begin(), t->getOperands().end());
			get_vars(s, terms);
			std::erase_if(s, [v](const Term& x){return v == x;});
			vars.insert(vars.end(), s.begin(), s.end());
			// uvodimo novi predikat p sa argumentima terms
			a = FormulaDatabase::getFormulaDatabase().makeAtom("x" + to_string(++i), vars);
			// p(terms) <=> !X.F(x, terms)
			// !X. (~p | F) & (p | ~F)
			CNF.push_back({Literal{a, true}, Literal{t, false}});
			CNF.push_back({Literal{a, false}, Literal{t, true}});
			quants.push_back(Quant{f->getVariable(), false});
			return a;
		case BaseFormula::T_EXISTS:
			t = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand(), CNF, quants));
			v = TermDatabase::getTermDatabase().makeVariableTerm(f->getVariable());
			terms.insert(terms.end(), t->getOperands().begin(), t->getOperands().end());
			get_vars(s, terms);
			std::erase_if(s, [v](const Term& x){return v == x;});
			vars.insert(vars.end(), s.begin(), s.end());
			// uvodimo novi predikat p sa argumentima terms
			a = FormulaDatabase::getFormulaDatabase().makeAtom("x" + to_string(++i), vars);
			// p(terms) <=> !X.F(x, terms)
			// !X. (~p | F) & (p | ~F)
			CNF.push_back({Literal{a, true}, Literal{t, false}});
			CNF.push_back({Literal{a, false}, Literal{t, true}});
			quants.push_back(Quant{f->getVariable(), true});
			return a;
	}
	return f;
}

int main() {
  yyparse();
  
  if(parsed_formula.get() != 0)
    cout << parsed_formula << '\n';
  
  std::vector<Clause> cnf;
  std::list<Quant> quants;
  tseitin(parsed_formula, cnf, quants);
  
  std::cout << "KNF je:\n";
  for(Clause c : cnf) {
  	for(Literal l : c) {
  		std::cout << print_neg(l.isNeg) << l.a << " ";
  	}
  	std::cout << '\n';
  }
  
  cout << endl;

  return 0;
}
