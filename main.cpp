#include "fol.hpp"
#include <string>
#include <vector>
#include <list>
#include <set>
#include <tuple>

extern int yyparse();

/* Ovaj pokazivac ce nakon parsiranja dobiti vrednost 
   adrese parsirane formule. */
extern Formula parsed_formula;

using atomic_pointer = std::shared_ptr<const Atom>;

typedef struct Literal {
	Formula a;
	bool isNeg;
} Literal;

/*
typedef struct Quant {
	Term var;
	bool type;
} Quant;
*/

using Quant = Term;

inline
std::string print_neg(bool x) {
	return (x)? "~" : "";
}
/*
inline std::string print_quant(bool x) {
	return (x)? "!" : "?"; 
}
*/
using Clause = std::vector<Literal>;

unsigned int i = 0;
long unsigned int j = 0;
long unsigned int k = 0;

void get_vars_from_term(std::set<Term>& vars, Term& term) {
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

void get_vars(std::set<Term>& vars, std::vector<Term>& terms) {
	for(Term term : terms) {
		get_vars_from_term(vars, term);
	}
}

Term rename_var_in_term(const Term& t, Term& v1, Term& v2) {
	BaseTerm::Type type = t->getType();
	switch(type) {
		case BaseTerm::TT_VARIABLE:
			return (t == v1)? v2 : t;
		case BaseTerm::TT_FUNCTION:
			std::vector<Term> operands;
			for(const Term& x : t->getOperands()) {
				operands.push_back(rename_var_in_term(x, v1, v2));
			}
			return TermDatabase::getTermDatabase().makeFunctionTerm(t->getSymbol(), operands);
	}
	return t;
}

atomic_pointer rename_var_in_atom(atomic_pointer& a, Term& v1, Term& v2) {
		std::vector<Term> operands;
		for(const Term& x : a->getOperands()) {
			operands.push_back(rename_var_in_term(x, v1, v2));
		}
		return std::dynamic_pointer_cast<const Atom>(FormulaDatabase::getFormulaDatabase().makeAtom(a->getSymbol(), operands));
}

void set_new_vars_unary(std::vector<Term> &vars, std::list<Quant>& quants, atomic_pointer &t) {
		for(Term& var : vars) {
			Term s = TermDatabase::getTermDatabase().makeVariableTerm("X" + to_string(++j));
			t = rename_var_in_atom(t, var, s);
			var = s;
			quants.push_back(var);
		}
}

void set_new_vars_binary(std::vector<Term> &vars, std::list<Quant>& quants, atomic_pointer &t1, atomic_pointer &t2) {
		for(Term& var : vars) {
			Term s = TermDatabase::getTermDatabase().makeVariableTerm("X" + to_string(++j));
			t1 = rename_var_in_atom(t1, var, s);
			t2 = rename_var_in_atom(t2, var, s);
			var = s;
			quants.push_back(var);
		}
}

Formula tseitin_helper(const Formula&, std::vector<Clause>&, std::list<Quant>&);

Formula eliminate_consts(const Formula& f) {
	BaseFormula::Type type = f->getType();
	
	Formula f1, f2;
	
	switch(type) {
		case BaseFormula::T_TRUE:
		case BaseFormula::T_FALSE:
		case BaseFormula::T_ATOM:
			return f;
		case BaseFormula::T_NOT:
			f1 = eliminate_consts(f->getOperand());
			if(f1->getType() == BaseFormula::T_TRUE) {
				return FormulaDatabase::getFormulaDatabase().makeFalse();
			} else if(f1->getType() == BaseFormula::T_FALSE) {
				return FormulaDatabase::getFormulaDatabase().makeTrue();
			}
			return FormulaDatabase::getFormulaDatabase().makeNot(f1);
		case BaseFormula::T_AND:
			f1 = eliminate_consts(f->getOperand1());
			f2 = eliminate_consts(f->getOperand2());
			std::cout << f1 << " " << f2 << '\n';
			if(f1->getType() == BaseFormula::T_TRUE) {
				return f2;	
			} else if(f1->getType() == BaseFormula::T_FALSE) {
				return FormulaDatabase::getFormulaDatabase().makeFalse();
			}
			
			if(f2->getType() == BaseFormula::T_TRUE) {
				return f1;	
			} else if(f2->getType() == BaseFormula::T_FALSE) {
				return FormulaDatabase::getFormulaDatabase().makeFalse();
			}
			return FormulaDatabase::getFormulaDatabase().makeAnd(f1, f2);
		case BaseFormula::T_OR:
			f1 = eliminate_consts(f->getOperand1());
			f2 = eliminate_consts(f->getOperand2());
			if(f1->getType() == BaseFormula::T_FALSE) {
				return f2;	
			} else if(f1->getType() == BaseFormula::T_TRUE) {
				return FormulaDatabase::getFormulaDatabase().makeTrue();
			}
			
			if(f2->getType() == BaseFormula::T_FALSE) {
				return f1;	
			} else if(f2->getType() == BaseFormula::T_TRUE) {
				return FormulaDatabase::getFormulaDatabase().makeTrue();
			}
			return FormulaDatabase::getFormulaDatabase().makeOr(f1, f2);
		case BaseFormula::T_IMP:
			f1 = eliminate_consts(f->getOperand1());
			f2 = eliminate_consts(f->getOperand2());
			if(f1->getType() == BaseFormula::T_TRUE) {
				return eliminate_consts(FormulaDatabase::getFormulaDatabase().makeNot(f2));	
			} else if(f1->getType() == BaseFormula::T_FALSE) {
				return FormulaDatabase::getFormulaDatabase().makeTrue();
			}
			
			if(f2->getType() == BaseFormula::T_TRUE) {
				return FormulaDatabase::getFormulaDatabase().makeTrue();	
			} else if(f2->getType() == BaseFormula::T_FALSE) {
				return eliminate_consts(FormulaDatabase::getFormulaDatabase().makeNot(f1));
			}
			return FormulaDatabase::getFormulaDatabase().makeImp(f1, f2);
		case BaseFormula::T_IFF:
			f1 = eliminate_consts(f->getOperand1());
			f2 = eliminate_consts(f->getOperand2());
			if(f1->getType() == BaseFormula::T_TRUE) {
				return f2;	
			} else if(f1->getType() == BaseFormula::T_FALSE) {
				return eliminate_consts(FormulaDatabase::getFormulaDatabase().makeNot(f2));
			}
			
			if(f2->getType() == BaseFormula::T_TRUE) {
				return f1;	
			} else if(f2->getType() == BaseFormula::T_FALSE) {
				return eliminate_consts(FormulaDatabase::getFormulaDatabase().makeNot(f1));
			}
			
			return FormulaDatabase::getFormulaDatabase().makeIff(f1, f2);
			
		case BaseFormula::T_FORALL:
			f1 = eliminate_consts(f->getOperand());
			if(f1->getType() == BaseFormula::T_TRUE) {
				return f1;
			} else if(f1->getType() == BaseFormula::T_FALSE) {
				return f1;
			}
			
			return FormulaDatabase::getFormulaDatabase().makeForall(f->getVariable(), f1);
		case BaseFormula::T_EXISTS:
			f1 = eliminate_consts(f->getOperand());
			if(f1->getType() == BaseFormula::T_TRUE) {
				return f1;
			} else if(f1->getType() == BaseFormula::T_FALSE) {
				return f1;
			}
			return FormulaDatabase::getFormulaDatabase().makeExists(f->getVariable(), f1);
		
	}
	return f;
}

void cnf_transform(const Formula& f, std::vector<Clause>& CNF, std::list<Quant>& quants) {
	Formula t = eliminate_consts(f);
	if(t->getType() == BaseFormula::T_TRUE || t->getType() == BaseFormula::T_FALSE) {
		CNF.push_back({Literal{t, false}});
		return;
	}
	t = tseitin_helper(t, CNF, quants);
	
	// ono sto je ostalo od formule treba staviti u KNF
	CNF.push_back({Literal{t, false}});

	return;
}

std::tuple<Formula, Formula, atomic_pointer> resolve_quant(atomic_pointer& t, const Formula& f, std::list<Quant>& quants) {
	// izvlacimo promenljivu po kojoj se kvantifikuje
	Term v = TermDatabase::getTermDatabase().makeVariableTerm(f->getVariable());
	// vadimo podtermove od podformule
	std::vector<Term> terms;
	std::vector<Term> vars, vars1;
	terms.insert(terms.end(), t->getOperands().begin(), t->getOperands().end());
	// vadimo promenljive iz podformule
	std::set<Term> s;
	get_vars(s, terms);
	vars.insert(vars.end(), s.begin(), s.end());
	vars1 = vars;
	// flag oznacava da li se u podformuli javlja v
	bool flag;
	if(std::erase_if(vars, [v](const Term& x){return v == x;})) {
		flag = true;
	}
	// u ova dva vektora smestamo promenljive koje cemo kasnije da preimenujemo
	// prvo se u vektorima nalazi sve sto je pod univerzalnim kvantifikatorom
	// i nije vezano za vezanu promenljivu v
	std::vector<Term> new_vars, new_vars1;
	new_vars.insert(new_vars.end(), vars.begin(), vars.end());
	new_vars1 = new_vars;
	
	// kreiramo drugi atom, jer bice kreirana dva nova atoma
	atomic_pointer t1 = std::dynamic_pointer_cast<const Atom>(FormulaDatabase::getFormulaDatabase().makeAtom(t->getSymbol(), vars1));
	
	// kreiramo ono sto ce biti povratna vrednost za tseitin_helper
	Formula ret = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(++i), vars);
	//std::erase_if(vars, [v](const Term& x){return v == x;});
	// uvodimo novi predikat p sa argumentima terms
	// v = set_new_vars_quant(old_vars, quants, t, v, true);
	// v1 = TermDatabase::getTermDatabase().makeVariableTerm(f->getVariable());
	//v1 = set_new_vars_quant(old_vars1, quants, t1, v1, false);
	
	for(auto it = new_vars.begin(), it1 = new_vars1.begin(); it != new_vars.end() && it1 != new_vars1.end(); ++it, ++it1) {
		// pravimo novu promenljivu
		Term s = TermDatabase::getTermDatabase().makeVariableTerm("X" + to_string(++j));
		// Term s1 = TermDatabase::getTermDatabase().makeVariableTerm("X" + to_string(j));
		quants.push_back(s);
		t = rename_var_in_atom(t, *it, s);
		*it = s;
		t1 = rename_var_in_atom(t1, *it1, s);
		*it1 = s;
	}
	
	if(flag) {
		// sada u t stavljamo egzistencijalni kvantifikator
		new_vars.push_back(v);
		new_vars1.push_back(v);
		std::vector<Term> new_terms;
		for(auto Q : quants) {
			new_terms.push_back(Q);
		}
		Term s = TermDatabase::getTermDatabase().makeFunctionTerm(((quants.empty())? "C" : "F") + to_string(++k), new_terms);
		t = rename_var_in_atom(t, *new_vars.rbegin(), s);
		
		// a u t1 univerzalni kvantifikator
		Term s1 = TermDatabase::getTermDatabase().makeVariableTerm("X" + to_string(++j));
		quants.push_back(s1);
		t1 = rename_var_in_atom(t1, *new_vars.rbegin(), s1);
		new_vars.pop_back();
		new_vars1.pop_back();
	}
	
	Formula a = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(i), new_vars);
	
	// std::cout << "Formula a je : " << a << '\n';
	
	return {ret, a, t1};

}


Formula tseitin_helper(const Formula &f, std::vector<Clause> &CNF, std::list<Quant>& quants) {
	BaseFormula::Type type = f->getType();
	//std::cout << type << '\n';
	Formula a, b;
	Formula ret;
	atomic_pointer t, t1, t2;
	std::vector<Term> terms;
	std::vector<Term> vars, vars1;
	std::vector<Term> old_vars, old_vars1;
	std::set<Term> s;
	Term v, v1;
	bool flag = false;
	
	switch(type) {
		case BaseFormula::T_ATOM:
			// ne radimo nista kad je atom u pitanju
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
			ret = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(++i), vars);
			// preimenujemo promenljive
			set_new_vars_unary(vars, quants, t);
			a = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(i), vars);
			CNF.push_back({Literal{a, false}, Literal{t, false}});
			CNF.push_back({Literal{a, true}, Literal{t, true}});
			// vracamo xi+1
			return ret;
		case BaseFormula::T_AND:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			ret = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(++i), vars);
			// preimenujemo promenljive
			set_new_vars_binary(vars, quants, t1, t2);
			a = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(i), vars);
			// operand1 --> a, operand2 --> b
			// f --> xi+1
			// xi+1 <=> (a & b)
			// (~xi+1 | (a & b)) & (~(a & b) | xi+1)
			// (~xi+1 | a) & (~xi+1 | b) & (~a | ~b | xi+1)
			CNF.push_back({Literal{t1, false}, Literal{a, true}});
			CNF.push_back({Literal{t2, false}, Literal{a, true}});
			CNF.push_back({Literal{t1, true}, Literal{t2, true}, Literal{a, false}});
			return ret;
		case BaseFormula::T_OR:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			ret = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(++i), vars);
			set_new_vars_binary(vars, quants, t1, t2);
			a = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(i), vars);
			// xi+1 <=> (a | b)
			// (~xi+1 | a | b) & (xi+1 | (~a & ~b))
			// (~xi+1 | a | b) & (xi+1 | ~a) & (xi+1 | ~b)
			CNF.push_back({Literal{t1, true}, Literal{a, false}});
			CNF.push_back({Literal{t2, true}, Literal{a, false}});
			CNF.push_back({Literal{t1, false}, Literal{t2, false}, Literal{a, true}});
			return ret;
		case BaseFormula::T_IMP:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			ret = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(++i), vars);
			set_new_vars_binary(vars, quants, t1, t2);
			a = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(i), vars);
			// xi+1 <=> (a -> b)
			// (xi+1) <=> (~a | b)
			// (~xi+1 | ~a | b) & (xi+1 | a) & (xi+1 | ~b)
			CNF.push_back({Literal{t1, false}, Literal{a, false}});
			CNF.push_back({Literal{t2, true}, Literal{a, false}});
			CNF.push_back({Literal{t1, true}, Literal{t2, false}, Literal{a, true}});
			return ret;
		case BaseFormula::T_IFF:
			t1 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand1(), CNF, quants));
			t2 = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand2(), CNF, quants));
			terms.insert(terms.end(), t1->getOperands().begin(), t1->getOperands().end());
			terms.insert(terms.end(), t2->getOperands().begin(), t2->getOperands().end());
			get_vars(s, terms);
			vars.insert(vars.end(), s.begin(), s.end());
			ret = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(++i), vars);
			set_new_vars_binary(vars, quants, t1, t2);
			a = FormulaDatabase::getFormulaDatabase().makeAtom("s" + to_string(i), vars);
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
			return ret;
			
		case BaseFormula::T_FORALL:
			t = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand(), CNF, quants));
			std::tie(ret, a, t1) = resolve_quant(t, f, quants);
			// s(terms) <=> !X.F(x, terms)
			// (~s | !X.F) & (s | ~!X.F)
			// !X.(~s | F) & ?X(s | ~F)
			CNF.push_back({Literal{a, true}, Literal{t1, false}});
			CNF.push_back({Literal{a, false}, Literal{t, true}});
			return ret;
		case BaseFormula::T_EXISTS:
			t = std::dynamic_pointer_cast<const Atom>(tseitin_helper(f->getOperand(), CNF, quants));
			std::tie(ret, a, t1) = resolve_quant(t, f, quants);
			// p(terms) <=> ?X.F(x, terms)
			// ?X.(~p | F) & !X(p | ~F)
			CNF.push_back({Literal{a, true}, Literal{t, false}});
			CNF.push_back({Literal{a, false}, Literal{t1, true}});
			return ret;
	}
	return f;
}

int main() {
  yyparse();
  
  if(parsed_formula.get() != 0)
    cout << parsed_formula << '\n';
  
  std::vector<Clause> cnf;
  std::list<Quant> quants;
  cnf_transform(parsed_formula, cnf, quants);
  
  std::cout << "KNF je:\n";
  for(Quant& q : quants) {
  	std::cout << "!" << q->getVariable() << " ";
  }
  
  std::cout << '\n';
  
  for(Clause c : cnf) {
  	for(Literal l : c) {
  		std::cout << print_neg(l.isNeg) << l.a << " ";
  	}
  	std::cout << '\n';
  }
  
  cout << endl;

  return 0;
}
