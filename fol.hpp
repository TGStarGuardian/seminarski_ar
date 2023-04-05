#ifndef _FOL_H
#define _FOL_H

#include <iostream>
#include <string>
#include <vector>
#include <memory>
#include <functional>
#include <unordered_set>

using namespace std;

typedef string FunctionSymbol;
typedef string PredicateSymbol;
typedef string Variable;


class BaseTerm;
typedef shared_ptr<const BaseTerm> Term;


class BaseTerm : public enable_shared_from_this<const BaseTerm> {

public:
  enum Type { TT_VARIABLE, TT_FUNCTION };
  virtual Type getType() const = 0;
  virtual void printTerm(ostream & ostr) const = 0;
  virtual bool equalTo(const BaseTerm * t) const = 0;
  virtual unsigned long hashCode() const = 0;

  virtual const Variable & getVariable() const
  {
    throw "Not implemented";
  }

  virtual const FunctionSymbol & getSymbol() const
  {
    throw "Not implemented";
  }

  virtual const vector<Term> & getOperands() const
  {
    throw "Not implemented";
  }

  
  
  virtual ~BaseTerm() {}
};

class TermDatabase;

class VariableTerm : public BaseTerm {
  friend class TermDatabase;
private:
  Variable _v;

  VariableTerm(const Variable & v)
    :_v(v)
  {}

public:

  virtual Type getType() const
  {
    return TT_VARIABLE;
  }

  virtual const Variable & getVariable() const
  {
    return _v;
  }

  virtual bool equalTo(const BaseTerm * t) const
  {
    return t->getType() == TT_VARIABLE && t->getVariable() == _v;
  }
  
  virtual void printTerm(ostream & ostr) const
  {
    ostr << _v;
  }

  virtual unsigned long hashCode() const
  {
    return hash<string>()(_v);
  }
};

class FunctionTerm : public BaseTerm {
  friend class TermDatabase;
private:
  FunctionSymbol _f;
  vector<Term> _ops;

  FunctionTerm(const FunctionSymbol & f, 
	       const vector<Term> & ops)
    :_f(f),
     _ops(ops)
  {}
  
  FunctionTerm(const FunctionSymbol & f,
	       vector<Term> && ops = vector<Term> ())
    :_f(f),
     _ops(move(ops))
  {}

public:
  
  virtual Type getType() const
  {
    return TT_FUNCTION;
  }

  virtual const FunctionSymbol & getSymbol() const
  {
    return _f;
  }

  virtual const vector<Term> & getOperands() const
  {
    return _ops;
  }

  virtual bool equalTo(const BaseTerm * t) const
  {
    if(t->getType() != TT_FUNCTION)
      return false;

    if(t->getSymbol() != _f)
      return false;

    const vector<Term> & tops = t->getOperands();
    if(tops.size() != _ops.size())
      return false;

    for(unsigned i = 0; i < _ops.size(); i++)
      if(!_ops[i]->equalTo(tops[i].get()))
	return false;

    return true;    
  }

  virtual unsigned long hashCode() const
  {
    unsigned long h = hash<string>()(_f);

    for(unsigned i = 0; i < _ops.size(); i++)
      h ^= _ops[i]->hashCode();
    
    return h;
  }
  
  virtual void printTerm(ostream & ostr) const
  {
    ostr << _f;

    for(unsigned i = 0; i < _ops.size(); i++)
      {
	if(i == 0)
	  ostr << "(";
	_ops[i]->printTerm(ostr);
	if(i != _ops.size() - 1)
	  ostr << ",";
	else
	  ostr << ")";
      }
  }
};

class BaseFormula;
typedef shared_ptr<const BaseFormula> Formula;

class BaseFormula : public enable_shared_from_this<BaseFormula> {
  
public:

  enum Type { T_TRUE, T_FALSE, T_ATOM, T_NOT, 
	      T_AND, T_OR, T_IMP, T_IFF, T_FORALL, T_EXISTS };

  virtual void printFormula(ostream & ostr) const = 0;
  virtual bool equalTo(const BaseFormula * f) const = 0;
  virtual unsigned long hashCode() const = 0;
  virtual Type getType() const = 0;

  virtual const PredicateSymbol & getSymbol() const
  {
    throw "Not implemented";
  }

  virtual const vector<Term> & getOperands() const
  {
    throw "Not implemented";
  }

  virtual const Term & getLeftOperand() const
  {
    throw "Not implemented";
  }
  
  virtual const Term & getRightOperand() const
  {
    throw "Not implemented";
  }

  virtual const Formula & getOperand() const
  {
    throw "Not implemented";
  }
  
  virtual const Formula & getOperand1() const
  {
    throw "Not implemented";
  }

  virtual const Formula & getOperand2() const
  {
    throw "Not implemented";
  }

  virtual const Variable & getVariable() const
  {
    throw "Not implemented";
  }

  
  virtual ~BaseFormula() {}
};

class FormulaDatabase;

class AtomicFormula : public BaseFormula {
public:
};


class LogicConstant : public AtomicFormula {

public:
};


class True : public LogicConstant {
  friend class FormulaDatabase;
private:
  True() {}
public:
  virtual void printFormula(ostream & ostr) const
  {
    ostr << "true";
  }

  virtual Type getType() const
  {
    return T_TRUE;
  }

  virtual bool equalTo(const BaseFormula * f) const
  {
    return f->getType() == T_TRUE;
  }

  virtual unsigned long hashCode() const
  {
    return hash<string>()("true");
  }
  
};


class False : public LogicConstant {
  friend class FormulaDatabase;
private:
  False() {}
public:
  virtual void printFormula(ostream & ostr) const
  {
    ostr << "false";
  }

  virtual Type getType() const
  {
    return T_FALSE;
  }

  virtual bool equalTo(const BaseFormula * f) const
  {
    return f->getType() == T_FALSE;
  }

  virtual unsigned long hashCode() const
  {
    return hash<string>()("false");
  }
  
};


class Equality;
class Disequality;

class Atom : public AtomicFormula {
  friend class FormulaDatabase;
  friend class Equality;
  friend class Disequality;
private:
  Atom(const PredicateSymbol & p, 
       const vector<Term> & ops)
    :_p(p),
     _ops(ops)
  {}

  Atom(const PredicateSymbol & p, 
       vector<Term> && ops = vector<Term>())
    :_p(p),
     _ops(move(ops))
  {}

protected:  
  PredicateSymbol _p;
  vector<Term> _ops;

public:
  
  virtual const PredicateSymbol & getSymbol() const
  {
    return _p;
  }

  virtual const vector<Term> & getOperands() const
  {
    return _ops;
  }

  virtual void printFormula(ostream & ostr) const
  {
    ostr << _p;
    for(unsigned i = 0; i < _ops.size(); i++)
      {
	if(i == 0)
	  ostr << "(";
	_ops[i]->printTerm(ostr);
	if(i != _ops.size() - 1)
	  ostr << ",";
	else
	  ostr << ")";
      }
  }

  virtual bool equalTo(const BaseFormula * f) const
  {
    if(f->getType() != T_ATOM)
      return false;

    if(f->getSymbol() != _p)
      return false;

    const vector<Term> & fops = f->getOperands();
    if(fops.size() != _ops.size())
      return false;

    for(unsigned i = 0; i < _ops.size(); i++)
      if(!_ops[i]->equalTo(fops[i].get()))
	return false;

    return true;    

  }
  
  virtual Type getType() const
  {
    return T_ATOM;
  }

  virtual unsigned long hashCode() const
  {
    unsigned long h = hash<string>()(_p);

    for(unsigned i = 0; i < _ops.size(); i++)
      h ^= _ops[i]->hashCode();
    
    return h;    
  }
  
};

class Equality : public Atom {
  friend class FormulaDatabase;
private:
  Equality(const Term & lop, const Term & rop)
    :Atom("=", vector<Term> ())
  {
    _ops.push_back(lop);
    _ops.push_back(rop);
  }

public:  
  virtual const Term & getLeftOperand() const
  {
    return _ops[0];
  }
  
  virtual const Term & getRightOperand() const
  {
    return _ops[1];
  }

  virtual void printFormula(ostream & ostr) const
  {
    _ops[0]->printTerm(ostr);
    ostr << " = ";
    _ops[1]->printTerm(ostr);
  }

};

class Disequality : public Atom {
  friend class FormulaDatabase;
private:
  Disequality(const Term & lop, const Term & rop)
    :Atom("~=", vector<Term> ())
  {
    _ops.push_back(lop);
    _ops.push_back(rop);
  }
  
public:
  
  virtual const Term & getLeftOperand() const
  {
    return _ops[0];
  }
  
  virtual const Term & getRightOperand() const
  {
    return _ops[1];
  }

  virtual void printFormula(ostream & ostr) const
  {

    _ops[0]->printTerm(ostr);
    ostr << " ~= ";
    _ops[1]->printTerm(ostr);
  }
};


class UnaryConnective : public BaseFormula {
  friend class FormulaDatabase;
protected:
   Formula _op;
  UnaryConnective(const Formula & op)
    :_op(op)
  {}

public:

  virtual const Formula & getOperand() const
  {
    return _op;
  }

  virtual bool equalTo(const BaseFormula * f) const
  {
    return f->getType() == this->getType() &&
      _op->equalTo(f->getOperand().get());
  }


  virtual unsigned long hashCode() const
  {
    return (0x0101010101010101 << ((unsigned long)this->getType() - 3)) ^ _op->hashCode();
  }
  
};

class Not : public UnaryConnective {
  friend class FormulaDatabase;
private:
  Not(const Formula & op)
    :UnaryConnective(op)
  {}
public:

  virtual void printFormula(ostream & ostr) const
  { 
    ostr << "~";
    Type op_type = _op->getType();

    if(op_type == T_AND || op_type == T_OR || 
       op_type == T_IMP || op_type == T_IFF ||
       op_type == T_FORALL || op_type == T_EXISTS)
      ostr << "(";

    _op->printFormula(ostr);

    if(op_type == T_AND || op_type == T_OR || 
       op_type == T_IMP || op_type == T_IFF ||
       op_type == T_FORALL || op_type == T_EXISTS)
      ostr << ")";
  }

  virtual Type getType() const
  {
    return T_NOT;
  }
};


class BinaryConnective : public BaseFormula {
  friend class FormulaDatabase;
protected:
   Formula _op1, _op2;
  BinaryConnective(const Formula & op1, const Formula & op2)
    :_op1(op1),
     _op2(op2)
  {}

public:

  virtual const Formula & getOperand1() const
  {
    return _op1;
  }

  virtual const Formula & getOperand2() const
  {
    return _op2;
  }

  virtual bool equalTo(const BaseFormula * f) const
  {
    return f->getType() == this->getType() &&
      _op1->equalTo(f->getOperand1().get()) &&
      _op2->equalTo(f->getOperand2().get());
  }

  virtual unsigned long hashCode() const
  {
    return (0x0101010101010101 << ((unsigned long)this->getType() - 3)) ^ _op1->hashCode() ^ _op2->hashCode();
  }

};


class And : public BinaryConnective {
  friend class FormulaDatabase;
private:
  And(const Formula & op1, const Formula & op2)
    :BinaryConnective(op1, op2)
  {}

public:

  virtual void printFormula(ostream & ostr) const
  {
    Type op1_type = _op1->getType();
    Type op2_type = _op2->getType();

    if(op1_type == T_OR || op1_type == T_IMP || 
       op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << "(";
    
    _op1->printFormula(ostr);
    
    if(op1_type == T_OR || op1_type == T_IMP || 
       op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << ")";

    ostr << " & ";

    if(op2_type == T_OR || op2_type == T_IMP || 
       op2_type == T_IFF || op2_type == T_AND ||
       op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << "(";
    
    _op2->printFormula(ostr);

    if(op2_type == T_OR || op2_type == T_IMP || 
       op2_type == T_IFF || op2_type == T_AND ||
       op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << ")";
  }

  virtual Type getType() const
  {
    return T_AND;
  }
 };



class Or : public BinaryConnective {
  friend class FormulaDatabase;
private:
  Or(const Formula & op1, const Formula & op2)
    :BinaryConnective(op1, op2)
  {}

public:

  virtual void printFormula(ostream & ostr) const
  {

    Type op1_type = _op1->getType();
    Type op2_type = _op2->getType();

    if(op1_type == T_IMP || op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << "(";
    
    _op1->printFormula(ostr);
    
    if(op1_type == T_IMP || op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << ")";

    ostr << " | ";

    if(op2_type == T_IMP || 
       op2_type == T_IFF || op2_type == T_OR ||
       op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << "(";
    
    _op2->printFormula(ostr);

    if(op2_type == T_IMP || 
       op2_type == T_IFF || op2_type == T_OR ||
       op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << ")";
  }

  virtual Type getType() const
  {
    return T_OR;
  }
};


class Imp : public BinaryConnective {
  friend class FormulaDatabase;
private:
  Imp(const Formula & op1, const Formula & op2)
    :BinaryConnective(op1, op2)
  {}

public:
  
  virtual void printFormula(ostream & ostr) const
  {

    Type op1_type = _op1->getType();
    Type op2_type = _op2->getType();

    if(op1_type == T_IMP || op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << "(";
    
    _op1->printFormula(ostr);
    
    if(op1_type == T_IMP || op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << ")";

    ostr << " => ";

    if(op2_type == T_IFF ||
       op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << "(";
    
    _op2->printFormula(ostr);

    if(op2_type == T_IFF ||
       op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << ")";
  }
  
  virtual Type getType() const
  {
    return T_IMP;
  }
};



class Iff : public BinaryConnective {
  friend class FormulaDatabase;
private:
  Iff(const Formula & op1, const Formula & op2)
    :BinaryConnective(op1, op2)
  {}

public:

  virtual void printFormula(ostream & ostr) const
  {

    Type op1_type = _op1->getType();
    Type op2_type = _op2->getType();

    if(op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << "(";
    
    _op1->printFormula(ostr);

    if(op1_type == T_IFF ||
       op1_type == T_FORALL || op1_type == T_EXISTS)
      ostr << ")";
    
    ostr << " <=> ";

    if(op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << "(";
    
    _op2->printFormula(ostr);

    if(op2_type == T_FORALL || op2_type == T_EXISTS)
      ostr << ")";

  }
  
  virtual Type getType() const
  {
    return T_IFF;
  }
};


class Quantifier : public BaseFormula {
  friend class FormulaDatabase;

protected:
  Variable _v;
  Formula  _op;

  Quantifier(const Variable & v, const Formula & op)
    :_v(v),
     _op(op)
  {}

public:

  virtual const Variable & getVariable() const
  {
    return _v;
  }

  virtual const Formula & getOperand() const
  {
    return _op;
  }

  virtual bool equalTo(const BaseFormula * f) const
  {
    return f->getType() == this->getType() &&
      f->getVariable() == _v &&
      _op->equalTo(f->getOperand().get());
  }

  virtual unsigned long hashCode() const
  {
    return (0x0101010101010101 << ((unsigned long)this->getType() - 3)) ^ _op->hashCode() ^ (unsigned long)hash<string>()(_v);
  }
  
};

class Forall : public Quantifier {
  friend class FormulaDatabase;
private:
  Forall(const Variable & v, const Formula & op)
    :Quantifier(v, op)
  {}
  
public:

  virtual Type getType() const
  {
    return T_FORALL;
  }
  virtual void printFormula(ostream & ostr) const
  {
    cout << "!" << _v << " . ";
    
    _op->printFormula(ostr);
  }
};

class Exists : public Quantifier {
  friend class FormulaDatabase;
private:
  Exists(const Variable & v, const Formula & op)
    :Quantifier(v, op)
  {}

public:

  virtual Type getType() const
  {
    return T_EXISTS;
  }

  virtual void printFormula(ostream & ostr) const
  {
    cout  << "?" << _v << " . ";
   
    _op->printFormula(ostr);    
  }
};

inline
ostream & operator << (ostream & ostr, const Term & t)
{
  t->printTerm(ostr);
  return ostr;
}

inline
ostream & operator << (ostream & ostr, const Formula & f)
{
  f->printFormula(ostr);
  return ostr;
}

namespace std {

  template <>
  struct hash<const BaseTerm*> {
    unsigned long operator () (const BaseTerm * t) const
    {      
      return t->hashCode();
    }
  };

  template <>
  struct equal_to<const BaseTerm*> {
    bool operator () (const BaseTerm * t1, const BaseTerm * t2) const
    {
      return t1->equalTo(t2);
    }
  };
  
  template <>
  struct hash<const BaseFormula *> {
    unsigned long operator () (const BaseFormula * f) const
    {
      return f->hashCode();
    }
  };

  template <>
  struct equal_to<const BaseFormula*> {
    bool operator () (const BaseFormula * t1, const BaseFormula * t2) const
    {
      return t1->equalTo(t2);
    }
  };
  
}


class TermDatabase {
private:
  unordered_set<const BaseTerm *> _terms;
  TermDatabase() {};
  static shared_ptr<TermDatabase>  _term_database;

  struct Deleter {
    TermDatabase * _tdb;
    Deleter(TermDatabase * tdb)
      :_tdb(tdb)
    {}
    void operator () (const BaseTerm * t)
    {
      _tdb->removeTerm(t);
    }
    
  };
  
  Term addTerm(const BaseTerm * t)
  {
    auto it = _terms.find(t);
    if(it != _terms.end())
      {
	delete t;
	return (*it)->shared_from_this();
      }
    else
      {
	_terms.insert(t);
	return shared_ptr<const BaseTerm>(t, Deleter(this));
      }
  }

  void removeTerm(const BaseTerm * t)
  {
    _terms.erase(t);
    delete t;
  }
  
public:
  static TermDatabase & getTermDatabase()
  {
    if(_term_database == nullptr)
      _term_database = shared_ptr<TermDatabase>(new TermDatabase());
    return *_term_database;
  }

  Term makeVariableTerm(const Variable & v)
  {
    VariableTerm * vt = new VariableTerm(v);
    return addTerm(vt);
  }

  Term makeFunctionTerm(const FunctionSymbol & f, const vector<Term> & ops)
  {
    FunctionTerm * ft = new FunctionTerm(f, ops);
    return addTerm(ft);
  }

  Term makeFunctionTerm(const FunctionSymbol & f, vector<Term> && ops = vector<Term>())
  {
    FunctionTerm * ft = new FunctionTerm(f, move(ops));
    return addTerm(ft);
  }
  
};


class FormulaDatabase {
private:
  unordered_set<const BaseFormula *> _formulas;
  FormulaDatabase() {};
  static shared_ptr<FormulaDatabase>  _formula_database;

  struct Deleter {
    FormulaDatabase * _fdb;
    Deleter(FormulaDatabase * fdb)
      :_fdb(fdb)
    {}
    void operator () (const BaseFormula * f)
    {
      _fdb->removeFormula(f);
    }
    
  };
  
  Formula addFormula(const BaseFormula * f)
  {
    auto it = _formulas.find(f);
    if(it != _formulas.end())
      {
	delete f;
	return (*it)->shared_from_this();
      }
    else
      {
	_formulas.insert(f);
	return shared_ptr<const BaseFormula>(f, Deleter(this));
      }
  }

  void removeFormula(const BaseFormula * f)
  {
    _formulas.erase(f);
    delete f;
  }
  
public:
  static FormulaDatabase & getFormulaDatabase()
  {
    if(_formula_database == nullptr)
      _formula_database = shared_ptr<FormulaDatabase>(new FormulaDatabase());
    return *_formula_database;
  }

  Formula makeTrue()
  {
    True * t = new True();
    return addFormula(t);
  }

  Formula makeFalse()
  {
    False * f = new False();
    return addFormula(f);
  }
  
  Formula makeAtom(const PredicateSymbol & p, const vector<Term> & ops)
  {
    Atom * a = new Atom(p, ops);
    return addFormula(a);
  }

  Formula makeAtom(const PredicateSymbol & p, vector<Term> && ops = vector<Term>())
  {
    Atom * a = new Atom(p, move(ops));
    return addFormula(a);
  }

  Formula makeEquality(const Term & l, const Term & r)
  {
    Equality * e = new Equality(l, r);
    return addFormula(e);
  }

  Formula makeDisequality(const Term & l, const Term & r)
  {
    Disequality * e = new Disequality(l, r);
    return addFormula(e);
  }

  
  Formula makeNot(const Formula & f)
  {
    Not * a = new Not(f);
    return addFormula(a);
  }

  Formula makeAnd(const Formula & l, const Formula & r)
  {
    And * a = new And(l, r);
    return addFormula(a);
  }

  Formula makeOr(const Formula & l, const Formula & r)
  {
    Or * a = new Or(l, r);
    return addFormula(a);
  }

  Formula makeImp(const Formula & l, const Formula & r)
  {
    Imp * a = new Imp(l, r);
    return addFormula(a);
  }

  Formula makeIff(const Formula & l, const Formula & r)
  {
    Iff * a = new Iff(l, r);
    return addFormula(a);
  }

  Formula makeForall(const Variable & v, const Formula & f)
  {
    Forall * a = new Forall(v, f);
    return addFormula(a);
  }

  Formula makeExists(const Variable & v, const Formula & f)
  {
    Exists * a = new Exists(v, f);
    return addFormula(a);
  }

  
};

extern Formula parsed_formula;

#endif // _FOL_H
