/****************************************************************************
  FileName     [ v3SvrPDRSat.cpp ]
  PackageName  [ v3/src/pdr ]
  Synopsis     [ Define PDR sat sovler interface ]
  Author       [ Cheng-Yin Wu, SillyDuck ]
  Copyright    [ Copyright(c) 2016 DVLab, GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef V3_SVR_PDRSAT_C
#define V3_SVR_PDRSAT_C

#include "v3SvrPDRSat.h"
#include <unistd.h>
#include <cassert>
#include <vector>
#include <map>
#include "reader.h"
#include "v3Msg.h"
#include "v3Ntk.h"

#include <cmath>


/* -------------------------------------------------- *\
 * Class V3SvrPDRSat Implementations
\* -------------------------------------------------- */
inline void buf(SolverV* SS, const Lit& a, const Lit& b)
{
   vec<Lit> lits; lits.clear();
   lits.push(~a); lits.push( b); SS->addClause(lits); lits.clear();
   lits.push( a); lits.push(~b); SS->addClause(lits); lits.clear();
}

inline void and_2(SolverV* SS, const Lit& y, const Lit& a, const Lit& b)
{
   vec<Lit> lits; lits.clear();
   lits.push( a); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push( b); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push(~a); lits.push(~b); lits.push( y); SS->addClause(lits); lits.clear();
}

inline void xor_2(SolverV* SS, const Lit& y, const Lit& a, const Lit& b)
{
   vec<Lit> lits; lits.clear();
   lits.push( a); lits.push( b); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push(~a); lits.push(~b); lits.push(~y); SS->addClause(lits); lits.clear();
   lits.push( a); lits.push(~b); lits.push( y); SS->addClause(lits); lits.clear();
   lits.push(~a); lits.push( b); lits.push( y); SS->addClause(lits); lits.clear();
}


// Constructor and Destructor
V3SvrPDRSat::V3SvrPDRSat(V3Ntk* ntk, const bool& freeBound, const bool& proofLog)
   : _ntk(ntk), _freeBound(freeBound) , _L(_ntk->getLatchSize()) , _I(_ntk->getInputSize()) {

   _Solver = new SolverV();
   if(proofLog) _Solver->proof = new Proof(); // MODIFICATION FOR SoCV
   assert (_Solver); assumeRelease(); initRelease();
   _curVar = 0; _Solver->newVar(); ++_curVar;  // 0 for Recycle Literal, if Needed
   _ntkData = new V3SvrMVarData[ntk->getNetSize()];
   for (uint32_t i = 0; i < ntk->getNetSize(); ++i) _ntkData[i].clear();
   _actVars.clear();
}

V3SvrPDRSat::~V3SvrPDRSat() {
   delete _Solver; assumeRelease(); initRelease();
   for (uint32_t i = 0; i < _ntk->getNetSize(); ++i) _ntkData[i].clear(); delete [] _ntkData;
}

// Basic Operation Functions
void
V3SvrPDRSat::reset() {
   delete _Solver; _Solver = new SolverV(); assert (_Solver); assumeRelease(); initRelease();
   _curVar = 0; _Solver->newVar(); ++_curVar;  // 0 for Recycle Literal, if Needed
   for (uint32_t i = 0; i < _ntk->getNetSize(); ++i) _ntkData[i].clear();
}

void
V3SvrPDRSat::assumeInit() {
   for (uint32_t i = 0; i < _init.size(); ++i) _assump.push(_init[i]);
}

void
V3SvrPDRSat::assertInit() {
   for (uint32_t i = 0; i < _init.size(); ++i) _Solver->addUnit(_init[i]);
}

void
V3SvrPDRSat::initRelease() { _init.clear(); }

void
V3SvrPDRSat::assumeRelease() { _assump.clear(); }

void
V3SvrPDRSat::assumeProperty(const size_t& var, const bool& invert) {
   _assump.push(mkLit(getOriVar(var), invert ^ isNegFormula(var)));
}

void
V3SvrPDRSat::assertProperty(const size_t& var, const bool& invert) {
   _Solver->addUnit(mkLit(getOriVar(var), invert ^ isNegFormula(var)));
}

void
V3SvrPDRSat::assumeProperty(const V3NetId& id, const bool& invert, const uint32_t& depth) {
   assert (validNetId(id)); assert (1 == _ntk->getNetWidth(id));
   const Var var = getVerifyData(id, depth); assert (var);
   _assump.push(mkLit(var, invert ^ isV3NetInverted(id)));
}

void
V3SvrPDRSat::assertProperty(const V3NetId& id, const bool& invert, const uint32_t& depth) {
   assert (validNetId(id)); assert (1 == _ntk->getNetWidth(id));
   const Var var = getVerifyData(id, depth); assert (var);
   _Solver->addUnit(mkLit(var, invert ^ isV3NetInverted(id)));
}

const bool
V3SvrPDRSat::simplify() { return _Solver->simplifyDB(); }

const bool
V3SvrPDRSat::solve() {
   double ctime = (double)clock() / CLOCKS_PER_SEC;
   _Solver->solve(); ++_solves;
   _runTime += (((double)clock() / CLOCKS_PER_SEC) - ctime);
   return _Solver->okay();
}

const bool
V3SvrPDRSat::assump_solve() {
   double ctime = (double)clock() / CLOCKS_PER_SEC;
   bool result = _Solver->solve(_assump); ++_solves;
   _runTime += (((double)clock() / CLOCKS_PER_SEC) - ctime);
   return result;
}

// Manipulation Helper Functions
void
V3SvrPDRSat::setTargetValue(const V3NetId& id, const V3BitVecX& value, const uint32_t& depth, V3SvrDataVec& formula) {
   // Note : This Function will set formula such that AND(formula) represents (id == value)
   uint32_t i, size = value.size(); assert (size == _ntk->getNetWidth(id));
   const Var var = getVerifyData(id, depth); assert (var);
   if (isV3NetInverted(id)) {
      for (i = 0; i < size; ++i) {
         if ('1' == value[i]) formula.push_back(getNegVar(var + i));
         else if ('0' == value[i]) formula.push_back(getPosVar(var + i));
      }
   }
   else {
      for (i = 0; i < size; ++i) {
         if ('1' == value[i]) formula.push_back(getPosVar(var + i));
         else if ('0' == value[i]) formula.push_back(getNegVar(var + i));
      }
   }
}

void
V3SvrPDRSat::assertImplyUnion(const V3SvrDataVec& vars) {
   // Construct a CNF formula (var1 + var2 + ... + varn) and add to the solver
   if (vars.size() == 0) return; vec<Lit> lits; lits.clear();
   for (V3SvrDataVec::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      assert (*it); lits.push(mkLit(getOriVar(*it), isNegFormula(*it)));
   }
   _Solver->addClause(lits); lits.clear();
}

const size_t
V3SvrPDRSat::setTargetValue(const V3NetId& id, const V3BitVecX& value, const uint32_t& depth, const size_t& prev) {
   // Construct formula y = b0 & b1' & b3 & ... & bn', and return variable y
   assert (!prev || !isNegFormula(prev));  // Constrain input prev variable should NOT be negative!
   uint32_t i, size = value.size(); assert (size == _ntk->getNetWidth(id));
   const Var _var = getVerifyData(id, depth); assert (_var);
   Lit aLit = (prev) ? mkLit(getOriVar(prev)) : lit_Undef, bLit, yLit;
   vec<Lit> lits; lits.clear();
   for (i = 0; i < size; ++i) {
      if ('1' == value[i]) bLit = mkLit(_var + i, isV3NetInverted(id));
      else if ('0' == value[i]) bLit = ~mkLit(_var + i, isV3NetInverted(id));
      else bLit = lit_Undef;
      if (!(bLit == lit_Undef)) {
         if (!(aLit == lit_Undef)) {
            yLit = mkLit(newVar(1));
            lits.push(aLit); lits.push(~yLit); _Solver->addClause(lits); lits.clear();
            lits.push(bLit); lits.push(~yLit); _Solver->addClause(lits); lits.clear();
            lits.push(~aLit); lits.push(~bLit); lits.push(yLit); _Solver->addClause(lits); lits.clear();
            aLit = yLit; assert (!sign(aLit));
         }
         else aLit = bLit;
      }
   }
   if (aLit == lit_Undef) return 0;
   else if (sign(aLit)) {
      yLit = mkLit(newVar(1));
      lits.push(~aLit); lits.push(yLit); _Solver->addClause(lits); lits.clear();
      lits.push(aLit); lits.push(~yLit); _Solver->addClause(lits); lits.clear();
      aLit = yLit;
   }
   assert (!isNegFormula(getPosVar(var(aLit))));
   return getPosVar(var(aLit));
}

const size_t
V3SvrPDRSat::setImplyUnion(const V3SvrDataVec& vars) {
   // Construct a CNF formula (y' + var1 + var2 + ... + varn), and return variable y
   if (vars.size() == 0) return 0; vec<Lit> lits; lits.clear();
   Lit lit = mkLit(newVar(1), true); lits.push(lit);
   for (V3SvrDataVec::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      assert (*it); lits.push(mkLit(getOriVar(*it), isNegFormula(*it)));
   }
   _Solver->addClause(lits); lits.clear();
   assert (!isNegFormula(getPosVar(var(lit))));
   return getPosVar(var(lit));
}

const size_t
V3SvrPDRSat::setImplyIntersection(const V3SvrDataVec& vars) {
   // Goal : y --> (var1 && var2 && ... && varn)
   // Construct CNF formulas (y' + var1) && (y' + var2) &&  ... (y' + varn), and return variable y
   if (vars.size() == 0) return 0;
   Lit lit = mkLit(newVar(1), true);
   vec<Lit> lits; lits.clear();
   for (V3SvrDataVec::const_iterator it = vars.begin(); it != vars.end(); ++it) {
      assert (*it); lits.push(lit);
      lits.push(mkLit(getOriVar(*it), isNegFormula(*it)));
      _Solver->addClause(lits); lits.clear();
   }
   assert (!isNegFormula(getPosVar(var(lit))));
   return getPosVar(var(lit));
}

const size_t
V3SvrPDRSat::setImplyInit() {
   Lit lit = mkLit(newVar(1), true);
   vec<Lit> lits; lits.clear();
   for (uint32_t i = 0; i < _init.size(); ++i) {
      lits.push(lit); lits.push(_init[i]); _Solver->addClause(lits); lits.clear();
   }
   assert (!isNegFormula(getPosVar(var(lit))));
   return getPosVar(var(lit));
}

const V3BitVecX
V3SvrPDRSat::getDataValue(const V3NetId& id, const uint32_t& depth) const {
   Var var = getVerifyData(id, depth); assert (var);
   uint32_t i, width = _ntk->getNetWidth(id);
   V3BitVecX value(width);
   if (isV3NetInverted(id)) {
      for (i = 0; i < width; ++i)
         if (l_True == _Solver->model[var + i]) value.set0(i);
         else value.set1(i);
   }
   else {
      for (i = 0; i < width; ++i)
         if (l_True == _Solver->model[var + i]) value.set1(i);
         else value.set0(i);
   }
   return value;
}

const bool
V3SvrPDRSat::getDataValue(const size_t& var) const {
   return (isNegFormula(var)) ^ (l_True == _Solver->model[getOriVar(var)]);
}

void
V3SvrPDRSat::getDataConflict(V3SvrDataVec& vars) const {
   for (int i = 0; i < _Solver->conflict.size(); ++i)
      vars.push_back(getPosVar(var(_Solver->conflict[i])));
}

const size_t
V3SvrPDRSat::getFormula(const V3NetId& id, const uint32_t& depth) {
   Var var = getVerifyData(id, depth); assert (var);
   assert (!isNegFormula(getPosVar(var)));
   return (isV3NetInverted(id) ? getNegVar(var) : getPosVar(var));
}

const size_t
V3SvrPDRSat::getFormula(const V3NetId& id, const uint32_t& bit, const uint32_t& depth) {
   Var var = getVerifyData(id, depth); assert (var);
   assert (bit < _ntk->getNetWidth(id)); assert (!isNegFormula(getPosVar(var + bit)));
   return (isV3NetInverted(id) ? getNegVar(var + bit) : getPosVar(var + bit));
}

// Print Data Functions
void
V3SvrPDRSat::printInfo() const {
   Msg(MSG_IFO) << "#Vars = " << _Solver->nVars() << ", #Cls = " << _Solver->nClauses() << ", "
                << "#SV = " << totalSolves() << ", AccT = " << totalTime();
}

// Gate Formula to Solver Functions
void
V3SvrPDRSat::add_FALSE_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (AIG_FALSE == _ntk->getGateType(out)); assert (!getVerifyData(out, depth));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   // Set SATVar
   _ntkData[index].push_back(newVar(1)); assert (getVerifyData(out, depth));
   _Solver->addUnit(mkLit(_ntkData[index].back(), true));
}

void
V3SvrPDRSat::add_PI_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (V3_PI == _ntk->getGateType(out)); assert (!getVerifyData(out, depth));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   // Set SATVar
   _ntkData[index].push_back(newVar(_ntk->getNetWidth(out))); assert (getVerifyData(out, depth));
}

void
V3SvrPDRSat::add_FF_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (V3_FF == _ntk->getGateType(out)); assert (!getVerifyData(out, depth));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   const uint32_t width = _ntk->getNetWidth(out); assert (width);
   if (_freeBound) {
      // Set SATVar
      _ntkData[index].push_back(newVar(width));
   }
   else if (depth) {
      // Build FF I/O Relation
      const V3NetId in1 = _ntk->getInputNetId(out, 0); assert (validNetId(in1));
      const Var var1 = getVerifyData(in1, depth - 1); assert (var1);
      // Set SATVar
      if (isV3NetInverted(in1)) {
         _ntkData[index].push_back(newVar(width));
         for (uint32_t i = 0; i < width; ++i)
            buf(_Solver, mkLit(_ntkData[index].back() + i), mkLit(var1 + i, true));
      }
      else _ntkData[index].push_back(var1);
   }
   else {
      // Set SATVar
      _ntkData[index].push_back(newVar(width));
      const Var& var = _ntkData[index].back();
      // Build FF Initial State
      const V3NetId in1 = _ntk->getInputNetId(out, 1); assert (validNetId(in1));
      _init.push_back(mkLit(var, !isV3NetInverted(in1)));
   }
   assert (getVerifyData(out, depth));
}

void
V3SvrPDRSat::add_AND_Formula(const V3NetId& out, const uint32_t& depth) {
   // Check Output Validation
   assert (validNetId(out)); assert (!getVerifyData(out, depth));
   assert ((AIG_NODE == _ntk->getGateType(out)) || (BV_AND == _ntk->getGateType(out)));
   const uint32_t index = getV3NetIndex(out); assert (depth == _ntkData[index].size());
   const uint32_t width = _ntk->getNetWidth(out); assert (width);
   // Set SATVar
   _ntkData[index].push_back(newVar(_ntk->getNetWidth(out))); assert (getVerifyData(out, depth));
   const Var& var = _ntkData[index].back();
   // Build AND I/O Relation
   const V3NetId in1 = _ntk->getInputNetId(out, 0); assert (validNetId(in1));
   const V3NetId in2 = _ntk->getInputNetId(out, 1); assert (validNetId(in2));
   const Var var1 = getVerifyData(in1, depth); assert (var1);
   const Var var2 = getVerifyData(in2, depth); assert (var2);
   for (uint32_t i = 0; i < width; ++i)
      and_2(_Solver, mkLit(var + i), mkLit(var1 + i, isV3NetInverted(in1)), mkLit(var2 + i, isV3NetInverted(in2)));
}


// Network to Solver Functions
void
V3SvrPDRSat::addVerifyData(const V3NetId& id, const uint32_t& depth) {
   V3GateType type = _ntk->getGateType(id); assert (type < V3_XD);
   if (V3_PIO >= type) return add_PI_Formula(id, depth);
   else if (V3_FF == type) return add_FF_Formula(id, depth);
   else {
      if (AIG_FALSE == type) return add_FALSE_Formula(id, depth);  // AIG_FALSE
      return add_AND_Formula(id, depth);  // AIG_NODE
   }
}

void
V3SvrPDRSat::addBoundedVerifyData(const V3NetId& id, const uint32_t& depth) {
   if (existVerifyData(id, depth)) return;
   uint32_t qq = depth;
   addBoundedVerifyDataRecursively(id, qq);
}

void
V3SvrPDRSat::addBoundedVerifyDataRecursively(const V3NetId& id, uint32_t& depth)
{
    assert( validNetId(id) );
    if( existVerifyData(id,depth) ) return;
    const V3GateType type = _ntk->getGateType(id); assert(type < V3_XD);
    if( V3_PIO >= type ) add_PI_Formula(id,depth);
    else if( V3_FF == type ) {
        if(depth) { --depth; addBoundedVerifyDataRecursively(_ntk->getInputNetId(id,0), depth); ++depth; }
        add_FF_Formula(id, depth);
    }
    else if(AIG_FALSE >= type) {
        if(AIG_NODE == type) {
            addBoundedVerifyDataRecursively(_ntk->getInputNetId(id,0), depth);
            addBoundedVerifyDataRecursively(_ntk->getInputNetId(id,1), depth);
            add_AND_Formula(id,depth);
        }
        else {
            assert(AIG_FALSE == type);
            add_FALSE_Formula(id,depth);
        }
    }
    else {
        assert(0);
    }
}

const bool
V3SvrPDRSat::existVerifyData(const V3NetId& id, const uint32_t& depth) {
   return getVerifyData(id, depth);
}

// MODIFICATION FOR SoCV
void V3SvrPDRSat::resizeNtkData(const uint32_t& num) {
  V3SvrMVarData* ntkData_tmp = new V3SvrMVarData[_ntk->getNetSize()];
  for(uint32_t i = 0, j = (_ntk->getNetSize()-num); i < j; ++i) {
    ntkData_tmp[i] = _ntkData[i];
  }
  delete[] _ntkData;
  _ntkData = ntkData_tmp;
}

// MiniSat Functions
const Var
V3SvrPDRSat::newVar(const uint32_t& width) {
   Var cur_var = _curVar;
   for (uint32_t i = 0; i < width; ++i) _Solver->newVar();
   _curVar += width; return cur_var;
}

const Var
V3SvrPDRSat::getVerifyData(const V3NetId& id, const uint32_t& depth) const {
   assert (validNetId(id));
   if (depth >= _ntkData[getV3NetIndex(id)].size()) return 0;
   else return _ntkData[getV3NetIndex(id)][depth];
}




/*****************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
**********************ABOVE IS NOT RELEVANT TO PDR****************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
******************************************************************************
*****************************************************************************/





void V3SvrPDRSat::setFrame(vector< vector<Cube*>* >* f){
  _F = f;
}
void V3SvrPDRSat::setMonitor(const V3NetId& m){
  _monitor = m;
}
void V3SvrPDRSat::addInitiateState(){
  if(heavy_debug) cerr << "_actVars[0] : " << _actVars[0] << endl;
  for (uint i = 0; i < _L; ++i){
    vec<Lit> lits;
    lits.push(mkLit( getVerifyData(_ntk->getLatch(i),0),true));
    if(heavy_debug) cerr << getVerifyData(_ntk->getLatch(i),0) << " ";
    lits.push(mkLit(_actVars[0],true));
    _Solver->addClause(lits);
  }

}
void V3SvrPDRSat::dfs(V3NetVec& orderedNets){
  orderedNets.clear();
  orderedNets.reserve(_ntk->getNetSize());
  _ntk->newMiscData();
  for(unsigned i = 0, n = _ntk->getLatchSize(); i < n; ++i) {
    const V3NetId& nId = _ntk->getLatch(i);
    V3NetId tmp = _ntk->getInputNetId(nId, 0);
    _ntk->dfsOrder(tmp,orderedNets);
    _ntk->dfsOrder(nId,orderedNets);
  } 
  for(unsigned i = 0, n = _ntk->getOutputSize(); i < n; ++i) {
    const V3NetId& nId = _ntk->getOutput(i);
    _ntk->dfsOrder(nId,orderedNets);
  }
}
void V3SvrPDRSat::v3SimOneGate(const V3NetId &id){
  const V3GateType type = _ntk->getGateType(id);
  if(type == AIG_NODE) {
    Value3 in1 = _Value3List[ (_ntk->getInputNetId(id, 0)).id ] ;
    Value3 in2 = _Value3List[ (_ntk->getInputNetId(id, 1)).id ] ;
#if 1  // this improves efficiency
    in1._bit ^= (_ntk->getInputNetId(id, 0)).cp; 
    in2._bit ^= (_ntk->getInputNetId(id, 1)).cp;
#else
    if((_ntk->getInputNetId(id, 0)).cp) in1 = ~in1;
    if((_ntk->getInputNetId(id, 1)).cp) in2 = ~in2;
#endif
    _Value3List[ id.id ] =  in1 & in2;
  }
}
void V3SvrPDRSat::OAO_v3SimOneGate(const V3NetId &id, V3Vec<Value3>::Vec& myList){
  const V3GateType type = _ntk->getGateType(id);
  if(type == AIG_NODE) {
    Value3 in1 = myList[ (_ntk->getInputNetId(id, 0)).id ] ;
    Value3 in2 = myList[ (_ntk->getInputNetId(id, 1)).id ] ;
    in1._bit ^= (_ntk->getInputNetId(id, 0)).cp; 
    in2._bit ^= (_ntk->getInputNetId(id, 1)).cp;
    myList[ id.id ] =  in1 & in2;
  }
}
Cube* V3SvrPDRSat::ternarySimulation(Cube* c, bool b, bool* input){
   // TODO: SAT generalization
   // b = 0 -> getBadCube(),  check monitor contains 'X' or not
   // b = 1 -> solveRelative, check Latch Fanins contain 'X' or not
   //initValue3Data();
   static bool firstTime = true;
   static V3NetVec dfsList;
   if (firstTime){
      dfs(dfsList);
      firstTime = false;
   }
   // set initial value for PI and FFs
   for( uint i = 0; i < _I; ++i ){
      V3NetId pi = _ntk->getInput(i);
      _Value3List[pi.id]._dontCare = false;
      _Value3List[pi.id]._bit = input[i];
   }
   for( uint i = 0; i < _L; ++i ){
      V3NetId FF = _ntk->getLatch(i);
      _Value3List[FF.id] = c->_latchValues[i];
   }
#if 0 
   // for each literal in C: remove it and do sim3V 
   // check: if the output have 'x' -> undo the removel of literal
   
   for(uint i = 0; i < _L; ++i){
      V3NetId FF = _ntk->getLatch(i);
      if( _Value3List[FF.id]._dontCare == true) continue;
      
      _Value3List[FF.id]._dontCare = true;
      // do sim3v
      for(uint j = 0, n = dfsList.size(); j < n; ++j){
         v3SimOneGate(dfsList[j]);
      }
      
      bool x_is_found = false;
      if(b){
         // check latch values
         for(uint j = 0; j < _L; ++j){
            V3NetId FF_in = _ntk->getInputNetId(_ntk->getLatch(j),0);
            if(_Value3List[FF_in.id]._dontCare == true){
               x_is_found = true;
               break;
            }
         }
      }
      else{
         // check monitor
         #if 1 //this improves efficiency
         x_is_found = _Value3List[_monitor.id]._dontCare;
        
         #else
         if(_Value3List[_monitor.id]._dontCare == true)
            x_is_found = true;
         #endif
      }

      // undo the removal if needed
      if(x_is_found){
         _Value3List[FF.id]._dontCare = false;
      }
      else{
         c->_latchValues[i]._dontCare = true;
      }

   }
   return c;
#else
   V3Vec<Value3>::Vec  myValue3List;
   OAO_InitValue3Data(myValue3List);
   queue<V3NetId> qSim;
   // first simulate the _Value3List, to get the "Reference Answer"
   for(uint i = 0, n = dfsList.size(); i < n; ++i){
      v3SimOneGate(dfsList[i]);
   }
   
   /* //this is useless
   // [optional] push PI info. into the list, and to 3vSim
   for( uint i = 0; i < _I; ++i ){
      V3NetId pi = _ntk->getInput(i);
      myValue3List[pi.id] = Value3( input[i], 0 );
   }
   for(uint i = 0, n = dfsList.size(); i < n; ++i){
      OAO_v3SimOneGate(dfsList[i], myValue3List);
   }
   */
   
   // push watched gate into the list
   if(b)
      for(uint i = 0; i < _L; ++i){
         V3NetId FF_in = _ntk->getInputNetId(_ntk->getLatch(i), 0);
         myValue3List[FF_in.id] = _Value3List[FF_in.id];
         qSim.push(FF_in);
      }
   else{
      myValue3List[_monitor.id] = _Value3List[_monitor.id];
      qSim.push(_monitor);
   }
   
   while(!qSim.empty()){
      V3NetId tt = qSim.front();
      qSim.pop();
      if (_ntk->getGateType(tt) != AIG_NODE) continue;
      
      // tt = X -> illegal.
      //assert(myValue3List[tt.id]._dontCare == 0);
      
      V3NetId in0 = _ntk->getInputNetId(tt, 0);
      V3NetId in1 = _ntk->getInputNetId(tt, 1);
      if(myValue3List[tt.id]._bit){
         // tt = 1
         if(myValue3List[in0.id]._dontCare){
            myValue3List[in0.id] = Value3( !in0.cp, 0 );
            qSim.push(in0);
         }
         if(myValue3List[in1.id]._dontCare){
            myValue3List[in1.id] = Value3( !in1.cp, 0 );
            qSim.push(in1);
         }
      }
      else{
         // tt = 0
         if( myValue3List[in0.id]._dontCare == myValue3List[in1.id]._dontCare){
            // in0, in1 both known -> skip
            if (!myValue3List[in0.id]._dontCare) continue; 
            // in0 = X, in1 = X --> copy reference answer
            #if 0
            if( _Value3List[in0.id]._bit ^ in0.cp == 0){
               myValue3List[in0.id] = _Value3List[in0.id];
               qSim.push(in0);
            }
            else{
               myValue3List[in1.id] = _Value3List[in1.id];
               qSim.push(in1);
            }
            #else // this one is faster
            myValue3List[in0.id] = _Value3List[in0.id];
            myValue3List[in1.id] = _Value3List[in1.id];
            qSim.push(in0);
            qSim.push(in1);
            #endif
         }
         else{
            V3NetId &knownId = myValue3List[in0.id]._dontCare? in1 : in0;
            V3NetId &unknown = myValue3List[in0.id]._dontCare? in0 : in1;
            if(myValue3List[knownId.id]._bit ^ knownId.cp){
               // known = 1, (effictively)
               // unknown fanin = 0
               myValue3List[unknown.id] = Value3( unknown.cp, 0);
               qSim.push(unknown);
            }

         }
      }
   }

   for( uint i = 0; i < _L; ++i)
      c->_latchValues[i] = myValue3List[_ntk->getLatch(i).id];
   return c;
#endif
}
void V3SvrPDRSat::getSATAssignmentToCube(Cube* cube){
  // get SAT assignment from sovler if the cube is reachable from previous frame
  for (uint i = 0; i < _L; ++i){
    Var tv = getVerifyData( _ntk->getLatch(i), 0);
    if(tv)
      cube->_latchValues[i]._bit = getValue( tv );
    cube->_latchValues[i]._dontCare = 0;
  }
}
bool* V3SvrPDRSat::ternarySimInit(Cube* c){
  getSATAssignmentToCube(c); //for latch

  //for inputs
  bool* ii = new bool[_I];
  for (uint i = 0; i < _I; ++i){
    Var tv = getVerifyData( _ntk->getInput(i), 0);
    if(tv)
      ii[i] = getValue( tv );
  }
  return ii;
}
Cube* V3SvrPDRSat::getBadCube(uint depth){
  // 0 -> init
  // SAT ? [R_k and !P]
  assumeRelease();
  assumeProperty(_monitor, false, 0);

  if(soft_debug) cerr << "\nGet bad cube, _actVars.size() : " << _actVars.size() <<" depth : "<< depth << endl;
  if(heavy_debug) cerr << "added actVars from " << depth << " to " << _actVars.size()-1 << endl;

  //add R_k
  for (unsigned i = depth; i < _actVars.size(); ++i){
    _assump.push( Lit( _actVars[i] ) );
  }
  if(heavy_debug){
    cerr << "_assump : ";
    for (int i = 0; i < _assump.size(); ++i){
      cerr << _assump[i].x << " ";
    }
    cerr << endl;
  }

  Cube* c = new Cube();
  if(assump_solve()){
    if(soft_debug) cerr << "result : SAT\n";
    bool* ii = ternarySimInit(c);
    if (heavy_debug){cerr << "cube before 3-sim : "; c->show(); }
    //TODO: uncomment the following line to evoke SAT generalization
    c = ternarySimulation(c,0,ii);
    if (soft_debug){cerr << "cube after 3-sim : " ; c->show(); }
    delete[] ii;
    return c;
  }
  else{
    if(soft_debug) cerr << "result : UNSAT\n";
    delete [] c->_latchValues;
    c->_latchValues = NULL;
    return c;
  }
}
void V3SvrPDRSat::newActVar(){
    Var v = newVar(1);
    _actVars.push_back(v);
}
void V3SvrPDRSat::initValue3Data(){
   _Value3List.clear();
   for (unsigned i = 0; i < _ntk->getNetSize(); ++i){
      _Value3List.push_back(Value3(0,1));
   }
   // OAO: set CONSTgate initial value
   _Value3List[0] = Value3(0,0);
}

void V3SvrPDRSat::OAO_InitValue3Data(V3Vec<Value3>::Vec &myList){
   // almost same as the function above,
   // except that it passes in arbitory vector& myList
   myList.clear();
   for (unsigned i = 0; i < _ntk->getNetSize(); ++i){
      myList.push_back(Value3(0,1));
   }
   myList[0] = Value3(0,0);
}

// OAO: int -> bool
#if 110
bool V3SvrPDRSat::getValue(Var v) const {
   return (_Solver->model[v] == l_True);
}
#else
int V3SvrPDRSat::getValue(Var v) const {
  if(_Solver->model[v]==l_True)return 1;
  if(_Solver->model[v]==l_False)return 0;
  assert(0);
  return -1;
}
#endif

bool V3SvrPDRSat::isBlocked(TCube c){
  //TCube t = solveRelative(c,c._frame);
  //if(t._frame == -1){return false;}
  //else return true;
  return false;
}
bool V3SvrPDRSat::isInitial(Cube* c){
  // check if a cube subsumes R0
  for (unsigned i = 0; i < _L; ++i){
    if(c->_latchValues[i]._bit == 1 &&
       c->_latchValues[i]._dontCare == 0)
      return false;
  }
  return true;
}

void V3SvrPDRSat::blockCubeInSolver(TCube s){
  if(soft_debug){
    cerr<<"@@blocked cube in solver in frame : "<<s._frame << " cube is : ";
    s._cube->show();
  }
  assert(s._frame != 0);

  vec<Lit> lits;
  Lit l;
  for (uint i = 0; i < _L; ++i){
    if(!(s._cube->_latchValues[i]._dontCare)){
      #if 1  // not sure if this improves efficiency
      l = mkLit(getVerifyData(_ntk->getLatch(i),0), 
                s._cube->_latchValues[i]._bit);
      #else // this one is easier to read 
      l = s._cube->_latchValues[i]._bit ?
        mkLit(getVerifyData(_ntk->getLatch(i),0), true ) :
        mkLit(getVerifyData(_ntk->getLatch(i),0), false);
      #endif      
      lits.push(l);
    }
  }
  if(s._frame != INT_MAX){
    assert( (uint)s._frame < _actVars.size() );
    lits.push( mkLit( _actVars[s._frame], true ) );
  }
  if(heavy_debug){
    for (int i = 0; i < lits.size(); ++i) cerr << lits[i].x << " + ";
    cerr << endl;
  }
  _Solver->addClause(lits);
}

Var V3SvrPDRSat::addNotSToSolver(Cube* c){
   // !s
  Var tmpActVar = newVar(1);
  vec<Lit> lits;
  Lit l;
  for (uint i = 0; i < _L; ++i){
    if(!(c->_latchValues[i]._dontCare)){
      #if 1
       l = mkLit(getVerifyData(_ntk->getLatch(i),0),
                 c->_latchValues[i]._bit);
      #else 
      l = c->_latchValues[i]._bit ?
        mkLit(getVerifyData(_ntk->getLatch(i),0), true ) :
        mkLit(getVerifyData(_ntk->getLatch(i),0), false);
      #endif
      lits.push(l);
    }
  }
  lits.push(mkLit(tmpActVar,true));
  _Solver->addClause(lits);
  if(heavy_debug){
    cerr << "!s : ";
    for (int i = 0; i < lits.size(); ++i){
       cerr << lits[i].x << " ";
    }
    cerr  << endl;
  }
  _assump.push(mkLit(tmpActVar,false)); // actVar of !s
  return tmpActVar;
}

void V3SvrPDRSat::addNextStateSToSolver(Cube* c, vector<Lit>& Lit_vec_origin){
  if(heavy_debug) cerr << "Var of s'\n";
  for (uint i = 0; i < _L; ++i){ // s'

    V3NetId id = _ntk->getInputNetId(_ntk->getLatch(i),0);// get input of Latch(i)
    Var tmp =  getVerifyData(id ,0); // get Var of it
    if(!tmp) assert(0); // make sure it's valid
    //cerr << tmp << " ";
    /*cerr << "invert?" << id.cp << endl;*/
    if(c->_latchValues[i]._dontCare == 0){
      bool p = (c->_latchValues[i]._bit ^ id.cp ) ;
#if 1
      _assump.push( mkLit(tmp, !p) );
      Lit_vec_origin.push_back( mkLit(tmp, !p) );
#else
      _assump.push( p ? mkLit(tmp,false): mkLit(tmp,true));
      Lit_vec_origin.push_back( p ? mkLit(tmp,false): mkLit(tmp,true));
#endif
    }
    else Lit_vec_origin.push_back( Lit(0) ); // use Lit(0) to represent NULL
  }

  if(heavy_debug){
    cerr << "Lit_vec_origin : ";
    for (uint i = 0; i < _L; ++i){
      cerr << Lit_vec_origin[i].x << " ";
    }
    cerr << endl;
  }
}


Cube* V3SvrPDRSat::UNSATGeneralizationWithUNSATCore(Cube * c, vector<Lit>& Lit_vec_origin){
  vector<Lit> Lit_vec_new;
  Lit_vec_new.resize(_L);
  for (unsigned i = 0; i < _L; ++i){
    Lit_vec_new[i] = Lit(0);
  }
  if(heavy_debug){
    cerr <<  "conflict core : ";
    for (int j = 0; j < _Solver -> conflict.size(); ++j){
      cerr << (_Solver -> conflict[j]).x << " ";
    }
    cerr  << endl;
  }
  // find which lit is in unsat core and generalize the cube
  for (uint i = 0; i < Lit_vec_origin.size(); ++i){
    for (int j = 0; j < _Solver -> conflict.size(); ++j){
      if (Lit_vec_origin[i] != Lit(0) ){
#if 1
         if(var(Lit_vec_origin[i]) == var(_Solver->conflict[j])){
           Lit_vec_new[i] = Lit_vec_origin[i];
           break;
         }
#else
         if( ~(Lit_vec_origin[i]) == _Solver -> conflict[j] ){
          Lit_vec_new[i] = Lit_vec_origin[i];
          break;
        }
        else if(Lit_vec_origin[i] == _Solver -> conflict[j]){
          Lit_vec_new[i] = Lit_vec_origin[i];
          break;
        }
#endif
      }
    }
  }

  Cube* tmpCube = new Cube(c);
  //bool tmpb;
  for (uint i = 0; i < _L; ++i){
    if(Lit_vec_new[i] == Lit(0)) tmpCube->_latchValues[i]._dontCare = 1;
  }

  if(isInitial(tmpCube)){ // if tc isInitial ,then use origin
#if 1
     delete tmpCube;
     return c;
#else
    assert(c->_latchValues);
    for (uint i = 0; i < _L; ++i){
      tmpCube->_latchValues[i] = c->_latchValues[i];
    }
#endif
  }
  return tmpCube;
}
void V3SvrPDRSat::assertCubeUNSAT(Cube*c, uint d){
  // This is just a heavy_debug function
  assert(d);
  assumeRelease();
  vector<Lit> Lit_vec_origin;
  addNextStateSToSolver(c, Lit_vec_origin);
  Var tmpActVar = addNotSToSolver(c);
  int k = d - 1;
  uint idx = k;
  if(idx < _actVars.size())
    for (; idx < _actVars.size(); ++idx){ // actVars, here is to represent R_k
      _assump.push( Lit( _actVars[idx] ) );
    }
  if(assump_solve()){
    _Solver->addUnit(mkLit(tmpActVar, true));
    assert(0);
  }
  else{
    _Solver->addUnit(mkLit(tmpActVar, true));
    return;
  }
}
TCube V3SvrPDRSat::solveRelative(TCube s, size_t param){
  // important preliminary
  // class Var == int
  // class Lit.x == (2*var) + (int)sign

  //param 0 = if the query satisfiable, just return (CUBE NULL, FRAME NULL).
  /*Parameter 1 “EXTRACTMODEL” means: SAT ? [ Rk-1 and !s and T and s' ]
    Parameter 2 “NOIND”        means: SAT ? [ Rk-1 and T and s' ] */
  if(soft_debug){
    cerr << "--Solve Relative in frame : "<< s._frame << " param : " << param;
    cerr << ", cube is : ";s._cube->show();
  }
  assert(s._frame != 0);

  assumeRelease();
  vector<Lit> Lit_vec_origin;
  addNextStateSToSolver(s._cube, Lit_vec_origin);// s'

  Var tmpActVar = 0;
  if(param == 1)
    tmpActVar = addNotSToSolver(s._cube);// !s

  // R_k
  int k = s._frame - 1;
  if(heavy_debug) cerr << "added actVars from " << k << " to " << _actVars.size()-1 << endl;

  uint idx = k;
  if(idx < _actVars.size())
    for (; idx < _actVars.size(); ++idx){ // actVars, here is to represent R_k
      _assump.push( Lit( _actVars[idx] ) );
    }

  if(heavy_debug){
    cerr << "_assump : ";
    for (int i = 0; i < _assump.size(); ++i){
      cerr << _assump[i].x << " ";
    }
    cerr << endl;
  }

  // SAT solve here
  if(assump_solve()){ //SAT
    if(soft_debug) cerr << "result: SAT , ";
    if(param == 1) _Solver->addUnit(mkLit(tmpActVar, true)); // unvalid this tmp actVar forever
    if(param == 0){ // param == 0, return Cube_NULL,Frame_NULL
      return TCube();
    }
    else{
      Cube* tmpCube = new Cube();
      bool* ii = ternarySimInit(tmpCube);
      if (soft_debug){cerr << "cube before 3-sim:";tmpCube->show();}
      //TODO: uncomment the following line to evoke SAT generalization
      tmpCube = ternarySimulation(tmpCube,1,ii);
      if(soft_debug){cerr << "returned cube after 3-sim:"; tmpCube->show(); }
      delete [] ii;
      TCube r(tmpCube,-1);
      return r;
    }
  }
  else{ //UNSAT
    if(param == 1) _Solver->addUnit(mkLit(tmpActVar, true)); // unvalid this tmp actVar forever


    Cube * tmpCube = UNSATGeneralizationWithUNSATCore(s._cube,Lit_vec_origin);
    //Cube * tmpCube = s._cube;

    // find the lowest act used
    for (uint i = k; i < _actVars.size(); ++i){
      for (int j = 0; j < _Solver -> conflict.size(); ++j){
        if( ~Lit(_actVars[i]) == _Solver -> conflict[j] ){
          if(soft_debug){
            cerr << "result: UNSAT in frame : " << i+1 <<  ", "; cerr << "return:"; tmpCube->show();
          }
          TCube r(tmpCube,i+1);
          //assertCubeUNSAT(tmpCube,i+1);
          return r;
        }
      }
    }
    // UNSAT core has no actvars, mean it's will always UNSAT in any Frame (so put in Frame_INF)
    if(soft_debug){
      cerr << "result: UNSAT in frame INT_MAX , "; cerr << "return:"; tmpCube->show();
    }
    TCube r(tmpCube,INT_MAX);
    //assertCubeUNSAT(tmpCube,INT_MAX);
    return r;
  }
}

#endif

