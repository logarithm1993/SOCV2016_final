/****************************************************************************
  FileName     [ pdrMgr.cpp ]
  PackageName  [ pdr ]
  Synopsis     [ Define PDR main functions ]
  Author       [ SillyDuck ]
  Copyright    [ Copyright(c) 2016 DVLab, GIEE, NTU, Taiwan ]
 ****************************************************************************/
#define showinfo 0

#include <fstream>
#include <iostream>
#include <iomanip>
#include <string>
#include <cstdio>
#include <stdlib.h>
#include <cassert>
#include <climits>
#include <cmath>
#include <unistd.h>
#include <queue>
#include <vector>
#include <algorithm>

#include "v3Msg.h"
#include "v3NtkUtil.h"
#include "v3SvrPDRSat.h"
#include "v3NtkHandler.h" // MODIFICATION FOR SoCV BDD
#include "v3Ntk.h"
#include "PDRDef.h"
#include "reader.h"
#include "pdrMgr.h"
using namespace std;

unsigned Cube::_L = 0;

struct cmp
{
  bool operator() (const TCube lhs, const TCube rhs)
                  { return lhs._frame > rhs._frame; }
};


void PDRMgr::verifyProperty(const string& name, const V3NetId& monitor) {

  // Main verification starts here
  _ntk = new V3Ntk(); *_ntk = *(v3Handler.getCurHandler()->getNtk());
  SatProofRes pRes;

  V3SvrPDRSat* satSolver = new V3SvrPDRSat(_ntk, false, false);

  // monitor is a V3NetId,
  // Please figure out how V3 present a circuit
  // by V3Ntk and V3NetId in src/ntk/V3Ntk.h and V3Type.h
  satSolver->setMonitor(monitor);

  pRes.setMaxDepth(100);
  pRes.setSatSolver(satSolver);
  double runTime=0;
  double ctime = (double)clock() / CLOCKS_PER_SEC;

  PDR(monitor, pRes);

  runTime += (((double)clock() / CLOCKS_PER_SEC) - ctime);
  pRes.reportResult(name);
  cerr << "runTime:" << runTime << endl;
  delete satSolver; delete _ntk;
  reset();
}

void PDRMgr::reset() {
  _ntk = NULL;
}

void PDRMgr::buildAllNtkVerifyData(const V3NetId& monitor){
  // Added all circuit constrain to SAT solver here.

  for (uint32_t i = 0; i < _ntk->getLatchSize(); ++i)
     Z->addBoundedVerifyData(_ntk->getLatch(i), 0);
  for (uint32_t i = 0; i < _ntk->getLatchSize(); ++i)
     Z->addBoundedVerifyData(_ntk->getLatch(i), 1);
  Z->addBoundedVerifyData(monitor, 0);
  Z->initValue3Data();
  /*V3NetVec orderedNets;

  orderedNets.clear();
  orderedNets.reserve(_ntk->getNetSize());
  _ntk->newMiscData();
  for(unsigned i = 0, n = _ntk->getLatchSize(); i < n; ++i) {
    const V3NetId& nId = _ntk->getLatch(i);
    V3NetId tmp = _ntk->getInputNetId(nId, 0);
    _ntk->dfsOrder(tmp,orderedNets);
    _ntk->dfsOrder(nId,orderedNets);
  }
  for(unsigned i = 0, n = _ntk->getInoutSize(); i < n; ++i) {
    const V3NetId& nId = _ntk->getInout(i);
    V3NetId tmp = _ntk->getInputNetId(nId, 0);
    _ntk->dfsOrder(tmp,orderedNets);
  }
  for(unsigned i = 0, n = _ntk->getOutputSize(); i < n; ++i) {
    const V3NetId& nId = _ntk->getOutput(i);
    _ntk->dfsOrder(nId,orderedNets);
  }
  assert (orderedNets.size() <= _ntk->getNetSize());
  Z->initValue3Data();
  for (unsigned i = 0; i < orderedNets.size(); ++i){
    V3NetId tmp = orderedNets[i];
    Z->addVerifyData(tmp,0);
  }*/
}

bool PDRMgr::PDR(const V3NetId& monitor, SatProofRes& pRes){

  Z = pRes.getSatSolver();
  L = _ntk->getLatchSize();
  if(_ntk->getInoutSize()){assert(0);}
  Cube::_L = L;

  F = new vector< vector<Cube*>* >();
  Z->setFrame(F);
  buildAllNtkVerifyData(monitor);
  F->push_back(new vector<Cube*>()); // this is F_inf
                                    // which means the cube that will never be reached
                                    // in any time frame
                                    // watch out that _frame of cube in this Frame will be INT_MAX
  depth = 0;
  newFrame();                       // F[0]

  Z->addInitiateState();
  Z->setMonitor(monitor);

  /*if(heavy_debug){
    for (int i = 0; i < Z->_Solver->nClauses(); ++i){
      for (int j = 0; j < Z->_Solver->clauses[i]->size(); ++j){
        cerr<< (((((*(Z->_Solver->clauses[i]))[j]).x) & 1ul) ? "-" : "");
        cerr<< ((((*(Z->_Solver->clauses[i]))[j]).x)/2)  <<",";
      }
      cerr << endl;
    }
  }*/

  vector<TCube> vCex;
  vector<bool*> vInput;
// PDR Main function
  while(true){

    Cube* cube = Z->getBadCube(depth);  // find the BadCube
                                        // ( check SAT ? (!P & R_k) )
    vCex.clear();
    if(!vInput.empty())
    {
       for(uint x = 0, n = vInput.size(); x < n; ++x)
          delete [] vInput[x];
       vInput.clear();
    }
    if(heavy_debug){
      if(cube->_latchValues) { cerr<<"bad cube in frame:" << depth << endl; cube->show();}
      else cerr << "bad cube is NULL\n";
    }
    if (cube->_latchValues != NULL){
      TCube t(cube,depth);
      if (!recursiveBlockCube(t, vCex, vInput)) {
        pRes.setFired(0);
        if(showinfo){
          system("clear");
          cerr << "Number of Cubes:" << endl;
          for (unsigned i = 0; i < F->size()-1; ++i){
            cerr << "Frame "<< i << " : " << (*F)[i]->size() << endl;
          }
          cerr << "Frame INF :" << (*F)[F->size()-1]->size() << endl;
        }
        // OAO: print cex here < state, input TODO >
        for(int x = vCex.size()-1, s = x; x >=0; --x){
           cout<<"<time - "<< s-x << "> ";
           cout<<"input : ";
           for(uint y = 0; y < Z->_I; ++y){
              cout<< (vInput[x][y]? "1" : "0");
           }
           cout<<"\tstate : "; vCex[x]._cube->show();
           
           cout<<endl;
        }
        return true; // Cex found
      }
    }
    else{
      depth++;  // only here the depth will be increase
      newFrame();
      if(propagateBlockedCubes(pRes)){
        if(showinfo){
          system("clear");
          cerr << "Number of Cubes:" << endl;
          for (unsigned i = 0; i < F->size()-1; ++i){
            cerr << "Frame "<< i << " : " << (*F)[i]->size() << endl;
          }
          cerr << "Frame INF :" << (*F)[F->size()-1]->size() << endl;
        }
        return false;
      }
    }
  }
}

bool PDRMgr::recursiveBlockCube(TCube s0, vector<TCube>& vCex, vector<bool*>& vInput){
  if(soft_debug) cerr << "\n\n'''recursiveBlockCube'''\n" << endl;

  priority_queue< TCube, vector<TCube>, cmp >  Q;
  Q.push(s0);
  vCex.push_back(s0);
  
  if(heavy_debug) {cerr << "pushed : " << s0._cube << ", "; s0._cube->show();}
  while(Q.size() > 0){
    TCube s = Q.top();
    Q.pop();
    if(medium_debug) {cerr << "\n***poped : " << s._cube << ", "; s._cube->show();}
    if (s._frame == 0)
      return false;

    if( isBlocked(s) == false ){

      assert(! (Z->isInitial( s._cube ) ));

      TCube z = Z->solveRelative(s,1);
      
      if(z._frame != -1){
        // UNSAT, s is blocked
        z = generalize(z);

        if(heavy_debug){cerr << "cube after generalized :"; z._cube->show(); cerr << " frame : " << z._frame << endl; }

        if(medium_debug) cerr <<  "push to higher frame" << endl;
        while(z._frame < (int)(depth-1)  &&
          condAssign( z , Z->solveRelative(next(z),1) )
        );

        addBlockedCube(z);

        if( (s._frame < (int)depth) && (z._frame != INT_MAX) ){
          TCube a = next(s);
          Q.push(a);
          if(heavy_debug) {cerr << "pushed : " << s._cube << ", "; s._cube->show();}
        }
      }else{
        // SAT, s is not blocked
        //  TODO: to generate counterexample trace for unsafe property,
        //  you need to record the SAT pattern here.
        z._frame = s._frame - 1;
        Q.push(z);
        if(heavy_debug) {cerr << "pushed : " << z._cube << ", "; z._cube->show();}
        Q.push(s); // put it in queue again
        if(heavy_debug) {cerr << "pushed : " << s._cube << ", "; s._cube->show();}
        // OAO: record input assign. 
        bool* cexII = new bool [Z->_I];
        for (uint i = 0; i < Z->_I; ++i){
            Var tv = Z->getVerifyData( _ntk->getInput(i), 0);
            if(tv)
               cexII[i] = Z->getValue( tv );
        }
        vInput.push_back(cexII);
        vCex.push_back(z);
      }
    }
  }
  return true;
}

bool PDRMgr::isBlocked(TCube s){
  // isBlocked check if a cube is already blocked (in solver)
  // but we can first check if it is subsumes by that frame
  // then check by solver (more time-consuming)

  for (uint d = s._frame; d < F->size(); ++d){
    for (uint i = 0; i < (*F)[d] -> size(); ++i){
      if ( (*((*F)[d]))[i]->subsumes(s._cube) ){
        if(heavy_debug){
          cerr << "F->size():" << F->size() << endl;
          cerr << "already blocked in frame:" << d << endl;
          (*((*F)[d]))[i]->show();
        }
        return true;
      }
    }
  }
  return Z->isBlocked(s);
}

TCube PDRMgr::generalize(TCube s){
  // UNSAT generalization
  if(medium_debug) cerr << "UNSAT generalization\n";
  for (uint i = 0; i < L; ++i){
    Cube* tc = new Cube(s._cube);
    if (tc->_latchValues[i]._dontCare == 1) continue;
    else tc->_latchValues[i]._dontCare = 1;

    if( !(Z->isInitial(tc)) )
      condAssign(s, Z->solveRelative( TCube(tc,s._frame), 1 ));
  }
  return s;
}

bool PDRMgr::propagateBlockedCubes(SatProofRes& pRes){
  if(soft_debug) cerr << "\n\n'''propagateBlockedCubes'''\n" << endl;

  for (uint k = 1; k < depth; ++k){
    for (uint i = 0; i < (*F)[k]->size(); ++i){
      TCube s = Z -> solveRelative ( TCube((*((*F)[k]))[i],k+1) , 2);
      if(s._frame != -1) addBlockedCube(s);
    }
    if ((*F)[k]->size() == 0 ){ pRes.setProved(k);return true;}
  }
  return false;
}

void PDRMgr::newFrame(bool force){

  if(force || depth >= F->size()-1){
    unsigned n = F -> size();
    F -> push_back(new vector<Cube*>());
    (*F)[n] -> swap( *((*F)[n-1]) );
    Z->newActVar();
    assert(Z->_actVars.size() == F->size()-1); // the Frame_inf doesn't need ActVar
    if(heavy_debug){
      cerr << endl;
      cerr << "Newed frame:" << F->size() << endl;
      cerr << "actVar:" << Z->_actVars[Z->_actVars.size()-1] << endl;
    }
  }
  // else, frame has been newed, just ignore
  assert ( depth <= F->size()-2 ) ;
}

bool PDRMgr::condAssign(TCube& s, TCube t){
  if (t._frame != -1){
    s = t;
    return true;
  }
  else
    return false;
}

void PDRMgr::addBlockedCube(TCube s){
  assert(s._frame != -1);
  //addBlockedCube (To Frame Structure)

  if(medium_debug){
    cerr << "@@addBlockCube " ;cerr << "in frame : " <<s._frame << ", cube is : ";
    s._cube->show();
    //cerr << "frame size now is " << F->size() << endl;
  }

  if((uint)s._frame == F->size()-1){
    newFrame(true);
  }

  int l = s._frame;
  int r = F->size()-1;
  int min = l > r ? r : l ;
  unsigned k = (unsigned) min;

  for (uint d = 1; d <= k; ++d){
    for (uint i = 0; i < (*F)[d] -> size();){
      if( s._cube->subsumes((*((*F)[d]))[i]) ){
        if(medium_debug) {cerr << "subsumed cube in frame << " << d << ", cube is :"; (*((*F)[d]))[i]->show();}
        delete ((*((*F)[d]))[i]);
        (*((*F)[d]))[i] = (*F)[d]->back();
        (*F)[d] -> pop_back();
      }
      else
        i++;
    }
  }

  (*F)[k]->push_back(s._cube);


  Z->blockCubeInSolver(s);
}

TCube PDRMgr::next(const TCube& s){
  return TCube(s._cube,s._frame+1);
}
