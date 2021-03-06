/****************************************************************************
  FileName     [ PDRDef.h ]
  PackageName  [ pdr ]
  Synopsis     [ Define pdr basic classes ]
  Author       [ ]
  Copyright    [ Copyright(c) 2016 DVLab, GIEE, NTU, Taiwan ]
 ****************************************************************************/

#define show_address 0

#include <iostream>
#include <cassert>

#ifndef PDRDEF_H
#define PDRDEF_H
typedef unsigned int uint;
using namespace std;

class Value3
{
  // This is not dual rail encoding,
  // If the _dontCare is one it means it's X,
  // Otherwise it's decided by _bit
 public:
  Value3() : _bit(0), _dontCare(1) {}
  Value3(bool b,bool d) : _bit(b), _dontCare(d){}
  Value3(const Value3& a){
    _bit = a._bit;
    _dontCare = a._dontCare;
  }

  Value3 operator & (Value3 a)const{
#if 1 // this improves efficiency
    return Value3(_bit&a._bit, (_dontCare&(a._bit|a._dontCare)) | (_bit&a._dontCare));
#else
    if((_bit == 0 && _dontCare == 0) || a == Value3(0,0) ) return Value3(0,0);
    else if(a._dontCare || _dontCare) return Value3(0,1);
    else return Value3(1,0);
#endif
  }
  Value3 operator & (bool a)const{
    if(a == 0) return Value3(0,0);
    else if(_dontCare) return Value3(0,1);
    else return Value3(1,0);
  }
  Value3 operator | (Value3 a)const{
    if( (_bit == 1 && _dontCare == 0) || a == Value3(1,0) ) return Value3(1,0);
    else if(a._dontCare || _dontCare) return Value3(0,1);
    else return Value3(0 , 0);
  }
  Value3 operator | (bool a)const{
    if (a) return Value3(1,0);
    else if(_dontCare) return Value3(0,1);
    else return Value3(0, 0);
  }
  Value3 operator ~ ()const{
#if 0 // this is useless
     return Value3(!_bit,_dontCare);
#else
    if(_dontCare) {return Value3(0,1);}
    else{return Value3(!_bit, 0);}
#endif
  }
  bool operator == (const Value3& a) const{
    if(_dontCare ^ a._dontCare) return false;
    else if(_dontCare && a._dontCare) return true;
    else if(_bit == a._bit) return true;
    else return false;
  }
  bool operator != (const Value3& a) const {
    return !((*this) == a);
  }
  bool _bit;
  bool _dontCare;
};


class Cube
{
public:
  Cube(){
    // be careful cube is all zero for default constructor
    _latchValues = new Value3[_L];
    for (uint i = 0; i < _L; ++i){
      _latchValues[i]._bit = 0;
      _latchValues[i]._dontCare = 0;
    }
  }
  Cube(bool* b){
    _latchValues = new Value3[_L];
    for (uint i = 0; i < _L; ++i){
      _latchValues[i]._bit = b[i];
    }
  }
  Cube(bool* b, bool* d){
    _latchValues = new Value3[_L];
    for (uint i = 0; i < _L; ++i){
      _latchValues[i]._bit = b[i];
      _latchValues[i]._dontCare = d[i];
    }
  }
  Cube(Cube* c){
    if(c->_latchValues){
      _latchValues = new Value3[_L];
      for (uint i = 0; i < _L; ++i){
        _latchValues[i] = c->_latchValues[i];
      }
    }
    else{
      _latchValues = NULL;
    }
  }
  Cube(Cube* c, char* str)
  {
    _latchValues = c->_latchValues;
  }
  Cube(const Cube& c){
    if(c._latchValues){
      _latchValues = new Value3[_L];
      for (uint i = 0; i < _L; ++i){
        _latchValues[i] = c._latchValues[i];
      }
    }
    else{
      _latchValues = NULL;
    }
  }
  ~Cube(){
    if (_latchValues){
      delete [] _latchValues;
    }
    _latchValues = NULL;
  }
  bool subsumes(Cube* s)const{
    for (uint i = 0; i < _L; ++i){
#if 0 // it seems useless
      if(_latchValues[i]._dontCare) continue;
      if( (!s->_latchValues[i]._dontCare) & (_latchValues[i]._bit == s->_latchValues[i]._bit)) continue;
      return false;
#else
      if(!_latchValues[i]._dontCare){
        if(s->_latchValues[i]._dontCare) return false;
        if(s->_latchValues[i]._bit != _latchValues[i]._bit) return false;
      }
#endif
    }
    return true;
  }
  void show(){
    // debug fuction
    for (unsigned i = _L - 1; i != 0; --i){
      if(_latchValues[i]._dontCare) cerr << "X";
      else cerr << ((_latchValues[i]._bit) ? "1" : "0");
    }
    if(_latchValues[0]._dontCare) cerr << "X";
    else cerr << ((_latchValues[0]._bit) ? "1" : "0");
    cerr << endl;
  }
  static unsigned _L;                // latch size
  Value3* _latchValues;             // latch size long
};

class TCube
{
 public:
  TCube() : _cube(NULL), _frame(-1){
    //if(show_address){
      cerr << "NULL constructor\n";
    //}
  }
  TCube(Cube* c, unsigned d) : _cube(c), _frame((int)d){
    if(show_address){
      cerr << "default constructor\n";
      cerr << c << endl;
    }
  }
  
  TCube(const TCube& t){
    if(show_address){
      cerr << "copy constructor\n";
      cerr << _cube << endl;
      cerr << t._cube << endl;
    }
    _cube = t._cube;
    _frame = t._frame;
  }
  ~TCube(){
    if(show_address) cerr << "destructor\n";
  }
  TCube& operator = (const TCube& t){
    if(show_address){
      cerr << "= constructor\n";
      cerr << _cube << endl;
      cerr << t._cube << endl;
    }
    //if(_cube && _cube!= t._cube ) delete _cube;
    _cube = t._cube;
    _frame = t._frame;
    return (*this);
  }
  friend bool operator > (const TCube& l, const TCube& r){ return l._frame > r._frame; }

  Cube* _cube;
  int _frame; // -1 = frame_null
              // INT_MAX = INF;
};

#endif
