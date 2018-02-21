#ifndef MEOW_DG_WORD_H
#define MEOW_DG_WORD_H
#include<iostream>
#include<fstream>
#include<sstream>
#include<cstring>
#include<set>
#include<vector>
#include<map>
#include<queue>
#include <stdlib.h>
#include <bitset> 
#include <time.h>  
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "misc/extra/extra.h"
#include <algorithm> 
using namespace std;
class meowDGWord{ // we will need this when we construct dependency
  public:
    meowDGWord(vector<int>& gateIDs){
      for(int i = 0; i < gateIDs.size(); ++i)
        _gateIDs.push_back(gateIDs[i]);
    }


    void updateIDs(map<int, int>& old2newID){
      for(int i = 0; i < _gateIDs.size(); ++i)
        _gateIDs[i] = old2newID[_gateIDs[i]];
    }
    unsigned getSize(){ return _gateIDs.size(); }
    vector<int>& getGateIDs(){ return _gateIDs; }
    void printDGWord(){
      for(int i = 0; i < _gateIDs.size(); ++i)
        cerr<<" "<<_gateIDs[i];
      cerr<<endl;
    }
   int getMaxGateID(){
     int max = 0;
     for(int i = 0; i < _gateIDs.size(); ++i){
       if(abs(_gateIDs[i])> max)
         max = abs(_gateIDs[i]);
     }
     return max;
   }    
  // ideally we don't need to worry about phase....
  private:
    vector<int> _gateIDs; // output ids on the original circuit
};
#endif
