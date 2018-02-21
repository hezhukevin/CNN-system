#ifndef MEOW_DG_TRANS_H
#define MEOW_DG_TRANS_H
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
#include "ext/meow/meowMux.h"
#include "ext/meow/meowDGWord.h"
#include <algorithm> 
using namespace std;
class meowDGTrans{
  public:
    meowDGTrans(Gia_Man_t* cir);
    
    ~meowDGTrans();
    void printTrans();
    void getGatedFFs(vector<vector<int> >& inputs,
                     vector<vector<int> >& outputs,
                     vector<vector<int> >& controls);
    bool checkGatedFF(muxNode* target, bool& isFanin0,
                      vector<int>& roList);
    void getGatedFFRecur(muxNode* current,
                         muxNode* target,
                         vector<int>& controls,
                         vector<muxNode*>& nodeSeq);
  
    void getOtherTrans(vector<vector<int> >& input0s,
                       vector<vector<int> >& input1s,
                       vector<vector<int> >& outputs,
                       vector<int>& controls);

  private:
    Gia_Man_t* _cir;
    set<muxNode*> _gatedFFs;
    meowMux* _muxAPI;
};
#endif
