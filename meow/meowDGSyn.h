#ifndef MEOW_DG_SYN_H
#define MEOW_DG_SYN_H
#include<iostream>
#include<fstream>
#include <sstream>
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
#include "ext/meow/meowDGTrans.h"
#include "ext/meow/meowDG.h"
#include "ext/meow/meowAIG.h" 
using namespace std;

class meowDGSyn{// top class to synthesis based on dependency graph
  public: 
    meowDGSyn(Gia_Man_t* cir, int depth, int greedy);
    ~meowDGSyn();
    void performSynthesis();
    void performVerification(Gia_Man_t* goldenCir);
    void performReduce();
    void drawGraph(char* fileName);
    meowDG* buildDG(Gia_Man_t* cir, bool merge);

    void createPiPo(Gia_Man_t* cir, meowDG* DG);
    void createGatedFFs(Gia_Man_t* cir, meowDG* DG, meowDGTrans* transAPI);
    void createTrans(Gia_Man_t* cir, meowDG* DG, meowDGTrans* transAPI);


    void createOthers(Gia_Man_t* cir, meowDG* DG, bool merge);
    void createOthersInput(set<int>& FFList, 
                           Gia_Man_t* cir, meowDG* DG);
    void createOthersOutput(set<int>& FFList,
                            Gia_Man_t* cir, meowDG* DG);
    void findFaninWordsRecur(int gateID, Gia_Man_t* cir, meowDG* DG, 
                             map<int, set<int> >& faninWords);
    void findFanoutWordsRecur(int gateID, Gia_Man_t* cir, meowDG* DG,
                              map<int, set<int> >& fanoutWords);

    void mergedByMap(set<int>& FFList, map<int, set<int> >& id2List, 
                     meowDG* DG);
    void connect(Gia_Man_t* cir, meowDG* DG);
    void connectNode(meowDGNode* target, Gia_Obj_t* node, 
                     Gia_Man_t* cir, 
                     map<int, meowDGNode*>& dgMap,
                     map<int, set<meowDGNode*> >& id2Terminal);
    int createEnable(Gia_Man_t* pNew, vector<int>& controls);
    meowAIGNode* getUpdatingCondition(meowAIG* updating, meowDGNode* target);
    void addInputNode(vector<int>& inputs, Gia_Man_t* cir, meowDG* DG);
    
    void findControlMapping(Gia_Man_t* goldenCir, 
                            map<int, int>& G2RMap); 
    void findVerificationTarget(meowDG* goldDG, Gia_Man_t* goldenCir, 
                                map<int, int>& G2RId,
                                vector<meowDGNode*>& candidates);
    void orderCandidates(vector<meowDGNode*>& candidates);
    bool checkVerificationTargetNode(meowDG* goldDG,
                                     Gia_Man_t* goldenCir,
                                     map<int, int>& G2RId,
                                     meowDGNode* target);
    void verificationNode(meowDGNode* target,
                          meowDG* goldDG,
                          Gia_Man_t* goldenCir,
                          map<int, int>& G2RId
                          );
    void getOldNewEnable( meowDGNode* target, 
                          vector<int>& oldControl,
                          meowDG* goldDG,
                          Gia_Man_t* goldenCir,
                          map<int, int>& R2GId);

    bool proveSATSynthesis(meowDGNode* target, meowAIG* cir, 
                           meowAIGNode* targetU, 
                           vector<int>& oldControl);

    bool proveOBSSynthesisSimp(meowDGNode* target, meowAIG* observable, vector<int>& oldControl);
    bool resolveXout(meowAIG* observable, meowAIGNode* Xout, 
                  meowDGNode* target, bool reverse);
    void reduceControl(meowDGNode* target, vector<int>& oldControl,
                        map<int, int>& G2RId);
    Gia_Man_t* preCopy();
    bool runPDR(Gia_Man_t* pNew);
    void satSynthesis(meowDGNode* target);
    void obsSynthesis(meowDGNode* target);
    void obsSynthesisGreedy(meowDGNode* target);
    void performGating(meowDGNode* target, meowAIG* cir,
                       meowAIGNode* control);
    void performGatingObv(meowDGNode* target, meowAIG* cir, 
                          meowAIGNode* control); 
    // same thing for two cases
    bool isUpToDate(meowDGNode* target, meowAIG* cir,
                    meowAIGNode* update, vector<int>& oldControl);
    Gia_Man_t* provePreprocess( meowDGNode* target, meowAIG* cir,
                                vector<int>& oldControl, 
                                set<int>& requiredFF);
    bool provePostProcess( Gia_Man_t* pNew, meowAIG* cir,
                           set<int>& requiredFF);
    void collectFF(meowDGNode* target, vector<int>& oldControl,
                   meowAIG* cir,
                   set<int>& requiredFF);
    void collectFFRecur(Gia_Obj_t* current, set<int>& requiredFF,
                        int token);
    void collectFullySupports(set<int>& signals); // for X synthesis
    int Gia_ObjCopy_rec(Gia_Man_t* pNew, Gia_Obj_t* current);
    void add2IDMap(map<int, int>& old2newID, Gia_Man_t* pNew, 
                   Gia_Obj_t* pObj);
   // void get
    Gia_Man_t* getNewCircuit(){
      if(_reducedNum ==0 && _gatedNum == 0)
        return NULL;

      return _currentCir;
    }
    bool isCombCycle(meowDGNode* target, meowDGNode* input){
      if(target->getType() == NODE_INTERNAL){
        if(target == input)
          return true;
        if(target->hasOutput(input) 
        && input->getType() == NODE_INTERNAL){
          return true;
        }
      }
      return false;
    }
    void printReport(){
      cerr<<"reduced FF numbers: "<<_reducedNum<<endl;
      cerr<<"Gated FF numbers: "<<_gatedNum<<endl;
    }
  private:
    Gia_Man_t* _currentCir;
    meowDGTrans* _transAPI;
    meowDG* _DG;
    int _reducedNum;
    int _gatedNum;
    int _depth;
    int _greedy;
};
#endif
