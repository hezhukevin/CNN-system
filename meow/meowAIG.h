#ifndef MEOW_AIG_H
#define MEOW_AIG_H
#include<iostream>
#include<fstream>
#include<sstream>
#include<cstring>
#include <utility> 
#include<set>
#include<vector>
#include<map>
#include<queue>
#include <stdlib.h>
#include <bitset> 
#include <time.h>  
#include <algorithm> 
#include<limits>
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"

using namespace std;
enum AIG_TYPE{
  MEOW_AIG_PI,
  MEOW_AIG_AND,
  MEOW_AIG_FF,
  MEOW_AIG_ZERO,
  MEOW_AIG_NEXT
};
const size_t FANIN_MASK = (std::numeric_limits<size_t>::max() >> 1) << 1;

class meowAIGNode{
  public:
    meowAIGNode(int meowID, int gateID, AIG_TYPE type);
    AIG_TYPE getType(){ return _type;}
    int getGateID(){ return _gateID;}
    int getMeowID(){ return _meowID;}
    void setFanin0(meowAIGNode* fanin0, int neg);
    void setFanin1(meowAIGNode* fanin1, int neg);
    meowAIGNode* getFanin0(){ return _fanin0;}
    meowAIGNode* getFanin1(){ return _fanin1;}
    meowAIGNode* getFanin0Reg();
    meowAIGNode* getFanin1Reg();
    int getFanin0Phase();
    int getFanin1Phase();
    void printNode();
  private:
    AIG_TYPE _type;
    meowAIGNode* _fanin0;
    meowAIGNode* _fanin1;
    int _gateID; // up-to-date ID in gia
    int _meowID;
};
class meowAIG{
  public:
    meowAIG(Gia_Man_t* cir);
    ~meowAIG();
    meowAIGNode* getZero(){return _nodeList[0];}
    meowAIGNode* getOne(){
      size_t temp1 = ((size_t)_nodeList[0])|1;
      return reinterpret_cast<meowAIGNode*>(temp1); 
    }
    int getPhase(meowAIGNode* node){
      size_t temp = ((size_t)node)&1;
      return temp;
    }
    meowAIGNode* getRegular(meowAIGNode* node){
      size_t temp1 = ((size_t)node)&FANIN_MASK;
      return reinterpret_cast<meowAIGNode*>(temp1); 
    }
    meowAIGNode* addNext(meowAIGNode* fanin0);
    meowAIGNode* addPI(int gateID);
    meowAIGNode* addExtraPI();
    meowAIGNode* addFF(int initial);
    meowAIGNode* addFF(meowAIGNode* fanin0, int neg0, int initial);
    meowAIGNode* addAND(meowAIGNode* fanin0, int neg0,
                        meowAIGNode* fanin1, int neg1, int outNeg);
    meowAIGNode* addEQ(meowAIGNode* fanin0, meowAIGNode* fanin1, 
                        int neg);
    meowAIGNode* addSince(meowAIGNode* a, meowAIGNode* b);
    meowAIGNode* checkExist( meowAIGNode* fanin0, int neg0,
                             meowAIGNode* fanin1, int neg1);
    meowAIGNode* neg(meowAIGNode* input);
    void getSupports(meowAIGNode* target, set<int>& supportList);
    void getFurtherList(set<int>& supportList, set<int>& furtherList);
    void addTable(meowAIGNode* node);
    void printAIG();
    int getFFNum(){  return _FFList.size();}
    int getPINum(){ return _PIList.size();}
    int getExtraPINum(){  return _extraPIs.size();}

    int getPIGateID(int PIindex){
       return _PIList[PIindex]->getGateID();
     }
    void addID2Value(int meowID, int value){
         _meowID2Value[meowID] = value;}
    void addFF2Value(int FFindex, int value){
      _meowID2Value[_FFList[FFindex]->getMeowID()] = value;
    }
    void addExtraPI2Value(int PIindex, int value){
      _meowID2Value[_extraPIs[PIindex]->getMeowID()] = value;
    }
    void addPI2Value(int PIindex, int value){
      _meowID2Value[_PIList[PIindex]->getMeowID()] = value;
    }
    int getFFInputValue(Gia_Man_t* pNew, int FFindex);
    void cleanMap(){
      _meowID2Value.clear();
      _meowID2Value[0] = 0;
    }
    int copy2GiaX(Gia_Man_t* pNew, meowAIGNode* target, int Xlevel,
                  map< pair<int, int>, int>& gateT2Value, int special);
    int copy2GiaTimeFrame(Gia_Man_t * pNew, int cirID, int Xlevel, map< pair<int, int>, int>& gateT2Value, int special);
    int copy2Gia(Gia_Man_t* pNew, meowAIGNode* target, int specail);

    void getSignals(set<int>& signals){
      for(int i = 0; i < _PIList.size(); ++i)
         signals.insert(_PIList[i]->getGateID());
    }
    void setOldControl(vector<int>* oldControl){
      _oldControl = oldControl;
    }
    vector<int>* getOldControl(){
      return _oldControl;
    }
  private:
    vector<int>* _oldControl;
    vector<meowAIGNode*> _nodeList; // meowID -> position 
    vector<meowAIGNode*> _FFList;
    vector<meowAIGNode*> _NextList;
    vector<meowAIGNode*> _PIList;
    vector<meowAIGNode*> _extraPIs;
    map<int, meowAIGNode*> _giaID2Node;
    map<string, meowAIGNode*> _hashTable;
    map<int, int> _meowID2Value;
    map<meowAIGNode*, set<int>* > _next2Supports;
    Gia_Man_t* _cir;
    map<int, set<int> > _gate2Supports;
   // meowAIGNode* _const0;
};
#endif
