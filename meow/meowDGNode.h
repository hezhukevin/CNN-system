#ifndef MEOW_DG_NODE_H
#define MEOW_DG_NODE_H
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
#include "ext/meow/meowDGWord.h"
#include "ext/meow/meowAIG.h"
#include <algorithm> 
using namespace std;
enum NODE_TYPE{
  NODE_PI, //0
  NODE_CONST,//1
  NODE_PO,//2
  NODE_FF,//3
  NODE_GATED,//4
  NODE_TRANS,//5
  NODE_INTERNAL //6 
};
class meowDGNode{
  public:
    meowDGNode(unsigned id, vector<int>& idList);    
    virtual ~meowDGNode();
    unsigned getID(){return _id;}
    vector<int>& getGates();
    int getMaxGateID();
    int getWidth(){
      return _word->getSize();  
    }
    NODE_TYPE getType(){ return _type;}
    void addInput(meowDGNode* input){
      _inputList.insert(input); }
    void removeInput(meowDGNode* input){
      _inputList.erase(input);
    }
    bool hasOutput(meowDGNode* output){
      return (_outputList.find(output)!= _outputList.end());
    }
    set<meowDGNode*>& getInput(){return _inputList;}
    set<meowDGNode*>& getOutput(){return _outputList;}
    void addOutput(meowDGNode* output){
      _outputList.insert(output);}
    void removeOutput(meowDGNode* output){
      _outputList.erase(output);
    }
    void setType(NODE_TYPE type){ _type = type;}
    virtual void formulateUpdate() = 0;


    virtual meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ) = 0;
    virtual meowAIGNode* constructUpdateCir(meowAIG* uCir, 
                                            set<meowDGNode*>& visited,
                                            int depth
                                            ) = 0;
    virtual meowAIGNode* constructObserveCir(meowAIG* oCir,
                                     set<meowDGNode*>& visited,
                                     int depth, 
                                    meowDGNode* source) = 0;
    // source is in "input"
    void updateID(map<int, int>& old2newID);
    void printDGNode(){
      cerr<<"Node ID "<<_id<<", type = "<<_type<<", size "<<getWidth()<<endl;
      _word->printDGWord();
    }
    void setGatedU(){
      _explored|=4;
    }
    bool isGatedU(){
      return (_explored&4)!=0;
    }
    void setExploredU(){
      _explored|=1;
    }
    void setExploredO(){
      _explored|=2;
    }
    bool isExploredU(){
      return (_explored&1)!=0;
    }
    bool isExploredO(){
      return (_explored&2)!=0;
    }
   // void updateGateID(map<int, int>& old2newID);
  private:
    set<meowDGNode*> _inputList;
    set<meowDGNode*> _outputList;
    unsigned _id;
    meowDGWord* _word;
    NODE_TYPE _type;
    int _explored;    
};
class meowDGPI: public meowDGNode{
  public:
    meowDGPI(unsigned id, vector<int>& idList);
    void formulateUpdate(){} // for verification?
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir, 
                                    set<meowDGNode*>& visited,
                                    int depth); // for synthesis
   meowAIGNode* constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
//    void updateID(map<int, int>& old2newID);

  private:

};

class meowDGConst: public meowDGNode{
  public:
    meowDGConst(unsigned id, vector<int>& idList);
    void formulateUpdate(){} // for verification
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir,
                                    set<meowDGNode*>& visited,
                                    int depth); // for synthesis
    meowAIGNode* constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
 //   void updateID(map<int, int>& old2newID);

  private:

};
class meowDGPO: public meowDGNode{
  public:
    meowDGPO(unsigned id, vector<int>& idList);
    void formulateUpdate(){}
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir,
                                    set<meowDGNode*>& visited,
                                    int depth);
    meowAIGNode* constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
  //  void updateID(map<int, int>& old2newID);

  private:
};

class meowDGFF:public meowDGNode{
  public:
    meowDGFF(unsigned id, vector<int>& idList);
    void formulateUpdate(){}
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir, 
                                    set<meowDGNode*>& visited, 
                                    int depth);
    meowAIGNode* constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
   // void updateID(map<int, int>& old2newID);

  private:

};
class meowDGTransBlock:public meowDGNode{
  public:
    meowDGTransBlock(unsigned id, vector<int>& idList);
    void setInput0(meowDGNode* input0){
      _input0 = input0;
      addInput(input0);
    }
    void setInput1(meowDGNode* input1){
      _input1 = input1;
      addInput(input1);
    }
    void replaceInput(meowDGNode* oldNode, meowDGNode* newNode){
      if(_input1 == oldNode)
        _input1 = newNode;
      if(_input0 == oldNode)
        _input0 = newNode;
    }
    void formulateUpdate(){}
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir, 
                                    set<meowDGNode*>& visited,
                                    int depth);
    meowAIGNode* constructObserveCir( meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
    void addSelect(int& sel);
    void reviseSel(map<int, int>& old2newID);

  private:
    int _selID; // must be positive
    meowDGNode* _input0;
    meowDGNode* _input1;
};
class meowDGCombCloud:public meowDGNode{ // useless?!
  public:
    meowDGCombCloud(unsigned id, vector<int>& idList);
    void formulateUpdate(){}
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir, 
                                    set<meowDGNode*>& visited,
                                    int depth);
    meowAIGNode* constructObserveCir( meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
   // void updateID(map<int, int>& old2newID);

  private:

};
class meowDGGatedFF:public meowDGNode{
  public:
    meowDGGatedFF(unsigned id, vector<int>& idList);
    void formulateUpdate(){}
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir,
                                    set<meowDGNode*>& visited,
                                    int depth);
    meowAIGNode* constructObserveCir( meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
    meowAIGNode* constructObserveCirSpecial( meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);


    vector<int>& getControlIDs(){
      return _controlIDs;
    }
    size_t getControlNum(){
      return getControlNum();
    }
    void addControlIDs(vector<int>& controls);
    void addControlID(int control);
    void reduceControlID(int newControl){
      _controlIDs.clear();
      _controlIDs.push_back(newControl);
    }
    void reviseControl(map<int, int>& old2newID);
   // void updateID(map<int, int>& old2newID);
    void getSignals(set<int>& signals){
      for(int i = 0; i < _controlIDs.size(); ++i){
        signals.insert(abs(_controlIDs[i]));
        //cerr<<"new: "<<_controlIDs[i]<<endl;
      }
    }
  private:
    vector<int> _controlIDs;
    bool _revised;
};
class meowDGInternal:public meowDGNode{
  public:
    meowDGInternal(unsigned id, vector<int>& idList);

    void formulateUpdate(){}
    meowAIGNode* formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           );
    meowAIGNode* constructUpdateCir(meowAIG* uCir, set<meowDGNode*>& visited, int depth);
     meowAIGNode* constructObserveCir( meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source);
 //   void updateID(map<int, int>& old2newID);

  private:

};
// create 8 different nodes below
#endif
