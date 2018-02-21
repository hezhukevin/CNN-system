#ifndef MEOW_DG_H
#define MEOW_DG_H
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
#include "ext/meow/meowDGNode.h"
#include "ext/meow/meowDGWord.h"
#include <algorithm> 
using namespace std;
class meowDG{
  public:
    meowDG();
    meowDGNode* addNode(NODE_TYPE type, vector<int>& gateList);
    ~meowDG();
    bool addGate2Node(meowDGNode* newNode, vector<int>& gateList);
    bool createdBefore(vector<int>& gateList);
    meowDGNode* getNode(int gateID);
    map<int, meowDGNode*>& getMap(){ return _gate2Node;}
    vector<meowDGNode*>& getList(){ return _nodeList;}
    void drawGraph(char* fileName, bool print);
    void getUpdatingOrder(vector<meowDGNode*>& candidates);
    void updatingOrderRecur(vector<meowDGNode*>& candidates, 
                            set<meowDGNode*>& visited, 
                            meowDGNode* current);
    void getObserveOrder(vector<meowDGNode*>& candidates);
    void observeOrderRecur(vector<meowDGNode*>& candidates,
                           set<meowDGNode*>& visited,
                           meowDGNode* current);
    void reviseNode(meowDGNode* target, int newControl);
    void reviseNodeReduce(meowDGNode* target, int newControl);
    void updateDGIDs(map<int, int>& old2newID);
    void reportNum(){
      cerr<<"totalDG Node Num = "<<_nodeList.size()<<endl;
      for(int i = 0; i < _nodeList.size(); ++i)
        _nodeList[i]->printDGNode();
    }
    set<int>& getControlList(){ return _controlList;}

    void addNode2Inputs(meowDGNode* gated, vector<int>& inputs){
      //cerr<<"add Inputs to "<<gated->getID()<<endl;
      /*for(int i = 0; i < inputs.size(); ++i)
        cerr<<inputs[i] <<" ";
      cerr<<endl;*/
      _node2Inputs[gated] = inputs;
    }
    vector<int> getNode2Inputs(meowDGNode* gated){
      return _node2Inputs[gated];
    }
    void replaceNode(meowDGNode* target, meowDGNode* newNode);
    bool isReplaced(meowDGNode* target){
      return (_replaced.find(target)!=_replaced.end());
    }
  private:
    map<meowDGNode*, vector<int> > _node2Inputs;
    vector<meowDGNode*> _nodeList;
    map<int, meowDGNode*> _gate2Node;
    set<int> _controlList;
    set<meowDGNode*> _replaced;
};
#endif
