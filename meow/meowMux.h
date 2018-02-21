#ifndef MEOW_MUX_H
#define MEOW_MUX_H
#include<iostream>
#include <sstream>
#include<cstring>
#include<set>
#include<vector>
#include<map>
#include <stdlib.h>  
#include"ext/meow/wordNode.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "misc/extra/extra.h"
#include <algorithm> 

using namespace std;
class muxNode{

  public:
    muxNode(int controlID, int nodeID){
      _controlID = controlID;//positive
      _nodeID = nodeID;
    }
    void addOneMux(int gateID, int dataID0, int dataID1){
      if(gateID < 0)
        cerr<<"Mux output must be positive?!"<<endl;
      _gateIDs.push_back(gateID); // must be positive
      _fanin0IDs.push_back(dataID0);
      _fanin1IDs.push_back(dataID1);
    }
    int getNodeID(){
      return _nodeID;
    }
    int getControlID(){
      return _controlID;
    }
    void getFaninPhase(int pos, int& fanin1, int& fanin0, int& gateID){
      fanin1 = _fanin1IDs[pos];
      fanin0 = _fanin0IDs[pos];
      gateID = _gateIDs[pos];
    }
    void getFanoutID(int pos, int& fanout){
      fanout = _gateIDs[pos];
    }
    void getFaninID(int pos, int& fanin1, int& fanin0){
      fanin1 = abs(_fanin1IDs[pos]);
      fanin0 = abs(_fanin0IDs[pos]);

    }
    vector<int>& getFaninIDPhase(bool fanin0){
      if(fanin0)
        return _fanin0IDs;
      else
        return _fanin1IDs;
    }
    void getFaninID0(vector<int>& faninID0){
      for(int i = 0; i < _fanin0IDs.size(); ++i){
        faninID0.push_back(abs(_fanin0IDs[i]));
      }

    }
    void getFaninID1(vector<int>& faninID1){
      for(int i = 0; i < _fanin1IDs.size(); ++i){
        faninID1.push_back(abs(_fanin1IDs[i]));
      }

    }

    void getFaninIDs(set<int>& faninIDs){
      for(int i = 0; i < _fanin0IDs.size(); ++i){
        faninIDs.insert(abs(_fanin0IDs[i]));
        faninIDs.insert(abs(_fanin1IDs[i]));
      }
    }
    void getFanoutIDs(set<int>& fanoutIDs){
      fanoutIDs.insert(_gateIDs.begin(), _gateIDs.end());
    }
    vector<int>& getFanoutIDs(){
      return _gateIDs;
    } 
    int getBitNum(){
      return _gateIDs.size();
    }
    int getMaxID(){
      int max = -1;
      for(int i = 0; i < _gateIDs.size(); ++i){
        if(_gateIDs[i] > max)
          max = _gateIDs[i];
      }
      return max;
    }
    void printMuxNode(){
      cerr<<"Node: "<<_nodeID<<"Control: "<<_controlID<<", width: "<<_gateIDs.size() <<endl;
      for(int i = 0; i < _gateIDs.size(); ++i){
        cerr<<_gateIDs[i]<<"\t, "<<_fanin0IDs[i]<<"\t, "<<_fanin1IDs[i]<<endl;

      }
    }
  private:
    vector<int> _gateIDs;
    int _controlID;
    int _nodeID;
    vector<int> _fanin0IDs;
    vector<int> _fanin1IDs;
};
class meowMux{
  public:
    meowMux(Gia_Man_t* cir);
    ~meowMux();
    void runAll(bool forward);
    void recognizeMux();
    void addMux(int currentID, int controlID,
                int dataID0, int dataID1);
    void collectWords();
    void cleanNodes();
    muxNode* getFaninNode(muxNode* target, bool isFanin0);
    void splitWords(muxNode* currentNode);
    void splitForDG();
    void examForDG(muxNode* currentNode);


    void sortNodes(vector<int>& nodeOrder);
    void reportWords();
    void forwardCheck();
    void backwardCheck();
    int computeDepth(muxNode* currentNode);
    void reportCount();
    void reportDepth();
    void getBoundaryList(set<muxNode*> & outputList);
    muxNode* getNodebyIndex(int idx){
      return _nodeList[idx];
    }
    //void reportCountBackward();
  private:
    vector<muxNode*> _nodeList;
    set<muxNode*> _badwords;
    map<int, muxNode*> _control2Mux; // initial
    map<int, muxNode*> _mux2Node; // output gateID 2 node
    map<int, set<muxNode*> > _in2Nodes;
    Gia_Man_t* _cir;
    map<muxNode*, int> _node2Depth;
    set<int> _poList;
    set<int> _singleList; 
};

#endif
