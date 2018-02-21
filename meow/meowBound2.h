#ifndef MEOW_BOUND_2_H
#define MEOW_BOUND_2_H
#include<iostream>
#include<fstream>
#include <sstream>
#include<cstring>
#include<set>
#include<vector>
#include<map>
#include <stdlib.h>  
#include "ext/meow/meowNode.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "misc/extra/extra.h"
#include <algorithm> 

using namespace std;
typedef map<int, vector<int> > my_out2EqList; 

class meowBound2{
  public:
    meowBound2(Gia_Man_t* cir);
    ~meowBound2();
    void runAll(bool drop);
    void decideOrder();
    void updateControlSupport(int gateID, Gia_Obj_t* pObj);
    void computeSingleControl();
    void computeMultipleControl();
    void moveForward(meowNode* current);
    void collectFanouts(set<int>& oneStepFanouts, vector<int>& outIDs);
    bool isMiddleWord(meowNode* current); //output itself
    bool isInternalWord(meowNode* current, set<int>& internalBitss);
    bool isFanoutMiddleWord(meowNode* current); // all fanouts are...
    void findPossibleCombine(set<int>& oneStepFanouts, 
                             vector<int>& outIDs,
                             vector<meowNode*>& possibleCombine,
                             meowNode* current );

    bool newCombine(set<int>& controls);
    void analyzeNode1();
    void analyzeNode2();
    void updateGate2WordList(meowNode* node);
    void addGate2Node(bool dropAllSingle);
    void collectNodes();
    void removeBadSingle();
    void collectIn2Nodes( map<int, set<meowNode*>* >& in2Nodes);
    void reconnect();
    void splitbyFanins(meowNode* current);
    void splitbyFanouts(meowNode* current,
                        map<int, set<meowNode*>* >& in2Nodes);
 
    void sortByOutputs(vector<int>& orders);
    void sortByOutputs(set<meowNode*>& inNodes, vector<meowNode*>& orders);
    void enumerateControls(set<int>& controls);
    void findEquivalence(vector<int>& gateIDs, vector<bool>& phases,
              my_out2EqList& out2EqList);
 
    void removeBadEqBits( vector<vector<int> >& tempEqList, set<int>& deletePos, vector<int>& gateIDs);

    void assignControls(vector<int>& gateIDs, vector<bool>& phases);
    void assignSides(vector<int>& gateIDs, map<int, int>& new2oldID,
                     set<int>& fanouts);
    void assignFanouts( set<int>& fanouts, set<int>& currentFront,
                        map<int, int>& new2oldID,
                        vector<vector<int> >& tempEqList,
                        map<int, int>& gate2prev,
                        map<int, int>& tail2Pos);
    void assignForward(set<int>& currentFront,
                       map<int, int>& new2oldID,
                       vector<vector<int> >& tempEqList,
                       map<int, int>& gate2prev,
                       map<int, int>& tail2Pos,
                       int sideBound,
                       set<int>& deletePos);
    void analyzeWords(map<int, my_out2EqList >& assign2EqList,
                      map<int, vector<bool> >& assign2Phases,
                      vector<int>& gateIDs,
                      map<int, vector<int> >& out2Assign);

    void computeOut2Assign(map<int, vector<int> >& out2Assign, int assign, map<int, vector<int> >& out2EqList );

    void computeAssign2Words(map<int, vector<int> >& out2Assign,
                             map<string, vector<int> >& key2Group,
                             map<string, vector<int> >& key2Assign);

    int addAnd(int Lit0, int Lit1); 
    void printNodes();
    void printReport();
    void printReportNew();
    void printLevel(set<meowNode*>& inNodes);
    void printLevelNew();
    int collectLevelRecur(meowNode* current,
                          map<meowNode*, int>& node2Level);
    void printForward(set<meowNode*>& inNodes);
    void printForwardNew();
    void printForwardPart(set<meowNode*>& inNodes); 
    // output usage//
    void createSubCircuits(vector<Gia_Man_t*>& circuits, vector<vector<int>* >& cirFanins, vector<vector<int>* >& cirFanouts, set<int>& needIDs);
    void groupSubCircuits(set<int>& transBits, vector<vector<int>* >& groups);
    void groupSubCircuits2(set<int>& transBits, vector<vector<int>* >& groups, set<int>& needIDs, vector<set<int>* >& fanouts, vector<set<int>* >& fanins);
    void addFaninCone(int currentID, set<int>& transBits, set<int>& include, set<int>* fanins);
    void writeOutVerilog(char* pFileSpec);
    void checkNeedIDs(set<int>& needIDs, meowNode* node, set<int>& extraPOs);
    void writeTransModule(ofstream& output, meowNode* node, set<int>& extraPOs);
    void writeTransBitRecur(ofstream& output, int gateID, 
                            map<int, string>& id2Name);
    void writeSubModule(Gia_Man_t* circuit, ofstream& output, int index);
    void writeSubCircuits(char* fileHead);
    void createCG(); 
  private:
    Gia_Man_t* _cir;
    set<int> _poIDs;
    vector< pair<int, int> > _control_score; 
    map<int, set<int>* > _gate2ControlSupports; // gate to control
    map<int, vector<int>* > _control2Fanouts; // control to
   
    map<int, vector<meowNode*>* > _control2Nodes; 
    set<int> _middleBits;

    set<int> _provedBits; // all
    set<meowNode*> _badNodes;
    set<meowNode*> _muxNodes;
    set<meowNode*> _middleNodes;
    set<meowNode*> _fanoutMiddleNodes;
 
    set<meowNode*> _internalWords;
    vector<meowNode*> _nodeList;
    map<int, set<meowNode*>* > _gate2WordList; // construct by stage 1

    map<int, meowNode*> _gate2Node;
    set<meowNode*> _goodNodes;
//    map<int, set<meowNode*>* > _in2Nodes;
 //   set<meowNode*> _storeIn2Nodes;
    set<string> _usedKey;  
    set<int> _goodControl;
    int _currentID;
};
#endif
