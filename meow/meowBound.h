#ifndef MEOW_BOUND_H
#define MEOW_BOUND_H

#include<iostream>
#include<fstream>
#include <sstream>
#include<cstring>
#include<set>
#include<vector>
#include<map>
#include <stdlib.h>  
//#include"ext/meow/meowBlock.h"
#include "ext/meow/wordNode.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "misc/extra/extra.h"
#include <algorithm> 

using namespace std;
class wordGroup{
  public:
    wordGroup(int id){
      _groupID = id;
    }
    void addNode(wordNode* newNode){
      _nodes.push_back(newNode);
    }
  private:
    vector<wordNode*> _nodes;
    int _groupID;
};

class meowBound{
  public:
    meowBound(Gia_Man_t* cir);
    ~meowBound();
    void reportEquivalence(Gia_Man_t* cir);
    void findEquivalence(vector<int>& gateIDs, vector<bool>& phases,
                        vector<vector<int> >& eqList );
    void analyzeWords( vector<int>& gateIDs, vector<bool>& phases,
                       vector<vector<int> >& eqList );
    void updateHashTable(vector<int>& gateIDs, vector<bool>& phases,
                         map<int, vector<int> >& value2List);
    void updateHashTable2(vector<int>& gateIDs, vector<bool>& phases,
                         map<int, vector<int> >& value2List);
    void updateHashTable3(vector<int>& gateIDs, vector<bool>& phases,
                         vector<vector<int> >& eqList);
 //   void addSupportTable();
//    set<int>* getSupportSet(int gateID); 
    int addAnd(int Lit0, int Lit1); 
    void applyCofactor(vector<int>& gateIDs, vector<bool>& phases);
    void enumerateControl(set<int>* controls);
    //void enumerateControl2(set<int>& controls);
 //   void findConnectBlock(vector<int>& inIDs, vector<int>& outIDs, set<meowBlock*>& connectedBlocks);
 //   void findSupportBlock(vector<int>& inIDs, set<meowBlock*>& supportBlock);
 //   void findTargetBlock(vector<int>& outIDs, set<meowBlock*>& targetBlock);
    void runAll();
    void addNewWord( vector<int>& gateIDs, vector<bool>& phases, vector<int>& inIDs, vector<int>& outIDs, vector<int>& levels, vector<int>& transPos, vector<int>& provedBits, vector<vector<int> >& eqList);
  //  meowBlock* addNewBlock(vector<int>& gateIDs, vector<bool>& phases, vector<int>& inIDs, vector<int>& outIDs);
  //  void updateBlock(  vector<int>& gateIDs, vector<bool>& phases, vector<int>& inIDs, vector<int>& outIDs, set<meowBlock*>& connectedBlocks);
    bool isMiddleWord(wordNode* word); 
    void decideOrder();
    void computeEachBlock();
    void proceedBlock2();
    void moveForward(wordNode* frontWord);
    void collectFanouts(set<int>& fanouts, vector<int>& current);
    void findPossibleCombine(set<int>& fanouts, vector<int>& current,
                             vector<wordNode* >& possibleCombine,
                             wordNode* currentNode);
    bool newCombine(set<int>& controls);
    void enumerateCombine(wordNode* node1, wordNode* node2);

 //   void proceedBlock(); // don't do this

  //  void colorTargets();
  //  void proceedWords();
  //  bool checkControlSet(set<int>& usedKeys, vector<set<int>* >& usedLists, set<int>* newList, int gateID);
  //  bool checkSupportSet(int gateID);
    void splitWords(); // TODO: how to remove?
    void decideSplitOrders(vector<int>& orders); 
    void splitWord( wordNode* current);
    void splitGroups();
    void arrangeBoundaries(vector<vector<int> >& supports, vector<vector<int> >& targets);
  //  void updateTarget2Block(int gateID, meowBlock* block);
  //  void updateSupport2Block(int gateID, meowBlock* block);
  //  void printBound(bool printAllWords);
    void printWord(bool printAllWords);
    void collectTargetBoundary(vector< vector<int> >& outputWords );
    void collectSupportBoundary(vector< vector<int> >& supportWords );
    void printBoundaries(ostream& output);
    //void printSupportBoundary(ostream& output);
    void printJson(char* pFileSpec, bool printAll);
    void writeNetList(char* pFileSpec);
    void drawCircuit();
    void analyzeWords(); // TODO collapse MUX
    void simpleReport();
    void forwardReport();
    void backwardReport();
    void collectLevel2();
    void collectLevel2Recur(int currentID, map<int, int>& gate2Level);
    void collectLevel();
    void collectLevelRecur(wordNode* current,
                           map<int, int>& gate2Level, set<wordNode*> & visitedWords);
  private:
    Gia_Man_t* _cir;
   // vector<bool> _phases;
    int _currentID;
   
    map<int, set<wordNode*>* > _gate2WordList; // gate on outputs
    map<int, wordNode*> _out2WideWord;
    map<int, wordGroup*> _id2Group;
    map<int, set<wordNode*>* > _in2WordList;
    map<int, vector<int>* > _control2Fanouts; 
   // set<set<int>* > _pureWords;
    map<int, set<int>* > _gate2Supports; // signals in faninCone 
   // map<int, wordNode*> _control2Word; // first run
    vector< pair<int, int> > _control_bigOut; 
    vector<wordNode*> _foundWords;
    vector<wordGroup*> _foundGroups;
    set<wordNode*> _badNodes; // splited 
    set<int> _middleBits;
    set<string> _usedKey;
 //   set<set<int> > _usedCombine; // TODO clean

  //  vector<wordNode*> _oneLevelWords;
    set<wordNode*> _middleWords;
  //  set<int> _badNodes;
    set<int> _goodControls;
    set<int> _transBits;
    set<int> _provedBits;
    set<int> _poIDs;
    set<wordNode*> _muxWords;
    int _counter;
};
#endif
