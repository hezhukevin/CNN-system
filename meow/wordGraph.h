#ifndef WORD_GRAPH_H
#define WORD_GRAPH_H
#include<iostream>
#include<set>
#include<vector>
#include<map>
#include"ext/meow/wordNode.h"
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "misc/extra/extra.h"
#include "proof/dch/dch.h"
using namespace std;
class wordGraph{
  public:
    wordGraph(Gia_Man_t* cir);
    ~wordGraph();
    bool addNewNode(vector<int>& inID, vector<int>& outID,vector<int>& IDs, vector<int>& values );
    void printNodes();

    void walkOneStep(); // V from front-tier to its' one distance fanout
    void getOneNode(int ID); //V get support of node ID

    void  findCandidate(); //V after walkOneStep => analyze target to get 

    void proveWord( vector<int>& wordCandidate ); // V after find candidate
    // get one good point to find assignemtn , call proveOneNode 
    void proveOneNode(int ID, vector<int>& lowID, vector<int>& highID); //use QBF to find assignmenr
  // separate to parameters and variables
  //
    int recurCopy(Gia_Man_t* pNew, int ID); // V 
    void apply( vector<int>& IDs, vector<int>& values, bool negate); // given one assignment, find all equivalent bits under this condition    
    bool isProved(int ID);
    bool stopOneRound();    
    bool checkOverlap(int ID);
    bool checkTerminate(); // check mix ofwords
    bool checkRepeat(vector<int>& inID, vector<int>& outID); 
    void cleanTarget(vector<int>& IDs);
    bool checkGroup(vector<int>& inID);
    void printSupport(); // for debug!
    void printTarget();

    void callQbf(vector<int>& lowID, vector<int>& highID, int ID, bool negate ); 
  private:
    int _callQBF;
    vector<wordNode*> _totalList;
    map<int, set<int>* > _supportMap; //id => support
    map<int, set<int>* > _targetMap; // id => target
//    map<int, set<int>* > _transMap; // internal to PI
    int* _loadNum; // target.size
    int* _provedData; // only PI
    Gia_Man_t* _cir;
    set<int> _currentFront;     
    int _objNum;
    int _piNum;
    int _wordGroup;
    bool _getNew;
};
#endif
