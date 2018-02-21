#ifndef MEOW_TRANS_H
#define MEOW_TRANS_H
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
#include "ext/meow/transWord.h"
#include "ext/meow/depGraph.h"

using namespace std;
class meowTrans{
  public:
    /* basic fuctions....shared functions*/
    meowTrans(Gia_Man_t* cir, bool forward, bool depth);

    void computeAll();
    void collectPOs();
    void decideOrder();

    void getCopyNSuppMap(vector<int> & gateIDs,
                               int currentControl, 
                               Gia_Man_t* pNew);
    /*forward */
   void collectSuppForward(vector<int>& fanouts, int control, set<int>& supps, Gia_Man_t* pNew);
   void collectTargetForward(set<int>& supps, vector<int>& fanouts, set<int>& newPOs);
   void collectTargetForwardRecur(set<int>& supps, set<int>& newPOs, int currentID);
   void computeForward(); 
   void finalizeForward();
   void proceedWords(); 
   void finalizeForward2(); // no use?
   void targetBoundary(vector<int>& gateIDs);  
    /* backward*/
    Gia_Man_t* getBackwardCircuit(set<int>& fanoutList);
    void computeBackward(); 
    void finalizeBackward();
    void collectBackwardPORecur(set<int>& poList, int currentID);
    void buildBackSuppMap(set<int>& targetPOs, set<int> & poList);
    int recurCopyN(Gia_Man_t* pNew, int currentID, int poID);
    bool fanoutProved(int gateID);
    bool faninProved(int gateID, int* supp, int suppNum);
   /* output functions*/
    void recurSupp(int currentID, int currentControl);
    bool checkSupp(int currentID); 
    void computeIso(Gia_Man_t* cir_copy);
   // void computeIsoBackward(Gia_Man_t* isoCir, set<int>& piList);
    void splitWords(vector<int>& outputs, int* suppMap, int suppNum,
                    vector<vector<int> >& splitWordVec );
    void classifySupports(vector<int>& outputs, int* suppMap,
                          int suppNum,
                          vector<transWord*> & wordCandidates); //consider intermediate word
    bool verifyWord(transWord* testWord); 
    bool findAssignment(int wordIndex, transWord* testWord, Gia_Man_t* cir_copy, vector<int>& controls); 
    void updateSuppBound(transWord* newWord);
    void computeTargetPOs(vector<int> & gateIDs); 
    void computeTargetPOsRecur(set<int> & newPOs, int cirGateID);
//////////////////////////////////////////////////////
    Gia_Man_t* buildTestCircuit(vector<int>& controls,
                                vector<int>& inputWord,
                                vector<int>& outputWord,
                                bool negate);
    //Gia_Man_t* buildTestCircuit2(vector<>)
    bool propagateAssignment(transWord* testWord); 
    int copyRecur(Gia_Man_t* pNew, Gia_Obj_t* pObj);
//////////////////////////////////////
    void getOutputsRecur(set<int>& outputs, int currentID);
    void noFanoutWords(vector<transWord*>& sinkWords );
    void computePO();
    void computeDepth();
    void computeDepthBackward();
    int countToBack(int currentId, int target);
    int countTo(int currentId,int target); 
    bool addProvedWord(vector<int> & outputs);
  //  void reduceProvedPi(vector<int>& outputs);
   // for control dependency
    void buildDepGraph();
  
    void connectDependency(vector<int> & gateList);
    void connectDependencyRecur(set<int> & visited, int currentID, int sourceID);
    void writeGraphDot();
    void writeCirDot();
    void writeAIGDot(Gia_Man_t* targetCir);
    void writeIsolateAIG();
    void labelIsolateAIG( set<int>& piList, set<int>& poList);
    void labelIsolateRecur(set<int>& piList,int currentID);
    ~meowTrans();
    void printResult();
  private:
    Gia_Man_t* _cir;
    ///// keep updating for each run////
    map<int, set<int> > _po_supp_map;
    vector<int> _copyPo_gateID;
    set<int> _piList;
    /////////////////////
    depGraph* _depGraph;
    vector< pair<int, int> > _control_bigOut; // (fanoutID, control) 
    ///////////////////
    vector<transWord*> _provedWords;
    set<transWord*> _successBack;
    set<int> _backTargetBound;
    set<int> _backSuppBound;
    set<int> _backSuppBits;
    set<int> _successBackBits;
    int* _gate2WordID; // cirGate ->wordID
    set<int> _usedControl;
    int _currentControl;
    char* _lastphase;
    int _minWordSize; 
    bool _newRun;
    // TODO add "TODO control!"
    bool _forward; // true for forward
    bool _getDepth;
    set<int> _candidateBits; // immediate fanout for controls
    set<int> _provedWordBits; // used for compute sub-circuits
    set<int> _badBits;
     
    set<int> _newProvedBits;
    set<int> _reducedPi;
    set<int> _poList;
    map<int, int> _wordId2depth;
    vector<transWord*> _newAddWords;
    set<int> _checkedProceedBits;
    int _poWordNum;
    //vector<transWord*> _newProvedWords;
};
#endif
