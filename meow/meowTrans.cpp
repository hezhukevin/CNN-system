#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "proof/fraig/fraig.h"
#include "opt/fxu/fxu.h"
#include "opt/cut/cut.h"
#include "map/fpga/fpga.h"
#include "map/if/if.h"
#include "opt/sim/sim.h"
#include "opt/res/res.h"
#include "opt/lpk/lpk.h"
#include "aig/gia/giaAig.h"
#include "opt/dar/dar.h"
#include "opt/mfs/mfs.h"
#include "proof/fra/fra.h"
#include "aig/saig/saig.h"
#include "proof/int/int.h"
#include "proof/dch/dch.h"
#include "proof/ssw/ssw.h"
#include "opt/cgt/cgt.h"
#include "bool/kit/kit.h"
#include "map/amap/amap.h"
#include "opt/ret/retInt.h"
#include "sat/cnf/cnf.h"
#include "proof/cec/cec.h"
#include "proof/pdr/pdr.h"
#include "misc/tim/tim.h"
#include "bdd/llb/llb.h"
#include "bdd/bbr/bbr.h"
#include "map/cov/cov.h"
#include "base/cmd/cmd.h"
#include "proof/abs/abs.h"
#include "sat/bmc/bmc.h"
#include "proof/ssc/ssc.h"
#include "opt/sfm/sfm.h"
#include "bool/rpo/rpo.h"
#include "map/mpm/mpm.h"
#include "aig/gia/gia.h"
#include "ext/meow/meowTrans.h"
#include<iostream>
#include<fstream>
#include <algorithm> 
using namespace std;
extern "C" int Gia_QbfSolve( Gia_Man_t * pGia, int nPars, int nIterLimit, int nConfLimit, int nTimeOut, int fVerbose, int*  outValue );
extern "C" Gia_Man_t * Gia_ManIsoNpnReduceMeow( Gia_Man_t * p, Vec_Ptr_t ** pvPosEquivs, int* po2Phase, int* po2Num, int* po2Supp, int fVerbose );

ABC_NAMESPACE_IMPL_START
void meowUsageTrans(){
  Abc_Print( -2, "usage: meowTrans [-bdowh] \n" );
  Abc_Print( -2, "\t compute transparent logic of the current Gia. \n");
  Abc_Print( -2, "\t   default is forward transparency. \n");
  Abc_Print( -2, "\t -b : toggle computing backward transparency\n");
  Abc_Print( -2, "\t -d: toggle report depths of proved words.\n ");
  Abc_Print( -2, "\t -o: toggle compute transparency from PI to PO, no internal words. \n");
  Abc_Print( -2, "\t -w: toggle to print Proved words and some results\n");
  Abc_Print( -2, "\t-h    : print the command usage\n");

}

meowTrans::meowTrans(Gia_Man_t* cir, bool forward,bool depth){
  _cir = cir;
  _depGraph = NULL;
  _poWordNum = 0;
  _forward = forward;
  _getDepth = depth;
  _gate2WordID = new int[Gia_ManObjNum(_cir)];
  _lastphase = new char[Gia_ManObjNum(_cir)];

  for(int i = 0; i < Gia_ManObjNum(_cir); ++i){
    _gate2WordID[i] = -1; 
    _lastphase[i] = '0';
  }// map from gate in _cir to words in _provedWords
  Gia_ManStaticFanoutStart(_cir);
  _candidateBits.clear();
  _provedWordBits.clear();
  _usedControl.clear();
  _piList.clear();
  _badBits.clear();
}

meowTrans::~meowTrans(){
  Gia_ManStaticFanoutStop(_cir);
  delete[] _gate2WordID;
  delete[] _lastphase;
  _cir = NULL;
  if(_depGraph)
    delete _depGraph;
  for(int i = 0; i < _provedWords.size(); ++i)
    delete _provedWords[i];
}
int meowTrans::recurCopyN(Gia_Man_t* pNew, int currentID, int poID){
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);
  if(~(pObj->Value))
    return pObj->Value;
  if(Gia_ObjIsAnd(pObj)){
    int id1 = Gia_ObjFaninId0( pObj, currentID);
    int id2 = Gia_ObjFaninId1( pObj, currentID);
    recurCopyN(pNew, id1, poID);
    recurCopyN(pNew, id2, poID);
    int newLit = Gia_ManHashAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
    pObj->Value = newLit;
  }
  else{
    int id1 = Gia_ObjFaninId0( pObj, currentID);
    recurCopyN(pNew, id1, poID);

    int newLit =  Gia_ObjFanin0Copy(pObj);
    pObj->Value = newLit;
  }
  return pObj->Value;
}
void meowTrans::getCopyNSuppMap(vector<int> & gateIDs, int currentControl, Gia_Man_t* pNew ){
  // this function update _po_supp_map & _copyPo_gateID and construct a gia
  //_copyPo_gateID.clear() //TODO;
  //cerr<<"new!"<<endl;
  _copyPo_gateID.clear();
 // _po_supp_map.clear(); // update 
//  Gia_Man_t *pTemp;
//  Gia_Obj_t * pObj;
//  int i;
  set<int> tempBad;
  for (int i = 0; i < gateIDs.size(); ++i){
    recurSupp(gateIDs[i], currentControl); 
    if( checkSupp(gateIDs[i])){
      _copyPo_gateID.push_back(gateIDs[i]);
      int outLit = recurCopyN(pNew, gateIDs[i], gateIDs[i]);
      Gia_ManAppendCo(pNew, outLit);
    }
  }
}
bool meowTrans::checkSupp(int currentID){
  set<int> suppSet = _po_supp_map[currentID];
  set<int> used;
  set<int>::iterator site = suppSet.begin();
  //cerr<<"Have "<<currentID<<endl;
  //bool badList = false;
  for(; site != suppSet.end(); ++site){
   // cerr<<"\t"<<(*site);
    if(_gate2WordID[*site] != -1){
      if(used.find(_gate2WordID[*site]) != used.end()){
       // _badBits.insert(currentID);
        return false;

      }
      used.insert(_gate2WordID[*site]);
    }
 //   if(_badBits.find(*site) != _badBits.end()){
   //   cerr<<"Got"<<*site<<endl;
    //  badList = true;
 //     _badBits.insert(currentID);
  //  }
  }
  return true;
}
void meowTrans::recurSupp(int currentID, int currentControl){
  if(_po_supp_map.find(currentID) != _po_supp_map.end())
    return;
//  cerr<<currentID<<endl;
//  if(currentID == currentControl)
  set<int> newSupp;
  newSupp = set<int>();
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);
  /*if(_badBits.find(currentID) != _badBits.end()){
    newSupp.insert(currentID);
  }*/
  if(currentID == 0){
    newSupp.insert(0);
  }
  else if(currentID == currentControl){
    newSupp.insert(currentID);
  }
  else if(_usedControl.find(currentID) != _usedControl.end())
    newSupp.insert(currentID);
  else if(_gate2WordID[currentID] != -1 ||Gia_ObjIsPi(_cir, pObj) ){ // is a word Bit!
    newSupp.insert(currentID);
  }
  else if(Gia_ObjIsPi(_cir, pObj)){
    newSupp.insert(currentID);
  }
  else{
    if(Gia_ObjIsAnd(pObj)){
      int id1 = Gia_ObjFaninId0( pObj, currentID);
      int id2 = Gia_ObjFaninId1( pObj, currentID);
      recurSupp(id1, currentControl);
      recurSupp(id2, currentControl);
      set<int> supp1 = _po_supp_map[id1];
      set<int> supp2 = _po_supp_map[id2];
      newSupp.insert(supp1.begin(), supp1.end());
      newSupp.insert(supp2.begin(), supp2.end());
    }
    else{
      int id1 = Gia_ObjFaninId0( pObj, currentID);
      recurSupp( id1, currentControl);
      set<int> supp1 = _po_supp_map[id1];
      newSupp.insert(supp1.begin(), supp1.end());
    }
  }
  _po_supp_map.insert(make_pair(currentID,newSupp));
}
void meowTrans::computeTargetPOsRecur(set<int> & newPOs, int cirGateID){
  if(newPOs.find(cirGateID)!= newPOs.end())// visited before
    return;
  if(_candidateBits.find(cirGateID)!= _candidateBits.end())// driven by control!
    return;
  newPOs.insert(cirGateID); 
  int j;
  Gia_Obj_t* pObj = Gia_ManObj(_cir, cirGateID);

  Gia_Obj_t* pFanout;
  Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
    computeTargetPOsRecur(newPOs, Gia_ObjId(_cir, pFanout));
  }

}
void meowTrans::computeTargetPOs(vector<int> & gateIDs){
  // TODO
  // add all function we want to check into gateIDs
  // the control id should be from depGraph 
  // where are we?
 //TODO use set, and assign
  int j;
  Gia_Obj_t* pObj;
  Gia_Obj_t* pFanout;
  set<int> newPOs; 
  if(_newRun){
    vector<int> newSignals;
    _depGraph->getNewSignals(newSignals); // they have multiple fanouts...
    for(int i = 0; i < newSignals.size(); ++i){
      pObj = Gia_ManObj(_cir, newSignals[i]);
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
        newPOs.insert(Gia_ObjId(_cir, pFanout));
      }
    }
    _newRun = false;
  }
  else{ // from current output walk forward until candidate bits
    set<int>::iterator site = _newProvedBits.begin();
    for(; site!= _newProvedBits.end(); ++site)
      computeTargetPOsRecur(newPOs, (*site));
    _newRun = true;
  }
  _newProvedBits.clear();
  gateIDs.assign(newPOs.begin(), newPOs.end());
}
void meowTrans::computeIso(Gia_Man_t* cir_copy){
  Gia_Man_t * pAig;
  Vec_Ptr_t * vPosEquivs;
 // Vec_Ptr_t * vPosEquivs2;
  Vec_Ptr_t * vPiPerms;
 // Gia_Man_t* pAig2;
  int poNum = Gia_ManPoNum(cir_copy);
  int* po2Phase = new int[poNum];
  int* po2Num = new int[poNum];
  int* po2Supp = new int[poNum*16];
//  Gia_Man_t* copy2 = Gia_ManDup(cir_copy);  
 // Gia_ManPrint(cir_copy);
  pAig = Gia_ManIsoReduce( cir_copy, &vPosEquivs, &vPiPerms, 0, 0, 0, 0 );
  Gia_ManStop(pAig);

/*  Gia_ManIsoNpnReduceMeow(copy2, &vPosEquivs2, po2Phase,
                                  po2Num, po2Supp,0); 
  Gia_ManStop(copy2);
/////TEST NpnReduceMeow
  int groupNum = Vec_PtrSize(vPosEquivs2);
  for(int k = 0; k < groupNum; ++ set<int> suppIDs = _po_supp_map[_copyPo_gateID[poGate]];
    vector<int> IDs;
    IDs.assign(suppIDs.begin(), suppIDs.end());

k){
    Vec_Int_t* eqMember = (Vec_Int_t*)Vec_PtrArray(vPosEquivs2)[k];
    int poGate, j;
    Vec_IntForEachEntry(eqMember, poGate, j){
      set<int> suppIDs = _po_supp_map[_copyPo_gateID[poGate]];
      vector<int> IDs;
      IDs.assign(suppIDs.begin(), suppIDs.end());


      cerr<<"GateID"<<_copyPo_gateID[poGate]<<" ";
      cerr<<"po2Phase:"<<po2Phase[poGate]<<endl;
      cerr<<"po2Num:"<<po2Num[poGate]<<endl;
      for(int m = 0; m < po2Num[poGate]; ++m)
        cerr<<IDs[po2Supp[poGate*16+m]]<<" ";
      cerr<<endl;
    }
    cerr<<endl;
  }
/////
  return;*/
  int totalIso = 0; 
  int equivNum = Vec_PtrSize(vPosEquivs);
  bool realRun = false;
  for (int i = equivNum -1; i >= 0; --i){ // for each group
    realRun = false;
    // TODO: order?
    Vec_Int_t* groupMember = (Vec_Int_t*)Vec_PtrArray(vPosEquivs)[i];
    int poGate, j;
    map<int, vector<int> > gate2supps;
    vector<int> outputs;
    int suppNum = 0;
    int poNum = Vec_IntSize(groupMember);
    if (poNum < 4) 
      continue;
    int* suppMap = NULL;
    totalIso+= poNum;
    outputs.clear();
//    cerr<<endl;
    Vec_IntForEachEntry(groupMember, poGate, j){
    //  cerr<<_copyPo_gateID[poGate]<<" ";
      outputs.push_back(_copyPo_gateID[poGate]);
      if(!fanoutProved(_copyPo_gateID[poGate]))
        realRun = true; 
      Vec_Int_t* vSupps =(Vec_Int_t*)Vec_PtrArray(vPiPerms)[poGate];
      
      if(j == 0){
        suppNum = Vec_IntSize(vSupps);
        suppMap = new int[poNum*suppNum];
      }
  //    cerr<<"size"<<Vec_IntSize(vSupps)<<endl;
      set<int> suppIDs = _po_supp_map[_copyPo_gateID[poGate]];
      vector<int> IDs;
      IDs.assign(suppIDs.begin(), suppIDs.end());
      int k, mappedID;
      //for(int x = 0; x < IDs.size(); ++x)
      //  cerr<<"\t"<<IDs[x];
      //cerr<<endl; 
      Vec_IntForEachEntry( vSupps, mappedID, k ){
       // cerr<<"Hello:"<<mappedID<<endl;
     
        if(mappedID >= IDs.size()){
     //     for(int x = 0; x < IDs.size(); ++x)
      //      cerr<<"\t"<<IDs[x];
      //    cerr<<"ERROR!!"<<mappedID<<endl;
          continue;
        }
        suppMap[j*suppNum+k] = IDs[mappedID];
      }
    }
//    cerr<<endl;
   /* if(!realRun){
      //if(faninProved(outputs[0], suppMap, suppNum)){
        _provedWordBits.insert(outputs.begin(), outputs.end());
        _backSuppBits.insert(outputs.begin(), outputs.end());
     //   cerr<<"add:";
     //   for(int x = 0; x < outputs.size(); ++x)
     //     cerr<<" "<<outputs[x];
     //   cerr<<endl;
      //}
      //cerr<<"skip"<<endl;
      continue;

    }*/
    vector<transWord*> candidateWords;
    classifySupports(outputs, suppMap, suppNum, candidateWords);
    for(int m = 0; m < candidateWords.size(); ++m){
       //candidateWords[m]->printTransWord();

      if(verifyWord(candidateWords[m])){
        //candidateWords[m]->printTransWord();

        candidateWords[m]->setWordID(_provedWords.size());
        vector<int> tempControl;
        candidateWords[m]->getNonInheritControls(tempControl);
        _usedControl.insert(tempControl.begin(), tempControl.end());
 
        //_provedWords.push_back(candidateWords[m]);
        vector<int> oneOutputWord;
        candidateWords[m]->getOutputWordIds(oneOutputWord);
        if(fanoutProved(oneOutputWord[0]) && faninProved(oneOutputWord[0], suppMap, suppNum ))
          _backSuppBits.insert(oneOutputWord.begin(), oneOutputWord.end()); 
        if(addProvedWord(oneOutputWord)){
          _provedWords.push_back(candidateWords[m]);
          _newAddWords.push_back(candidateWords[m]);
          if(!_forward)
            updateSuppBound(candidateWords[m]);

        }
        else
          delete candidateWords[m];
      }
      else
        delete candidateWords[m];
    }

  } // for each group
  Vec_VecFree( (Vec_Vec_t *)vPiPerms );
  Vec_VecFree( (Vec_Vec_t *)vPosEquivs ); 
 // Vec_VecFree( (Vec_Vec_t *)vPosEquivs2);
  delete[] po2Phase;
  delete[] po2Num;
  delete[] po2Supp;
}
bool meowTrans::addProvedWord(vector<int> & outputs){
  bool hasNew = false;
  for(int i = 0; i < outputs.size(); ++i){
    if(_provedWordBits.find(outputs[i]) == _provedWordBits.end())
      hasNew = true;
  }
  if (!hasNew)
    return hasNew;
  for(int i = 0; i < outputs.size(); ++i){
       _provedWordBits.insert(outputs[i]);
      _reducedPi.insert(outputs[i]);
    //_newProvedBits.insert(outputs[i]);
     if(_gate2WordID[outputs[i]] == -1)
       _gate2WordID[outputs[i]] = _provedWords.size();
    // else if (!Gia_ObjIsPi(_cir, Gia_ManObj(_cir, outputs[i])))
    //   cerr<<"What?"<<endl;
    
  }
  return hasNew;
}
int meowTrans::copyRecur(Gia_Man_t* pNew, Gia_Obj_t* pObj){
  if ( ~pObj->Value )
    return pObj->Value;
  //  assert( Gia_ObjIsAnd(pObj) );
  if(Gia_ObjIsAnd(pObj)){
    copyRecur( pNew, Gia_ObjFanin0(pObj) );
    copyRecur( pNew, Gia_ObjFanin1(pObj) );
    return pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
  }
  else{
    copyRecur(pNew, Gia_ObjFanin0(pObj));
    int newLit = Gia_ObjFanin0Copy(pObj);
    return pObj->Value = newLit;
  }

}
Gia_Man_t* meowTrans::buildTestCircuit(vector<int>& controls, 
                            vector<int>& inputWord,vector<int>& outputWord,
                            bool negate){
/*  cerr<<"Build!"<<endl;
  for(int i = 0; i < controls.size(); ++i)
    cerr<<"\t"<<controls[i];
  cerr<<endl;
*/
  Gia_Man_t* pNew, *pTemp ;
  Gia_Obj_t* pObj;
  pNew = Gia_ManStart(Gia_ManObjNum(_cir));
  Gia_ManHashAlloc(pNew);
  Gia_ManFillValue(_cir);
  Gia_ManConst0(_cir)->Value = 0;
  for(unsigned i = 0; i < controls.size(); ++i){ // add parameter
    pObj = Gia_ManObj( _cir, controls[i] );
 //   if(~pObj->Vfalse;)
 //     continue;
    pObj->Value = Gia_ManAppendCi(pNew); 
  }
  int j;
  Gia_ManForEachPi(_cir, pObj, j){
    if(~pObj->Value)
      continue;
    pObj->Value = Gia_ManAppendCi(pNew);
  }
  set<int> tempCollect;
  tempCollect.clear();
/*  if(!_forward){
    tempCollect.insert(_provedWordBits.begin(), _provedWordBits.end());
    tempCollect.insert(_piList.begin(), _piList.end());
    for(set<int>::iterator site2 = _reducedPi.begin(); site2 != _reducedPi.end(); ++site2){
      if(tempCollect.find(*site2)!= tempCollect.end()) 
       tempCollect.erase(*site2);
    }
  }*/
  if(!_forward){
    tempCollect.insert(_piList.begin(), _piList.end());
    tempCollect.insert(_backSuppBound.begin(), _backSuppBound.end());
    for(int k = 0; k < outputWord.size(); ++k){
      if(tempCollect.find(outputWord[k]) != tempCollect.end())
        tempCollect.erase(outputWord[k]);
    }
    // but remove "outputWord
  }
  tempCollect.insert(_usedControl.begin(), _usedControl.end());
  //cerr<<endl;
  set<int>::iterator site = tempCollect.begin();
  for(; site != tempCollect.end(); ++site){
   // cerr<<*site<<"\t";
    pObj = Gia_ManObj(_cir, (*site));
    if(~pObj->Value)
      continue;
    pObj->Value = Gia_ManAppendCi(pNew);
  }
 
  int andLit = 0;
  for(unsigned i = 0; i < outputWord.size(); ++i){
    pObj = Gia_ManObj(_cir, outputWord[i]);
    // 
    int outLit = copyRecur(pNew, pObj);
    int inLit = copyRecur(pNew, Gia_ManObj(_cir, inputWord[i])); 
    int xorLit;
    if(negate)
      xorLit = Gia_ManHashXor(pNew, outLit, inLit); 
    else
      xorLit = Gia_ManHashXor(pNew, Abc_LitNot(outLit), inLit);
    if (i == 0)
      andLit = xorLit;
    else
      andLit = Gia_ManHashAnd(pNew, andLit, xorLit);
  }
  // take existing assignment!
  int inputWordID = _gate2WordID[inputWord[0]];
  if(inputWordID != -1){
    transWord* inputWord = _provedWords[inputWordID];
    vector<int> partControl;
    vector<char> partAssign;
    inputWord->getNonInheritAssignment(partControl, partAssign);
    for(unsigned i = 0; i < partControl.size(); ++i){
      int xorLit;
      int controlLit = Gia_ManObj(_cir, partControl[i])->Value; 
      if(partAssign[i] == '1'){
        xorLit = Gia_ManHashXor(pNew, controlLit, 1 );
        andLit = Gia_ManHashAnd(pNew, andLit, Abc_LitNot(xorLit));
      }
      else if(partAssign[i] == '0'){
        xorLit = Gia_ManHashXor(pNew, controlLit, 0 );
        andLit = Gia_ManHashAnd(pNew, andLit, Abc_LitNot(xorLit));
      } 
    }
  }
  Gia_ManAppendCo(pNew, andLit);
  pNew = Gia_ManCleanup( pTemp = pNew );
  Gia_ManStop( pTemp );
  return pNew;
  // then take assignment!

}
bool meowTrans::findAssignment(int wordIndex, transWord* testWord, Gia_Man_t* cir_copy, vector<int>& controls){
 // call QBF function
  if(cir_copy == NULL)
    return false;
  int* outValue = new int[controls.size()]; 
  int result = Gia_QbfSolve(cir_copy, controls.size(), 0, 0, 0, 0,outValue );
  if(result == 0){
    testWord->putAssignment(controls, wordIndex, outValue); 
   // add value
    delete[] outValue;
    return true;
  }
  delete[] outValue;
  return false;
}
bool meowTrans::verifyWord(transWord* testWord){
  int inputWordNum = testWord->getInputWordNum();
  vector<int> outputIDs;
  testWord->getOutputWordIds(outputIDs);
  // 
  vector<int> nonInheritControls;
  testWord->getNonInheritControls(nonInheritControls);
/*  if(nonInheritControls.size() == 0) // no extra control introduced
    if(propagateAssignment(testWord))
      return true;
  nothing happen here
*/
  bool totalGot = false;
  for(int i = 0; i < inputWordNum; ++i){
    vector<int> inputIDs;
    testWord->getInputWordByIndex(i, inputIDs);

    vector<int> controls;
    vector<int> highControls;
    vector<char> assignments;
    bool got = false;
    Gia_Obj_t* testPI = Gia_ManObj(_cir, inputIDs[0]);
    if (Gia_ObjIsPi( _cir, testPI ) || _piList.find(inputIDs[0]) != _piList.end()){
      testWord->getNonInheritControls(controls);
      //for(unsigned j = 0 ; j < controls.size(); ++j)
      //  assignments.push_back('X');
      bool sign;
      if(controls.size() > 0) 
        sign = _lastphase[controls[0]] == '1'? true: false;
      else
        sign = false;
      Gia_Man_t* testCir = buildTestCircuit(
                           controls, inputIDs, outputIDs, sign );
      // call QBF solve
      got = findAssignment(i, testWord, testCir, controls);
      if(controls.size() > 0) 
        _lastphase[controls[0]] = sign? '0':'1';
      if(testCir)
        Gia_ManStop(testCir);
  
      if(!got){
        Gia_Man_t* testCir2 = buildTestCircuit(
                           controls, inputIDs, outputIDs, !sign );
        got = findAssignment(i, testWord, testCir2, controls);
        if(testCir2)
          Gia_ManStop(testCir2);
        if(controls.size() > 0) 
          _lastphase[controls[0]] = sign? '1':'0'; 

      }
      if(!got && !_forward){ //try all control!!
       int controlNum = controls.size();
         controls.clear();
       
        testWord->getAllControls(controls);
        if(controlNum == controls.size())
          return false;

        Gia_Man_t* testCir3 = buildTestCircuit(controls, inputIDs, outputIDs, false );
        got = findAssignment(i, testWord, testCir3, controls);
        if(testCir3) 
          Gia_ManStop(testCir3);

 
       if(!got){
          Gia_Man_t* testCir4 =  buildTestCircuit(
                           controls, inputIDs, outputIDs, true );
   
          got = findAssignment(i, testWord, testCir4, controls);
          if(testCir4) 
            Gia_ManStop(testCir4);
        }
      }
      if(got){
        _backSuppBits.insert(inputIDs.begin(), inputIDs.end());
      } 
      if(got && addProvedWord(inputIDs)){ // add inputWord
        transWord* newPiWord = new transWord(inputIDs.size(), 0, 0);
                vector<int> tempControl;
        newPiWord->setWordNSupp(inputIDs, tempControl, NULL);
        //newPiWord->printTransWord();

        newPiWord->setWordID(_provedWords.size());
        _provedWords.push_back(newPiWord);
        
        testWord->addFaninWord(newPiWord); 
      }
    }
    else if(_gate2WordID[inputIDs[0]] == -1){
      /*cerr<<"what?"<<endl;
      if(_usedControl.find(inputIDs[0])!= _usedControl.end())
        cerr<<"this is a control!"<<endl;*/
      return false;
    }
    else{ 
      
      transWord* inputWord = _provedWords[_gate2WordID[inputIDs[0]]];
      // check non_inherent control ?
    //  cerr<<inputIDs[0]<<" "<<_gate2WordID[inputIDs[0]]<<endl;
     // inputWord->printTransWord();
     // set<int> partialControls; // non-inherit and input
      vector<int> currentControl;
      testWord->getNonInheritControls(currentControl); // decide order
      vector<int> inputWordControl;
      inputWord->getNonInheritControls(inputWordControl);
      set<int> controlSet;
      controlSet.insert(currentControl.begin(), currentControl.end());
      controlSet.insert(inputWordControl.begin(), inputWordControl.end());
      controls.assign(controlSet.begin(), controlSet.end());
    //  for(int x = 0; x < inputWordControl.size(); ++x)
     //   controls.push_back(inputWordControl[x]); 
      Gia_Man_t* testCir = buildTestCircuit(controls, inputIDs, outputIDs, false );
      // call QBF solv
      got = findAssignment(i, testWord, testCir, controls);
      if(testCir) 
        Gia_ManStop(testCir);

      if(!got){
        Gia_Man_t* testCir2 = buildTestCircuit(
                           controls, inputIDs, outputIDs, true );
        got = findAssignment(i, testWord, testCir2, controls);
        if(testCir2)
          Gia_ManStop(testCir2);

      }
      if(!got){ //try all control!!
        controls.clear();
        testWord->getAllControls(controls);
        Gia_Man_t* testCir3 = buildTestCircuit(controls, inputIDs, outputIDs, false );

        got = findAssignment(i, testWord, testCir3, controls);
        if(testCir3) 
          Gia_ManStop(testCir3);
 
        if(!got){
          Gia_Man_t* testCir4 =  buildTestCircuit(
                           controls, inputIDs, outputIDs, true );
   
          got = findAssignment(i, testWord, testCir4, controls);
          if(testCir4) 
            Gia_ManStop(testCir4);
        }
      } 
    }
    if(!totalGot)
      totalGot = got;
    if(!got)
      return false;
  }
  if(!totalGot)
    return false;
  //testWord->printTransWord();
  return true;
}
void meowTrans::decideOrder(){
  // sort all high-fanout signals by their immediate POs. 
  int i, j;
  Gia_Obj_t* pObj;
  Gia_Obj_t* pFanout;
  Gia_ManForEachObj1(_cir, pObj, i){
    if(Gia_ObjFanoutNum(_cir, pObj) > 3){
      int gateID = Gia_ObjId(_cir, pObj);
      int bigOne = 0;
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
        // check all fanouts!
        int fanoutID = Gia_ObjId(_cir, pFanout);
        if(fanoutID > bigOne)
          bigOne = fanoutID;
      }
      _control_bigOut.push_back(pair<int, int>(bigOne, gateID));
    }
  }
  sort(_control_bigOut.begin(), _control_bigOut.end());
}
void meowTrans::buildDepGraph(){
  int i, j;
  Gia_Obj_t* pObj;
  Gia_Obj_t* pFanout;
  Gia_Obj_t* pOld;
  vector<int> gateList;
  Gia_ManCleanValue(_cir); // set to 0
  Gia_ManForEachObj1( _cir, pObj, i ){
    if(Gia_ObjFanoutNum( _cir, pObj ) > 2){
      int gateID = Gia_ObjId(_cir, pObj);
      gateList.push_back(gateID);
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
        _candidateBits.insert(Gia_ObjId(_cir, pFanout)); // add for future bound
        if(pFanout->Value != 0){ // compare load
          pOld = Gia_ManObj(_cir, pFanout->Value);
          if(Gia_ObjFanoutNum(_cir, pObj) > Gia_ObjFanoutNum(_cir, pOld))
            pFanout->Value = gateID;
        }
        else
          pFanout->Value = gateID;
      } 
    }
  }
  _depGraph = new depGraph(gateList, _forward); // forward
  connectDependency(gateList);
}
void meowTrans::connectDependency(vector<int> & gateList){
  set<int> visited;
  for(int i = 0; i < gateList.size(); ++i){
    visited.clear();
    int j;
    Gia_Obj_t* pObj = Gia_ManObj(_cir, gateList[i]);
    Gia_Obj_t* pFanout;
    Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
      connectDependencyRecur(visited, Gia_ObjId(_cir, pFanout), gateList[i]);
    } 
  }
  //_depGraph->printDepGraph();

}
void meowTrans::connectDependencyRecur(set<int>& visited,int currentID, int sourceID){
  if(visited.find(currentID) != visited.end())
    return;
  visited.insert(currentID);
  int i;
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);
  Gia_Obj_t* pFanout;
  Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, i){
    if(pFanout->Value != 0)
      _depGraph->addDependency(sourceID, pFanout->Value);
    else
      connectDependencyRecur(visited, Gia_ObjId(_cir, pFanout), sourceID);
  } 
}

void meowTrans::splitWords(vector<int>& outputs, int* suppMap, int suppNum,
                    vector< vector<int> >& splitWordVec ){
  map<int, set<int> > xor_bucket;
  for(int i = 0; i < outputs.size(); ++i){
    int xorValue = 0;
    int sum = 0;
    for(int j = 0; j < suppNum; ++j){
      if(suppMap[i*suppNum+j] < 0 || suppMap[i*suppNum+j] > Gia_ManObjNum(_cir))
        continue;
    //  cerr<<i<<". "<<j<<"."<< suppMap[i*suppNum+j]<<endl;
      if(_gate2WordID[suppMap[i*suppNum+j]]!= -1){
        xorValue ^= (_gate2WordID[suppMap[i*suppNum+j]] * (-1));
   //     xorValue = xorValue <<1;
        sum += (_gate2WordID[suppMap[i*suppNum+j]]); 
      //  cerr<<"bit "<<suppMap[i*suppNum+j]<<" becomes" << _gate2WordID[suppMap[i*suppNum+j]]<<endl; 
      }
      else{
        if(suppMap[i*suppNum+j] == _currentControl 
         || _usedControl.find(suppMap[i*suppNum+j]) != _usedControl.end()){ 
          xorValue ^= suppMap[i*suppNum+j];
         // xorValue = xorValue <<1;
          sum += suppMap[i*suppNum+j];
        }
      }
    }
    xorValue *= sum;
   // cerr<<"xorValue:"<<xorValue<<endl;
    if(xor_bucket.find(xorValue) == xor_bucket.end()){
      set<int> newSet;
      newSet.insert(i);
      xor_bucket[xorValue] = newSet;
    }
   else
     xor_bucket[xorValue].insert(i);

  }
  map<int, set<int> >::iterator mite = xor_bucket.begin();
  for(; mite!= xor_bucket.end(); ++mite){
    vector<int> newGroup;
    newGroup.assign((mite->second).begin(), (mite->second).end());
    splitWordVec.push_back(newGroup);
  //  cerr<<"size:"<<newGroup.size()<<endl;
  }
  //cerr<<"GroupNUm "<< splitWordVec.size()<<endl;
}
    
void meowTrans::classifySupports(vector<int>& outputs, int* suppMap, int suppNum, vector<transWord*> & wordCandidates){
  vector< vector<int> > splitWordVec; // store the pos in outputs
  splitWords(outputs, suppMap, suppNum, splitWordVec);
//  cerr<<"SupNum:"<<suppNum<<endl;
  // do split!
  for(int m = 0; m < splitWordVec.size(); ++m){ 
    map<int, int> suppCount; 
    int bitNum = splitWordVec[m].size();
    if(bitNum < 3)
      continue;
    int inputWordNum = 0;
    vector<int> realOutputs;
    for(int i = 0; i < bitNum; ++i)
      realOutputs.push_back(outputs[splitWordVec[m][i]]); 
  // find shared and same pos!
    for( int i = 0; i < bitNum; ++i){
      int realOrder = splitWordVec[m][i]; // realorder in outputs
      for( int j = 0; j < suppNum; ++j){
        if(suppCount.find(suppMap[realOrder*suppNum+j]) == suppCount.end())
          suppCount[suppMap[realOrder*suppNum+j]] = 0;
        suppCount[suppMap[realOrder*suppNum+j]]+=1;
      }
    } 
    set<int> controls;
    map<int, int>::iterator mite = suppCount.begin();
    for(; mite != suppCount.end(); ++mite){
      if(mite->second == bitNum){
        controls.insert(mite->first);
     //   cerr<<"we have controls!"<<mite->first<<endl;
      }
    }
//  if(controls.size() == 0)
//    return NULL;
    inputWordNum = suppNum - controls.size();
    if(inputWordNum == 0){
      //cerr<<"no word?"<<endl;
      continue;
    }
    map<int, int> controlPosMap;
    set<int> controlPos; 
    for(int i = 0; i < bitNum ; ++i){ // arrange bits!
      int realOrder = splitWordVec[m][i];
      if(i == 0){
        for(int j = 0; j < suppNum; ++j){
          if(controls.find(suppMap[realOrder*suppNum+j]) != controls.end()){
            controlPosMap[suppMap[realOrder*suppNum+j]] = j;
            controlPos.insert(j);
          }
          if(_gate2WordID[suppMap[realOrder*suppNum+j]] != -1){
            controlPosMap[ (_gate2WordID[suppMap[realOrder*suppNum+j]]*(-1)) ] = j;
          }
        }
      }
 /*     for(int j = 0; j < suppNum; ++j)
        cerr<<"pos "<<j<<" with "<<suppMap[realOrder*suppNum+j]<<endl;
*/
      for(int j = 0; j < suppNum; ++j){
        //cerr<<"pos "<<j<<" with "<<suppMap[realOrder*suppNum+j]<<endl;

        if(controls.find(suppMap[realOrder*suppNum+j]) != controls.end()){ // we get a control QQ
          int correctPos = controlPosMap[suppMap[realOrder*suppNum+j]];
          if(j != correctPos){
          // swap!
       //     cerr<<"Perform swap!\n"; 
            int temp = suppMap[realOrder*suppNum+j];
            suppMap[realOrder*suppNum+j] = suppMap[realOrder*suppNum+correctPos];
            suppMap[realOrder*suppNum+correctPos] = temp;
          } 
        }
        if( _gate2WordID[suppMap[realOrder*suppNum+j]] != -1){
          int correctPos = controlPosMap[ (_gate2WordID[suppMap[realOrder*suppNum+j]]*(-1)) ];
          if(j != correctPos){
          // swap!
       //     cerr<<"Perform swap!\n"; 
            int temp = suppMap[realOrder*suppNum+j];
            suppMap[realOrder*suppNum+j] = suppMap[realOrder*suppNum+correctPos];
            suppMap[realOrder*suppNum+correctPos] = temp;
          } 
        }
        //cerr<<"pos "<<j<<" with "<<suppMap[realOrder*suppNum+j]<<endl;
      }
 /*    for(int j = 0; j < suppNum; ++j)
       cerr<<"pos "<<j<<" with "<<suppMap[realOrder*suppNum+j]<<endl;
*/
    } // done with arrange
    int* inputWords = new int[bitNum*inputWordNum];
 // vector<int> outputWord;
  // use first one as the standard
    int wordIndex = 0;
    set<int> nonInheritControls(controls);
  //nonInheritControls = controls;
    bool success = true;
    vector<transWord*> faninWords; 
    for(int j = 0; j < suppNum; ++j){
      if(controlPos.find(j) == controlPos.end()){
        int provedWordID = -1; 
        for(int i = 0; i < bitNum; ++i){ // TODO, check word!!!
          int realOrder = splitWordVec[m][i];
          inputWords[wordIndex*bitNum+i] = suppMap[realOrder*suppNum+j];
          if(i == 0)
            provedWordID = _gate2WordID[suppMap[realOrder*suppNum+j]];
          if(provedWordID != _gate2WordID[suppMap[realOrder*suppNum+j]]){
            success = false;
            break;
          } 
        //cerr<<suppMap[i*suppNum+j]<<"\t";
        }
        if(!success)
          break;
        if(provedWordID != -1){
          faninWords.push_back(_provedWords[provedWordID]);
          int* inputControls = _provedWords[provedWordID]->getControls();
          for(int i = 0; i < _provedWords[provedWordID]->getControlNum(); ++i){
            controls.insert(inputControls[i]);
          //inheritControls.insert(inputControls[i]);
          }
        }
      //cerr<<endl;
        wordIndex++;
      }
    }
    if(!success || controls.size() == 0){
     // cerr<<"We fail QQ"<<endl;
      delete[] inputWords;
      continue;
   // return NULL;
    }
  // TODO consider proved case 
    transWord* newWord = new transWord(bitNum, inputWordNum, controls.size());
    vector<int> controlVec;
    controlVec.assign(controls.begin(), controls.end());
    newWord->setWordNSupp(realOutputs, controlVec, inputWords);
    newWord->setFaninWords(faninWords);
    newWord->setNonInheritControls(nonInheritControls);
    delete[] inputWords;
    wordCandidates.push_back(newWord); 
 // return newWord;
  }
}
int meowTrans::countToBack(int currentId, int target){
  int currentWordId = _gate2WordID[currentId];
  int targetWordId = _gate2WordID[target];
  if (_wordId2depth.find(targetWordId)!= _wordId2depth.end())
    return _wordId2depth[targetWordId];
  if(_gate2WordID[currentId] == -1)
    return 0;
  if(currentId == target){
        transWord* targetWord = _provedWords[targetWordId];
    int inputWordNum = targetWord->getInputWordNum();
    vector<int> outputIds;
    targetWord->getOutputWordIds(outputIds);
    int maxDepth = 0;
    for(int j = 0; j < inputWordNum; ++j){
      vector<int> inputIds;
      targetWord->getInputWordByIndex(j, inputIds);
      int depth = countToBack(outputIds[0],inputIds[0]);
      if(depth > maxDepth)
        maxDepth = depth;
    }
   // targetWord->printTransWord();
   //  cerr<<"Here?"<<maxDepth<<endl;
    _wordId2depth[targetWordId] = maxDepth;

  }
  if(currentId < target)
    return 0;
  if(_usedControl.find(currentId)!= _usedControl.end()){
    if(_gate2WordID[currentId] == -1){
      return 0;
    }
  }
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentId);
  if(Gia_ObjIsPi(_cir, pObj)){
    if(currentWordId == -1)
      return -1; //never happen!
    else
      return 1;
  }
  if(Gia_ObjIsAnd(pObj)){
    //cerr<<"Trace ID "<<currentId<<"target "<< target<<endl;
    int faninID0 = Gia_ObjFaninId0(pObj, currentId);
    int faninDepth1 = -1;
   // if(_gate2WordID[faninID0]!= -1)
      faninDepth1 = countToBack(faninID0, target);
    int faninID1 = Gia_ObjFaninId1(pObj, currentId);

    int faninDepth2 = -1;
   // if(_gate2WordID[faninID1]!= -1)
      faninDepth2 = countToBack(faninID1, target);
    if(faninDepth1 > faninDepth2)
      return faninDepth1+1;
    else
      return faninDepth2+1;
  }
  else
    return countToBack(Gia_ObjFaninId0(pObj, currentId), target)+1;
  

}
int meowTrans::countTo(int currentId, int target){
 // cerr<<"countTo"<<currentId<<" "<<target<<endl;
  int currentWord = _gate2WordID[currentId];
  if(currentId == target)
    return _wordId2depth[currentWord];
  if(currentId < target)
    return 0;
  if(_usedControl.find(currentId)!= _usedControl.end()){
    if(_gate2WordID[currentId] == -1){
      return 0;
    }
  }
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentId);
  if(Gia_ObjIsPi(_cir, pObj)){
    if(currentWord == -1)
      return -1; //never happen!
    else
      return 1;
  }
  if(Gia_ObjIsAnd(pObj)){
    int faninDepth1 = countTo(Gia_ObjFaninId0(pObj, currentId), target);
    int faninDepth2 = countTo(Gia_ObjFaninId1(pObj, currentId), target);
    if(faninDepth1 > faninDepth2)
      return faninDepth1+1;
    else
      return faninDepth2+1;
  }
  else
    return countTo(Gia_ObjFaninId0(pObj, currentId), target)+1;
  
}
void meowTrans::computeDepthBackward(){
  //int  = 0;
  map<int, int> depth2WordNum;

  set<transWord*>::iterator site = _successBack.begin();
  for(; site != _successBack.end(); ++site) {
    //(*site)->printTransWord();
    vector<int> outputIds;
    (*site)->getOutputWordIds(outputIds);

    int wordID = (*site)->getWordID();
    if((*site)->getInputWordNum() == 0)
      _wordId2depth[wordID] = 1;
    else if(_wordId2depth.find(wordID) == _wordId2depth.end()){
     // cerr<<"no one here?"<<endl;
      //(*site)->printTransWord();
 //TODO
      int inputWordNum = (*site)->getInputWordNum();
   //   vector<int> outputIds;
      int maxDepth = 0;
      for(int j = 0; j < inputWordNum; ++j){
        vector<int> inputIds;
        (*site)->getInputWordByIndex(j, inputIds);
        int depth = countToBack(outputIds[0],inputIds[0]);
       // cerr<<depth<<" "<<maxDepth<<endl;
        if(depth > maxDepth)
          maxDepth = depth;
      }
      
    //  (*site)->printTransWord();
    //  cerr<<"Depth"<<maxDepth<<endl;
      _wordId2depth[wordID] = maxDepth;

    }
    bool isPO = false;
    for(int k = 0; k < outputIds.size(); ++k){
      if(_poList.find(outputIds[k])!= _poList.end()){
        isPO = true;
        break;
      }
    }
    // check Po
    if(isPO){
      if(depth2WordNum.find(_wordId2depth[wordID])== depth2WordNum.end())
        depth2WordNum[_wordId2depth[wordID]] = 1;
      else
        depth2WordNum[_wordId2depth[wordID]]+=1;
    }
  }
  map<int, int>::iterator mite = depth2WordNum.begin();
  for(; mite!=depth2WordNum.end(); ++mite)
    cerr<<"Depth "<< mite->first<<" WordNum "<<mite->second<<endl;
}
void meowTrans::computeDepth(){
  vector<transWord*> sinkWords;
  set<transWord*> sinkWordSet;
  noFanoutWords(sinkWords);
  sinkWordSet.insert(sinkWords.begin(), sinkWords.end());
  map<int, int> depth2WordNum;
  for(int i = 0; i < _provedWords.size(); ++i ){
    if(_provedWords[i]->getInputWordNum() == 0)
      _wordId2depth[i] = 1;
    else{
      int inputWordNum = _provedWords[i]->getInputWordNum();
      vector<int> outputIds;
      _provedWords[i]->getOutputWordIds(outputIds);
      int maxDepth = 0;
      for(int j = 0; j < inputWordNum; ++j){
        vector<int> inputIds;
        _provedWords[i]->getInputWordByIndex(j, inputIds);
        int depth = countTo(outputIds[0],inputIds[0]);
      //  cerr<<depth<<" "<<maxDepth<<endl;
        if(depth > maxDepth)
          maxDepth = depth;
      }
      _wordId2depth[i] = maxDepth;

    }
    if(sinkWordSet.find( _provedWords[i]) != sinkWordSet.end()){
      if(depth2WordNum.find(_wordId2depth[i])== depth2WordNum.end())
        depth2WordNum[_wordId2depth[i]] = 1;
      else
        depth2WordNum[_wordId2depth[i]]+=1;

    }
  //  _provedWords[i]->printTransWord();
    //cerr<<"Depth?"<<_wordId2depth[i]<<endl;
  }
  map<int, int>::iterator mite = depth2WordNum.begin();
  for(; mite!=depth2WordNum.end(); ++mite)
    cerr<<"Depth "<< mite->first<<" WordNum "<<mite->second<<endl;
}
void meowTrans::computePO(){
  /*
  use POs to compute isomorphism classes directly,
  no internal words.
  */

  vector<int> newPOs;
  int i;
  Gia_Obj_t* pObj; 
  Gia_ManForEachPo(_cir, pObj, i){
    newPOs.push_back(Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj)));
  }
  _poList.insert(newPOs.begin(), newPOs.end()); // same as collect POs

 // set<int> newPOs;
  set<int> supps;
  Gia_Man_t* pNew;
  pNew = Gia_ManStart(Gia_ManObjNum(_cir));
  Gia_ManHashAlloc(pNew);
  Gia_ManFillValue(_cir);
  Gia_ManConst0(_cir)->Value = 0;


  collectSuppForward(newPOs, -1, supps, pNew);
    // collect Supp Done
  getCopyNSuppMap(newPOs, -1, pNew); 
  if(Gia_ManPoNum(pNew) > 2){
    computeIso(pNew);
  }
  Gia_ManStop(pNew); 
 // printResult();


}
void meowTrans::collectPOs(){
  int i;
  Gia_Obj_t* pObj; 
  Gia_ManForEachPo(_cir, pObj, i){
    _poList.insert(Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj)));
    _poList.insert(Gia_ObjId(_cir, pObj)); // maybe we don't need this
  } // collect signals which are POs
}
void meowTrans::computeAll(){
  decideOrder();
  collectPOs(); 
  if(_forward)
    computeForward();
  else
    computeBackward();
  if(_getDepth && _forward)
    computeDepth();
  else if(_getDepth && !_forward)
    computeDepthBackward();
//  writeIsolateAIG(); TODO, why do you make me slow?
  //writeCirDot();
}
void meowTrans::updateSuppBound(transWord* newWord){
  vector<int> outputBits; 
  newWord->getOutputWordIds(outputBits);
  for(int i = 0; i < outputBits.size(); ++i){
    if(_backSuppBound.find(outputBits[i])!= _backSuppBound.end())
      _backSuppBound.erase(outputBits[i]);
  }
  int faninWordNum = newWord->getInputWordNum();
  for(int i = 0; i < faninWordNum; ++i){
    vector<int> inputBits;
    newWord->getInputWordByIndex(i, inputBits);
    for(int j = 0; j < inputBits.size(); ++j){
      _backSuppBound.insert(inputBits[j]);
      if(inputBits[j] < 0 )
        cerr<<"Wrong!"<< inputBits[j]<<endl;;  
    }
  }
}
bool meowTrans::propagateAssignment(transWord* testWord){
  // extend a new proved assignment!
  if(testWord->provedFaninWordNum() != 2)
    return false;
  transWord* inputWord1 = testWord->getFaninWordByIndex(0);
  transWord* inputWord2 = testWord->getFaninWordByIndex(1);
  if(inputWord1->getInputWordNum() == 1 && inputWord2->getInputWordNum() == 1) { 
    vector<int> partialControl1;
    vector<int> partialControl2;
    inputWord1->getNonInheritControls(partialControl1);
    inputWord2->getNonInheritControls(partialControl2);
    if(partialControl1 == partialControl2){
      // copy assignment! 
      char* assignment1 = inputWord1->getAssignments(0);
      char* assignment2 = inputWord2->getAssignments(1);
      vector<char> value1;
      vector<char> value2;
      for(int i = 0; i < partialControl1.size(); ++i){
        int pos = inputWord1->getPosFromControl(partialControl1[i]);
        value1.push_back(assignment1[pos]);   
      }
      for(int i = 0; i < partialControl2.size(); ++i){
        int pos = inputWord2->getPosFromControl(partialControl2[i]);
        value2.push_back(assignment2[pos]);   
      }
      testWord->putAssignment2(partialControl1, 0, value1);
      testWord->putAssignment2(partialControl2, 1, value2);
      return true;
    }
 // check TODO 
  //check if their inputWords ..... 
//    return true;

  }
  return false;
}
void meowTrans::computeForward(){
  for(int k = 0; k < _control_bigOut.size(); ++k){
    int targetControl = _control_bigOut[k].second;
    _currentControl = targetControl;
    Gia_Obj_t* pObj;
    int j;
    Gia_Obj_t* pFanout;
    vector<int> newFanouts;

    pObj = Gia_ManObj(_cir, targetControl);
    Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
      newFanouts.push_back(Gia_ObjId(_cir, pFanout));//collect fanout 
    }
    set<int> newPOs;
    set<int> supps;
    Gia_Man_t* pNew;
    pNew = Gia_ManStart(Gia_ManObjNum(_cir));
    Gia_ManHashAlloc(pNew);
    Gia_ManFillValue(_cir);
    Gia_ManConst0(_cir)->Value = 0;


    collectSuppForward(newFanouts, targetControl, supps, pNew);
    // collect Supp Done
    collectTargetForward(supps, newFanouts, newPOs);
    // collect Target
    vector<int> gateIDs;
    gateIDs.assign(newPOs.begin(), newPOs.end());
    getCopyNSuppMap(gateIDs, targetControl, pNew);
    // run Iso 
    if( Gia_ManPoNum(pNew) > 2){ // number of Co > 2
      computeIso(pNew);
      proceedWords();
   
    }
    Gia_ManStop(pNew);
   // if(k%3 == 0)
   //   proceedWords();   
  }
  proceedWords();
  finalizeForward();
}
void meowTrans::printResult(){
  cerr<<"WordNum "<<_provedWords.size()<<" provedBit "<<_provedWordBits.size();
  int counter = 0;
  int maxWidth = -1;
  int minWidth = -1;
  for(int i = 0; i < _provedWords.size(); ++i){
    //_provedWords[i]->printTransWord();
    if(!_forward && _successBack.find(_provedWords[i])==_successBack.end() )
      continue;
    int wordWidth = _provedWords[i]->getWidth();
    if( wordWidth > maxWidth)
      maxWidth = wordWidth;
    if(minWidth == -1 || wordWidth < minWidth)
      minWidth = wordWidth;
  }
  cerr<<"Max width "<<maxWidth<<" Min width "<<minWidth<<endl;
  for(set<int>::iterator site = _provedWordBits.begin(); site != _provedWordBits.end(); ++site){
    if(_poList.find(*site) != _poList.end()){
      counter++;
      //cerr<<"PO:"<<*site<<endl;
    }
  }
  if(!_forward){
    cerr<<"True Bits "<<_successBackBits.size()<<endl;
    cerr<<"True Words "<<_successBack.size()<<endl;
    set<transWord*>::iterator site = _successBack.begin();
/*    for(; site != _successBack.end(); ++site)
      (*site)->printTransWord();*/
/*    set<int>::iterator site2 = _successBackBits.begin();
    for(; site2 != _successBackBits.end(); ++site2)
      cerr<<(*site2)<<endl;*/
  }
 /* for(int i = 0; i < _provedWords.size(); ++i){
    transWord* finalWord = _provedWords[i];
    if(_successBack.find(finalWord) != _successBack.end())
      finalWord->printTransWord();
  } */
 // cerr<<"counter"<<counter<<endl;
 //  vector<transWord*> sinkWords;
 // noFanoutWords(sinkWords);
  //set<int> levels;
 /* _cir->vLevels = Vec_IntStart( Gia_ManObjNum(_cir) );
  Gia_Obj_t * pObj;
  int i;
  Gia_ObjSetLevelId(_cir, 0, 0);
  Gia_ManForEachPi(_cir, pObj, i){
    Gia_ObjSetLevel( _cir, pObj, 0 );
  }
  Gia_ManForEachObj1(_cir, pObj, i){
    if(Gia_ObjIsPi(_cir, pObj))
      continue;
    Gia_ObjSetGateLevel( _cir, pObj );
  }
  map<int, int> level2Num;
  for(int i = 0; i < _provedWords.size(); ++i){
    transWord* finalWord = _provedWords[i];
  //  finalWord->printTransWord();
    vector<int> outIDs;
    finalWord->getOutputWordIds(outIDs);
    int level = Gia_ObjLevelId( _cir, outIDs[0]);
    if (level2Num.find(level) == level2Num.end())
      level2Num[level] = outIDs.size();
    else
      level2Num[level]+= outIDs.size();
 
  }*/
  cerr<<" PONum "<<counter<<endl;
 /* map<int, int>::iterator mite = level2Num.begin();
  for(; mite != level2Num.end(); ++mite)
    cerr<<"Level "<<mite->first<<" Num "<<mite->second<<endl;*/
}
void meowTrans::targetBoundary(vector<int>& gateIDs){
  set<int>::iterator site = _provedWordBits.begin(); 
  for(; site != _provedWordBits.begin(); ++site){

  }
} 
void meowTrans::finalizeForward2(){
  int i, j;
  Gia_Obj_t* pObj;
  Gia_Obj_t* pFanout;
  Gia_ManForEachObj1(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    if(_provedWordBits.find(gateID) != _provedWordBits.end())
      continue;
    if(Gia_ObjIsPo(_cir, pObj))
      break;
    if(_usedControl.find(gateID) != _usedControl.end())
      continue;
    bool fail = false;
    Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
      int fanoutID = Gia_ObjId(_cir, pFanout);
      if(_provedWordBits.find(fanoutID) == _provedWordBits.end()){
        fail = true;
        break;
      }
    }
    if(!fail )
      _provedWordBits.insert(gateID);
  } 

}
void meowTrans::proceedWords(){
  // start from new found words!
  set<int> targetPOs;
  set<int> currentFanouts;
  vector<int> newFanouts;
  for(int i = 0; i < _provedWords.size(); ++i){
    vector<int> outputIDs;
    _provedWords[i]->getOutputWordIds(outputIDs);
    for(int j = 0; j < outputIDs.size(); ++j){
        getOutputsRecur(currentFanouts, outputIDs[j]);
        currentFanouts.erase(outputIDs[j]);
    }  
 //   currentFanouts.insert(outputIDs.begin(), outputIDs.end());
  }
  if(currentFanouts.size() == 0)
    return;
  newFanouts.assign(currentFanouts.begin(), currentFanouts.end());
  set<int> newPOs;
  set<int> supps;
    
  Gia_Man_t* pNew;
  pNew = Gia_ManStart(Gia_ManObjNum(_cir));
  Gia_ManHashAlloc(pNew);
  Gia_ManFillValue(_cir);
  Gia_ManConst0(_cir)->Value = 0;
  
  collectSuppForward(newFanouts, -1, supps, pNew);
    // collect Supp Done
  collectTargetForward(supps, newFanouts, newPOs);
  set<int>::iterator site = newPOs.begin();
  set<int> provedPOs;
  for(; site != newPOs.end(); ++site){
    if(_checkedProceedBits.find(*site) != _checkedProceedBits.end())
      provedPOs.insert(*site);
    if(_provedWordBits.find(*site)!= _provedWordBits.end())
      provedPOs.insert(*site);
  }
  site = provedPOs.begin();
  for(; site!= provedPOs.end(); ++site)
    newPOs.erase(*site);  
  _checkedProceedBits.insert(newPOs.begin(), newPOs.end());

  vector<int> gateIDs;
  gateIDs.assign(newPOs.begin(), newPOs.end());
  getCopyNSuppMap(gateIDs, -1, pNew);
    // run Iso 
  if( Gia_ManPoNum(pNew) > 2){ // number of Co > 2
    computeIso(pNew);
   // cerr<<"proceed?!"<<endl;
  }
  Gia_ManStop(pNew);


  _newAddWords.clear();

} 
void meowTrans::finalizeForward(){
  // find no fanout words
  set<transWord*> usedWords;
  while(true){
    vector<transWord*> sinkWords;
    noFanoutWords(sinkWords);
    set<int> targetPOs;
    int oldSize = _provedWords.size();
    for(int i = 0; i < sinkWords.size(); ++i){ 
     // cerr<<"sink Word"<< sinkWords[i]->getWordID()<<endl;
      if(usedWords.find(sinkWords[i]) != usedWords.end())
        continue;
      usedWords.insert(sinkWords[i]);
      vector<int> outputIDs;
      sinkWords[i]->getOutputWordIds(outputIDs);
      for(int j = 0; j < outputIDs.size(); ++j){
        getOutputsRecur(targetPOs, outputIDs[j]);
        targetPOs.erase(outputIDs[j]);
      } 
    }
    if(targetPOs.size() == 0)
      break;

    vector<int> newFanouts;
    newFanouts.assign(targetPOs.begin(), targetPOs.end());
    set<int> newPOs;
    set<int> supps;
    Gia_Man_t* pNew;
    pNew = Gia_ManStart(Gia_ManObjNum(_cir));
    Gia_ManHashAlloc(pNew);
    Gia_ManFillValue(_cir);
    Gia_ManConst0(_cir)->Value = 0;


    collectSuppForward(newFanouts, -1, supps, pNew);
    // collect Supp Done
    collectTargetForward(supps, newFanouts, newPOs);
    // collect Target
    vector<int> gateIDs;
    gateIDs.assign(newPOs.begin(), newPOs.end());
    getCopyNSuppMap(gateIDs, -1, pNew);
    // run Iso 
    if( Gia_ManPoNum(pNew) > 2){ // number of Co > 2
      computeIso(pNew);
      Gia_ManStop(pNew);

    }
    else{
      break;
      Gia_ManStop(pNew);

    }

    if(_provedWords.size()== oldSize)
      break;
  }
  int i, j;
  Gia_Obj_t* pObj;
  Gia_Obj_t* pFanout;
  Gia_ManForEachObj1(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    if(_provedWordBits.find(gateID) != _provedWordBits.end())
      continue;
    if(Gia_ObjIsPo(_cir, pObj))
      break;
    if(_usedControl.find(gateID) != _usedControl.end())
      continue;
    bool fail = false;
    Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
      int fanoutID = Gia_ObjId(_cir, pFanout);
      if(_provedWordBits.find(fanoutID) == _provedWordBits.end()){
        fail = true;
        break;
      }
    }
    if(!fail )
      _provedWordBits.insert(gateID);
  }  
  // if all of its fanouts are proved bits, add it
}
void meowTrans::getOutputsRecur(set<int>& outputs, int currentID){
  if(outputs.find(currentID) != outputs.end())
    return;
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);
  if(Gia_ObjIsPo(_cir, pObj))
    return; 
//  outputs.insert(currentID);
   int j;
  Gia_Obj_t* pFanout;
  Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
    if(Gia_ObjIsPo(_cir, pFanout))
      continue;
    if(_gate2WordID[Gia_ObjId(_cir, pFanout)] != -1)
      continue;
    outputs.insert(Gia_ObjId(_cir, pFanout));
    //getOutputsRecur(outputs, Gia_ObjId(_cir, pFanout));
  }
}
void meowTrans::noFanoutWords(vector<transWord*> & sinkWords){
  set<int> wordPool;
  for(int i = 0; i < _provedWords.size(); ++i)
    wordPool.insert(i);
  for(int i = 0; i < _provedWords.size(); ++i){
    transWord* currentWord = _provedWords[i];
    int faninNum = currentWord->getProvedInputWordNum();
    for(int j = 0; j < faninNum; ++j){
      transWord* inputWord = currentWord->getFaninWord(j);
      if(wordPool.find(inputWord->getWordID()) != wordPool.end())
        wordPool.erase(inputWord->getWordID());
    } 
  }
  set<int>::iterator site = wordPool.begin();
  for(; site!= wordPool.end(); ++site){
    sinkWords.push_back( _provedWords[(*site)] );
   // _provedWords[(*site)]->printTransWord();
  }
}
void meowTrans::collectSuppForward(vector<int>& fanouts,
                              int control, set<int>& supps, Gia_Man_t* pNew){
  Gia_Obj_t * pObj;
  int i;
  _po_supp_map.clear(); 
  Gia_ManForEachPi(_cir, pObj, i){
    pObj->Value = Gia_ManAppendCi(pNew);
    int piID = Gia_ObjId(_cir, pObj);
    set<int> newSupp;
    newSupp.insert(piID);
    _po_supp_map[piID] = newSupp;  
  }
  set<int> tempCollect;
  tempCollect.clear();
  tempCollect.insert(_provedWordBits.begin(), _provedWordBits.end());
  tempCollect.insert(_usedControl.begin(), _usedControl.end());
  if(control != -1)
    tempCollect.insert(control);
  set<int>::iterator site = tempCollect.begin();
  for(; site!= tempCollect.end(); ++site){
    pObj = Gia_ManObj(_cir, (*site));
    if((~pObj->Value))
      continue;
    pObj->Value = Gia_ManAppendCi(pNew); // use proved bits a primary inputs
  }
  for(int j = 0; j < fanouts.size(); ++j){
    recurSupp(fanouts[j],control);
    set<int> temp = _po_supp_map[fanouts[j]];
    supps.insert(temp.begin(), temp.end());
  } 
}
void meowTrans::collectTargetForward(set<int>& supps, vector<int>& fanouts, set<int>& newPOs){
  for(int j = 0; j < fanouts.size(); ++j){
    collectTargetForwardRecur(supps, newPOs, fanouts[j]);
  }
}
void meowTrans::collectTargetForwardRecur(set<int>& supps, set<int>& newPOs, int currentID){
  if(newPOs.find(currentID) != newPOs.end())
    return;
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);
  if(Gia_ObjIsPo(_cir, pObj))
    return;
  // check its input!!
  if(Gia_ObjIsAnd(pObj)){
    int faninID0 = Gia_ObjFaninId0(pObj, currentID);
    int faninID1 = Gia_ObjFaninId1(pObj, currentID);
    if(supps.find(faninID0) == supps.end() 
    || supps.find(faninID1) == supps.end()){
      return;
    }
  }
 /* else{
    int faninID0 = Gia_ObjFaninId0(pObj, currentID);
    if(supps.find(faninID0) == supps.end() 
      return;
  }*/ //doesn't need this
  newPOs.insert(currentID);
  int j;
  Gia_Obj_t* pFanout;
  Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
    collectTargetForwardRecur(supps, newPOs,Gia_ObjId(_cir, pFanout));
  }

}
void meowTrans::computeBackward(){
  for(int k = _control_bigOut.size() -1; k >= 0; k--){
   
    int targetControl = _control_bigOut[k].second;
    _currentControl = targetControl;
    //cerr<<targetControl<<endl;
    Gia_Obj_t* pObj;
    _piList.clear();
    set<int> fanoutList;
    _piList.insert(targetControl);
    int j;
    Gia_Obj_t* pFanout;
    //int i;
 //   Gia_Obj_t* pFanin;
    pObj = Gia_ManObj(_cir, targetControl);
    Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
      int fanoutID = Gia_ObjId(_cir, pFanout);
      fanoutList.insert(fanoutID);  // temp fanout
      if(Gia_ObjIsAnd(pFanout)){
        _piList.insert(Gia_ObjFaninId0(pFanout, fanoutID  ));
        _piList.insert(Gia_ObjFaninId1(pFanout, fanoutID ));
      }
      else{
        _piList.insert(Gia_ObjFaninId0(pFanout, fanoutID ));
      } 
    }
    Gia_Man_t* isoCir = getBackwardCircuit(fanoutList);
    //writeAIGDot(isoCir);
    //done with circuit construction
    computeIso(isoCir);
    proceedWords();
    Gia_ManStop(isoCir); 
    //break;
  }
  finalizeForward();
  finalizeBackward();
}
void meowTrans::finalizeBackward(){
  // remove non transparent to PO words
  set<transWord*> successWords;
  set<int> successBits;
  set<int>::iterator site2 = _provedWordBits.begin();
  for(; site2 != _provedWordBits.end(); ++site2){
    if(_poList.find(*site2) != _poList.end())
      successBits.insert(*site2);
  }
  for(int i = 0; i < _provedWords.size(); ++i){
    transWord* outWord = _provedWords[i];
    vector<int> outBits;
    outWord->getOutputWordIds(outBits);
    bool fail = true;
    for(int j = 0; j < outBits.size(); ++j){
      if(_poList.find(outBits[j]) != _poList.end()){
        fail = false;
        break;
      }
    }
    if(!fail){
      successWords.insert(outWord);
      successBits.insert(outBits.begin(), outBits.end());
    }
  }
  set<int> backTrace;
  backTrace.insert(successBits.begin(), successBits.end());
  while(backTrace.size() != 0){
    set<int> newAdded;
    newAdded.clear();
    set<int>::iterator site = backTrace.begin();
    for(; site != backTrace.end(); ++site){
      Gia_Obj_t* pObj = Gia_ManObj(_cir, (*site));
      if(Gia_ObjIsPi(_cir, pObj))
        continue;
      if(Gia_ObjIsAnd(pObj)){
        int id1 = Gia_ObjFaninId0(pObj, (*site));
        int id2 = Gia_ObjFaninId1(pObj, (*site));
        if(_provedWordBits.find(id1) != _provedWordBits.end()){
          if(successBits.find(id1) == successBits.end()){
            newAdded.insert(id1);
            successBits.insert(id1);
          }
        }
        if(_provedWordBits.find(id2) != _provedWordBits.end()){
          if(successBits.find(id2) == successBits.end()){
            newAdded.insert(id2);
            successBits.insert(id2);
          }
        }
      }
      else{
        int id1 = Gia_ObjFaninId0(pObj, (*site));
        if(_provedWordBits.find(id1) != _provedWordBits.end()){
          if(successBits.find(id1) == successBits.end()){
            newAdded.insert(id1);
            successBits.insert(id1);
          }
        }
      } 
    }
    backTrace.clear();
    backTrace.insert(newAdded.begin(), newAdded.end()); 
  }
  // add successBackWord
  for(int i = 0; i < _provedWords.size(); ++i){
    transWord* outWord = _provedWords[i];
    vector<int> outBits;
    outWord->getOutputWordIds(outBits);
    bool fail = true;
    for(int j = 0; j < outBits.size(); ++j){
      if(successBits.find(outBits[j]) != successBits.end()){
        fail = false;
        break;
      }
    }
    if(!fail){
      successWords.insert(outWord);
    }

  }
 /* int i;
  Gia_Obj_t* pObj; 
  Gia_ManForEachPo(_cir, pObj, i){
    int faninID = Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj));
    if(successBits.find(faninID) != successBits.end())
      successBits.insert(Gia_ObjId(_cir, pObj)); // maybe we don't need this
  }*/ 
  //add PPO
  _successBackBits.insert(successBits.begin(), successBits.end());
  _successBack.insert(successWords.begin(), successWords.end()); 
}
void meowTrans::buildBackSuppMap(set<int> & targetPOs, set<int> & poList){
 // go through poList and remove those outside of this targets 
  targetPOs.insert(poList.begin(), poList.end());
  set<int>::iterator site = poList.begin();
  for(; site!= poList.end(); ++site){ // poList is sorted
    Gia_Obj_t* pObj = Gia_ManObj(_cir, *site);
    if(Gia_ObjIsAnd(pObj)){
      int id1 = Gia_ObjFaninId0(pObj, *site);
      int id2 = Gia_ObjFaninId1(pObj, *site);
      if(_po_supp_map.find(id1) == _po_supp_map.end()
       || _po_supp_map.find(id2) == _po_supp_map.end()){
        targetPOs.erase(*site); //remove
        continue;
      }
      set<int> newSupp;
      set<int> supp1 = _po_supp_map[id1];
      set<int> supp2 = _po_supp_map[id2];
      newSupp.insert(supp1.begin(), supp1.end());
      newSupp.insert(supp2.begin(), supp2.end());
      _po_supp_map[(*site)] = newSupp;
    }
    else{
      int id1 = Gia_ObjFaninId0(pObj, *site);
      if(_po_supp_map.find(id1) == _po_supp_map.end()){
        targetPOs.erase(*site);
        continue;
      }
      set<int> newSupp;
      set<int> supp1 = _po_supp_map[id1];
      newSupp.insert(supp1.begin(), supp1.end());
      _po_supp_map[(*site)] = newSupp;
    } 
  }
}
bool meowTrans::faninProved(int gateID, int* supp, int suppNum){
  for(int i = 0; i < suppNum; ++i){
   //  cerr<<" "<<supp[i]; 
     if(_usedControl.find(supp[i]) == _usedControl.end()){
       if(_backSuppBits.find(supp[i]) == _backSuppBits.end())
         return false;
     }

  }
 // cerr<<endl;
  return true;
}
bool meowTrans::fanoutProved(int gateID){
  // return true if all fanout has been proved
  Gia_Obj_t* pObj = Gia_ManObj(_cir, gateID);
  int j;
  Gia_Obj_t* pFanout;
  Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
    int fanoutID = Gia_ObjId(_cir, pFanout);
    //cout<<gateID<<" "<<fanoutID<<endl;
    if (_provedWordBits.find(fanoutID) == _provedWordBits.end())
      return false;
  }
  return true;
}
Gia_Man_t* meowTrans::getBackwardCircuit(set<int>& fanoutList){

  set<int> poList; // my "target"
  set<int>::iterator site = fanoutList.begin();
  _po_supp_map.clear();
  _copyPo_gateID.clear();
 
  for(; site!= fanoutList.end(); ++site)
    collectBackwardPORecur( poList, (*site));
 
  set<int> tempCollect;
  tempCollect.insert(_provedWordBits.begin(), _provedWordBits.end());
 /* set<int>::iterator sitex = poList.begin();
  for(; sitex != poList.end(); ++sitex){
    if(tempCollect.find(*sitex) != tempCollect.end())
      tempCollect.erase(*sitex);

  }*/
  tempCollect.insert(_piList.begin(), _piList.end()); // include _currentControl
  tempCollect.insert(_usedControl.begin(), _usedControl.end());
  
  // include current support, control, proved words
  site = tempCollect.begin();
  for(; site != tempCollect.end(); ++site){
    set<int> newSupp;
    newSupp.insert(*site);
    _po_supp_map[(*site)] = newSupp;
  }
  set<int> zeroSupp;
  zeroSupp.insert(0);
  _po_supp_map[0] = zeroSupp;
  //// build supp map and remove fanouts outside of the targets.
  set<int> targetPOs;
  buildBackSuppMap(targetPOs, poList);


  Gia_Man_t * pNew;
  Gia_Obj_t * pObj;
 
  pNew = Gia_ManStart(Gia_ManObjNum(_cir));
  Gia_ManHashAlloc(pNew);
  Gia_ManFillValue(_cir);
  Gia_ManConst0(_cir)->Value = 0;
  site = tempCollect.begin(); //supp as primary inputs
  for(; site!= tempCollect.end(); ++site){
   // cerr<<*site<<" ";
    pObj = Gia_ManObj(_cir, (*site));
    if(~pObj->Value){
      continue;
    }

    pObj->Value = Gia_ManAppendCi(pNew);
  }
  //cerr<<"Done with PI"<<endl;
  //cerr<<"Supp"<<endl;
  site = targetPOs.begin();
  for(; site!= targetPOs.end(); ++site){
    _copyPo_gateID.push_back(*site);
  // if(_backSuppBound.find(*site) != _backSuppBound.end())
  //   cerr<<*site<<" !!"<<endl;;
    int outLit = recurCopyN(pNew, *site, *site);
    Gia_ManAppendCo(pNew, outLit);  
  }
//  cerr<<"POs"<<endl;
//  writeAIGDot(pNew);
  return pNew;
}


void meowTrans::collectBackwardPORecur( set<int> & poList, int currentID){
  if(poList.find(currentID)!= poList.end())
    return;
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);
  if(Gia_ObjIsPo(_cir, pObj))
    return; 
// cerr<<"get PO Recur!" <<currentID<<endl;
  poList.insert(currentID);
  if(_gate2WordID[currentID] != -1) // dont walk forward
    return;
  int j;
  Gia_Obj_t* pFanout;
  Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
    int fanoutID = Gia_ObjId(_cir, pFanout);
    collectBackwardPORecur( poList, fanoutID);   
  }
}
void meowTrans::writeAIGDot(Gia_Man_t* targetCir){
  ofstream output("aigGraph.dot");
  output<<"digraph graphname{"<<endl;
  // step 1
  int i;
  Gia_Obj_t* pObj;
 // Gia_Obj_t* pFanout;
  Gia_ManForEachObj(targetCir, pObj, i){
    int gateID = Gia_ObjId(targetCir, pObj);
    output<<"g"<<gateID<<" [";
    if(Gia_ObjIsPi(targetCir, pObj)||Gia_ObjIsPo(targetCir, pObj) )
      output<<" shape=box, ";
    else 
      output<<" shape=diamond, ";
    output<<" fillcolor=white ]";
    output<<endl;
    if(Gia_ObjIsPi(targetCir, pObj)||i == 0)
      continue;
    if(Gia_ObjIsAnd(pObj)){
      int id1 = Gia_ObjFaninId0(pObj, gateID);
      int id2 = Gia_ObjFaninId1(pObj, gateID);
      int bubble1 = Gia_ObjFaninC0(pObj); 
      int bubble2 = Gia_ObjFaninC1(pObj); 
      
      output<<"g"<<id1<<" -> g"<<gateID;
      if(bubble1)
        output<<"[style=dotted]";
       output<<";"<<endl;

      output<<"g"<<id2<<" -> g"<<gateID;
      if(bubble2)
        output<<"[style=dotted]";
 
      output<<";"<<endl;
 

    }
    else{
      int id1 = Gia_ObjFaninId0(pObj, gateID);
      int bubble1 = Gia_ObjFaninC0(pObj); 

      output<<"g"<<id1<<" -> g"<<gateID;
      if(bubble1)
        output<<"[style=dotted]";
 
      output<<";"<<endl;

    }
  }
  // step 2
  
  output<<"}"<<endl;
  output.close();

}
void meowTrans::writeCirDot(){
  // decide node color
  // connect nodes in AIG
  ofstream output("cirGraph.dot");
  output<<"digraph graphname{"<<endl;
  // step 1
  int i;
  Gia_Obj_t* pObj;
 // Gia_Obj_t* pFanout;
  Gia_ManForEachObj(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    output<<"g"<<gateID<<" [";
    if(Gia_ObjIsPi(_cir, pObj)||Gia_ObjIsPo(_cir, pObj) )
      output<<" shape=box, ";
    else 
      output<<" shape=diamond, ";
    if(_forward && _provedWordBits.find(gateID)!= _provedWordBits.end())
      output<<" color=red style=filled ]";
    else if(!_forward && _successBackBits.find(gateID) != _successBackBits.end())
      output<<" color=blue style=filled ]";
    else
      output<<" fillcolor=white ]";
    output<<endl;
    if(Gia_ObjIsPi(_cir, pObj)||i == 0)
      continue;
    if(Gia_ObjIsAnd(pObj)){
      int id1 = Gia_ObjFaninId0(pObj, gateID);
      int id2 = Gia_ObjFaninId1(pObj, gateID);
      int bubble1 = Gia_ObjFaninC0(pObj); 
      int bubble2 = Gia_ObjFaninC1(pObj); 
      
      output<<"g"<<id1<<" -> g"<<gateID;
      if(bubble1)
        output<<"[style=dotted]";
       output<<";"<<endl;

      output<<"g"<<id2<<" -> g"<<gateID;
      if(bubble2)
        output<<"[style=dotted]";
 
      output<<";"<<endl;
 

    }
    else{
      int id1 = Gia_ObjFaninId0(pObj, gateID);
      int bubble1 = Gia_ObjFaninC0(pObj); 

      output<<"g"<<id1<<" -> g"<<gateID;
      if(bubble1)
        output<<"[style=dotted]";
 
      output<<";"<<endl;

    }
  }
  // step 2
  
  output<<"}"<<endl;
  output.close();
}
void meowTrans::labelIsolateRecur(set<int>& piList, int currentID ){
  if(_provedWordBits.find(currentID) != _provedWordBits.end()){
    piList.insert(currentID);
    return;
  }
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);


  if(Gia_ObjIsPi(_cir, pObj)){
    piList.insert(currentID);
    return;
  }
  if(Gia_ObjIsConst0(pObj))
    return;
  if(Gia_ObjIsAnd(pObj)){
    int id1 = Gia_ObjFaninId0( pObj, currentID);
    int id2 = Gia_ObjFaninId1( pObj, currentID);
    labelIsolateRecur(piList, id1);
    labelIsolateRecur(piList, id2); 
  }
  else{
    int id1 = Gia_ObjFaninId0( pObj, currentID);
    labelIsolateRecur(piList, id1);
  } 
}
void meowTrans::labelIsolateAIG(set<int>& piList, set<int>& poList){
  int i;
  Gia_Obj_t* pObj; 
  Gia_ManForEachPo(_cir, pObj, i){
    int poID = Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj));
    if(_provedWordBits.find(poID)!= _provedWordBits.end())
      continue;
    else{
      poList.insert(poID);
      labelIsolateRecur(piList, poID);
    }
  }
}
void meowTrans::writeIsolateAIG(){
  // step 1, take proved bits as PPI
  set<int> piList;
  set<int> poList;
  labelIsolateAIG(piList, poList);
  // step 2, start from PO, only take non-transparent PO
  Gia_Man_t * pNew;
  Gia_Obj_t * pObj;
//  int i;
  pNew = Gia_ManStart(Gia_ManObjNum(_cir));
  Gia_ManHashAlloc(pNew);
  Gia_ManFillValue(_cir);
  Gia_ManConst0(_cir)->Value = 0;
  set<int>::iterator site = piList.begin();
  for(; site != piList.end(); ++site){
    pObj = Gia_ManObj(_cir, (*site));
    pObj->Value = Gia_ManAppendCi(pNew);
  }
  site = poList.begin();
  for(; site!= poList.end(); ++site){
    int outLit = recurCopyN(pNew, *site, *site);
    Gia_ManAppendCo(pNew, outLit);
  } 
  //step 3, shrink
  writeAIGDot(pNew);
  Gia_ManStop(pNew);
}
void meowTrans::writeGraphDot(){
//  cerr<<"Hello?"<<endl;

  ofstream output("wordGraph.dot");
  output<<"digraph graphname{"<<endl;
  for(int i = 0; i < _provedWords.size(); ++i){
    int faninNum = _provedWords[i]->provedFaninWordNum();
    for(int j = 0; j < faninNum; ++j){
      output<<"w"<<_provedWords[i]->getFaninWord(j)->getWordID()<<" -> w"<<_provedWords[i]->getWordID()<<";"<<endl;

    }
  }
  output<<"}"<<endl;
  output.close();
}
ABC_NAMESPACE_IMPL_END
