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
#include "ext/meow/meowDGTrans.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START
meowDGTrans::meowDGTrans(Gia_Man_t* cir){
  _cir = cir;
  _muxAPI = new meowMux(cir);
  _muxAPI->runAll(true); // recognize
  _muxAPI->splitForDG(); // add to make sure we split words for DG.
  
//  _muxAPI->reportWords();  
  Gia_ManStaticFanoutStart(_cir);

}
meowDGTrans::~meowDGTrans(){
  delete _muxAPI;
  Gia_ManStaticFanoutStop(_cir);

}
void meowDGTrans::getGatedFFs(vector<vector<int> >& inputs,
                              vector<vector<int> >& outputs,
                              vector<vector<int> >& controls){
  // visit all words in reverse order, 
  vector<int> nodeOrder;
  _muxAPI->sortNodes(nodeOrder);
  for(int i =0; i < nodeOrder.size(); ++i){
    muxNode* target = _muxAPI->getNodebyIndex(nodeOrder[i]);
    if(_gatedFFs.find(target)!= _gatedFFs.end())// explored before
      continue;
  //  if(target->getBitNum() < 4)
  //    continue;
    bool isFanin0 = true; // fanin0 is FF itself
    vector<int> roList;
    if(checkGatedFF(target, isFanin0, roList)){
      //cerr<<"Get GatedFF!!"<<endl;
      _gatedFFs.insert(target);
      muxNode* faninNode = _muxAPI->getFaninNode(target, isFanin0);
      vector<int> controlSeq;
      vector<muxNode*> nodeSeq;
      if(isFanin0) // sel = 0 gated => sel = 1 input
        controlSeq.push_back(target->getControlID());
      else
        controlSeq.push_back(target->getControlID()*(-1));
      nodeSeq.push_back(target);
      if(faninNode)
        getGatedFFRecur(faninNode, target, controlSeq, nodeSeq);
      // add into the return vectors
      controls.push_back(controlSeq);
      outputs.push_back(roList);
      vector<int>& inputSeq = (nodeSeq.back())->getFaninIDPhase( controlSeq.back() < 0);
      /*vector<int> inputSeq; //  get phase here?
      if(controlSeq.back() < 0) // sel = 0 input
        (nodeSeq.back())->getFaninID0(inputSeq);
      else
        (nodeSeq.back())->getFaninID1(inputSeq); // ID only */
      inputs.push_back(inputSeq);
    }
  }
}
void meowDGTrans::getGatedFFRecur(muxNode* current, muxNode* target,
                                  vector<int>& controls, 
                                  vector<muxNode*>& nodeSeq){
  //
  int width = current->getBitNum();
  if(width != target->getBitNum()){ 
    cerr<<"Something wrong!"<<endl;
    return;
  }
  bool fail = false;
  bool isFanin0 = true;
  bool isNeg = true;
  for(int i = 0; i < width; ++i){
    if(fail)
      break;
    int fanin1, fanin0, targetOut, gateID;
    target->getFanoutID(i, targetOut);
    current->getFaninPhase(i, fanin1, fanin0, gateID);
    Gia_Obj_t* pObj = Gia_ManObj(_cir, abs(targetOut));
    Gia_Obj_t* pFanout = Gia_ObjFanout0(_cir, pObj); // only one
    int expectedInput =  Gia_ObjRiToRoId( _cir, 
                                         Gia_ObjId(_cir, pFanout) );
    if(abs(fanin1) == expectedInput){
      if(i == 0){
        if(fanin1> 0)
          isNeg = false;
        isFanin0 = false;
      }
      else{
        if(fanin1 > 0 && isNeg)
          fail = true;
        if(isFanin0)
          fail = true;
      }
    }
    else if(abs(fanin0) == expectedInput){
      if(i == 0){
        if(fanin0 > 0)
          isNeg = false;
      }
      else{
        if(fanin0 > 0 && isNeg)
          fail = true;
        if(!isFanin0)
          fail = true;
      }
    }
    else
      fail = true;

  }
  if(!fail){
    _gatedFFs.insert(current);
    if(isFanin0)
      controls.push_back(current->getControlID());
    else
      controls.push_back(current->getControlID()*(-1));
    nodeSeq.push_back(current);

    muxNode* faninNode = _muxAPI->getFaninNode(current, isFanin0);
      if(faninNode)
        getGatedFFRecur(faninNode, target, controls, nodeSeq);

    // keep going
  }
}
bool meowDGTrans::checkGatedFF(muxNode* target, bool& isFanin0, vector<int>& roList){
  // find: fanin0 = Ro, fanin1 = else, output = Ri
  int width = target->getBitNum();
  bool isNeg = true;
  for(int i = 0; i < width; ++i){
    int fanin1, fanin0, gateID;
    target->getFaninPhase(i, fanin1, fanin0, gateID);
  //  cerr<<"Mux:"<<gateID<<", "<<fanin1<<", "<<fanin0<<endl;
    Gia_Obj_t* pObj = Gia_ManObj(_cir, abs(gateID));
    if(Gia_ObjFanoutNum(_cir, pObj)!= 1)
      return false;
    Gia_Obj_t* pFanout = Gia_ObjFanout0(_cir, pObj); // only one
    if(!Gia_ObjIsRi( _cir, pFanout ) )
      return false;
    int expectedInput =  Gia_ObjRiToRoId( _cir, 
                                         Gia_ObjId(_cir, pFanout) );
    roList.push_back(expectedInput);
    if(abs(fanin1) == expectedInput){
      if(i == 0){
        if(fanin1> 0)
          isNeg = false;
        isFanin0 = false;
      }
      else{
        if(fanin1 > 0 && isNeg)
          return false;
        if(isFanin0)
          return false;
      }
    }
    else if(abs(fanin0) == expectedInput){
      if(i == 0){
        if(fanin0 > 0)
          isNeg = false;
      }
      else{
        if(fanin0 > 0 && isNeg)
          return false;
        if(!isFanin0)
          return false;
      }
    }
    else
      return false;
  }
  return true;
}
void meowDGTrans::getOtherTrans(vector<vector<int> >& input0s,
                                vector<vector<int> >& input1s,
                                vector<vector<int> >& outputs,
                                vector<int>& controls){
  // don't worry about gatedFF anymore
  vector<int> nodeOrder;
  _muxAPI->sortNodes(nodeOrder);
  for(int i = 0; i < nodeOrder.size(); ++i){
    muxNode* target = _muxAPI->getNodebyIndex(nodeOrder[i]);
    if(_gatedFFs.find(target)!= _gatedFFs.end())
      continue;
    controls.push_back(target->getControlID());
    outputs.push_back(target->getFanoutIDs()); 
    vector<int> faninID0s;
    target->getFaninID0(faninID0s);
    vector<int> faninID1s;
    target->getFaninID1(faninID1s);
    input0s.push_back(faninID0s);
    input1s.push_back(faninID1s);
  }
}
void meowDGTrans::printTrans(){
  _muxAPI->reportWords();
}
ABC_NAMESPACE_IMPL_END
