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
#include "ext/meow/meowDGNode.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START
meowDGNode::meowDGNode(unsigned id, vector<int>& idList){
  _id = id;
  _explored = 0;
  _word = new meowDGWord(idList); 
}
meowDGNode::~meowDGNode(){
  delete _word;

}
vector<int>& meowDGNode::getGates(){
  return _word->getGateIDs();
}
int meowDGNode::getMaxGateID(){
  return _word->getMaxGateID();
}
void meowDGNode::updateID(map<int, int>& old2newID){

  _word->updateIDs(old2newID);
  if(_type == NODE_TRANS )
    dynamic_cast<meowDGTransBlock*>(this)->reviseSel(old2newID);
 
  if(_type == NODE_GATED) 
    dynamic_cast<meowDGGatedFF*>(this)->reviseControl(old2newID);
}
meowDGPI::meowDGPI(unsigned id, vector<int>& idList):meowDGNode(id, idList){
  setType( NODE_PI);
}
meowAIGNode* meowDGPI::constructUpdateCir(meowAIG* uCir, 
                                          set<meowDGNode*>& visited,
                                          int depth){
  return uCir->getOne();
}
meowAIGNode* meowDGPI::constructObserveCir( meowAIG* oCir,
                                     set<meowDGNode*>& visited,
                                     int depth, 
                                    meowDGNode* source){
  cerr<<"ERROR DGPI should not be called for observable"<<endl;
  return oCir->getOne(); 
}
meowAIGNode* meowDGPI::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
  cerr<<"ERROR DGPI should not be called for observable"<<endl;
  return oCir->getOne(); 
}

meowDGConst::meowDGConst(unsigned id, vector<int>& idList):meowDGNode(id, idList){
  setType( NODE_CONST);
}
meowAIGNode* meowDGConst::constructUpdateCir(meowAIG* uCir,
                                             set<meowDGNode*>& visited,                                             int depth){
  // build 
  meowAIGNode* const0 = uCir->getZero();
  meowAIGNode* zConst0 = uCir->addFF(const0, 0, 1); // Z(const0)
  return zConst0; 
}
meowAIGNode* meowDGConst::constructObserveCir( meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source){
  cerr<<"ERROR DGConst should not be called for observable"<<endl;
  return oCir->getOne(); 

}
meowAIGNode* meowDGConst::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
  cerr<<"ERROR DGConst should not be called for observable"<<endl;
  return oCir->getOne(); 


}
meowDGPO::meowDGPO(unsigned id, vector<int>& idList):meowDGNode(id, idList){
  setType(NODE_PO); 
}
meowAIGNode* meowDGPO::constructUpdateCir(meowAIG* uCir, 
                                          set<meowDGNode*>& visited,
                                          int depth){
  cerr<<"PO updating? This should never be called"<<endl;
  return uCir->getZero();
}
meowAIGNode*  meowDGPO::constructObserveCir( meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source){
  return oCir->getOne();
}
meowAIGNode* meowDGPO::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
  return oCir->getOne();
}
meowDGFF::meowDGFF(unsigned id, vector<int>& idList):meowDGNode(id, idList){
  setType( NODE_FF);
}
meowAIGNode* meowDGFF::constructUpdateCir(meowAIG* uCir, 
                                          set<meowDGNode*>& visited,
                                          int depth){
  if(depth == 1)
    return uCir->getOne(); // reached limit
  if(visited.find(this)!= visited.end()) // sequential cycle
    return uCir->getOne();
  // 
  visited.insert(this);
  meowAIGNode* uInput = uCir->getZero();
  set<meowDGNode*>& inputs = getInput();
  set<meowDGNode*>::iterator site = inputs.begin();
  for(; site!= inputs.end(); ++site){
    meowAIGNode* subInput = (*site)->constructUpdateCir(uCir,
                                                         visited, 
                                                         depth-1);
    uInput = uCir->addAND(uInput, 1, subInput, 1, 1); // use OR 
  }
  // add Z
  meowAIGNode* zUInput = uCir->addFF(uInput, 0, 1); // Z(U) 
  // if uInput = true, it will handle it naturally
  return zUInput;
  // Z( or U in)
}
meowAIGNode* meowDGFF::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
  if(depth == 0) // we are formulating input's of FF based on output
    return oCir->getOne();
  if(visited.find(this)!= visited.end())
    return oCir->getOne();

  visited.insert(this);
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->formulateObserve(oCir, 
                                                     visited,
                                                     depth-1,
                                                     extraProperties,
                                                     this);
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == oCir->getOne())
      return targetO;
  }
  // create zX->X(targetO)
  meowAIGNode* zX = oCir->addExtraPI();
  // create FailX
  meowAIGNode* ZFalse = oCir->addFF( oCir->getZero(), 0, 1);
  meowAIGNode* YzX = oCir->addFF(zX, 0, 0);
  meowAIGNode* negZAndY = oCir->addAND(ZFalse, 1, YzX, 0, 0);
  meowAIGNode* failX = oCir->addAND(negZAndY, 0, targetO, 1, 0);
  extraProperties.insert(oCir->neg(failX)); // assert!
  return zX;
}

meowAIGNode* meowDGFF::constructObserveCir(meowAIG* oCir,
                                     set<meowDGNode*>& visited,
                                     int depth,
                                     meowDGNode* source){
  // next here...
  if(depth == 0)
    return oCir->getOne();
  if(visited.find(this)!= visited.end())
    return oCir->getOne();

  visited.insert(this);
  // collect Outputs
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    //cerr<<"find Observable of"<<(*site)->getID()<<endl;
    meowAIGNode* outputO = (*site)->constructObserveCir(oCir, 
                                                       visited,
                                                        depth-1,
                                                        this);
   // if(outputO == oCir->getOne())
   //   cerr<<"this one is const 1"<<endl;
   // cerr<<"get:"<<outputO<<endl;
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == oCir->getOne()){
      //cerr<<"result one?!"<<endl;
      return targetO;

    }
  }
  //cerr<<"get Non const observable?!"<<endl;
  // targetO is not a constant!! we need to put "X"
 // set<int> supportList;
 // oCir->getSupports(targetO, supportList);

 // set<int> furtherList; // how to get this?
 // oCir->getFurtherList(supportList, furtherList);
  // Note: observable case only result combinational meowAIG
  meowAIGNode* XtargetO = oCir->addNext(targetO);
  return XtargetO;
}
meowDGTransBlock::meowDGTransBlock(unsigned id, vector<int>& idList):meowDGNode(id, idList){
  setType(NODE_TRANS);
}
 meowAIGNode* meowDGTransBlock::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->formulateObserve(oCir, 
                                                       visited,
                                                        depth,
                                                 extraProperties, this);
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
  }

   meowAIGNode* selNode = oCir->addPI(_selID);    
   meowAIGNode* final = NULL;
   if(source == _input0){ // add neg _selID
     final = oCir->addAND(selNode, 1, targetO, 0, 0); 
   }
   else{
     final = oCir->addAND(selNode, 0, targetO, 0, 0);
   }
   return final;
}

meowAIGNode* meowDGTransBlock::constructUpdateCir(meowAIG* uCir,
                    set<meowDGNode*>& visited, int depth){
  meowAIGNode* uInput0 = _input0->constructUpdateCir(uCir, visited,
                                                     depth);
  meowAIGNode* uInput1 = _input1->constructUpdateCir(uCir, visited, 
                                                     depth);
  meowAIGNode* selNode = uCir->addPI(_selID); // _sel must be positive
  
  // case 0
  meowAIGNode* case0 = uCir->addAND(selNode, 0, uInput1, 0, 0);
  meowAIGNode* case1 = uCir->addAND(selNode, 1, uInput0, 0, 0);
  
  // case 2, different
  meowAIGNode* ySel = uCir->addFF(selNode, 0, 0);
  meowAIGNode* case2 = uCir->addEQ(selNode, ySel, 1); // neg

  meowAIGNode* orCase = uCir->addAND(case0, 1, case1, 1, 1);
  meowAIGNode* orCase2 = uCir->addAND(orCase,1, case2, 1, 1);
  // or all of them together!
  return orCase2;
}
meowAIGNode* meowDGTransBlock::constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source
){
  // find O(out) first
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->constructObserveCir(oCir, 
                                                       visited,
                                                        depth,
                                                        this);
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
  }
  if(_input0 == _input1) // go directly
    return targetO;
  //cerr<<"try trans: "<<this->getID()<<endl;
  return targetO; // don't use select
   meowAIGNode* selNode = oCir->addPI(_selID);    
   meowAIGNode* final = NULL;
   if(source == _input0){ // add neg _selID
     final = oCir->addAND(selNode, 1, targetO, 0, 0); 
   }
   else{
     final = oCir->addAND(selNode, 0, targetO, 0, 0);
   }
   return final;
}
void meowDGTransBlock::reviseSel(map<int,int>& old2newID){
  //updateGateID(old2newID);
  if(_selID > 0)
    _selID = old2newID[_selID];
  else
    _selID = -1*(old2newID[abs(_selID)]);
}

void meowDGTransBlock::addSelect(int& sel){
  _selID = sel;
}
meowDGCombCloud::meowDGCombCloud(unsigned id, vector<int>& idList):meowDGNode(id, idList){

}
meowAIGNode* meowDGCombCloud::constructUpdateCir(meowAIG* uCir, 
              set<meowDGNode*>& visited, int depth){
  set<meowDGNode*>& inputs = getInput();
  set<meowDGNode*>::iterator site = inputs.begin();
  meowAIGNode* uInput = uCir->getZero();
  for(; site!= inputs.end(); ++site){
    meowAIGNode* subInput = (*site)->constructUpdateCir(uCir,
                                                         visited, 
                                                         depth);
    uInput = uCir->addAND(uInput, 1, subInput, 1, 1); 
  }
  return uInput;
}
meowAIGNode* meowDGCombCloud::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->formulateObserve(oCir, 
                                                 visited,
                                                 depth,
                                                 extraProperties,
                                                 this);
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == oCir->getOne())
      return targetO;
  }
  return targetO;
}
meowAIGNode* meowDGCombCloud::constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source
){
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->constructObserveCir(oCir, 
                                                       visited,
                                                        depth,
                                                        this);
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == oCir->getOne())
      return targetO;
  }
  return targetO;
} 
// I don't think we have this node anymore@@?
meowDGGatedFF::meowDGGatedFF(unsigned id, vector<int>& idList):meowDGNode(id, idList){
  setType(NODE_GATED);
  _revised = false;
}
void meowDGGatedFF::addControlID(int newControl){ // for revised
  _revised = true;
  _controlIDs.push_back(newControl);

}
void meowDGGatedFF::reviseControl(map<int, int>& old2newID){
  //cerr<<"Revise?!"<<endl;
  for(int i = 0; i < _controlIDs.size(); i++){
    if(_controlIDs[i] > 0)
      _controlIDs[i] = old2newID[_controlIDs[i]];
    else
      _controlIDs[i] = -1*(old2newID[abs(_controlIDs[i])]);
  }
}
meowAIGNode* meowDGGatedFF::constructUpdateCir(meowAIG* uCir,
                     set<meowDGNode*>& visited, int depth){
  if(depth == 1)
    return uCir->getOne();
  if(visited.find(this)!= visited.end())
    return uCir->getOne();
//  cerr<<"try "<<getID()<<endl;
  visited.insert(this);
  if(_revised){ // no need for exploring inputs
    meowAIGNode* en = uCir->getOne();
    for(int i = 0; i < _controlIDs.size(); ++i){
      meowAIGNode* selNode = uCir->addPI(_controlIDs[i]);
      en = uCir->addAND(selNode, 0, en, 0, 0);
    }
    meowAIGNode* ZU = uCir->addFF(en, 0, 1);
    return ZU;
  }
  // there is only one input!
  meowDGNode* inputNode = *(getInput().begin());
  meowAIGNode* uInput = inputNode->constructUpdateCir(uCir, 
                                                      visited,
                                                      depth-1);
  // formulated "en"
  meowAIGNode* en = uCir->getOne();
  for(int i = 0; i < _controlIDs.size(); ++i){
    //cerr<<"control? "<<_controlIDs[i]<<endl;
    meowAIGNode* selNode = uCir->addPI(_controlIDs[i]);
    en = uCir->addAND(selNode, 0, en, 0, 0);
  }
  meowAIGNode* a = uCir->neg(en); // -en
  meowAIGNode* b =  uCir->addAND(uInput, 0, en, 1, 0); // U& - en
  meowAIGNode* aSb = uCir->addSince(a, b);
  meowAIGNode* Ys = uCir->addFF(aSb, 0, 0);
  meowAIGNode* UorYs = uCir->addAND(uInput, 1, Ys, 1, 1);
  meowAIGNode* enANDU = uCir->addAND(en, 0, UorYs, 0, 0);
  meowAIGNode* ZU = uCir->addFF(enANDU, 0, 1);
  return ZU;
  // now we have en and Uin
  // create S!!! 
}
meowAIGNode* meowDGGatedFF::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
//  cerr<<"run: "<<this->getID()<<endl;
  if(depth == 0)
    return oCir->getOne();
  if(visited.find(this)!= visited.end())
    return oCir->getOne();
  visited.insert(this);
 // formulate O(out) first

  // TODO if visited?
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->formulateObserve(oCir, 
                                                     visited,
                                                     depth-1,
                                                     extraProperties,
                                                     this);
//    cerr<<"get OutputO!"<<endl;
//   (oCir->getRegular(outputO))->printNode(); 
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
  }
  /*cerr<<"target O = "<<endl;
  (oCir->getRegular(targetO))->printNode();*/
  // if targetO == true
  meowAIGNode* enableNew = oCir->getOne();
  for(int i = 0; i < _controlIDs.size(); ++i){
    meowAIGNode* controlNode = oCir->addPI(_controlIDs[i]);
    enableNew = oCir->addAND(enableNew, 0, controlNode, 0, 0);
  }
  //cerr<<"get enableNew!"<<endl;
  //(oCir->getRegular(enableNew))->printNode(); 
  
  meowAIGNode* enableOld = oCir->getOne();
  if (source == this){
    vector<int>* oldControl = oCir->getOldControl();
    for(int i = 0; i < oldControl->size(); ++i){
      meowAIGNode* controlNode = oCir->addPI((*oldControl)[i]);
      enableOld = oCir->addAND(enableOld, 0, controlNode, 0, 0);
    }// use en_old saved in oCir
  }
  else
    enableOld = enableNew;  
  
//  cerr<<"get enableOld!"<<endl;
//  (oCir->getRegular(enableOld))->printNode(); 
  

  if(targetO == oCir->getOne()){
    //cerr<<"targetO is One"<<endl;
    return enableOld;

  }
    // return en_old directly, no need to check extraProperties

  
 
  meowAIGNode* zX = oCir->addExtraPI(); // z0 -> X(out)
  // create FailX
  meowAIGNode* ZFalse = oCir->addFF( oCir->getZero(), 0, 1);
  meowAIGNode* YzX = oCir->addFF(zX, 0, 0);
  meowAIGNode* negZAndY = oCir->addAND(ZFalse, 1, YzX, 0, 0);
  meowAIGNode* failX = oCir->addAND(negZAndY, 0, targetO, 1, 0);
  extraProperties.insert(failX); 
 /* cerr<<"make failX "<<failX<<endl;
  (oCir->getRegular(failX))->printNode(); 
  oCir->printAIG();
*/
  // done with z0
  meowAIGNode* zR = oCir->addExtraPI(); // z2
    // z2 -> z0 R neg(enableNew)
  // create pendingR
  meowAIGNode* YpendingR = oCir->addFF(0); // set fanin later
  meowAIGNode* z2OR = oCir->addAND(YpendingR, 1, zR, 1, 1);
  meowAIGNode* negz0ANDOR = oCir->addAND(zX, 1, z2OR, 0, 0);
  YpendingR->setFanin0(negz0ANDOR, 0);
  meowAIGNode* failR = oCir->addAND(enableNew, 0, z2OR, 0, 0);
  meowAIGNode* failR2 = oCir->addAND(failR, 1, ZFalse, 1, 1);
 // extraProperties.insert(failR2);
  
 /* cerr<<"make failR "<<failR<<endl;
  (oCir->getRegular(failR))->printNode(); 
  oCir->printAIG();
*/


  meowAIGNode* zX1 = oCir->addExtraPI(); //z1->XzR
  meowAIGNode* YzX1 = oCir->addFF(zX1, 0, 0);
  meowAIGNode* negZAndY1 = oCir->addAND(ZFalse, 1, YzX1, 0, 0);
  meowAIGNode* failX1 = oCir->addAND(negZAndY1, 0, zR, 1, 0); 
//  extraProperties.insert(failX1);
 
  /*cerr<<"make failX1 "<<failX1<<endl;
  (oCir->getRegular(failX1))->printNode(); 
  oCir->printAIG();
*/

  meowAIGNode* orCase = oCir->addAND(zX, 1, zX, 1, 1);
  meowAIGNode* final = oCir->addAND(enableOld, 0, orCase, 0, 0);
 // cerr<<"orCase:"<<orCase<<endl;
 // cerr<<"final:"<<final<<endl;
  return final;
  // finally, return enable & (z0 | z1)
}
meowAIGNode* meowDGGatedFF::constructObserveCirSpecial(
                                    meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source){

  visited.insert(this);
  // collect Outputs
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    //cerr<<"find Observable of"<<(*site)->getID()<<endl;
    meowAIGNode* outputO = (*site)->constructObserveCir(oCir, 
                                                       visited,
                                                        depth-1,
                                                        this);
  /*  if(outputO == oCir->getOne())
      cerr<<"this one is const 1"<<endl;
    cerr<<"get:"<<outputO<<endl;*/
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == oCir->getOne()){
      //cerr<<"result one?!"<<endl;
      return targetO;

    }
  }
 // cerr<<"get Non const observable?!"<<endl;
  // targetO is not a constant!! we need to put "X"
/*  set<int> supportList;
  oCir->getSupports(targetO, supportList);
 
  set<int> furtherList; // how to get this?
  oCir->getFurtherList(supportList, furtherList);*/
  // Note: observable case only result combinational meowAIG
  meowAIGNode* XtargetO = oCir->addNext(targetO);
  return XtargetO;
}
meowAIGNode* meowDGGatedFF::constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source
){
 // cerr<<"Hello?"<<endl;
  // observability for input of FF
  if(depth == 0)
    return oCir->getOne();
  if(visited.find(this)!= visited.end())
    return oCir->getOne();
  // for gatedFF, just _controlIDs = 1
 // cerr<<"work on "<<this->getID()<<endl;
  meowAIGNode* targetO = oCir->getOne();
  for(int i = 0; i < _controlIDs.size(); ++i){
  //  cerr<<"control ID?"<<_controlIDs[i]<<endl;
    meowAIGNode* controlNode = oCir->addPI(_controlIDs[i]);
    targetO = oCir->addAND(targetO, 0, controlNode, 0, 0);
  } 
//  cerr<<"return control"<<targetO<<endl;
  return targetO;
  // collect Outputs
}
void meowDGGatedFF::addControlIDs(vector<int>& controls){
  //cerr<<"this is"<<this->getID()<<endl;
  for(int i = 0; i < controls.size(); ++i){
    _controlIDs.push_back(controls[i]);
   // cerr<<"add Control "<<controls[i]<<endl;
  }
}
meowDGInternal::meowDGInternal(unsigned id, vector<int>& idList):meowDGNode(id, idList){
  setType( NODE_INTERNAL);
}
meowAIGNode* meowDGInternal::constructUpdateCir(meowAIG* uCir,
                         set<meowDGNode*>& visited, int depth){
  set<meowDGNode*>& inputs = getInput();
  meowAIGNode* uInput = uCir->getZero();
  set<meowDGNode*>::iterator site = inputs.begin();
//  cerr<<"Access Node"<<this->getID()<<endl;
  for(; site!= inputs.end(); ++site){
    meowAIGNode* subInput = (*site)->constructUpdateCir(uCir,
                                                         visited, 
                                                         depth);
    uInput = uCir->addAND(uInput, 1, subInput, 1, 1); 
  }
  return uInput;

}
meowAIGNode* meowDGInternal::formulateObserve(meowAIG* oCir,
                           set<meowDGNode*>& visited,
                           int depth,
                           set<meowAIGNode*>& extraProperties,
                           meowDGNode* source
                           ){
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->formulateObserve(oCir, 
                                                       visited,
                                                        depth,
                                                 extraProperties,
                                                 this);
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == oCir->getOne())
      return targetO;
  }
  return targetO;
}

meowAIGNode* meowDGInternal::constructObserveCir(meowAIG* oCir,
                                    set<meowDGNode*>& visited,
                                    int depth, 
                                    meowDGNode* source
){
  meowAIGNode* targetO = oCir->getZero();
  set<meowDGNode*>& outputNodes = getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    meowAIGNode* outputO = (*site)->constructObserveCir(oCir, 
                                                       visited,
                                                        depth,
                                                        this);
    //cerr<<"Internal get"<<outputO<<endl;
    targetO = oCir->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == oCir->getOne())
      return targetO;
  }
  //cerr<<"Internal return"<<targetO<<endl;
  return targetO;
}
ABC_NAMESPACE_IMPL_END
