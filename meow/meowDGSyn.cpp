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
#include "ext/meow/meowDGSyn.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START

void meowUsageDGSyn(){
  Abc_Print( -2, "usage: meowDGSyn -G <aig file> -F <filename> -d <depth> is for reducing clock-gating conditions on the current GIA\n" );
  Abc_Print(-2, "meowDGSyn -F <filename> -d <depth> [-g] is for performing synthesis on the current GIA\n");
  Abc_Print( -2, "\t -h    : print the command usage\n");
  Abc_Print( -2, "\t -d <depth> : depth for constructing conditions\n");
  Abc_Print( -2, "\t -g: toggle to run greedy synthesis algorithm\n");
  Abc_Print( -2, "\t -D <file.dot>: draw DG directly\n");
  Abc_Print( -2, "\t -F <filename>   : write out synthesized aig to <filename>\n");
  Abc_Print( -2, "\t -G <aig file>   : use <aig file> as golden to remove clock-gating, if not specified, add clock-gating\n");


}
meowDGSyn::meowDGSyn(Gia_Man_t* cir, int depth, int greedy){
  _currentCir = cir;
  _greedy = greedy;
//  _transAPI = new meowDGTrans(cir); // recognize transparent here
  _DG = NULL;
  _reducedNum = 0;
  _gatedNum = 0;
  _depth = depth; // set as a parameter from commandline
}
meowDGSyn::~meowDGSyn(){
//  delete _transAPI;
  Gia_ManStop(_currentCir); // it can be replaced
  if(_DG)
    delete _DG; 
}
void meowDGSyn::createGatedFFs(Gia_Man_t* cir, meowDG* DG, meowDGTrans* transAPI){
  vector<vector<int> > inputs;
  vector<vector<int> > outputs;
  vector<vector<int> > controls;

  transAPI->getGatedFFs(inputs, outputs, controls); //==> put to meowDG
  for(int i = 0; i < inputs.size(); ++i){
    // add Nodes for inputs and outputs
    meowDGNode* newNode = DG->addNode(NODE_GATED, outputs[i]);
    DG->addNode2Inputs(newNode, inputs[i]); // add for phase
    dynamic_cast<meowDGGatedFF*>(newNode)->addControlIDs(controls[i]);
    // keep inputs with phase in DG...
    if(!DG->createdBefore(inputs[i]))
      addInputNode(inputs[i], cir, DG); // remove sign inside 
          
    meowDGNode* inputNode = DG->getNode(abs(inputs[i][0]));
    newNode->addInput(inputNode);
    inputNode->addOutput(newNode);
    // finally add faninNode
  }
}
void meowDGSyn::createPiPo( Gia_Man_t* cir, meowDG* DG){
  vector<int> piList;
  Gia_Obj_t* pObj;
  int i;
  Gia_ManForEachPi(cir, pObj, i)
    piList.push_back(Gia_ObjId(cir, pObj));
  DG->addNode(NODE_PI, piList);

  vector<int> poList;
  Gia_ManForEachPo(cir, pObj, i)
    poList.push_back(Gia_ObjId(cir, pObj ));
  DG->addNode(NODE_PO, poList);
   
}
void meowDGSyn::addInputNode(vector<int>& inputs, Gia_Man_t* cir,
                             meowDG* DG){
  vector<int> absInputs;
  for(int i = 0; i < inputs.size(); ++i)
    absInputs.push_back(abs(inputs[i]));

  Gia_Obj_t* pInput = Gia_ManObj(cir, absInputs[0]);
  if(Gia_ObjIsPi(cir, pInput)) // this should never happen
    DG->addNode(NODE_PI, absInputs);
  else if(Gia_ObjIsCi(pInput)) // take Ro ids, not Ri
    DG->addNode(NODE_FF, absInputs);
  else
    DG->addNode(NODE_INTERNAL, absInputs);
}
void meowDGSyn::createTrans(Gia_Man_t* cir, meowDG* DG, meowDGTrans* transAPI){
  vector<vector<int> > input0s;
  vector<vector<int> > input1s;
  vector<vector<int> > outputs;
  vector<int> controls;
  transAPI->getOtherTrans( input0s, input1s, outputs, controls);
  for(int i = 0; i < outputs.size(); ++i){
    meowDGNode* newNode = DG->addNode(NODE_TRANS, outputs[i]);
    dynamic_cast<meowDGTransBlock*>(newNode)->addSelect(controls[i]);
    if(!DG->createdBefore(input0s[i]))
      addInputNode(input0s[i], cir, DG);
    if(!DG->createdBefore(input1s[i]))
      addInputNode(input1s[i], cir, DG);
    meowDGNode* inputNode0 = DG->getNode(input0s[i][0]);
    meowDGNode* inputNode1 = DG->getNode(input1s[i][0]);
    dynamic_cast<meowDGTransBlock*>(newNode)->setInput0(inputNode0);
    dynamic_cast<meowDGTransBlock*>(newNode)->setInput1(inputNode1);
    inputNode0->addOutput(newNode);
    inputNode1->addOutput(newNode);
  }
  // create!
}
void meowDGSyn::findFaninWordsRecur(int gateID, Gia_Man_t* cir, 
                      meowDG* DG, map<int, set<int> >& faninWords){
  if(faninWords.find(gateID)!= faninWords.end())
    return;
  if(gateID == 0){ // constant
    //cerr<<"constant?"<<endl;
    return;
  }
  if(DG->getNode(gateID)!= NULL){
    //cerr<<"reach node?"<<_DG->getNode(gateID)->getID()<<endl;
    set<int> newList;
    newList.insert(DG->getNode(gateID)->getID()*(-1));
    // PI has been covered
    faninWords[gateID] = newList;
    return;
  }
  Gia_Obj_t* pObj = Gia_ManObj(cir, gateID);
  if(Gia_ObjIsRo(cir, pObj)){
    set<int> newList;
    newList.insert(gateID);
    faninWords[gateID] = newList;
    return;
  }
  if(Gia_ObjIsRi(cir, pObj)){
    int faninID0 = Gia_ObjFaninId0( pObj, gateID );
    
    findFaninWordsRecur(faninID0, cir, DG, faninWords);
    set<int> newList;
    newList.insert(faninWords[faninID0].begin(), 
                   faninWords[faninID0].end());
    faninWords[gateID] = newList;
    return;
  } 
  assert(Gia_ObjIsAnd(pObj));
  int faninID0 = Gia_ObjFaninId0( pObj, gateID );
  int faninID1 = Gia_ObjFaninId1( pObj, gateID );
  findFaninWordsRecur(faninID0, cir, DG, faninWords);
  findFaninWordsRecur(faninID1, cir, DG, faninWords);
  set<int> newList;
  newList.insert(faninWords[faninID0].begin(), 
                 faninWords[faninID0].end());
  newList.insert(faninWords[faninID1].begin(), 
                 faninWords[faninID1].end()); 
  faninWords[gateID] = newList;
}
void meowDGSyn::findFanoutWordsRecur(int gateID, Gia_Man_t* cir,
                        meowDG* DG, map<int, set<int> >& fanoutWords){
  if(fanoutWords.find(gateID)!= fanoutWords.end())
    return;
  if(DG->getNode(gateID) != NULL){
    set<int> newList;
    newList.insert(DG->getNode(gateID)->getID()*(-1));
    fanoutWords[gateID] = newList;
    return;
  }
  Gia_Obj_t* pObj = Gia_ManObj(cir, gateID);
  if(Gia_ObjIsRi(cir, pObj)){

    set<int> newList;
    Gia_Obj_t* pRo = Gia_ObjRiToRo(cir, pObj);
    int RoID = Gia_ObjId(cir, pRo);
    if(DG->getNode(RoID)!= NULL)
      newList.insert(DG->getNode(RoID)->getID()*(-1));
    else
      newList.insert(RoID);
    
    fanoutWords[gateID] = newList;
    return;
  }
  Gia_Obj_t* pFanout;
  int j;
  set<int> newList;
  Gia_ObjForEachFanoutStatic(cir, pObj, pFanout, j){
    int fanoutID = Gia_ObjId(cir, pFanout); 
    findFanoutWordsRecur(fanoutID, cir, DG, fanoutWords);
    newList.insert(fanoutWords[fanoutID].begin(),
                   fanoutWords[fanoutID].end());
  }
  fanoutWords[gateID] = newList;
  // TOOD
}
void meowDGSyn::mergedByMap(set<int>& FFList, 
                            map<int, set<int> >& id2List, meowDG* DG){
  map<int, int> node2NewID;
  bool finished = false;
  while(!finished){
    finished = true;
    map<string, vector<int> > io2IDs;
    set<int>::iterator site = FFList.begin();
    for(; site != FFList.end(); ++site){
      ostringstream Convert;
      set<int> sList = id2List[*site];
      set<int>::iterator site2 = sList.begin();
      bool hasBits = false;
      set<int> realList;
      for(; site2 != sList.end(); ++site2){
        if(node2NewID.find(*site2)!= node2NewID.end()) // merged!
          realList.insert(node2NewID[*site2]);
        else
          realList.insert(*site2);
      }
      site2 = realList.begin();
      for(; site2 != realList.end(); ++site2){
        Convert<<"&"<<(*site2);
        if(*site2 > 0)
          hasBits = true;
      } // note: the order might be an issue
      string token = Convert.str();
      if(hasBits)
        continue;
     // cerr<<"test token "<<token<<endl;
      if(io2IDs.find(token) == io2IDs.end()){
        vector<int> newVec;
        io2IDs[token] = newVec;
      }
      io2IDs[token].push_back(*site);
    }
    // done with ioMap
    map<string, vector<int> >::iterator mite = io2IDs.begin();
    for(; mite!= io2IDs.end(); ++mite){
      if((mite->second).size() < 2) // single
        continue;
     // cerr<<"token: "<<mite->first<<endl;
      vector<int> nodeList = mite->second;
      meowDGNode* newNode =  DG->addNode(NODE_FF, nodeList);
      finished = false;
      for(int k = 0; k < nodeList.size(); ++k){
        FFList.erase(nodeList[k]);
        node2NewID[nodeList[k]] = (newNode->getID())*(-1);
      }
    }
  } // keep working until no new can be added

}
void meowDGSyn::createOthersInput(set<int>& FFList, Gia_Man_t* cir,
                                  meowDG* DG){
  
  map<int, set<int> > faninWords;// internal is included // reached
  //
  map<int, set<int> > faninWords2;
  Gia_Obj_t* pObj;

  set<int>::iterator site = FFList.begin();
  for(; site!= FFList.end(); ++site){
    pObj = Gia_ManObj(cir, *site);
    Gia_Obj_t* pRi = Gia_ObjRoToRi(cir, pObj );
    findFaninWordsRecur(Gia_ObjId(cir, pRi), cir, DG, faninWords);
   
    set<int> newList = faninWords[Gia_ObjId(cir, pRi)];
    faninWords2[*site] = newList;
    //cerr<<"number of inputs"<<newList.size()<<endl;
  }
  mergedByMap(FFList, faninWords2, DG);
}
void meowDGSyn::createOthersOutput(set<int>& FFList, Gia_Man_t* cir,
                                   meowDG* DG){
 // Gia_Obj_t* pObj;
  set<int>::iterator site = FFList.begin();
  map<int, set<int> > fanoutWords;
  for(; site!= FFList.end(); ++site)
    findFanoutWordsRecur(*site, cir, DG, fanoutWords);

  mergedByMap(FFList, fanoutWords, DG);

}
void meowDGSyn::createOthers(Gia_Man_t* cir, meowDG* DG, bool merge){
  // create all remaining FFs
  Gia_Obj_t* pObj;
  int i;
 //
  set<int> FFList;
  Gia_ManForEachRo(cir, pObj, i){
    int RoID = Gia_ObjId(cir, pObj);
    if(DG->getNode(RoID) == NULL ) // not covered
      FFList.insert(RoID);
  }
  if(merge){
    createOthersInput(FFList, cir, DG);
//  cerr<<"done with merge by inputs"<<endl;
//  _DG->reportNum();
    createOthersOutput(FFList, cir, DG);
//  cerr<<"done with merge by outputs"<<endl;
 // _DG->reportNum();
  }

  // all remaining FFs
  set<int>::iterator site = FFList.begin();
  for(; site != FFList.end(); ++site){
    vector<int> ffID;
    ffID.push_back(*site);
    DG->addNode(NODE_FF, ffID); 
  } 
}
void meowDGSyn::connect(Gia_Man_t* cir, meowDG* DG){
  // all nodes are there, backtraverse until reach _gate2Node
  // but Gated and Trans are done
  map<int, set<meowDGNode*> > id2Terminal;
  vector<meowDGNode*>& dgNodes = DG->getList();  
  map<int, meowDGNode*>& dgMap = DG->getMap();
  for(int i = 0; i < dgNodes.size(); ++i){
    NODE_TYPE targetType = dgNodes[i]->getType();
    if(targetType == NODE_GATED 
    || targetType == NODE_TRANS 
    || targetType == NODE_PI)
      continue;
    if(DG->isReplaced(dgNodes[i]))
      continue;
 //   cerr<<"Connect "<<i<<endl;
    vector<int>& gateIDs = dgNodes[i]->getGates();
    for(int j = 0; j < gateIDs.size(); ++j){
      // take back to
      Gia_Obj_t* pObj = Gia_ManObj(cir, gateIDs[j]) ;
      if( Gia_ObjIsRo(cir, pObj)){
        Gia_Obj_t* pRi =  Gia_ObjRoToRi(cir, pObj );
        connectNode(dgNodes[i], pRi, cir, dgMap,id2Terminal);
      
      }
      else if(Gia_ObjIsAnd(pObj)){
        Gia_Obj_t* pFanin0 = Gia_Regular(Gia_ObjFanin0(pObj));
        Gia_Obj_t* pFanin1 = Gia_Regular(Gia_ObjFanin1(pObj));
        connectNode(dgNodes[i], pFanin0, cir, dgMap, id2Terminal);
        connectNode(dgNodes[i], pFanin1, cir, dgMap, id2Terminal);
      }
      else{
        Gia_Obj_t* pFanin0 = Gia_Regular(Gia_ObjFanin0(pObj));
        connectNode(dgNodes[i], pFanin0, cir, dgMap, id2Terminal);
      }
    }
  }
}
void meowDGSyn::connectNode(meowDGNode* target, Gia_Obj_t* node,
                            Gia_Man_t* cir,
                            map<int, meowDGNode*>& dgMap, 
                            map<int, set<meowDGNode*> >& id2Terminal){
  // recursive

  // node: avoid combinational cycle
//  cerr<<node<<endl;
  int nodeId = Gia_ObjId(cir, node);
  if(id2Terminal.find(nodeId)!= id2Terminal.end()){
    set<meowDGNode*> terminals = id2Terminal[nodeId];
    set<meowDGNode*>::iterator site = terminals.begin();
    for(; site!= terminals.end(); ++site){
      if(isCombCycle(target, *site))
        continue;
      target->addInput(*site);
      (*site)->addOutput(target);
    }
    return; // explored
  }
  if(dgMap.find(nodeId)!= dgMap.end()){ // return!
    meowDGNode* input = dgMap[nodeId];
    if(!isCombCycle(target, input)){
      target->addInput(input);
      input->addOutput(target);
      set<meowDGNode*> terminals;
      terminals.insert(input);
      id2Terminal[nodeId] = terminals;
      return;
    }
  }
  if(Gia_ObjIsAnd(node)){
    Gia_Obj_t* pFanin0 = Gia_Regular(Gia_ObjFanin0(node));
    Gia_Obj_t* pFanin1 = Gia_Regular(Gia_ObjFanin1(node));
    connectNode(target, pFanin0, cir, dgMap, id2Terminal);
    connectNode(target, pFanin1, cir, dgMap, id2Terminal);
    set<meowDGNode*> terminals;
    int faninId0 = Gia_ObjId(cir, pFanin0);
    int faninId1 = Gia_ObjId(cir, pFanin1);
    terminals.insert(id2Terminal[faninId0].begin(),
                     id2Terminal[faninId0].end());
    terminals.insert(id2Terminal[faninId1].begin(),
                     id2Terminal[faninId1].end());
    id2Terminal[nodeId] = terminals;

  }
  else{
    Gia_Obj_t* pFanin0 = Gia_Regular(Gia_ObjFanin0(node));
    connectNode(target, pFanin0, cir, dgMap, id2Terminal);
    set<meowDGNode*> terminals;
    int faninId0 = Gia_ObjId(cir, pFanin0);
    terminals.insert(id2Terminal[faninId0].begin(),
                     id2Terminal[faninId0].end());
    id2Terminal[nodeId] = terminals;


  }
// keep tracking
}
meowDG* meowDGSyn::buildDG(Gia_Man_t* cir, bool merge){
  meowDGTrans*  transAPI = new meowDGTrans(cir);
  meowDG* newDG = new meowDG;
  createPiPo(cir, newDG); // there are only one NODE_PI and one NODe_PO
  createGatedFFs( cir, newDG, transAPI);
 // cerr<<"done with Gated"<<endl;
  createTrans(cir, newDG, transAPI);
//  cerr<<"done with Trans"<<endl;
 // _DG->reportNum();
  createOthers(cir, newDG, merge);
  connect(cir, newDG);
//  cerr<<"done with constructing DG!"<<endl;
  delete transAPI;

  return newDG;
  // build dependencies
}
void meowDGSyn::findControlMapping(Gia_Man_t* goldenCir,
                                   map<int, int>& G2RMap){
  Gia_ManFillValue(_currentCir); // R
  Gia_ManFillValue(goldenCir); //G
  
  Gia_Man_t * pNew;
  Gia_Obj_t * pObj; // G
  Gia_Obj_t* pObj2; //R
  int i;
  pNew = Gia_ManStart( Gia_ManObjNum(_currentCir) );
  Gia_ManHashAlloc(pNew); 

  Gia_ManConst0(_currentCir)->Value = 0;
  Gia_ManConst0(goldenCir)->Value = 0;
  // golden has fewer FF (Ci)
  Gia_ManForEachCi( goldenCir, pObj, i ){
    pObj->Value = Gia_ManAppendCi(pNew);
    pObj2 = Gia_ManCi(_currentCir, i);
    pObj2->Value = pObj->Value;
    G2RMap[Gia_ObjId(goldenCir, pObj)] = Gia_ObjId(_currentCir, pObj2);
  }
  Gia_ManForEachCi(_currentCir, pObj2, i){ // R has more Ci
    if(~pObj2->Value) // filled
      continue;
    pObj2->Value = Gia_ManAppendCi(pNew); // no mapping! 
  }
  map<int, int> value2GId; // G has this Value
  Gia_ManForEachAnd(goldenCir, pObj, i){
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj),
                                        Gia_ObjFanin1Copy(pObj) );
    value2GId[pObj->Value] = Gia_ObjId(goldenCir, pObj);
 
  }
  Gia_ManForEachAnd(_currentCir, pObj2, i){
    pObj2->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj2),
                                         Gia_ObjFanin1Copy(pObj2));
    if(value2GId.find(pObj2->Value)!= value2GId.end()) // hit
      G2RMap[value2GId[pObj2->Value]] = Gia_ObjId(_currentCir, pObj2);
  } 
  // done with G2RMap! 
}
bool meowDGSyn::checkVerificationTargetNode(meowDG* goldDG, 
                                            Gia_Man_t* goldenCir,
                                            map<int, int>& G2RId,
                                            meowDGNode* target){
  vector<int>& gateIds = target->getGates(); // all Ros
  //set<meowDGNode*> exploredFF;
  //for(int j = 0; j < gateIds.size(); ++j){
    /*
      ideally it should be from two cases: FF to gFF
       or gFF to gFF -> should have only one node

      no gating case: gFF to gFF with identical control
      here we could just check one gateID
    */
 // cerr<<"check: "<<target->getID()<<", r IDs = "<< gateIds[0]<<endl;
  int CiId = Gia_ManIdToCioId(_currentCir, gateIds[0]);
 // cerr<<"co ID??"<<CiId<<endl;
  int goldenID = Gia_ManCiIdToId( goldenCir, CiId ); // CoId  mapped
 // cerr<<"gold ID? "<<goldenID<<endl;
  meowDGNode* goldenNode = goldDG->getNode(goldenID);
  if(goldenNode == NULL){
    cerr<<"mismatch FF"<<endl;
    return false;
  }
 /* if(exploredFF.find(goldenNode)!= exploredFF.end())
      continue; // skip this Node, ideally will skip all after first
    exploredFF.insert(goldenNode);
*/
  if(goldenNode->getType() == NODE_FF) // must be gated
    return true;

   /* if(goldenNode->getWidth() != target->getWidth()) 
      return false;*/ 
    //if non FF and width is not matching -> possible, partially gated

  if(goldenNode->getType() == NODE_GATED){ // check controls
    vector<int>& controlIDs = dynamic_cast<meowDGGatedFF*>(target)->getControlIDs();
    vector<int>& goldenControl = dynamic_cast<meowDGGatedFF*>(goldenNode)->getControlIDs();
    
    if(controlIDs.size()!= goldenControl.size())
      return true; // must change something
        
    for(int k = 0; k < goldenControl.size(); ++k){ // G
      int control = abs(goldenControl[k]);
      bool Found2 = false;
      for(int l = 0; l < controlIDs.size(); ++l){ //R
        if( abs(controlIDs[l]) == G2RId[control]){
            Found2 = true; // same control found
            break;
          }
        }
        if(!Found2) // mismatched control, can be clock-gating
          return true; // in G but not in this R-FF (in fanin cone) 
      } // GatedFF case
    }
  else
    cerr<<" node type mismatching!"<<endl;
//  } // loop for each bit
  return false;
}
void meowDGSyn::findVerificationTarget(meowDG* goldDG, 
                                     Gia_Man_t* goldenCir, 
                                     map<int, int>& G2RId, 
                                     vector<meowDGNode*>& candidates){
  vector<meowDGNode*>& nodeList = _DG->getList();
  for(int i = 0; i < nodeList.size(); ++i){
    if(nodeList[i]->getType() != NODE_GATED)
      continue;
    if(checkVerificationTargetNode(goldDG,goldenCir,G2RId,nodeList[i]))
      candidates.push_back(nodeList[i]);
  } // i loop
}
void meowDGSyn::getOldNewEnable(meowDGNode* target, 
                                vector<int>& oldControl,
                                meowDG* goldDG,
                                Gia_Man_t* goldenCir,
                                map<int, int>& G2RId
                                ){
  vector<int>& gateIds = target->getGates(); // all Ros
  //vector<int>& controlIDs = dynamic_cast<meowDGGatedFF*>(target)->getControlIDs();

  int CiId = Gia_ManIdToCioId(_currentCir, gateIds[0]);
  // ok, we only takes one
  int goldenID = Gia_ManCiIdToId( goldenCir, CiId ); // CoId  mapped
  meowDGNode* goldenNode = goldDG->getNode(goldenID);
  if(goldenNode->getType() == NODE_FF )
    return;
  
  //
  vector<int>& goldenControl = dynamic_cast<meowDGGatedFF*>(goldenNode)->getControlIDs();
  for(int i = 0; i < goldenControl.size(); ++i){ // take from G to R
    int oldControlID = abs(goldenControl[i]);
    if(G2RId.find(oldControlID) == G2RId.end())
      cerr<<"cannot find this mapping"<<oldControlID<<endl;
    //cerr<<oldControlID<<" map to "<<G2RId[oldControlID]<<endl;
    if(goldenControl[i]> 0)
      oldControl.push_back(G2RId[oldControlID]);
    else
      oldControl.push_back(G2RId[oldControlID]*(-1));
  }
}
void meowDGSyn::verificationNode(meowDGNode* target, meowDG* goldDG,
                                 Gia_Man_t* goldenCir, 
                                 map<int, int>& G2RId){
  // we only work on all standard FFs  
  // or old width >= new Width it must be true by construction 
  vector<int> oldControl;
  getOldNewEnable(target, oldControl,
                  goldDG, goldenCir, G2RId);   

  // step 1, check old is up-to-date
  meowAIG* updating = new meowAIG(_currentCir); 
  meowAIGNode* targetU = getUpdatingCondition(updating, target);
  bool runSAT = false;
  if(oldControl.size() != 0){ // need to check
    if(isUpToDate(target, updating, targetU, oldControl))
      runSAT = true;
  }
  else
    runSAT = true;
  bool runObs = true;
  if(runSAT && targetU!=updating->getOne()){
    if(proveSATSynthesis(target, updating, targetU, oldControl)){
      runObs = false;
      reduceControl(target, oldControl, G2RId);
    }
  }
 
  delete updating;
  if(runObs){
    meowAIG* observable = new meowAIG(_currentCir);
   // cerr<<"Try observable verification!"<<endl;
    if(proveOBSSynthesisSimp(target, observable, oldControl)) {
     // cerr<<"reduce bits: "<<target->getWidth()<<endl;
      reduceControl(target, oldControl, G2RId);}
    delete observable;
  }
}
bool meowDGSyn::proveSATSynthesis(meowDGNode* target, meowAIG* cir,
                                  meowAIGNode* targetU, 
                                  vector<int>& oldControl){
  set<int> requiredFF;
  Gia_Man_t* pNew = provePreprocess(target, cir, oldControl,
                                    requiredFF);
  // prepare other signals
 // Gia_Obj_t * pObj;
  
  /*cir->printAIG(); 
  cerr<<"what is targetU?"<<targetU<<endl;
  (cir->getRegular(targetU))->printNode();*/
  int uSignalLit = cir->copy2Gia(pNew, targetU, 0);
  // we need enold' or en_new
  int en_old = createEnable(pNew, oldControl);
  int en_new = createEnable(pNew, dynamic_cast<meowDGGatedFF*>(target)->getControlIDs());
  //cerr<<"en_old"<<en_old<<endl; 
  //cerr<<"en_new?"<<en_new<<endl;
  // en_old^~en_ned 
  int enLit = Gia_ManHashAnd(pNew, en_old, en_new^1);
  int propertyLit = Gia_ManHashOr(pNew, enLit^1, uSignalLit^1);
  Gia_ManAppendCo(pNew,propertyLit^1); //<= this is assertion
//  cerr<<"perform SAT synthesis checking!"<<endl;
  return provePostProcess(pNew, cir, requiredFF);
}
int meowDGSyn::createEnable(Gia_Man_t* pNew, vector<int>& controls){
  int en = 1;
  Gia_Obj_t* pObj;
  for(int j = 0; j < controls.size(); ++j){
   // cerr<<"create enable of"<<controls[j]<<endl;
    pObj = Gia_ManObj(_currentCir, abs(controls[j]));
    pObj->Value = Gia_ObjCopy_rec(pNew, pObj);
    //cerr<<"Value is "<<pObj->Value<<endl;
    if(controls[j] < 0)
      en = Gia_ManHashAnd(pNew, en, (pObj->Value)^1);
    else
      en = Gia_ManHashAnd(pNew, en, pObj->Value); 
  } 
  // if nothing in controls -> enable1
  return en;
}
Gia_Man_t* meowDGSyn::preCopy(){
  Gia_Man_t * pNew;
  Gia_Obj_t * pObj;
  int i;
  pNew = Gia_ManStart( Gia_ManObjNum(_currentCir) );
  Gia_ManFillValue( _currentCir );
  Gia_ManHashAlloc(pNew); 
  pNew->pName = Abc_UtilStrsav( "property" );
 // pNew->pSpec = Abc_UtilStrsav( _currentCir->pSpec );
  Gia_ManConst0(_currentCir)->Value = 0;
  Gia_ManForEachCi( _currentCir, pObj, i )
    pObj->Value = Gia_ManAppendCi(pNew);
  
  Gia_ManForEachAnd( _currentCir, pObj, i ){
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj),
                                          Gia_ObjFanin1Copy(pObj) );
  }


  return pNew;
}
bool meowDGSyn::resolveXout(meowAIG* observable, meowAIGNode* Xout, meowDGNode* target, bool reverse){
  vector<int>& controls = dynamic_cast<meowDGGatedFF*>(target)->getControlIDs();
  Gia_Man_t * pNew = preCopy();
  Gia_Obj_t * pObj;
  int i;
  int XoutLit = observable->copy2Gia(pNew, Xout, 1);
 // cerr<<"XoutLit: "<<XoutLit<<endl;
  int controlLit = createEnable(pNew, controls);
 // cerr<<"controlLit: "<<controlLit<<endl;
  // add property Xout -> en_current ==>  Xout' or en_new
  int property = Gia_ManHashOr(pNew, XoutLit^1, controlLit);
  if(reverse){ 

  // reverse, prove en_current -> en_current&&Xout 
    int en_new = Gia_ManHashAnd(pNew, controlLit, XoutLit);
    property = Gia_ManHashOr(pNew, en_new, controlLit^1);
   // cerr<<"en_new "<<en_new<<" property "<<property<<endl;
  }
  //cerr<<"property: "<<property<<endl;
  Gia_ManAppendCo(pNew, property^1);
  Gia_ManForEachCo( _currentCir, pObj, i ){
    if(Gia_ObjIsRi(_currentCir, pObj))
      continue; // we don't want other POs...  
    pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
  }
  Gia_ManSetRegNum( pNew, Gia_ManRegNum(_currentCir));
  //cerr<<"Check U property"<<endl;
  return runPDR(pNew); // true: proved U is false
}
bool meowDGSyn::proveOBSSynthesisSimp(meowDGNode* target, meowAIG* observable, vector<int>& oldControl){

  //set<int> fullySupported;
//  collectFullySupports(fullySupported); // for X synthesis

  // target must be GatedFFs
  //  
  meowAIGNode* targetO = observable->getZero();
  set<meowDGNode*>& outputNodes = target->getOutput();
  set<meowDGNode*>::iterator site = outputNodes.begin();
 /* if(outputNodes.size() == 1)
    cerr<<"one fanout?"<<endl;*/
  for(; site!= outputNodes.end(); ++site){
    set<meowDGNode*> visited;
    //cerr<<"one fanout?"<<endl;
    meowAIGNode* outputO = (*site)->constructObserveCir(observable, 
                                                       visited,
                                                        _depth-1,
                                                 (*site));
    targetO = observable->addAND(targetO, 1, outputO, 1, 1);
    if(targetO == observable->getOne())
      break;
  }
  if(targetO == observable->getOne())
    return false; // no way to be obs-gated
  // target is a FF node, we need to check its X"O(out)" first 
  // step 1 construct X(O(out))
  /*cerr<<"Oout is not True"<<endl; 
  observable->getRegular(targetO)->printNode();*/
/*  set<int> supportList;
  observable->getSupports(targetO, supportList);

  set<int> furtherList; // how to get this?
  observable->getFurtherList(supportList, furtherList);*/
  // Note: observable case only result combinational meowAIG
  meowAIGNode* XtargetO = observable->addNext(targetO);
  // step 2: check if XtargetO -> en_new
  bool Uresult = resolveXout(observable, XtargetO, target, false);
 // cerr<<"run resolbe U"<<endl;
  // step 3: formualte final proof
  Gia_Man_t * pNew = preCopy();
  Gia_Obj_t * pObj;
  int i;

  int en_old = createEnable(pNew, oldControl);
  int en_new = createEnable(pNew, dynamic_cast<meowDGGatedFF*>(target)->getControlIDs() );
  
  int Oin = 0;
  if(Uresult){
    // U = false
    int XoutLit = observable->copy2Gia(pNew, XtargetO, 1);
    Oin = Gia_ManHashAnd(pNew, en_old, XoutLit);
    // O(in) = en_old & Xout
  } 
  else
    Oin = en_old;

 // cerr<<Oin<<endl;
  int enLit = Gia_ManHashAnd(pNew, en_old, en_new^1);
  // G(en_old&-en_new -> -Oin)
  int property = Gia_ManHashOr(pNew, Oin^1, enLit^1);
  //cerr<<"property: "<<property<<endl;
  Gia_ManAppendCo(pNew, property^1);
  Gia_ManForEachCo( _currentCir, pObj, i ){
    if(Gia_ObjIsRi(_currentCir, pObj))
      continue; // we don't want other POs...  
    pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
  }
  Gia_ManSetRegNum( pNew, Gia_ManRegNum(_currentCir));
 
  // step 3: check obs property
//  cerr<<"Check Obs property"<<endl;
  return runPDR(pNew);
}
void meowDGSyn::reduceControl(meowDGNode* target, 
                              vector<int>& oldControl,
                              map<int, int>& G2RId){
  // get R_inputData from _DG
  //remember to update ids in G2R and _DG
  _reducedNum += target->getWidth();  
  map<int, int> old2newID;
  //
  Gia_Man_t * pNew;
  Gia_Obj_t * pObj;
  int i;
  pNew = Gia_ManStart( Gia_ManObjNum(_currentCir) );
  Gia_ManFillValue( _currentCir );
  Gia_ManHashAlloc(pNew); 
  pNew->pName = Abc_UtilStrsav( _currentCir->pName );
  pNew->pSpec = Abc_UtilStrsav( _currentCir->pSpec );
  Gia_ManConst0(_currentCir)->Value = 0;
  Gia_ManForEachCi( _currentCir, pObj, i ){
    pObj->Value = Gia_ManAppendCi(pNew);
    add2IDMap(old2newID, pNew, pObj);
  }
  vector<int>& targetFFs = target->getGates();
  vector<int> inputDatas = _DG->getNode2Inputs(target); 
  set<int> targetRi;
  map<int, int> Ri2Data;
  map<int, int> Ri2InputValue;
  for(int j = 0; j < targetFFs.size(); ++j){
    //cerr<<"map FF"<<targetFFs[j]<<" to "<<inputDatas[j]<<endl;
    int Ri = Gia_ObjRoToRiId( _currentCir, targetFFs[j] );
    targetRi.insert(Ri);
    Ri2Data[Ri] = inputDatas[j]; // we need to check size of controls 
  }
  Gia_ManForEachAnd( _currentCir, pObj, i ){
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj),
                                        Gia_ObjFanin1Copy(pObj) );
    add2IDMap(old2newID, pNew, pObj);    
  }
  int enable = createEnable(pNew, oldControl);
 // cerr<<"enable is"<<enable<<endl;
  // then....when we do FF, change it directly if input is in targetRi
  Gia_ManForEachCo(_currentCir, pObj, i){
    int gateID = Gia_ObjId(_currentCir, pObj);
    if(targetRi.find(gateID)!= targetRi.end()){
      Gia_Obj_t* Ro = Gia_ObjRiToRo(_currentCir, pObj); 
      int faninID = abs(Ri2Data[gateID]); // get its value
      int faninValue = Gia_ManObj(_currentCir, faninID)->Value;
      if(Ri2Data[gateID] < 0)
        faninValue = faninValue^1;
      int regValue = Ro->Value;
      regValue^=1;  
     // cerr<<"faninValue = "<<faninValue<<", regValue = "<<regValue<<endl; 
      int select = Gia_ManHashAnd( pNew, enable, faninValue );
      int gated = Gia_ManHashAnd(pNew, enable^1, regValue);
      int result =  Gia_ManHashOr(pNew, select, gated);
      Ri2InputValue[gateID] = result^1; // add MUX
     // cerr<<"resultValue "<<result<<endl;
    }
  }
  Gia_ManForEachCo( _currentCir, pObj, i ){ 

    // put all Co now
    int gateID = Gia_ObjId(_currentCir, pObj);
    if(targetRi.find(gateID)== targetRi.end()){
      pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
      add2IDMap(old2newID, pNew, pObj);   /// we should not need this 
    }
    else //!!!! clock-gating!!!!!!!!!!!!!!!!!
      pObj->Value = Gia_ManAppendCo(pNew, Ri2InputValue[gateID]);
  }
  Gia_ManHashStop( pNew );
 
  Gia_ManDupRemapEquiv( pNew, _currentCir );
  // should we simplify again?
  Gia_ManSetRegNum( pNew, Gia_ManRegNum(_currentCir));
  assert( Gia_ManIsNormalized(pNew) );
  Gia_ManStop(_currentCir); // replace!
  _currentCir = pNew; 

  _DG->updateDGIDs(old2newID);
  
  int newControlID = enable >> 1;
  if(enable&1)
    newControlID *= (-1);

  _DG->reviseNodeReduce(target, newControlID);
  //  update G2RId with old2new
  map<int, int>::iterator mite = G2RId.begin();
  for(; mite!= G2RId.end(); ++mite){
    int oldR = mite->second;
    int newR = old2newID[oldR];
    mite->second = newR;
  }
}
meowAIGNode* meowDGSyn::getUpdatingCondition(meowAIG* updating, 
                                           meowDGNode* target){
  set<meowDGNode*> visited;
  set<meowDGNode*>& inputNodes = target->getInput();
  set<meowDGNode*>::iterator site = inputNodes.begin();
  meowAIGNode* targetU = updating->getZero();
  for(; site!= inputNodes.end(); ++site){ 
    meowAIGNode* inputU = (*site)->constructUpdateCir(updating, 
                                                      visited, _depth); 
    targetU = updating->addAND(targetU, 1, inputU, 1, 1); 
    // OR together
  }
  /*vector<int>& reviseControl = dynamic_cast<meowDGGatedFF*>(target)->getControlIDs();
  cerr<<"check reviseControl == "<<reviseControl[0]<<endl;
   */
  return targetU;
}
void meowDGSyn::performReduce(){
  if(_DG == NULL)
    _DG = buildDG(_currentCir, true); // merge
}
void meowDGSyn::orderCandidates(vector<meowDGNode*>& candidates){
  vector<pair<int, meowDGNode*> > max_node;
  for(int i = 0; i < candidates.size(); ++i){
    max_node.push_back(pair<int, meowDGNode*>(
                            candidates[i]->getMaxGateID(),
                            candidates[i]));

  }
  sort(max_node.begin(), max_node.end());
  candidates.clear();
  for(int i = max_node.size()-1; i >=0; --i)
    candidates.push_back(max_node[i].second);
}
void meowDGSyn::performVerification(Gia_Man_t* goldenCir){
  if(_DG == NULL)
    _DG = buildDG(_currentCir, false);
  meowDG* goldDG = buildDG(goldenCir, false);
  // step 1, use structure hashing to find mapped controls
  // control in golden -> control in current 
  map<int, int> G2RId;
  findControlMapping(goldenCir, G2RId); // done with id Mapping!
  vector<meowDGNode*> candidates;
  findVerificationTarget(goldDG, goldenCir, G2RId, candidates);
  orderCandidates(candidates); // reverse topo order 
  for(int i = 0; i < candidates.size(); ++i){
    //cerr<<"Verification on: "<<candidates[i]->getID()<< "DG Nodes."<<endl;
    verificationNode(candidates[i], goldDG, goldenCir, G2RId);

  }
  cerr<<"Reduce "<< _reducedNum << "FFs."<<endl; 
  delete goldDG;
}
void meowDGSyn::drawGraph(char* fileName){
  _DG = buildDG(_currentCir, true);
  _DG->drawGraph(fileName, true);
}
void meowDGSyn::performSynthesis(){
  //  transparency has been found
  if(_DG == NULL)
    _DG =  buildDG(_currentCir, true); // build DG for the current circuit 
 
  // step 2  SAT synthesis
  vector<meowDGNode*> candidates;
  _DG->getUpdatingOrder(candidates);
  orderCandidates(candidates); // big to small
  // updating condition first
  for(int i = candidates.size()-1; i >= 0; --i){ // topological order
    satSynthesis(candidates[i]); 
  }
//  _DG->drawGraph();

  cerr<<"Perform Synthesis."<<endl; 

  candidates.clear();

  _DG->getObserveOrder(candidates);
  orderCandidates(candidates); // reverse topological order
  for(int i = 0; i < candidates.size(); ++i){
    if(candidates[i]->getType() == NODE_GATED){
      if(_greedy == 0)
        continue;
      obsSynthesisGreedy(candidates[i]);
    }
    else
      obsSynthesis(candidates[i]);

  }
  cerr<<"Gated FF numbers: "<<_gatedNum<<endl;
}
void meowDGSyn::collectFFRecur(Gia_Obj_t* current, set<int>& requiredFF,
                    int token){
  if(current == NULL)
    return;
  //cerr<<"Hello?"<<Gia_ObjId(_currentCir, current)<<endl;
  if(current->Value == token)
    return;
  current->Value = token;

  if(Gia_ObjIsPi(_currentCir, current))
    return;
  if(Gia_ObjIsRo(_currentCir, current)){ // Ci
    int gateID = Gia_ObjId(_currentCir, current);
    //cerr<<"collect!"<<gateID<<endl;
    if(requiredFF.find(gateID)== requiredFF.end())
      requiredFF.insert(gateID);
    Gia_Obj_t* Ri = Gia_ObjRoToRi( _currentCir, current ); // Co
    collectFFRecur(Ri, requiredFF, token); 
  } //??!!??
  else{
    Gia_Obj_t* fanin1, *fanin2;
    fanin1 = Gia_ObjFanin0( current);    
    fanin2 = Gia_ObjFanin1( current); 
 
//  if(fanin1 != current)  
    if (fanin1 != Gia_ManConst0(_currentCir) ) 
      collectFFRecur( fanin1, requiredFF, token);
    if(!Gia_ObjIsCo(current))
      collectFFRecur( fanin2, requiredFF, token);
  }

}
void meowDGSyn::collectFF(meowDGNode* target, vector<int>& oldControl, meowAIG* cir, set<int>& requiredFF){

  // step 1, get all essential ids
  set<int> signals;
  cir->getSignals(signals);
//  cir->printAIG();
  for(int i = 0; i < oldControl.size(); ++i){
   // cerr<<"oldControl:"<<oldControl[i]<<endl;
    signals.insert(abs(oldControl[i]));

  }
  dynamic_cast<meowDGGatedFF*>(target)->getSignals(signals);
  Gia_ManFillValue(_currentCir);
  Gia_Obj_t* currentObj;
  set<int>::iterator site = signals.begin();
  for(; site!= signals.end(); ++site){
    currentObj = Gia_ManObj(_currentCir, *site);
   // cerr<<"Call collect for "<<*site<<endl;
    if( (*site) > 0)
      collectFFRecur(currentObj, requiredFF, 100);
  } // ideally this should go across all timeframes!!
}
int meowDGSyn::Gia_ObjCopy_rec(Gia_Man_t* pNew, Gia_Obj_t* current){
  // current is an object in _currentCir
  if(~current->Value)
    return current->Value;
 // cerr<<"current is"<<Gia_ObjId(_currentCir, current)<<endl;
  assert(Gia_ObjIsAnd(current));
  Gia_ObjCopy_rec(pNew, Gia_ObjFanin0(current));
  Gia_ObjCopy_rec(pNew, Gia_ObjFanin1(current));
  current->Value = Gia_ManHashAnd(pNew,Gia_ObjFanin0Copy(current),
                                       Gia_ObjFanin1Copy(current) );
  return current->Value;
}
Gia_Man_t* meowDGSyn::provePreprocess(meowDGNode* target, meowAIG* cir,
 vector<int>& oldControl, set<int>& requiredFF){
 // set<int> requiredFF;
  collectFF(target, oldControl, cir, requiredFF);
//  cerr<<"requireFF "<<requiredFF.size()<<endl; 
  // because we don't want to copy all
  cir->cleanMap(); // meowID to Value
  // ok, start to create new circuit!!!
  Gia_Man_t* pNew;
  Gia_Obj_t * pObj;
  //Gia_Obj_t * pExtra;
  int i; //, iLit, andLit, orLit, outLit; //, andLit2, orLit2;
  pNew = Gia_ManStart( Gia_ManObjNum(_currentCir));
    // map combinational inputs
  Gia_ManFillValue( _currentCir );
  Gia_ManConst0(_currentCir)->Value = 0;
  pNew->pName = Abc_UtilStrsav( "property" );
  Gia_ManHashAlloc( pNew );
  Gia_ManForEachPi(_currentCir, pObj, i)
    pObj->Value = Gia_ManAppendCi(pNew);
  // create Extra PIs in cir
  int extraPI = cir->getExtraPINum();
  for(int j = 0; j < extraPI; ++j){
    int value = Gia_ManAppendCi(pNew);
    cir->addExtraPI2Value(j, value);
  }

  set<int>::iterator site = requiredFF.begin();
  for(; site!= requiredFF.end(); ++site ){
 //   cerr<<"build in New"<<*site<<endl;
    pObj = Gia_ManObj(_currentCir, (*site));
    pObj->Value = Gia_ManAppendCi(pNew);
  }
  int extraFFNum = cir->getFFNum();
  for(int j = 0; j < extraFFNum; ++j){
    int value = Gia_ManAppendCi(pNew);
    cir->addFF2Value(j, value);
  }
  int cirPINum = cir->getPINum();// saved with signal 
  for(int j = 0; j < cirPINum; ++j){
    pObj = Gia_ManObj(_currentCir, cir->getPIGateID(j));
  //  cerr<<"build for "<<cir->getPIGateID(j)<<endl;
    pObj->Value = Gia_ObjCopy_rec(pNew, pObj);
    cir->addPI2Value(j, pObj->Value);
  }
  return pNew;
}
bool meowDGSyn::runPDR(Gia_Man_t* pNew){
  Aig_Man_t * pAig = Gia_ManToAig( pNew, 0 );
  Pdr_Par_t Pars, * pPars = &Pars;
  Pdr_ManSetDefaultParams( pPars );
  pPars->fSilent = 1;
  pPars->fVerbose = 0;
  pPars->fSolveAll = 0;
  int proveRev = Pdr_ManSolve( pAig, pPars );
//  cerr<<"call pdr?!"<<proveRev<<endl;
  Gia_ManHashStop( pNew );

  Aig_ManStop( pAig ); 
  Gia_ManStop(pNew); 
  // prove by &pdr
  if(proveRev == 1) // property proved!! 
    return true;
  else 
    return false; 



}
bool meowDGSyn::provePostProcess(Gia_Man_t* pNew, meowAIG* cir, set<int>& requiredFF){
  Gia_Obj_t * pObj;
  Gia_Obj_t * pObj2;
  //Gia_Obj_t * pExtra;
 // int i; //, iLit, andLit, orLit, outLit; //, andLit2, orLit2;
  
  set<int>::iterator site = requiredFF.begin();
  for(; site!= requiredFF.end(); ++site ){
    pObj = Gia_ManObj(_currentCir, (*site));
    pObj2 = Gia_ObjRoToRi(_currentCir, pObj);
    Gia_ObjCopy_rec(pNew, Gia_ObjFanin0(pObj2));
    pObj2->Value = Gia_ManAppendCo(pNew, Gia_ObjFanin0Copy(pObj2));
  }
  int extraFFNum = cir->getFFNum();

  for(int j = 0; j < extraFFNum; ++j)
    Gia_ManAppendCo(pNew, cir->getFFInputValue(pNew, j)); 

  Gia_ManSetRegNum(pNew, extraFFNum+requiredFF.size());
  return runPDR(pNew);
}
bool meowDGSyn::isUpToDate(meowDGNode* target, meowAIG* cir, meowAIGNode* update, vector<int>& oldControl){
  // construct circuit!
  set<int> requiredFF;
  Gia_Man_t* pNew = provePreprocess(target, cir, oldControl,
                                    requiredFF);
 // Gia_Obj_t * pObj;
//  Gia_Obj_t * pObj2;
  //Gia_Obj_t * pExtra;
 // int i; //, iLit, andLit, orLit, outLit; //, andLit2, orLit2;
  
  int uSignalLit = cir->copy2Gia(pNew, update, 0);
  vector<int>& controls = dynamic_cast<meowDGGatedFF*>(target)->getControlIDs();
  vector<int> useControl(controls.begin(), controls.end());
  if(oldControl.size() > 0) // used for verification
    useControl = oldControl; // use oldControls

  int controlLit = createEnable(pNew, useControl);
    // finally append Po for checkingi U' | C
  int propertyLit = Gia_ManHashOr(pNew, uSignalLit^1, controlLit);
  Gia_ManAppendCo(pNew, propertyLit^1); // this is assertion
//  cerr<<"perform IsUpToDate Checking!"<<endl;
  return provePostProcess(pNew, cir, requiredFF);
}
void meowDGSyn::satSynthesis(meowDGNode* target){
  // step 1: formulate updating condition but
  meowAIG* updating = new meowAIG(_currentCir);

  meowAIGNode* targetU = getUpdatingCondition(updating, target);
 
  if(targetU == updating->getOne()){
    delete updating;
    return; // nothing can be done...

  }
  // target U is the updating condition for this FF input

  // step 2: check up-to-date
  if(target->getType() == NODE_GATED){
    vector<int> empty;
    if(!isUpToDate(target, updating, targetU, empty)){ // call pdr
      delete updating;
      return;
    }
  }
/*  cerr<<"new Gating!! "<<target->getID()<<endl;
  updating->printAIG();
  cerr<<"target U is: "<<endl;
  updating->getRegular(targetU)->printNode();*/
  performGating(target, updating, targetU);
  // step 3, synthesis 

  delete updating;
}
void meowDGSyn::collectFullySupports(set<int>& signals){
  // TODO speed-up
  set<int> piList;
  int i;
  Gia_Obj_t* pObj;
 // Gia_Obj_t* pFanout;
  Gia_ManForEachObj1(_currentCir, pObj, i){
    int gateId = Gia_ObjId(_currentCir, pObj);
    if(Gia_ObjIsPi(_currentCir, pObj)){
      piList.insert(gateId);
      continue;
    }
    if(Gia_ObjIsPo(_currentCir, pObj)) // wait until Ri
      continue;
    
    if(Gia_ObjIsRo(_currentCir, pObj)){ // Ci: push directly
      signals.insert(gateId);
    }
    if(Gia_ObjIsRi(_currentCir, pObj)){
      /*Gia_Obj_t* pRo = Gia_ObjRiToRo(_currentCir, pObj);
      int faninID = Gia_ObjFaninId0( pObj, gateId );
      if(piList.find(faninID)== piList.end()){
        signals.insert(gateId); 
        int RoID = Gia_ObjId(_currentCir, pRo);
        signals.insert(RoID);
      }*/
      continue;
    }
    int faninID0 = Gia_ObjFaninId0( pObj, gateId );
    int faninID1 = Gia_ObjFaninId1( pObj, gateId );
   /* if(gateId == 329){
      cerr<<"what? "<<faninID0<<", "<<faninID1<<endl;
    }*/
    if(piList.find(faninID0) == piList.end() 
    && piList.find(faninID1) == piList.end()){
      signals.insert(gateId);
    }
    else
      piList.insert(gateId); 
  } 
}
void meowDGSyn::obsSynthesisGreedy(meowDGNode* target){
  // step1: get special XO(out)
  //cerr<<"obsSynthesisSpecial: "<<target->getWidth()<<endl;

  meowAIG* observable = new meowAIG(_currentCir);
  // target must be normal FFs
  set<meowDGNode*> visited; 
  // target is a FF node, we need to check its X"O(out)" 
  meowAIGNode* targetO = dynamic_cast<meowDGGatedFF*>(target)->constructObserveCirSpecial( observable, visited, _depth, target);
  if(targetO == observable->getOne()){
   // cerr<<"observable condition is One!"<<endl;
    delete observable;
    return; // nothing can be done...

  }
  if(!resolveXout(observable, targetO, target, false)){
  // step 2: check xO(out) -> en_old
    delete observable;
    return;
  }
  /*if(resolveXout(observable, targetO, target, true)){
   // step 3: optional check en_old^Xout <= en_old
    delete observable;
    return;
  }*/
 // cerr<<"Gating obsSynthesisSpecial: "<<target->getWidth()<<endl;


  performGatingObv(target, observable, targetO); 
  delete observable;

}
void meowDGSyn::obsSynthesis(meowDGNode* target){
 // cerr<<"obsSynthesis: "<<target->getID()<<endl;
  // formulate observe recursively
  // find fully supported signals?!
 // set<int> fullySupported;
 // collectFullySupports(fullySupported); // for X synthesis

  meowAIG* observable = new meowAIG(_currentCir);
  // target must be normal FFs
  set<meowDGNode*> visited; 
  // target is a FF node, we need to check its X"O(out)" 
  meowAIGNode* targetO = target->constructObserveCir(observable, 
                                                     visited, _depth,
                                                     target);
  // 

  if(targetO == observable->getOne()){
   // cerr<<"observable condition is One!"<<endl;
    delete observable;
    return; // nothing can be done...

  }
  //cerr<<"Gating?!"<<endl;
  performGatingObv(target, observable, targetO); 
  delete observable;
  // if get some, add to target
}
void meowDGSyn::add2IDMap(map<int, int>& old2newID, Gia_Man_t* pNew,
                          Gia_Obj_t* pObj){
  Gia_Obj_t* newObj = Gia_ObjCopy(pNew, pObj);
  int oldID = Gia_ObjId(_currentCir, pObj);
  int newID = Gia_ObjId(pNew, newObj);
  old2newID[oldID] = newID;

}
void meowDGSyn::performGatingObv(meowDGNode* target, meowAIG* cir,
                              meowAIGNode* control){
  // copy copy copy and then create extra control!!!
  map<int, int> old2newID;
  cir->cleanMap();
  Gia_Man_t * pNew;
  Gia_Obj_t * pObj;
  int i;
  pNew = Gia_ManStart( Gia_ManObjNum(_currentCir) );
  Gia_ManFillValue( _currentCir );
  Gia_ManHashAlloc(pNew); 
  pNew->pName = Abc_UtilStrsav( _currentCir->pName );
  pNew->pSpec = Abc_UtilStrsav( _currentCir->pSpec );
  Gia_ManConst0(_currentCir)->Value = 0;
  Gia_ManForEachCi( _currentCir, pObj, i ){
    pObj->Value = Gia_ManAppendCi(pNew);
    add2IDMap(old2newID, pNew, pObj);
  }
  Gia_ManForEachAnd( _currentCir, pObj, i ){
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj),
                                          Gia_ObjFanin1Copy(pObj) );
    add2IDMap(old2newID, pNew, pObj);    
  }
 /* cir->printAIG();
  cerr<<"targetControl: "<<control<<endl;*/
  int newControlLit = cir->copy2Gia(pNew, control, 1); 
  if(newControlLit == 1 || newControlLit == 0){
    Gia_ManHashStop( pNew );
 
    Gia_ManStop(pNew);
    return;

 }
 _gatedNum += target->getWidth(); 


  //cerr<<"newControlLit = "<<newControlLit<<endl;
  // check with old

  vector<int>& targetFFs = target->getGates(); // Ro!!! change to Ri
  set<int> targetRi;
  for(int j = 0; j < targetFFs.size(); ++j){
    int Ri = Gia_ObjRoToRiId( _currentCir, targetFFs[j] );
    targetRi.insert(Ri);
  }
  // 
  map<int, int> Ri2InputValue; 
  Gia_ManForEachCo( _currentCir, pObj, i ){ 
    // 
    int gateID = Gia_ObjId(_currentCir, pObj);
    if(targetRi.find(gateID)!= targetRi.end()){
      Gia_Obj_t* Ro = Gia_ObjRiToRo(_currentCir, pObj); 
      int faninValue = Gia_ObjFanin0Copy(pObj);
      int regValue = Ro->Value;  
      // controlValue: newControlLit!
     //!!!! clock-gating!!!!!!!!!!!!!!!!!
      int select = Gia_ManHashAnd( pNew, newControlLit, faninValue );
      int gated = Gia_ManHashAnd(pNew, newControlLit^1, regValue);
      int result =  Gia_ManHashOr(pNew, select, gated);
      Ri2InputValue[gateID] = result; // add MUX
    }
  }
  Gia_ManForEachCo( _currentCir, pObj, i ){ 

    // put all Co now
    int gateID = Gia_ObjId(_currentCir, pObj);
    if(targetRi.find(gateID)== targetRi.end()){
      pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
      add2IDMap(old2newID, pNew, pObj);    
    }
    else //!!!! clock-gating!!!!!!!!!!!!!!!!!
      pObj->Value = Gia_ManAppendCo(pNew, Ri2InputValue[gateID]);
    
  }
  Gia_ManHashStop( pNew );
 
  Gia_ManDupRemapEquiv( pNew, _currentCir );
  Gia_ManSetRegNum( pNew, Gia_ManRegNum(_currentCir));
  assert( Gia_ManIsNormalized(pNew) );
  Gia_ManStop(_currentCir); // replace!
  _currentCir = pNew; 


  _DG->updateDGIDs(old2newID); // update first
  int newControlID = newControlLit >> 1;
  if(newControlLit&1)
    newControlID *= (-1);
  _DG->reviseNode(target, newControlID); 


}
void meowDGSyn::performGating(meowDGNode* target, meowAIG* cir, 
                              meowAIGNode* control){
  // keep a table while copy
 // cerr<<"Gating?"<<endl;
  _gatedNum += target->getWidth(); 
  map<int, int> old2newID;
  cir->cleanMap();
  Gia_Man_t * pNew;
  Gia_Obj_t * pObj;
  int i;
  pNew = Gia_ManStart( Gia_ManObjNum(_currentCir) );
  Gia_ManFillValue( _currentCir );
  Gia_ManHashAlloc(pNew); 
  pNew->pName = Abc_UtilStrsav( _currentCir->pName );
  pNew->pSpec = Abc_UtilStrsav( _currentCir->pSpec );
  Gia_ManConst0(_currentCir)->Value = 0;
  Gia_ManForEachCi( _currentCir, pObj, i ){
    pObj->Value = Gia_ManAppendCi(pNew);
    add2IDMap(old2newID, pNew, pObj);
  }
  int extraFFNum = cir->getFFNum();
  for(int j = 0; j < extraFFNum; ++j){
    int value = Gia_ManAppendCi(pNew);
    cir->addFF2Value(j, value);
    // add extra Ci!
  }
    
  Gia_ManForEachAnd( _currentCir, pObj, i ){
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj),
                                          Gia_ObjFanin1Copy(pObj) );
    add2IDMap(old2newID, pNew, pObj);    
  }
  int cirPINum = cir->getPINum();
  for( int j = 0; j < cirPINum; ++j){
    pObj = Gia_ManObj(_currentCir, cir->getPIGateID(j));
    cir->addPI2Value(j, pObj->Value);
  }
  // we need to add PI2Value here
  int newControlLit = cir->copy2Gia(pNew, control, 0);

  vector<int>& targetFFs = target->getGates(); // Ro!!! change to Ri
  set<int> targetRi;
  for(int j = 0; j < targetFFs.size(); ++j){
    int Ri = Gia_ObjRoToRiId( _currentCir, targetFFs[j] );
    targetRi.insert(Ri);
  }
  // 
  map<int, int> Ri2InputValue; 
  Gia_ManForEachCo( _currentCir, pObj, i ){ 
    // 
    int gateID = Gia_ObjId(_currentCir, pObj);
    if(targetRi.find(gateID)!= targetRi.end()){
      Gia_Obj_t* Ro = Gia_ObjRiToRo(_currentCir, pObj); 
      int faninValue = Gia_ObjFanin0Copy(pObj);
      int regValue = Ro->Value;  
      // controlValue: newControlLit!
     //!!!! clock-gating!!!!!!!!!!!!!!!!!
      int select = Gia_ManHashAnd( pNew, newControlLit, faninValue );
      int gated = Gia_ManHashAnd(pNew, newControlLit^1, regValue);
      int result =  Gia_ManHashOr(pNew, select, gated);
      Ri2InputValue[gateID] = result; // add MUX
    }
  }
  for(int j = 0; j < extraFFNum; ++j) // create logic for FF
    cir->getFFInputValue(pNew, j);

  // add real Co
  Gia_ManForEachCo( _currentCir, pObj, i ){ 
    // put all Co now
    int gateID = Gia_ObjId(_currentCir, pObj);
    if(targetRi.find(gateID)== targetRi.end()){
      pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
      add2IDMap(old2newID, pNew, pObj);    
    }
    else //!!!! clock-gating!!!!!!!!!!!!!!!!!
      pObj->Value = Gia_ManAppendCo(pNew, Ri2InputValue[gateID]);
    
  }
  // finally
  for(int j = 0; j < extraFFNum; ++j)
    Gia_ManAppendCo(pNew, (cir->getFFInputValue(pNew, j)));
    // add extra FF!
  
//  Gia_ManSetRegNum( pNew, extraFF.size()+FF.size() );
  Gia_ManHashStop( pNew );
 
  Gia_ManDupRemapEquiv( pNew, _currentCir );
  Gia_ManSetRegNum( pNew, Gia_ManRegNum(_currentCir)+extraFFNum );
  assert( Gia_ManIsNormalized(pNew) );
  Gia_ManStop(_currentCir); // replace!
  _currentCir = pNew; 


  _DG->updateDGIDs(old2newID); // update first
  int newControlID = newControlLit >> 1;
  if(newControlLit&1)
    newControlID *= (-1);
  _DG->reviseNode(target, newControlID); 
}
ABC_NAMESPACE_IMPL_END
