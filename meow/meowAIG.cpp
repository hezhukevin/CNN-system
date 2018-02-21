#include "ext/meow/meowAIG.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START
meowAIGNode::meowAIGNode(int meowID, int gateID, AIG_TYPE type){
  _meowID = meowID;
  _gateID = gateID; // -1 means not in GIA
  _type = type;
  _fanin0 = NULL;
  _fanin1 = NULL;
// const 0 
}
void meowAIGNode::setFanin0(meowAIGNode* fanin0, int neg){
  size_t temp0 = ((size_t)fanin0)^neg; // 0 or 1
  // fanin0 can be negated
  _fanin0 = reinterpret_cast<meowAIGNode*>(temp0);
}
void meowAIGNode::setFanin1(meowAIGNode* fanin1, int neg){
  size_t temp1 = ((size_t)fanin1)^neg; // 0 or 1
  _fanin1 = reinterpret_cast<meowAIGNode*>(temp1);
}
meowAIGNode* meowAIGNode::getFanin0Reg(){
  size_t temp0 = ((size_t)_fanin0)&FANIN_MASK;
  return reinterpret_cast<meowAIGNode*>(temp0); 
}
meowAIGNode* meowAIGNode::getFanin1Reg(){
  size_t temp1 = ((size_t)_fanin1)&FANIN_MASK;
  return reinterpret_cast<meowAIGNode*>(temp1); 
}
int meowAIGNode::getFanin0Phase(){
  size_t temp0 = ((size_t)_fanin0)&1;
  return (int)temp0;
}
int meowAIGNode::getFanin1Phase(){
  size_t temp1 = ((size_t)_fanin1)&1;
  return (int)temp1;
}
void meowAIGNode::printNode(){
  cerr<<"Node ID"<<getMeowID()<<": type is "<<_type<<", ptr"<<this<<" gateID is "<<getGateID()<<endl;
  if(_fanin0){
    cerr<<"Fanin0 is "<<getFanin0Reg()->getMeowID()<<", phase ";
    cerr<<getFanin0Phase() <<endl;
  }
  if(_fanin1){
    cerr<<"Fanin1 is "<<getFanin1Reg()->getMeowID()<<", phase ";
    cerr<<getFanin1Phase() <<endl;
  }
    

}
//=======
meowAIG::meowAIG(Gia_Man_t* cir){
  _cir = cir;
  meowAIGNode* const0 = new meowAIGNode(0, -1, MEOW_AIG_ZERO);
  _nodeList.push_back(const0);
  _meowID2Value[0] = 0;
  _oldControl = NULL; 
}
meowAIG::~meowAIG(){
  for(int i = 0; i < _nodeList.size(); ++i)
    delete _nodeList[i];

  map<meowAIGNode*, set<int>* >::iterator mite = _next2Supports.begin();
  for(; mite!= _next2Supports.end(); ++mite)
    delete (mite->second);
}
meowAIGNode* meowAIG::addExtraPI(){
  meowAIGNode* piNode = new meowAIGNode(_nodeList.size(),
                            -1, MEOW_AIG_PI);
  _nodeList.push_back(piNode);
  _extraPIs.push_back(piNode);
  return piNode;
}
meowAIGNode* meowAIG::addPI(int gateID){
  meowAIGNode* piNode = NULL;
  if(_giaID2Node.find(abs(gateID))!= _giaID2Node.end())
    piNode = _giaID2Node[abs(gateID)];
  else{
    //cerr<<"create Node?!"<<gateID<<endl; 
    piNode = new meowAIGNode(_nodeList.size(),
                             abs(gateID), MEOW_AIG_PI);
    _nodeList.push_back(piNode);
    _PIList.push_back(piNode);
    _giaID2Node[abs(gateID)] = piNode;

  }
 // cerr<<"gateID = "<<gateID<<endl;
  if(gateID > 0)
    return piNode;
  else{
    size_t temp1 = ((size_t)piNode)|1;
    return reinterpret_cast<meowAIGNode*>(temp1); 
  }
}
meowAIGNode* meowAIG::addFF(meowAIGNode* fanin0, int neg0,
                            int initial){
  neg0 = int(((size_t)fanin0&1)^neg0);
  size_t temp0 = ((size_t)fanin0)&FANIN_MASK;
  fanin0 =  reinterpret_cast<meowAIGNode*>(temp0); 
  // if Z(const1) => const1
  // Y(const0) => const0
  if((fanin0 == _nodeList[0]) && (neg0 == initial)){
    if(neg0)
      return getOne();
    else
      return getZero();
  }

  meowAIGNode* node = checkExist(fanin0, neg0^initial, NULL, 0);
  
  if(!node){
    node = new meowAIGNode(_nodeList.size(), -1, MEOW_AIG_FF);
    _nodeList.push_back(node);
    _FFList.push_back(node);
    node->setFanin0(fanin0, neg0^initial);
    addTable(node);
  }
  if(initial){
    size_t temp1 = ((size_t)node)|1;
    return reinterpret_cast<meowAIGNode*>(temp1); 
  }
  else
    return node;
}
meowAIGNode* meowAIG::addAND(meowAIGNode* fanin0, int neg0,
                             meowAIGNode* fanin1, int neg1, 
                             int outNeg){
  // sort ID, fanin0 has bigger ID
  neg0 = int(((size_t)fanin0&1)^neg0);
  neg1 = int(((size_t)fanin1&1)^neg1);
  size_t temp0 = ((size_t)fanin0)&FANIN_MASK;
  fanin0 =  reinterpret_cast<meowAIGNode*>(temp0); 
  size_t temp1 = ((size_t)fanin1)&FANIN_MASK;
  fanin1 =  reinterpret_cast<meowAIGNode*>(temp1);
  if(fanin0->getMeowID() < fanin1->getMeowID()){ // swap
    int swap = neg0;
    neg0 = neg1;
    neg1 = swap;

    meowAIGNode* sNode = fanin0;
    fanin0 = fanin1;
    fanin1 = sNode;
  }
  meowAIGNode* node = checkExist(fanin0, neg0, fanin1, neg1);
  if(!node){
    node = new meowAIGNode(_nodeList.size(), -1, MEOW_AIG_AND);
    _nodeList.push_back(node);
    node->setFanin0(fanin0, neg0);
    node->setFanin1(fanin1, neg1);
    addTable(node);
  }
  if(outNeg){
    size_t temp1 = ((size_t)node)^1;
    return reinterpret_cast<meowAIGNode*>(temp1); 
  }
  else
    return node;
}
meowAIGNode* meowAIG::addEQ(meowAIGNode* fanin0, meowAIGNode* fanin1, int neg){

  meowAIGNode* posCase = addAND(fanin0, 0, fanin1, 0, 0);
  meowAIGNode* negCase = addAND(fanin0, 1, fanin1, 1, 0);
  meowAIGNode* bothCase = addAND(posCase, 1, negCase, 1, 1);
  if(neg){
    size_t temp1 = ((size_t)bothCase)|1;
    return reinterpret_cast<meowAIGNode*>(temp1); 
  }
  else
    return bothCase;
}
meowAIGNode* meowAIG::addNext(meowAIGNode* fanin0){
  meowAIGNode* node = new meowAIGNode(_nodeList.size(), 
                                      -1, MEOW_AIG_NEXT);
  _nodeList.push_back(node);
  _NextList.push_back(node);
  node->setFanin0(fanin0, 0);

  return node;
}
meowAIGNode* meowAIG::addFF(int initial){
  meowAIGNode* node = new meowAIGNode(_nodeList.size(), -1,
                                      MEOW_AIG_FF);
  _nodeList.push_back(node);
  _FFList.push_back(node);
 // fill in fanin later 
  if(initial){
    size_t temp1 = ((size_t)node)|1;
    return reinterpret_cast<meowAIGNode*>(temp1); 
  }
  else
    return node;

}
meowAIGNode* meowAIG::addSince(meowAIGNode* a, meowAIGNode* b){
  // create $Y(s)$
  // check a and b to avoid const and extra signal
  if(getOne() == b) // always true
    return getOne();
  if(getZero() == a)
    return b;
  if(a == b) // 
   return a; 
  // else: construct circuits with special FF
  meowAIGNode* sNode = addFF(0); // this is Y(s)
  meowAIGNode* sANDa = addAND(a, 0, sNode, 0, 0);
  meowAIGNode* saORb = addAND(b, 1, sANDa, 1, 1);
  // build S = (Y(s)&&a )||b
  sNode->setFanin0(saORb, 0);
  addTable(sNode);
  return saORb;
}
meowAIGNode* meowAIG::neg(meowAIGNode* input){
  size_t temp1 = ((size_t)input)^1;
  return reinterpret_cast<meowAIGNode*>(temp1); 

}
meowAIGNode* meowAIG::checkExist( meowAIGNode* fanin0, int neg0,
                                  meowAIGNode* fanin1, int neg1){
  if(fanin0 == fanin1){
    if(neg0 == neg1){
      size_t temp1 = ((size_t)fanin0)|neg0;
      return reinterpret_cast<meowAIGNode*>(temp1); 
    }
    else
      return _nodeList[0]; 
  }
  if(fanin1 == _nodeList[0]){ // one is constant fanin0 ID is bigger
    if(neg1){
      size_t temp1 = ((size_t)fanin0)|neg0;
      return reinterpret_cast<meowAIGNode*>(temp1); 
    }
    else
      return _nodeList[0];
  }
 

  ostringstream Convert;
  Convert<<neg0<<"&"<<fanin0->getMeowID()<<"|";
  if(fanin1)
    Convert<<neg1<<"&"<<fanin1->getMeowID();
  else
    Convert<<"0";

  string token = Convert.str();
  if(_hashTable.find(token)!= _hashTable.end())
    return _hashTable[token];
  else 
    return NULL;  // nothing exist
  // sorted and neg has be resolved befor 
}
void meowAIG::addTable(meowAIGNode* node){
  ostringstream Convert; 
  int neg0 = node->getFanin0Phase();
  int neg1 = node->getFanin1Phase();
  meowAIGNode* fanin0 = node->getFanin0Reg();
  meowAIGNode* fanin1 = node->getFanin1Reg();
  Convert<<neg0<<"&"<<fanin0->getMeowID()<<"|";
  if(fanin1)
    Convert<<neg1<<"&"<<fanin1->getMeowID();
  else
    Convert<<"0";

  string token = Convert.str();

  _hashTable[token] = node;

}
int meowAIG::copy2GiaTimeFrame(Gia_Man_t* pNew, int cirID, int Xlevel, map< pair<int, int>, int>& gateT2Value, int special){
  pair<int, int> index = make_pair(cirID, Xlevel);
  if(gateT2Value.find(index)!= gateT2Value.end())
    return gateT2Value[index];

  Gia_Obj_t* pObj = Gia_ManObj(_cir, cirID);
  if(cirID == 0) // const
    return 0;
 // cerr<<"call cirID = "<<cirID<<", Xlevel = "<<Xlevel<<endl;
  int regValue = 0;
  if(Xlevel == 0)
    return pObj->Value;// use constructed directly

  // need to go across timeframe cases
  if(Gia_ObjIsPi(_cir, pObj)){
    if(Xlevel!= 0){ //handle by speial! 1 -> even -1 ->old
      //cerr<<"ERROR: we cannot push PI anymore!"<<endl;
      if(special == 1)
        return 1;
      else
        return 0;
    }
    else
      return pObj->Value;
  }
  if(Gia_ObjIsRo(_cir, pObj)){
    // acoss timeframe
    Gia_Obj_t* pRi = Gia_ObjRoToRi(_cir, pObj);
    int RiID = Gia_ObjId(_cir, pRi);
    int faninId0 = Gia_ObjFaninId0(pRi, RiID);
    if(Gia_ObjFaninC0(pRi))
      special = special*(-1);
    regValue = copy2GiaTimeFrame(pNew, faninId0 , Xlevel-1, 
                                 gateT2Value, special);
    if(Gia_ObjFaninC0(pRi))
      regValue = regValue^1;    
  }
  else{ // 
    assert(Gia_ObjIsAnd(pObj));
    int faninId0 = Gia_ObjFaninId0( pObj, cirID );
    int faninId1 = Gia_ObjFaninId1( pObj, cirID );
    int special0 = special;
    if(Gia_ObjFaninC0(pObj))
      special0 = special0*(-1);
    int fanin0Value = copy2GiaTimeFrame(pNew, faninId0, 
                                        Xlevel, gateT2Value, special0);
    int special1 = special;
    if(Gia_ObjFaninC1(pObj))
      special1 = special1*(-1);
 
    int fanin1Value = copy2GiaTimeFrame(pNew, faninId1, 
                                        Xlevel, gateT2Value, special1);
    if(Gia_ObjFaninC0(pObj))
      fanin0Value = fanin0Value^1;
    if(Gia_ObjFaninC1(pObj))
      fanin1Value = fanin1Value^1;
    regValue = Gia_ManHashAnd(pNew, fanin0Value, fanin1Value);
  }
  // finally copy AND Gate 
  gateT2Value[index] = regValue;
  return regValue;  
}
int meowAIG::copy2GiaX(Gia_Man_t* pNew, meowAIGNode* target, int Xlevel, map< pair<int, int>, int>& gateT2Value, int special){
  if(target == getZero())
    return 0;
  if(target == getOne())
    return 1;
  // check phase
  meowAIGNode* regular = getRegular(target);
  int phase = getPhase(target);
  if(phase && special)
    special = -1;

  AIG_TYPE type = regular->getType();
  int regValue = 0; 
  if(type == MEOW_AIG_NEXT){
    regValue = copy2GiaX(pNew, regular->getFanin0(), Xlevel+1, 
                         gateT2Value, special); 
  }
  else if(type == MEOW_AIG_AND){
    int special0 = special;
    if(regular->getFanin0Phase())
      special0 = special0*(-1);
    int value0 = copy2GiaX(pNew, regular->getFanin0(), Xlevel, 
                           gateT2Value, special0);
    int special1 = special;
    if(regular->getFanin1Phase())
      special1 = special1*(-1); 
    int value1 = copy2GiaX(pNew, regular->getFanin1(), Xlevel,
                           gateT2Value, special1);
  // AND gate? recursive first...
    regValue = Gia_ManHashAnd(pNew, value0, value1);
   // _meowID2Value[regular->getMeowID()] = regValue;

  }
  else if(type == MEOW_AIG_PI){ 
    // go across timeframe according to Xlevel
    int cirGateID = regular->getGateID();
  //  cerr<<"Push this: "<<cirGateID<<endl;
    regValue = copy2GiaTimeFrame(pNew, cirGateID, Xlevel, 
                                 gateT2Value, special);
    // same PI can be in different timeframes
  }
  else
    cerr<<"ERROR: copyX should not be here!"<<endl;
 
  if(phase)
    return regValue^1; // flip
  else
    return regValue;

}
int meowAIG::copy2Gia(Gia_Man_t* pNew, meowAIGNode* target, int special){
  if(target == getZero())
    return 0;
  if(target == getOne())
    return 1;
  // check phase
  if(target == NULL)
    return 1;
  meowAIGNode* regular = getRegular(target);
  int phase = getPhase(target);
  AIG_TYPE type = regular->getType();
  if(type == MEOW_AIG_NEXT){
    map< pair<int, int>, int> gateT2Value; 
    return copy2GiaX(pNew, target, 0, gateT2Value, special);

  }
  int regValue = 0;
  if(_meowID2Value.find(regular->getMeowID())!= _meowID2Value.end() )
    regValue = _meowID2Value[regular->getMeowID()];
  else{
    int value0 = copy2Gia(pNew, regular->getFanin0(), special); 
    int value1 = copy2Gia(pNew, regular->getFanin1(), special);
  // AND gate? recursive first...
    regValue = Gia_ManHashAnd(pNew, value0, value1);
    _meowID2Value[regular->getMeowID()] = regValue;
  }
  if(phase)
    return regValue^1; // flip
  else
    return regValue;
}
void meowAIG::getFurtherList(set<int>& supportList,
                             set<int>& furtherList){
  // go from support, find furtherList
  //map<int, set<int> > gate2Support;
  if(_gate2Supports.size() == 0){
    int i;
    Gia_Obj_t* pObj;
    Gia_ManForEachObj(_cir, pObj, i){
      int gateId = Gia_ObjId(_cir, pObj);
      if(Gia_ObjIsCi(pObj)){  
        
        set<int> suppList;
        suppList.insert(gateId);
        _gate2Supports[gateId] = suppList;
      }
      else if(Gia_ObjIsCo(pObj)){
        int faninID0 = Gia_ObjFaninId0( pObj, gateId );
        set<int> suppList;
        suppList.insert(_gate2Supports[faninID0].begin(), 
                        _gate2Supports[faninID0].end());
        _gate2Supports[gateId] = suppList; 
      }
      else{
        int faninID0 = Gia_ObjFaninId0( pObj, gateId );
        int faninID1 = Gia_ObjFaninId1( pObj, gateId );
        set<int> suppList;
        suppList.insert(_gate2Supports[faninID0].begin(), 
                        _gate2Supports[faninID0].end());
        suppList.insert(_gate2Supports[faninID1].begin(), 
                        _gate2Supports[faninID1].end());
        _gate2Supports[gateId] = suppList; 

      }
    }
  }
  set<int>::iterator site = supportList.begin();
  for(; site!= supportList.end(); ++site){
    Gia_Obj_t* pObj2 = Gia_ManObj(_cir, *site);
    if(Gia_ObjIsRo(_cir, pObj2)){ // Ro
      Gia_Obj_t* pRi = Gia_ObjRoToRi(_cir, pObj2);
      int gateId = Gia_ObjId(_cir, pRi);
      furtherList.insert(_gate2Supports[gateId].begin(),
                         _gate2Supports[gateId].end()); 
    }
    else{
      furtherList.insert(_gate2Supports[*site].begin(),
                         _gate2Supports[*site].end()); 
   
    }
  }
}
int meowAIG::getFFInputValue(Gia_Man_t* pNew, int FFindex){
  meowAIGNode* fanin0 = _FFList[FFindex]->getFanin0();
  return copy2Gia(pNew, fanin0, 0); 
}
void meowAIG::printAIG(){
  for(int i = 0; i < _nodeList.size(); ++i)
    _nodeList[i]->printNode();
}
void meowAIG::getSupports(meowAIGNode* target, set<int>& supportList){
  meowAIGNode* regular = getRegular(target);
  if(regular->getGateID() > 0){
    supportList.insert(regular->getGateID()); 
    return;
  }
  if(regular->getType() == MEOW_AIG_NEXT ){ // push again!?
    set<int>* furtherSupp = _next2Supports[regular];
    supportList.insert(furtherSupp->begin(), furtherSupp->end()); 
    return; 

  }
  meowAIGNode* fanin0 = regular->getFanin0Reg();
  meowAIGNode* fanin1 = regular->getFanin1Reg();
  if(fanin0)
    getSupports(fanin0, supportList);
  if(fanin1)
    getSupports(fanin1, supportList); 
}
ABC_NAMESPACE_IMPL_END
