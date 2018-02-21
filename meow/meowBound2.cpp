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
#include "ext/meow/meowBound2.h"
//#include "ext/meow/meowBlock.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START
void meowUsageBound2(){
  Abc_Print( -2, "usage: meowReverse [-aswrhVC] \n" );
  Abc_Print( -2, "\t compute transparent logic of the current Gia. \n");
  Abc_Print( -2, "\t -w: toggle to print Proved words\n");
  Abc_Print( -2, "\t -s: toggle to split words\n");
  Abc_Print( -2, "\t -a <mode>: drop single words with different modes. default is no drop\n");
  Abc_Print( -2, "\t -d: toggle to drop words less then 4 bits.\n");
  Abc_Print( -2, "\t -r: toggle to print width and depths\n");
  Abc_Print( -2, "\t -V <filename>: write out Verilog with transparent logic\n");
  Abc_Print( -2, "\t -C <fileHead>: write out AIGs of subcircuits\n");
  Abc_Print( -2, "\t -h    : print the command usage\n");


}
meowBound2::meowBound2(Gia_Man_t* cir){
  _cir = cir;
  Gia_ManStaticFanoutStart(_cir);
  
  int i;
  Gia_Obj_t* pObj; 
  Gia_ManForEachPo(_cir, pObj, i){
    _poIDs.insert(Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj)));
  }
}

meowBound2::~meowBound2(){
  Gia_ManStaticFanoutStop(_cir);

  for(int i = 0; i < _nodeList.size(); ++i)
    delete _nodeList[i];

  map<int, set<int>* >::iterator mite = _gate2ControlSupports.begin();
  for(; mite!=_gate2ControlSupports.end();++mite)
    delete (mite->second);

  map<int, vector<int>* >::iterator mite2 = _control2Fanouts.begin();
  for(; mite2!= _control2Fanouts.end(); ++mite2)
    delete (mite2->second);

  map<int, set<meowNode*>* >::iterator mite3 = _gate2WordList.begin();
  for(; mite3!= _gate2WordList.end(); ++mite3)
    delete (mite3->second);

  map<int, vector<meowNode*>* >::iterator mite4 = _control2Nodes.begin();
  for(; mite4 != _control2Nodes.end(); ++mite4)
    delete mite4->second;

/*  map<int, set<meowNode*>* >::iterator mite5 = _in2Nodes.begin();
  for(; mite5!= _in2Nodes.end() ;++mite5)
    delete mite5->second; 
*/
}
void meowBound2::runAll(bool drop){
  decideOrder(); // done
  computeSingleControl();
  analyzeNode1(); // badNodes, provedBits, muxNodes, middleNodes
                  //gate2WordList 
  computeMultipleControl(); // for proceeding words 
                            // -> update provedBits and gate2WordList

  analyzeNode2(); // start to remove "outIDs" single outputs

  addGate2Node(drop); // take All!!
  collectNodes(); // take width >=4 
  //removeSingle();

}
void meowBound2::computeMultipleControl(){
  set<meowNode*> checkedNodes;
  for(int i = 0; i < _nodeList.size(); ++i ){
    if(_badNodes.find(_nodeList[i])!= _badNodes.end())
      continue;
    if(_muxNodes.find(_nodeList[i])!= _muxNodes.end())
      continue;
    if(_fanoutMiddleNodes.find(_nodeList[i])!= _fanoutMiddleNodes.end())
      continue;

    if(isFanoutMiddleWord(_nodeList[i])){
      _fanoutMiddleNodes.insert(_nodeList[i]);
      continue;
    }
    if(checkedNodes.find(_nodeList[i]) != checkedNodes.end())
      continue;
    int oldSize = _nodeList.size();
    moveForward(_nodeList[i]);
    while(oldSize != _nodeList.size()){
      int start = oldSize;
      oldSize = _nodeList.size();
     
      for(int j = start; j < oldSize; ++j){
        moveForward(_nodeList[j]);
      }
    }
  }

}
void meowBound2::moveForward(meowNode* current){
  //cerr<<"moveForward"<<endl;
  //current->printNode();
  vector<int>& outIDs = current->getOutIDs();
  set<int> oneStepFanouts;
  collectFanouts(oneStepFanouts, outIDs);

  vector<meowNode*> possibleCombine;
  findPossibleCombine(oneStepFanouts,
                      outIDs, possibleCombine, current);
  vector<int>& control1 = current->getControlIDs();
  for(int i = 0; i < possibleCombine.size(); ++i){
    vector<int>& control2 = possibleCombine[i]->getControlIDs();
    set<int> controls;
    controls.insert(control1.begin(), control1.end());
    controls.insert(control2.begin(), control2.end());
    if(newCombine(controls))
      enumerateControls(controls); 
  }
}
bool meowBound2::newCombine(set<int>& controls){
  if(controls.size() < 2)
    return false;
  ostringstream Convert;
  set<int>::iterator site = controls.begin();
  for(; site!= controls.end(); ++site){
    Convert<<(*site)<<"&";
  }
  string token = Convert.str();
  if(_usedKey.find(token)== _usedKey.end()){ //new!!
    _usedKey.insert(token);
   // cerr<<"Combine!"<<token<<endl;
    return true;
  }
  else
    return false;
}
void meowBound2::findPossibleCombine( set<int>& oneStepFanouts, 
                             vector<int>& outIDs,
                             vector<meowNode*>& possibleCombine,
                             meowNode* current){
  map<meowNode*, int> hitWords;
  map<meowNode*, set<int> > side2Bits;
  set<int> currentSignals;
  currentSignals.insert(outIDs.begin(), outIDs.end());
  
  set<int>::iterator site = oneStepFanouts.begin();
  for(; site!= oneStepFanouts.end(); ++site){
    Gia_Obj_t* target = Gia_ManObj(_cir, (*site));

    int c0 = Gia_ObjFaninC0( target);
    int c1 = Gia_ObjFaninC1( target);
   // if(c0 == 0 || c1 == 0)
   //   continue; // not OR
    // only consider "OR"
    int faninID0 = Gia_ObjFaninId0(target, (*site)); 
    int faninID1 = Gia_ObjFaninId1(target, (*site));
    if( (currentSignals.find(faninID0)!= currentSignals.end())
     && (currentSignals.find(faninID1)== currentSignals.end())){
      if(_gate2WordList.find(faninID1)!= _gate2WordList.end()){
        set<meowNode*>* list1 = _gate2WordList[faninID1];
        set<meowNode*>::iterator w = list1->begin();
        for( ; w != list1->end(); ++w){
          if(hitWords.find((*w))!= hitWords.end()){
            hitWords[(*w)]+=1;
            side2Bits[(*w)].insert(faninID0);
          }
          else{
            hitWords[(*w)] = 1;
            set<int> newList;
            newList.insert(faninID0);
            side2Bits[(*w)] = newList;
          }
        }
      } 
    }
    else if(_gate2WordList.find(faninID0)!= _gate2WordList.end()){
      set<meowNode*>* list0 = _gate2WordList[faninID0];
      set<meowNode*>::iterator w = list0->begin();
      for(; w != list0->end(); ++w){
        if(hitWords.find((*w))!= hitWords.end()){
          hitWords[(*w)]+=1;
          side2Bits[(*w)].insert(faninID1);
        }
        else{
          hitWords[(*w)] = 1;
          set<int> newList;
          newList.insert(faninID1);
          side2Bits[(*w)] = newList;

        }
      }
    }
  }
  map<meowNode*, int>::iterator mite =  hitWords.begin();
  for(; mite!= hitWords.end(); ++mite){
    //cerr<<"combine:"<<endl;
    //(mite->first)->printNode();
    if(_muxNodes.find(mite->first)!= _muxNodes.end())
      continue;
    if(_fanoutMiddleNodes.find(mite->first)!= _fanoutMiddleNodes.end())
      continue;
    if(mite->first  == current)
      continue;

    if(mite->second == outIDs.size() ){ // TODO
      if(side2Bits[mite->first].size() >= 4)
        possibleCombine.push_back(mite->first);
    }
  }
}
void meowBound2::collectFanouts(set<int>& oneStepFanouts, vector<int>& outIDs){
  Gia_Obj_t* pCurrent;
  Gia_Obj_t* pFanout;
  int j;
  for(int i = 0; i < outIDs.size(); ++i){
    pCurrent = Gia_ManObj(_cir, abs(outIDs[i]));
    Gia_ObjForEachFanoutStatic(_cir, pCurrent, pFanout, j){
      int fanoutID = Gia_ObjId(_cir, pFanout);
      if(_middleBits.find(fanoutID)!= _middleBits.end())
        continue;
      if(Gia_ObjIsPo(_cir, pFanout))
        continue;
      
      oneStepFanouts.insert(fanoutID);
    }
  }

}
bool meowBound2::isFanoutMiddleWord(meowNode* current){
  // not bad guy, they are feeding into transparent
  if (_fanoutMiddleNodes.find(current)!= _fanoutMiddleNodes.end())
    return true;
  vector<int>& outIDs = current->getOutIDs();
  for(int j = 0; j < outIDs.size(); ++j){
    Gia_Obj_t* pObj = Gia_ManObj(_cir, abs(outIDs[j]));
    Gia_Obj_t* pFanout;
    int k;
     // bool getBound = false;
    Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, k){
      int fanoutID = Gia_ObjId(_cir, pFanout);
      if(_middleBits.find(fanoutID) == _middleBits.end()){
        return false;
      }
    }
  }
  return true;

}
bool meowBound2::isInternalWord(meowNode* current, set<int>& internalBits){

  // one internal -> true  
  vector<int>& outIDs = current->getOutIDs();
  for(int j = 0; j < outIDs.size(); ++j){
    if(internalBits.find(abs(outIDs[j])) != internalBits.end()){
      //if(!current->fixInternal(j, internaBits))
        return true;
    }
  }
  return false;

 
}
bool meowBound2::isMiddleWord(meowNode* current){
  // they are bad... 
  if (_middleNodes.find(current)!= _middleNodes.end())
    return true;
  vector<int>& outIDs = current->getOutIDs();
  for(int j = 0; j < outIDs.size(); ++j){
    if(_middleBits.find(abs(outIDs[j])) == _middleBits.end()){
        return false;
    }
  }
  return true;

}
void meowBound2::analyzeNode1(){
  // collect MUX, remove "in MUX", repeat?
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_nodeList[i]->isMux()){
      _nodeList[i]->addMiddleBits(_middleBits);
      _muxNodes.insert(_nodeList[i]);
    }
   
  }
  // find Multiplier
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_muxNodes.find(_nodeList[i]) == _muxNodes.end()){
      if(isMiddleWord(_nodeList[i])){
        _middleNodes.insert(_nodeList[i]);
        _badNodes.insert(_nodeList[i]);
        continue;
      }
      //else
      //  _nodeList[i]->addMiddleBits(_middleBits);   
    }
    //_nodeList[i]->addProvedBits(_provedBits); // proved: include input
    updateGate2WordList(_nodeList[i]);
    
  }
 
}
void meowBound2::updateGate2WordList(meowNode* node){
  // output => wordNodes
  vector<int>& outIDs = node->getOutIDs();
  for(int j = 0; j < outIDs.size(); ++j){
    if(_gate2WordList.find(abs(outIDs[j]))== _gate2WordList.end()){
      set<meowNode*>* newList = new set<meowNode*>;
      _gate2WordList[abs(outIDs[j])] = newList;
    }
    _gate2WordList[abs(outIDs[j])]->insert(node);
  } 
}
void meowBound2::analyzeNode2(){
  // collect internal Bits;
  set<int> internalBits;
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badNodes.find(_nodeList[i])== _badNodes.end())
      _nodeList[i]->addInternal(internalBits); 
  }
//  collect internalWords;
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badNodes.find(_nodeList[i])!= _badNodes.end())
      continue;
    if(_muxNodes.find(_nodeList[i])!= _muxNodes.end()){
      _nodeList[i]->addGoodControl(_goodControl);
      continue;
    }
    if(isInternalWord(_nodeList[i], internalBits)) // any bits is in ..
      _internalWords.insert(_nodeList[i]);
    else{
      _nodeList[i]->addGoodControl(_goodControl);
    } 
  }
}
void meowBound2::removeBadSingle(){
  set<int> middleBits;
  set<meowNode*>::iterator site = _goodNodes.begin();
  for(; site!= _goodNodes.end(); ++site)
    (*site)->addMiddleBits(middleBits);
  set<meowNode*> badNodes;
  site = _goodNodes.begin();
  for(; site!= _goodNodes.end(); ++site){
    if((*site)->getLevel() >= 3)
      continue;
    vector<int>& outIDs = (*site)->getOutIDs();
    bool success = false;
    Gia_Obj_t* pCurrent;
    Gia_Obj_t* pFanout;
    int j;
    for(int i = 0; i < outIDs.size(); ++i){
      if(outIDs[i] == 0)
        continue; 
      pCurrent = Gia_ManObj(_cir, outIDs[i]);
      Gia_ObjForEachFanoutStatic(_cir, pCurrent, pFanout, j){
        int fanoutID = Gia_ObjId(_cir, pFanout);
        if(middleBits.find(fanoutID)!= middleBits.end()){
          success = true; 
          break;
        }
      }
    }
    if(!success)
      badNodes.insert(*site);
  }
  site = badNodes.begin();
  for(; site != badNodes.end(); ++site){
    vector<int>& outIDs = (*site)->getOutIDs();
    _goodNodes.erase(*site);
    for(int i = 0; i < outIDs.size(); ++i)
      _gate2Node.erase(outIDs[i]);
  }
    // remove fanouts not middle one
  
}
void meowBound2::collectNodes(){
  map<int, meowNode*>::iterator mite = _gate2Node.begin();
  set<int> driveOuts;
  set<int> remove;
  _middleBits.clear();
  _goodNodes.clear();
  for(; mite!= _gate2Node.end(); ++mite){
    if(_goodNodes.find(mite->second)!= _goodNodes.end())
       continue;
    //vector<int>& outIDs = mite->second->getOutIDs();
    if((mite->second)->getWidth() >= 4){
      _goodNodes.insert(mite->second); 
      (mite->second)->addGoodControl(_goodControl);
      mite->second->addMiddleBits(_middleBits);
      /*for(int i = 0; i < outIDs.size(); ++i){
        if(outIDs[i] == 0)
          continue;
        if(driveOuts.find(outIDs[i])!= driveOuts.end())
          cerr<<"Hey!"<<outIDs[i]<<endl;
        driveOuts.insert(outIDs[i]);
      }*/
    }
    else{
      remove.insert(mite->first);
      // clean _gate2Node
    } 
  }
  set<int>::iterator site = remove.begin();
  for(; site!= remove.end(); ++site)
    _gate2Node.erase(*site);
  // when to deal with those single level words


}
void meowBound2::addGate2Node(bool dropAllSingle){
  // this is important: after finding all words
// make unique gate to node! ideally no conflict here ?

  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badNodes.find(_nodeList[i])!= _badNodes.end())
      continue;
    if(_internalWords.find(_nodeList[i])!= _internalWords.end())
      continue;
    if(_muxNodes.find(_nodeList[i]) == _muxNodes.end()){
      if(!_nodeList[i]->isGoodNode(dropAllSingle)) 
        continue;

    }
    vector<int>& outIDs = _nodeList[i]->getOutIDs();
    for(int j = 0; j < outIDs.size(); ++j){
      if(outIDs[j] == 0)
        continue;
      if(_gate2Node.find(outIDs[j])== _gate2Node.end())
        _gate2Node[outIDs[j]] = _nodeList[i];
      else{
        meowNode* oldNode = _gate2Node[outIDs[j]];
        if(_nodeList[i]->isBetter(oldNode)){ // update2New!
          _gate2Node[outIDs[j]] = _nodeList[i];
          oldNode->removeOut(outIDs[j]);
        }
        else
          _nodeList[i]->removeOut(outIDs[j]);
      }
    }
  }
}
// for reconnect
void meowBound2::sortByOutputs(set<meowNode*>& inNodes, vector<meowNode*>& orders){
  vector< pair<int, meowNode*> > max_node;
  set<meowNode*>::iterator site = inNodes.begin();
  for(; site!= inNodes.end(); ++site){
    int maxOut = (*site)->getMaxOut();
    if(maxOut)
      max_node.push_back(pair<int, meowNode*>(maxOut, (*site)));
  }
  sort(max_node.begin(), max_node.end());
  for(int i = 0; i < max_node.size(); ++i)
    orders.push_back(max_node[i].second);
}
void meowBound2::sortByOutputs(vector<int>& orders){
  vector< pair<int, int> > index_max;
  for(int i = 0; i < _nodeList.size(); ++ i){
    if(_badNodes.find(_nodeList[i])== _badNodes.end()&&
      _internalWords.find(_nodeList[i])== _internalWords.end()){
      if(_muxNodes.find(_nodeList[i]) == _muxNodes.end()){
        if(!_nodeList[i]->isGoodNode(false))
          continue;
      }
      int maxOut = _nodeList[i]->getMaxOut();
      if(maxOut)
        index_max.push_back(pair<int, int>(maxOut, i)); 
    }
  }
  sort(index_max.begin(), index_max.end());
  for(int i = 0; i < index_max.size(); ++i)
    orders.push_back(index_max[i].second);
}
void meowBound2::splitbyFanouts(meowNode* current, map<int, set<meowNode*>* >& in2Nodes ){
  map<string, vector<int>*> key2List;
  vector< vector<int>* > tempList; 
  vector<int>& outIDs = current->getOutIDs();
  if(outIDs.size() < 2)
    return;
  for(int i = 0; i < outIDs.size(); ++i){
    if(outIDs[i]){
      ostringstream convert;
      if(in2Nodes.find(outIDs[i])!= in2Nodes.end()){
        set<meowNode*>* nodeList = in2Nodes[outIDs[i]];
        set<meowNode*>::iterator site = nodeList->begin();
        for(; site!= nodeList->end(); ++site)
          convert<<(*site)->getWordID()<<"&";
      }
      else
        convert<<"NA";
      
      string key = convert.str();
      if(key2List.find(key) == key2List.end()){
        vector<int>* newList = new vector<int>;
        key2List[key] = newList;
        tempList.push_back(newList);
      }
      key2List[key]->push_back(i);
    }
  }
  if(key2List.size() > 1){
    map<string, vector<int>* >::iterator mite = key2List.begin();
    for(; mite!= key2List.end(); ++mite){
    //  current->printNode();
      meowNode* newNode = current->splitNode(_nodeList.size(),
                                             mite->second );
      _nodeList.push_back(newNode);
      _goodNodes.insert(newNode);
      for(int x = 0; x < (mite->second)->size(); ++x)
        _gate2Node[outIDs[(*(mite->second))[x]]] = newNode;
      // update _gate2Node
     // newNode->printNode();
      //if(_storeIn2Nodes.find(current)!= _storeIn2Nodes.end()){
      set<int> fanins;
      newNode->getInputs(fanins);
      
      set<int>::iterator site = fanins.begin();
      for(; site!= fanins.end(); ++site){
        if(in2Nodes.find(*site) == in2Nodes.end())
          cerr<<"why?"<<*site<<endl;
        if(in2Nodes[*site]->find(current)!= in2Nodes[*site]->end())
          in2Nodes[*site]->erase(current);
        in2Nodes[*site]->insert(newNode);

      }
    }
    _goodNodes.erase(current);
    _badNodes.insert(current);
  }
  for(int i = 0; i < tempList.size() ; ++i)
    delete tempList[i];


}
void meowBound2::splitbyFanins(meowNode* current){
  map<string, vector<int>*> key2List;
  vector< vector<int>* > tempList; 
  vector<int>& outIDs = current->getOutIDs();
  if(outIDs.size() < 2)
    return;
  for(int i = 0; i < outIDs.size(); ++i){
    if(outIDs[i]){
      vector<int> fanins;
      current->getFanins(i, fanins);
      ostringstream convert;
      for(int j = 0; j < fanins.size(); ++j){
        Gia_Obj_t* pFanin = Gia_ManObj(_cir, fanins[j]);
        if(Gia_ObjIsPi(_cir, pFanin))
          convert<<"PI&";
        else if(_gate2Node.find(fanins[j]) != _gate2Node.end()){
          convert<<_gate2Node[fanins[j]]->getWordID()<<"&";
        }
        else
          convert<<"NO&"; 

      }
      Gia_Obj_t* pFanout = Gia_ManObj(_cir, outIDs[i]);
      if(Gia_ObjIsPo(_cir, pFanout))
        convert<<"PO";
      string key = convert.str();
      if(key2List.find(key) == key2List.end()){
        vector<int>* newList = new vector<int>;
        key2List[key] = newList;
        tempList.push_back(newList);
      }
      key2List[key]->push_back(i);
    }
  }
  if(key2List.size() > 1){
    map<string, vector<int>* >::iterator mite = key2List.begin();
    for(; mite!= key2List.end(); ++mite){
      meowNode* newNode = current->splitNode(_nodeList.size(),
                                             mite->second );
      _nodeList.push_back(newNode); // newNode
      _goodNodes.insert(newNode);
      for(int x = 0; x < (mite->second)->size(); ++x) 
        _gate2Node[outIDs[(*(mite->second))[x]]] = newNode;
    }
    _goodNodes.erase(current);
    _badNodes.insert(current);
  }
  for(int i = 0; i < tempList.size() ; ++i)
    delete tempList[i];
}
void meowBound2::reconnect(){
 // merge or split
  // 0. sort by outputs
  vector<meowNode*> orders;
  sortByOutputs(_goodNodes, orders);
  for(int i = 0; i < orders.size(); ++i)
    splitbyFanins(orders[i]); 
  // 1. split by fanins
  
  // 2.0 collect inID -> nodes
  map<int, set<meowNode*>* > in2Nodes;
  collectIn2Nodes(in2Nodes);
  orders.clear();
  sortByOutputs(_goodNodes, orders);

  for(int i = orders.size()-1; i >= 0; --i){
    splitbyFanouts(orders[i], in2Nodes);
  }
  map<int, set<meowNode*>* >::iterator mite = in2Nodes.begin();
  for(; mite != in2Nodes.end(); ++mite)
    delete mite->second; 
    //2. split by fanouts
}
void meowBound2::collectIn2Nodes( map<int, set<meowNode*>* >& in2Nodes){
  set<meowNode*>::iterator site = _goodNodes.begin(); 
  for(; site != _goodNodes.end(); ++site){
    set<int> fanins;
    (*site)->getInputs(fanins);
    set<int>::iterator site2 = fanins.begin();
    for(; site2!= fanins.end(); ++site2){
      if(in2Nodes.find(*site2) == in2Nodes.end()){
        set<meowNode*>* newSet = new set<meowNode*>;
        in2Nodes[*site2] = newSet;
      }
      in2Nodes[*site2]->insert(*site);
    } 
     // cerr<<endl;
  }
}
void meowBound2::updateControlSupport(int gateID, Gia_Obj_t* pObj){
  if(Gia_ObjIsPi(_cir, pObj) || Gia_ObjIsPo(_cir, pObj))
    return;
  // this function takes all control candidates into list for each gate
  set<int>* supportSet = NULL;
  if(_gate2ControlSupports.find(gateID) == _gate2ControlSupports.end()){
    supportSet = new set<int>;
    _gate2ControlSupports[gateID] = supportSet;
  }
  else
    supportSet = _gate2ControlSupports[gateID];
  
  int faninID0 = Gia_ObjFaninId0(pObj, gateID);
  if(_gate2ControlSupports.find(faninID0) != _gate2ControlSupports.end()){
    supportSet->insert(_gate2ControlSupports[faninID0]->begin(),
                       _gate2ControlSupports[faninID0]->end());
  }
  int faninID1 = Gia_ObjFaninId1(pObj, gateID);
  if(_gate2ControlSupports.find(faninID1) != _gate2ControlSupports.end()){
    supportSet->insert(_gate2ControlSupports[faninID1]->begin(),
                       _gate2ControlSupports[faninID1]->end());
  }
}
void meowBound2::decideOrder(){
  int i, j;
  Gia_Obj_t* pObj;
  Gia_Obj_t* pFanout;
  Gia_ManForEachObj1(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj); // control candidate
    if(Gia_ObjFanoutNum(_cir, pObj) > 3){
      int bigOne = 0;
      vector<int>* newList = new vector<int>; 
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
        if(Gia_ObjIsPo(_cir, pFanout))
          continue;
        int fanoutID = Gia_ObjId(_cir, pFanout);
        if(_gate2ControlSupports.find(fanoutID) == _gate2ControlSupports.end()){
          set<int>* newSet = new set<int>;
          newSet->insert(gateID);
          _gate2ControlSupports[fanoutID] = newSet;
        }
        else
          _gate2ControlSupports[fanoutID]->insert(gateID);

        newList->push_back(fanoutID);
        if(fanoutID > bigOne)
          bigOne = fanoutID;
      }
      _control2Fanouts[gateID] = newList;
      //bigOne  = Gia_ObjFanoutNum(_cir, pObj);
      _control_score.push_back(pair<int, int>(bigOne, gateID));

      // bigOne could be fanout numbers
    }
    updateControlSupport(gateID, pObj); 
    // collect control supports for ALL signals
  }
  sort(_control_score.begin(), _control_score.end());
}
void meowBound2::computeSingleControl(){
  for(int k = 0; k < _control_score.size(); ++k){
  //for(int k = _control_score.size()-1; k >= 0; --k){
    set<int> control;
    control.insert(_control_score[k].second);
    enumerateControls(control); 
  }
}
void meowBound2::enumerateControls(set<int>& controls){
  vector<int> gateIDs;
  set<int>::iterator site = controls.begin();
  for(; site!= controls.end(); ++site)
    gateIDs.push_back(*site);
  map<int, my_out2EqList > assign2EqList;
  map<int, vector<bool> > assign2Phases;
  map<int, vector<int> > out2Assign; // assign ids
 
  vector<bool> phases;
  int upperBound = 1<<(gateIDs.size());
  for(int i = 0; i < upperBound; ++i){
    phases.clear();
    for(int j = 0; j < gateIDs.size(); ++j){
      if(i&(1<<j))
        phases.push_back(true);
      else
        phases.push_back(false);
    }
    my_out2EqList out2EqList;
    findEquivalence(gateIDs, phases, out2EqList);
    if(out2EqList.size() > 3){
      assign2EqList[i] = out2EqList;
      assign2Phases[i] = phases;
      computeOut2Assign(out2Assign, i, out2EqList);
    }
  }
  analyzeWords(assign2EqList, assign2Phases, gateIDs, out2Assign);
}
void meowBound2::computeOut2Assign(map<int, vector<int> >& out2Assign, int assign, map<int, vector<int> >& out2EqList){
  // this function collect outpus -> assigns make it equivalent
  map<int, vector<int> >::iterator mite = out2EqList.begin();
  for(; mite!= out2EqList.end(); ++mite){
    if(out2Assign.find(mite->first)!= out2Assign.end())
      out2Assign[mite->first].push_back(assign);
    else{
      vector<int> newList;
      newList.push_back(assign);
      out2Assign[mite->first] = newList;
    }
  }
}
void meowBound2::assignControls(vector<int>& gateIDs,
                                vector<bool>& phases){
  Gia_Obj_t * pObj;

  for(int k = 0; k < gateIDs.size(); ++k){ // assign control
    pObj = Gia_ManObj(_cir, gateIDs[k]);
    if(phases[k]) // True->1
      pObj->Value = 1;
    else
      pObj->Value = 0;
  }
}
void meowBound2::assignSides(vector<int>& gateIDs, map<int, int>& new2oldID, set<int>& fanouts){
  Gia_Obj_t * pObj;

  for(int k = 0; k < gateIDs.size(); ++k){ // for all controls
    vector<int>* fanoutList = _control2Fanouts[gateIDs[k]];
    fanouts.insert(fanoutList->begin(), fanoutList->end());

    for(int j = 0; j < fanoutList->size(); ++j){
      pObj = Gia_ManObj(_cir, (*fanoutList)[j]);
      Gia_Obj_t* fanin0 = Gia_ObjFanin0(pObj);
      Gia_Obj_t* fanin1 = Gia_ObjFanin1(pObj);
      if(fanin0->Value == ~0){ // empty
        new2oldID[_currentID] = Gia_ObjId(_cir, fanin0); 
        fanin0->Value = _currentID << 1;
        _currentID++;
      }
      if(fanin1->Value == ~0){
        new2oldID[_currentID] = Gia_ObjId(_cir, fanin1);
        fanin1->Value = _currentID<<1;
 
        _currentID++;
      }
    }
  }
}
int meowBound2::addAnd(int Lit0, int Lit1){

  // currently: only constant propagation
  if ( Lit0 < 2 )
    return Lit0 ? Lit1 : 0;
  if ( Lit1 < 2 )
    return Lit1 ? Lit0 : 0;
  if ( Lit0 == Lit1 )
    return Lit1;
  if ( Lit0 == Abc_LitNot(Lit1) )
    return 0;
  // TODO consider two level logic 
  int assignedLit =  _currentID << 1;
  _currentID++;
  return assignedLit;
}

void meowBound2::assignFanouts(
    set<int>& fanouts, 
    set<int>& currentFront,
    map<int, int>& new2oldID,
    vector<vector<int> >& tempEqList,
    map<int, int>& gate2prev,
    map<int, int>& tail2Pos){
  set<int>::iterator site = fanouts.begin();
  // step3, handle fanouts
  Gia_Obj_t * pObj;

  for(; site!= fanouts.end(); ++site){
    pObj = Gia_ManObj(_cir, (*site));
    if(~pObj->Value)
      continue;
    int oldCurrent = _currentID;
    pObj->Value = addAnd(Gia_ObjFanin0Copy(pObj),
                         Gia_ObjFanin1Copy(pObj));
    if(oldCurrent != _currentID)
      cerr<<"something Wrong!"<<endl;
    else{
      int mapID = (pObj->Value) >> 1;
      int oldID = Gia_ObjId(_cir, pObj);

      if(mapID!= 0){//transparent!
        if(Abc_LitIsCompl(pObj->Value))
          oldID = -1*oldID;
        if(new2oldID.find(mapID) == new2oldID.end())
          cerr<<"something wrong2!"<<endl;
        else{
          vector<int> newList;
          newList.push_back(new2oldID[mapID]);
          newList.push_back(oldID);
          tail2Pos[abs(oldID)] = tempEqList.size();
          tempEqList.push_back(newList);
        }
      }
      int x;
      Gia_Obj_t* pFanout;
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, x){
        if(Gia_ObjIsPo(_cir, pFanout))
          continue;
        currentFront.insert(Gia_ObjId(_cir, pFanout));
        if(mapID!= 0){
          gate2prev[Gia_ObjId(_cir, pFanout)] = abs(oldID);
        }
      }
    } // successfully move forward
  } 
}
void meowBound2::assignForward(set<int>& currentFront,
                       map<int, int>& new2oldID,
                       vector<vector<int> >& tempEqList,
                       map<int, int>& gate2prev,
                       map<int, int>& tail2Pos,
                       int sideBound,
                       set<int>& deletePos){
  Gia_Obj_t * pObj;

  while(currentFront.size() != 0){
    set<int> nextFront;
    set<int>::iterator site = currentFront.begin();
    for(; site!= currentFront.end(); ++site){
      pObj = Gia_ManObj(_cir, (*site));
      if(~pObj->Value){ // not empty
        if( (pObj->Value)>>1 >= sideBound )
          continue;
      }
      if(Gia_ObjFanin0(pObj)->Value == ~0 
      || Gia_ObjFanin1(pObj)->Value == ~0){
        continue;// unknown side
      }
      int oldCurrent = _currentID;
      pObj->Value = addAnd(Gia_ObjFanin0Copy(pObj),
                           Gia_ObjFanin1Copy(pObj) );
      //cerr<<"ID "<<(*site)<<", new ID"<< ((pObj->Value)>>1)<<endl;
      if(oldCurrent ==  _currentID){ // transparent
        int oldID = Gia_ObjId(_cir, pObj);
        int mapID = (pObj->Value) >> 1;
        if(Abc_LitIsCompl(pObj->Value))
          oldID = -1*oldID;
        if(mapID != 0){
          if(gate2prev.find(abs(oldID)) == gate2prev.end())
            continue;
          int prevG = gate2prev[abs(oldID)];
          if(mapID != ((Gia_ManObj(_cir, prevG)->Value)>>1)){
            continue;
          }
          if(tail2Pos.find(prevG) == tail2Pos.end()){
           // cerr<<"Wrong4"<<endl;
            continue;
          }
          int tempListPos = tail2Pos[prevG];
          deletePos.insert(tempListPos);
          vector<int> newList;
          for(int w = 0; w < tempEqList[tempListPos].size();++w)
            newList.push_back(tempEqList[tempListPos][w]);
          newList.push_back(oldID);
          tail2Pos[abs(oldID)] = tempEqList.size();
          tempEqList.push_back(newList);   
        }
        int x;
        Gia_Obj_t* pFanout;
        Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, x){
          if(Gia_ObjIsPo(_cir, pFanout))
            continue;
          currentFront.insert(Gia_ObjId(_cir, pFanout));
          if(mapID!= 0){
            gate2prev[Gia_ObjId(_cir, pFanout)] = abs(oldID);
          }
        }
      }
    } 
    currentFront.swap(nextFront); 
  }
}
void meowBound2::removeBadEqBits(
vector<vector<int> >& tempEqList, set<int>& deletePos, vector<int>& gateIDs){
  for(int i = 0; i < tempEqList.size(); ++i){
    if(deletePos.find(i)!= deletePos.end())
      continue;
    
    bool getSide = false;
    bool getSupp = true;
    int targetID = abs(tempEqList[i][1]);
    Gia_Obj_t* target = Gia_ManObj(_cir, targetID);
    int faninID0 = Gia_ObjFaninId0(target, targetID);
    int faninID1 = Gia_ObjFaninId1(target, targetID);
    int thisOut = abs(tempEqList[i].back());
    set<int>* suppSet = _gate2ControlSupports[thisOut]; 
    for(int m = 0; m < gateIDs.size(); ++m){
      if(faninID0 == gateIDs[m] || faninID1 == gateIDs[m])
        getSide = true;
      if(suppSet->find(gateIDs[m]) == suppSet->end()){
        getSupp = false;
        break;
      }
    }
    if(!getSide || !getSupp) // bad
      deletePos.insert(i);
  }

}

void meowBound2::findEquivalence(vector<int>& gateIDs, vector<bool>& phases, my_out2EqList& out2EqList ){
  vector<vector<int> > tempEqList;
  set<int> deletePos;
  map<int, int> gate2prev;
  map<int, int> tail2Pos;
  map<int, int> new2oldID; // ? 
 
  Gia_Obj_t * pObj;
  Gia_ManFillValue( _cir );
  Gia_ManConst0(_cir)->Value = 0;
  assignControls(gateIDs, phases);

  _currentID = 1;
  set<int> fanouts;
  assignSides(gateIDs, new2oldID, fanouts);
 
  int sideBound = _currentID;
  set<int> currentFront;
  assignFanouts( fanouts, currentFront, new2oldID, tempEqList,
                 gate2prev, tail2Pos);

  assignForward(currentFront, new2oldID, tempEqList, gate2prev, 
                tail2Pos, sideBound, deletePos);

  // add: remove bad/weird bits
  removeBadEqBits(tempEqList, deletePos, gateIDs); 
 
  for(int i = 0; i < tempEqList.size(); ++i){
    if(deletePos.find(i) == deletePos.end()){
      out2EqList[abs(tempEqList[i].back())] = tempEqList[i];
    }
  }

}
void meowBound2::computeAssign2Words(map<int, vector<int> >& out2Assign, map<string, vector<int> >& key2Group,
  map<string, vector<int> >& key2Assign){
  map<int, vector<int> >::iterator mite = out2Assign.begin();
  for(; mite!= out2Assign.end(); ++mite){
    ostringstream convert; 
    for(int i = 0; i < (mite->second).size(); ++i)
      convert<<(mite->second)[i]<<"&";
   
    string key = convert.str();
    if(key2Group.find(key)!= key2Group.end()){
      key2Group[key].push_back(mite->first);
    }
    else{
      key2Assign[key] = mite->second;
      vector<int> newGroup;
      newGroup.push_back(mite->first);
      key2Group[key] = newGroup;
    }
  } 

}
void meowBound2::analyzeWords(
     map<int, my_out2EqList >& assign2EqList,
     map<int, vector<bool> >& assign2Phases,
     vector<int>& gateIDs, map<int, vector<int> >& out2Assign){ 
  // this function analyzes all equi List and create "words"

// gateIDs -> control
  map<string, vector<int> > key2Group;
  map<string, vector<int> > key2Assign;
  computeAssign2Words(out2Assign, key2Group, key2Assign);
  // here we do not consider "level" 
  // finally add words, middle bits?
  vector<meowNode*>* newList = NULL;
  if(gateIDs.size() == 1){
    vector<meowNode*>* newList = new vector<meowNode*>;
    _control2Nodes[gateIDs[0]] = newList;
  }
  map<string, vector<int> >::iterator mite = key2Group.begin();
  for(; mite!= key2Group.end(); ++mite){ // foreach group
    vector<int>& assigns = key2Assign[mite->first];
    meowNode* newNode = new meowNode(_nodeList.size(), 
                                     gateIDs, mite->second); 
    _nodeList.push_back(newNode);
    if(newList)
      newList->push_back(newNode);
    for(int i = 0; i < assigns.size(); ++i){ // foreach input
      vector<int> faninIDs;
      vector<vector<int> > eqList;
      for(int j = 0; j < mite->second.size(); ++j){ // foreach bits
        vector<int>& subEqList = 
            assign2EqList[assigns[i]][mite->second[j]];
        if(mite->second[j] != abs(subEqList.back()))
          cerr<<"ERROR!!"<<endl;
        int faninID = subEqList.front();
        if(subEqList.back() < 0)
          faninID = faninID*(-1);
        faninIDs.push_back(faninID);
        eqList.push_back(subEqList);
      }
      newNode->addFaninWord(assign2Phases[assigns[i]],
                            faninIDs, eqList); 
    }
    if(gateIDs.size() > 1){ // add gate2Word & _provedBits
      // MeowMeow 
      if(newNode->isGoodNode(false)){ // ?
        //newNode->addProvedBits(_provedBits);
        newNode->addMiddleBits(_middleBits);
      }
     // else
     //   _badNodes.insert(newNode);
      updateGate2WordList(newNode);
    }
    //add for proceeding words
  } // for each new node 
}
void meowBound2::printNodes(){ // isGoodNode(true) do not print simple
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badNodes.find(_nodeList[i])== _badNodes.end()&&
      _internalWords.find(_nodeList[i])== _internalWords.end()){
      if(_nodeList[i]->isGoodNode(true))
        _nodeList[i]->printNode();
    }
  }
}
void meowBound2::printReport(){
  int maxWidth = 0;
  int minWidth = 0;
  set<meowNode*> inNodes;
  // update _middle
  _middleBits.clear();
  _fanoutMiddleNodes.clear();
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badNodes.find(_nodeList[i])== _badNodes.end()&&
      _internalWords.find(_nodeList[i])== _internalWords.end()){
      if(_nodeList[i]->isGoodNode(false)){ 
         int thisWidth = _nodeList[i]->getWidth();
         if(thisWidth < 4)
           continue;
         _nodeList[i]->addMiddleBits(_middleBits);
      } 
    }
  }  
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badNodes.find(_nodeList[i])== _badNodes.end()&&
      _internalWords.find(_nodeList[i])== _internalWords.end()){
      if(true){ // TODO
         int thisWidth = _nodeList[i]->getWidth();
         if(thisWidth < 4)
           continue;
         if(_nodeList[i]->getInputNum() < 2
          && !isFanoutMiddleWord(_nodeList[i]) ) // single Level
           continue; // TODO
         _nodeList[i]->addProvedBits(_provedBits);
         inNodes.insert(_nodeList[i]);
         //_nodeList[i]->printNode();
         if(minWidth == 0 || thisWidth < minWidth)
           minWidth = thisWidth;
         if(maxWidth == 0 || thisWidth > maxWidth)
           maxWidth = thisWidth;
      }
    }
  }
  cerr<<"Bits:"<<_provedBits.size()<<endl;
  cerr<<"Wdith:"<<minWidth<<" to "<<maxWidth<<endl;
  printLevel(inNodes);
  printLevelNew();
  printForward(inNodes);
  printForwardNew(); 
}
void meowBound2::printReportNew(){
  // we should only consider "_goodNodes"
  int maxWidth = 0;
  int minWidth = 0;
  set<int> bits;
  _middleBits.clear();
  _fanoutMiddleNodes.clear();
  _provedBits.clear();
  set<meowNode*>::iterator site = _goodNodes.begin();
  for(; site!= _goodNodes.end(); ++site){
    (*site)->addMiddleBits(_middleBits); // only exclude fanin 
    (*site)->addProvedBits(_provedBits); // all
    if((*site)->getWidth() > maxWidth)
      maxWidth = (*site)->getWidth();
    if(minWidth == 0 || (*site)->getWidth() < minWidth)
     minWidth = (*site)->getWidth();
  } 
  cerr<<"Bits:"<<_provedBits.size()<<endl;
  cerr<<"Wdith:"<<minWidth<<" to "<<maxWidth<<endl;
  
  printLevel(_goodNodes);
  printLevelNew();
  printForward(_goodNodes);
  printForwardNew();
}
int meowBound2::collectLevelRecur(meowNode* current, map<meowNode*, int>& node2Level){
  if(node2Level.find(current)!= node2Level.end())
    return node2Level[current];

  
  vector<int>& outIDs = current->getOutIDs();
  vector<int> levels;
  current->getLevels(levels); // level has been modified
  node2Level[current] = levels[0];
 // current->getInputs(fanins); // work after split
  int maxLevel = 0;
 // set<int>::iterator site = fanins.begin();
  for( int i = 0; i < outIDs.size(); ++i){
    //int max = 0;
    if(outIDs[i] == 0)
      continue;
    vector<int> fanins;
    current->getFanins(i, fanins);
    for(int j = 0; j < fanins.size(); ++j){
      if(_gate2Node.find(fanins[j])!=_gate2Node.end()){
        int mLevel = collectLevelRecur(_gate2Node[fanins[j]], node2Level);
        if((mLevel+levels[j]) > maxLevel)
          maxLevel = mLevel+levels[j];
      }
      else if(levels[j] > maxLevel)
        maxLevel = levels[j];
    }
  }
  node2Level[current] = maxLevel;
//  cerr<<"max Level?"<<maxLevel<<endl;
  return maxLevel;
  //vector<int>& outputs = current->getOutIDs();
  //for(int i = 0; i < outputs.size(); ++i) 
}
void meowBound2::printLevelNew(){
  map<int, int> gate2Level;
  set<int>::iterator site = _middleBits.begin();
  int maxLevel = 0;
  for(; site != _middleBits.end(); ++site){
    Gia_Obj_t* current = Gia_ManObj(_cir, (*site));
    if(Gia_ObjIsPi(_cir, current)) { 
      gate2Level[*site] = 0;
      continue;
    }
  /*  if(_middleBits.find(*site) == _middleBits.end()){
      gate2Level[*site] = 0;
      continue;
    }*/
    int faninID0 = Gia_ObjFaninId0(current, (*site)); 
    int faninID1 = Gia_ObjFaninId1(current, (*site));
    int max = -1;
    if(_middleBits.find(faninID0)!= _middleBits.end())
      max = gate2Level[faninID0];
    if(_middleBits.find(faninID1)!= _middleBits.end()){
      if(max < gate2Level[faninID1])
        max = gate2Level[faninID1];
    }
    gate2Level[*site] = max+1;
    if(gate2Level[*site] > maxLevel)
      maxLevel = gate2Level[*site];
  } 
  cerr<<"Max Level:"<<maxLevel<<endl;
}
void meowBound2::printLevel(set<meowNode*>& inNodes){
  int maxLevel = 0;
  int minLevel = 0;
  map<meowNode*, int> node2Level;
  set<meowNode*>::iterator site = inNodes.begin();
  for(; site!= inNodes.end(); ++site){
    collectLevelRecur(*site, node2Level); 
    if(!isFanoutMiddleWord((*site))){
      if(node2Level[*site] > maxLevel)
        maxLevel = node2Level[*site];
      if(minLevel == 0 || node2Level[*site] < minLevel)
        minLevel = node2Level[*site];
    }
    
      
    //  continue;
    //vector<int>& outIDs = (*site)->getOutIDs();
    //for(int j = 0; j < outIDs.size(); ++j)
    //  collectLevelRecur(outIDs[j]
  }
  cerr<<"maxLevel "<<maxLevel<<", minLevel "<<minLevel<<endl;
}
void meowBound2::printForwardPart(set<meowNode*>& inNodes){


}
void meowBound2::printForwardNew(){
  set<int> piList;
  set<int> bitList; 
  Gia_Obj_t* pObj;
  int i;
  Gia_ManForEachPi(_cir, pObj, i){
    piList.insert(Gia_ObjId(_cir, pObj));
  }
  set<int>::iterator site = _provedBits.begin();
  for(; site!= _provedBits.end(); ++site){
    if(piList.find(*site)!= piList.end()){
      bitList.insert(*site);
      continue;
    }
    if(_middleBits.find(*site) == _middleBits.end())
      continue;
    Gia_Obj_t* current = Gia_ManObj(_cir, (*site));

    int faninID0 = Gia_ObjFaninId0(current, (*site)); 
    int faninID1 = Gia_ObjFaninId1(current, (*site));
    if(( (piList.find(faninID0)!= piList.end())
       ||(_goodControl.find(faninID0)!=_goodControl.end())) 
    && ( (piList.find(faninID1)!= piList.end())
       ||(_goodControl.find(faninID1)!=_goodControl.end()))){
      bitList.insert(*site);
      piList.insert(*site); 
    }
  }
  cerr<<"new Forward!"<<bitList.size()<<endl;
}
void meowBound2::printForward(set<meowNode*>& inNodes){
  //vector<meowNode*> orders;
  //sortByOutputs(inNodes, orders);
  vector<meowNode*> orders;
  sortByOutputs(inNodes, orders); //
  set<int> piList;
  set<int> bitList; 
  Gia_Obj_t* pObj;
  int i;
  Gia_ManForEachPi(_cir, pObj, i){
    piList.insert(Gia_ObjId(_cir, pObj));
  }

  for(int i = 0; i < orders.size(); ++i){
    set<int> faninList;
    orders[i]->getInputs(faninList);
    set<int>::iterator site = faninList.begin();
    bool fail = false;
    for(; site!= faninList.end(); ++site){
      if(piList.find((*site)) == piList.end()){
        fail = true;
        break;
      }
    }
    if(!fail){
      orders[i]->addProvedBits(bitList);
      vector<int>& outputs = orders[i]->getOutIDs();
      piList.insert(outputs.begin(), outputs.end());
    }
  }
  cerr<<"Forward Bits: "<<bitList.size()<<endl;
}
void meowBound2::addFaninCone(int currentID, set<int>& transBits, set<int>& include, set<int>* fanins){
  if(currentID == 0)
    return; // should not happen
  if(include.find(currentID)!= include.end())
    return;
  if(transBits.find(currentID)!= transBits.end()){
    fanins->insert(currentID);
    return;
  }
  
  Gia_Obj_t* current = Gia_ManObj(_cir, currentID);
  if(Gia_ObjIsPi(_cir, current)){
    fanins->insert(currentID);
    return;

  }
 
  include.insert(currentID);
  if(currentID == 2584)
    cerr<<"Hello?"<<endl; 
  int faninID0 = Gia_ObjFaninId0(current, currentID); 
  int faninID1 = Gia_ObjFaninId1(current, currentID);
  addFaninCone(faninID0, transBits, include, fanins);
  addFaninCone(faninID1, transBits, include, fanins);
}
void meowBound2::groupSubCircuits2(set<int>& transBits, vector<vector<int>* >& groups, set<int>& needIDs, vector<set<int>* >& fanouts, vector<set<int>* >& fanins){
  set<meowNode*>::iterator site = _goodNodes.begin();
  int groupID = 0;
  map<int, int> id2Group;
  set<int> controls;
  map<int, set<int>* > group2Set;
  for(; site!=_goodNodes.end(); ++site){
    (*site)->addGoodControl(controls);
    vector<vector<int> >& inputs = (*site)->getInIDs();
    vector<int>& outputs = (*site)->getOutIDs();
    for(int i = 0; i < inputs.size(); ++i){
      set<int> newSet; 
      for(int j = 0; j < inputs[i].size(); ++j){
        if(outputs[j] == 0) // removed
          continue;
        Gia_Obj_t* current = Gia_ManObj(_cir, abs(inputs[i][j]));
        if(Gia_ObjIsPi(_cir, current))
          continue; 
        if(transBits.find(abs(inputs[i][j]))!= transBits.end())
          continue; 
        if(id2Group.find(abs(inputs[i][j]))== id2Group.end()){
          newSet.insert(abs(inputs[i][j]));
          id2Group[abs(inputs[i][j])] = groupID;
        }
      }
      if(newSet.size() != 0){
        set<int>* addSet = new set<int>;
        addSet->insert(newSet.begin(), newSet.end());
        group2Set[groupID] = addSet;
        groupID++;
      }
    }
  } // for each "input words"/ collect non-overlapping ids
  set<int>* controlSet = new set<int>;
  set<int>::iterator site2 = controls.begin();
  
  for(; site2!= controls.end(); ++site2){
    //cerr<<"control "<<(*site2)<<endl;
      if(id2Group.find((*site2))== id2Group.end()){
      //cerr<<"add"<<endl;
        Gia_Obj_t* current = Gia_ManObj(_cir, *site2);
        if(Gia_ObjIsPi(_cir, current))
          continue; 
   
        if(transBits.find(*site2)!= transBits.end())
          continue;
      controlSet->insert((*site2));
      id2Group[(*site2)] = groupID;
    }
  }
  group2Set[groupID] = controlSet;
  groupID++;
  set<int>* fanoutSet = new set<int>;
  site2 = needIDs.begin();
  
  for(; site2!=needIDs.end(); ++site2){
    if(id2Group.find((*site2))==id2Group.end()){
      if(transBits.find(*site2)== transBits.end()){
        Gia_Obj_t* current = Gia_ManObj(_cir, *site2);
        if(Gia_ObjIsPi(_cir, current))
          continue; 
   

        fanoutSet->insert(*site2);
        id2Group[(*site2)] = groupID;
      }
    }
  }
  group2Set[groupID] = fanoutSet;
  // done with partition!!
  map<int, set<int>* >::iterator mite = group2Set.begin();
  for(; mite!= group2Set.end(); ++mite){
    set<int> include;
    set<int>::iterator site3 = (mite->second)->begin();
    set<int>* gfanins = new set<int>;
    for(; site3!= (mite->second)->end(); ++site3)
      addFaninCone((*site3), transBits, include, gfanins);

    vector<int>* newGroup = new vector<int>;
    site3 = include.begin();
    for(; site3 != include.end(); ++site3)
      newGroup->push_back(*site3);

    groups.push_back(newGroup);
    fanouts.push_back(mite->second);
    fanins.push_back(gfanins);
  //  delete mite->second;
    // recursive
    // find fanincone and put into "groups"  
    
  }
}
void meowBound2::groupSubCircuits(set<int>& transBits, vector<vector<int>* >& groups){
  int i;
  Gia_Obj_t* pObj;
  map<int, set<int>*> gate2Supps;
  // step 2 decide supports
  Gia_ManForEachObj1(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    if(transBits.find(gateID)!= transBits.end())
      continue;
    if(Gia_ObjIsPo(_cir, pObj))
      continue;
    if(Gia_ObjIsPi(_cir, pObj)){
      set<int>* newList = new set<int>;
      newList->insert(-1); // -1, pi
      gate2Supps[gateID] = newList;
      continue;
    }
 
    // AND gate outside of transparent blocks
    int faninID0 = Gia_ObjFaninId0(pObj, gateID);
    int faninID1 = Gia_ObjFaninId1(pObj, gateID);
    set<int>* newList = new set<int>;
    if(gate2Supps.find(faninID0) != gate2Supps.end()){
      newList->insert(gate2Supps[faninID0]->begin(),
                      gate2Supps[faninID0]->end());
    }
    else{
      if(_gate2Node.find(faninID0)!= _gate2Node.end())
        newList->insert(_gate2Node[faninID0]->getWordID());
      else
        newList->insert(-2);
    } 
    if(gate2Supps.find(faninID1) != gate2Supps.end()){
      newList->insert(gate2Supps[faninID1]->begin(),
                      gate2Supps[faninID1]->end());
    }
    else{
      if(_gate2Node.find(faninID1)!= _gate2Node.end())
        newList->insert(_gate2Node[faninID1]->getWordID());
      else
        newList->insert(-2);
    } 
    gate2Supps[gateID] = newList;
  }
  map<string, vector<int>* > key2Groups;

  map<int,set<int>* >::iterator mite = gate2Supps.begin();
  for(; mite!= gate2Supps.end(); ++mite){
    // skip pi
    Gia_Obj_t* current = Gia_ManObj(_cir, mite->first);
    if(Gia_ObjIsPi(_cir, current))
      continue; 
    ostringstream convert;
    set<int>::iterator site = (mite->second)->begin();
    for(; site!= (mite->second)->end(); ++site)
      convert<<(*site)<<"&";
    
    string key = convert.str();
   // cerr<<"key: "<<key<<endl;
    if(key2Groups.find(key)!= key2Groups.end())
      key2Groups[key]->push_back(mite->first);
    else{
      vector<int>* newGroup = new vector<int>;
      newGroup->push_back(mite->first);
      key2Groups[key] = newGroup;
      groups.push_back(newGroup);
    }
  }
  mite = gate2Supps.begin();
  for(; mite!= gate2Supps.end(); ++mite)
    delete mite->second;
}
void meowBound2::createSubCircuits(vector<Gia_Man_t*>& circuits, vector<vector<int>* >& cirFanins, vector<vector<int>* >& cirFanouts,
 set<int>& needIDs){
  // step one, finalize wordList
  set<int> transBits;
  set<meowNode*>::iterator site = _goodNodes.begin();
  //cerr<<"final Words"<<endl;
  for(; site != _goodNodes.end(); ++site){
    (*site)->addMiddleBits(transBits);
  }
 
  vector<vector<int>* > groups;
  vector<set<int>* > gfanouts;
  vector<set<int>* > gfanins;
//  bool type = false;
//  if(type)
//    groupSubCircuits(transBits, groups);
//  else
  groupSubCircuits2(transBits, groups, needIDs, gfanouts, gfanins);

  // groups: a group of signals contained in this subcircuit

  for(int i = 0; i < groups.size(); ++i){ 
    // take po and create Circuit 
    set<int>* fanins = gfanins[i];
    set<int>* fanouts = gfanouts[i];
    needIDs.insert(fanins->begin(), fanins->end());
    if(fanins->size() ==0 || fanouts->size() == 0){
      continue;
    }
    Gia_Man_t* pNew;
    Gia_Obj_t* pObj;
    pNew = Gia_ManStart(fanins->size()+groups[i]->size()+fanouts->size());
    Gia_ManHashAlloc(pNew);
    Gia_ManFillValue(_cir);
    Gia_ManConst0(_cir)->Value = 0;
    vector<int>* faninVec = new vector<int>;
    vector<int>* fanoutVec = new vector<int>;
    set<int>::iterator site2 = fanins->begin();
    for(; site2 != fanins->end(); ++site2){
      faninVec->push_back((*site2));
      pObj = Gia_ManObj(_cir, (*site2));
      pObj->Value = Gia_ManAppendCi(pNew);
    } // create Ci
    // create AND
    for(int j = 0; j < groups[i]->size(); ++j){
      int currentID = (*groups[i])[j];
      Gia_Obj_t* currentNode = Gia_ManObj(_cir, currentID);
      if(~(currentNode->Value)){// ?Error
        //  cerr<<"Error: why?!\n";
        continue;
      }
      // ideally, Copy should be ready
      currentNode->Value = Gia_ManHashAnd(pNew,
                             Gia_ObjFanin0Copy(currentNode),
                             Gia_ObjFanin1Copy(currentNode));
      if((currentNode->Value) == ~0)
        cerr<<"Error: fanin missing! \n";
    }
    site2 = fanouts->begin();
    for(; site2 != fanouts->end(); ++site2){
      //if((*site2) == 2584)
      //  cerr<<"Hello?2"<<endl;
      Gia_Obj_t* fanoutNode = Gia_ManObj(_cir, (*site2));
      fanoutVec->push_back(*site2);
      Gia_ManAppendCo(pNew, fanoutNode->Value);
    }
    circuits.push_back(pNew);
    cirFanins.push_back(faninVec);
    cirFanouts.push_back(fanoutVec);
    // ready to get a new Circuit!

    // send out Fanins and Fanouts
  }
  // TODO we need to revise po if needed for other module 
//  set<int> non_transBits;
  // support ID 
  // create all => group signals with shared supports
}
void meowBound2::writeSubModule(Gia_Man_t* circuit, ofstream& output, int index){
  map<int, string> id2Name;
  output<<"module sub"<<index<<"(";
  Gia_Obj_t * pObj;
  int i;
  Gia_ManForEachPi(circuit, pObj, i){
    int gateID = Gia_ObjId(circuit, pObj);
    if(i!=0)
      output<<", ";
    ostringstream Convert;
    Convert<<"in"<<i;

    id2Name[gateID] = Convert.str();
    output<<Convert.str();
  }
  Gia_ManForEachPo(circuit, pObj, i){
    int gateID = Gia_ObjId(circuit, pObj);
    output<<", ";
    ostringstream Convert;
    Convert<<"out"<<i;
    id2Name[gateID] = Convert.str();
    output<<Convert.str();
  }
  // pi, po,  
  output<<");"<<endl;
  output<<"input ";
  Gia_ManForEachPi(circuit, pObj, i){
    if(i!= 0)
      output<<", ";
    output<<"in"<<i; 
  }
  output<<";"<<endl;
  output<<"output ";
  Gia_ManForEachPo(circuit, pObj, i){
    if( i!= 0)
      output<<", ";
    output<<"out"<<i; 
  }
  output<<";"<<endl;
  Gia_ManForEachObj1(circuit, pObj, i){
    if(Gia_ObjIsPi(circuit, pObj))
      continue;

    if(Gia_ObjIsPo(circuit, pObj)){
      int gateID = Gia_ObjId(circuit, pObj);
      int faninID0 = Gia_ObjFaninId0(pObj, gateID);
      int bubble0 = Gia_ObjFaninC0(pObj); 
      output<<"assign "<<id2Name[gateID]<<" = ";
      if(bubble0)
        output<<"~";
      output<<id2Name[faninID0]<<";"<<endl;
      continue; 
    }
    ostringstream Convert;

    int gateID = Gia_ObjId(circuit, pObj);
    Convert<<"w"<<gateID;
    id2Name[gateID] = Convert.str();
    int faninID0 = Gia_ObjFaninId0(pObj, gateID);
    int faninID1 = Gia_ObjFaninId1(pObj, gateID); 
    int bubble0 = Gia_ObjFaninC0(pObj); 
    int bubble1 = Gia_ObjFaninC1(pObj); 
    output<<"wire "<<Convert.str()<<" = "; 
    if(bubble0)
      output<<"~";
    output<<id2Name[faninID0]<<"&";
    if(bubble1)
      output<<"~";
    output<<id2Name[faninID1]<<";"<<endl;

  }
  output<<"endmodule"<<endl;
}
void meowBound2::checkNeedIDs(set<int>& needIDs, meowNode* node, set<int>& extraPOs){
  set<int> internal;
  node->addInternal(internal);
  set<int>::iterator site = internal.begin();
  for(; site!= internal.end(); ++site){
    if(needIDs.find(*site)!= needIDs.end())
      extraPOs.insert((*site));
  }
 /* if(internal.find(1387) != internal.end())
    cerr<<"found 1387"<<endl;
  if(internal.find(1439) != internal.end())
    cerr<<"found 1439"<<endl;

  if(internal.find(1413) != internal.end())
    cerr<<"found 1413"<<endl;*/
}
void meowBound2::writeOutVerilog(char* pFileSpec){
 // same Pi and Pos
  ofstream output(pFileSpec);
  set<int> needIDs;
//  set<meowNode*> finalWords;
//  map<int, meowNode*>::iterator mite = _gate2Node.begin();
  set<meowNode*>::iterator site = _goodNodes.begin();
  for(; site!= _goodNodes.end(); ++site){
  //  finalWords.insert(mite->second); 
    vector<int>& controls = (*site)->getControlIDs();
    needIDs.insert(controls.begin(), controls.end());
    (*site)->getInputs(needIDs);
  }
  Gia_Obj_t * pObj;
  map<int, string> id2Name;
  int idx;

  Gia_ManForEachPo(_cir, pObj, idx){
    int gateID = Gia_ObjId(_cir, pObj);
    int faninID0 = Gia_ObjFaninId0(pObj, gateID);
    needIDs.insert(faninID0);
  } 
  // collect controls

  vector<Gia_Man_t*> circuits;
  vector<vector<int>* > cirFanins;
  vector<vector<int>* > cirFanouts;
  createSubCircuits(circuits, cirFanins, cirFanouts, needIDs);
  // get circuits
    // create subModule
  map<meowNode*, set<int> > node2Extra;
  site = _goodNodes.begin();
  for(; site != _goodNodes.end(); ++site){
    set<int> extraPOs;
    checkNeedIDs(needIDs, (*site), extraPOs);
    if(extraPOs.size() != 0)
      node2Extra[(*site)] = extraPOs;
    if((*site)->isMux() && extraPOs.size() == 0) 
      (*site)->writeVerilog(output);
    else{ // copy the old one
      writeTransModule(output, *site, extraPOs);
    }
  }

  for(int i = 0; i < circuits.size(); ++i)
    writeSubModule(circuits[i], output, i);


  output<<"module top(";
  //output<<"module sub"<<index<<"(";
  Gia_ManForEachPi(_cir, pObj, idx){
    int gateID = Gia_ObjId(_cir, pObj);
    if(idx!=0)
      output<<", ";
    ostringstream Convert;
    Convert<<"in"<<idx;

    id2Name[gateID] = Convert.str();
    output<<Convert.str();
  }
  Gia_ManForEachPo(_cir, pObj, idx){
    int gateID = Gia_ObjId(_cir, pObj);
    output<<", ";
    ostringstream Convert;
    Convert<<"out"<<idx;
    id2Name[gateID] = Convert.str();
    output<<Convert.str();
  }
  // pi, po,  
  output<<");"<<endl;
  output<<"input ";
  Gia_ManForEachPi(_cir, pObj, idx){
    if(idx != 0)
      output<<", ";
    output<<"in"<<idx; 
  }
  output<<";"<<endl;
  output<<"output ";
  Gia_ManForEachPo(_cir, pObj, idx){
    if(idx != 0)
      output<<", ";
    output<<"out"<<idx; 
  }
  output<<";"<<endl;
  output<<"wire const0 = 1'b0;"<<endl;
  id2Name[0] = "const0";
  // name all wires
  site = _goodNodes.begin();
  for(; site!= _goodNodes.end(); ++site){
    //set<int> inputs;
    int wordID  = (*site)->getWordID();
    //(*site)->getInputs(inputs);
    vector<vector<int> >& inputs = (*site)->getInIDs();
    vector<int>& outputs = (*site)->getOutIDs();
    vector<int>& controls = (*site)->getControlIDs();
    for(int i = 0; i < controls.size(); ++i){
      if(id2Name.find(controls[i])== id2Name.end()){
        ostringstream Convert;
        Convert<<"w"<<controls[i];
        output<<"wire "<<Convert.str()<<";"<<endl;
        id2Name[controls[i]] = Convert.str();
      }
    }
    if(controls.size() > 1)
      output<<"wire ["<<controls.size()-1<<":0]";
    else 
      output<<"wire ";
    output<<" c"<<wordID<<" = {";
    for(int i = controls.size()-1; i >=0; --i){
      if(i != controls.size()-1)
        output<<", ";
      output<<id2Name[controls[i]];
    }
    output<<"};"<<endl;
    for(int i = 0; i < inputs.size(); ++i){
      for(int j = 0; j < inputs[i].size(); ++j){
        if( (outputs[j]!= 0)
        && id2Name.find(abs(inputs[i][j])) == id2Name.end() ){
          ostringstream Convert;
          Convert<<"w"<<abs(inputs[i][j]);
        output<<"wire "<<Convert.str()<<";"<<endl;
        id2Name[abs(inputs[i][j])] = Convert.str();

        }
      }
      output<<"wire ["<<(*site)->getWidth()-1<<":0] word";
      output<<wordID<<"_"<<i<<" = {";
      bool first = true;
      for(int j = inputs[i].size() -1; j >= 0; --j){
        if(outputs[j] == 0)
          continue;
        if(!first)
          output<<", ";
        first = false;
        if(inputs[i][j] < 0 && (*site)->isMux() 
        && node2Extra.find(*site) == node2Extra.end() ){
          output<<"~";
        }
        output<<id2Name[abs(inputs[i][j])];
      }
      output<<"};"<<endl;
    }
    output<<"wire ["<<(*site)->getWidth()-1<<":0] word";
    output<<wordID<<"_out;"<<endl;
    if(node2Extra.find(*site)!= node2Extra.end()){
      set<int> extraPOs = node2Extra[(*site)];
      set<int>::iterator siteP = extraPOs.begin();
      for(; siteP != extraPOs.end(); ++siteP){
        if(id2Name.find(*siteP) == id2Name.end()){
          ostringstream Convert;
          Convert<<"w"<<(*siteP);
          output<<"wire "<<Convert.str()<<";"<<endl;
          id2Name[*siteP] = Convert.str();
        }
      }
    }
    output<<"trans"<<wordID<<" t"<<wordID;
    output<<"( c"<<wordID<<", ";
    for(int i = 0; i < inputs.size(); ++i)
      output<<"word"<<wordID<<"_"<<i<<", ";
 
    if(node2Extra.find(*site)!= node2Extra.end()){
      set<int> extraPOs = node2Extra[(*site)];
      set<int>::iterator siteP = extraPOs.begin();
      for(; siteP != extraPOs.end(); ++siteP){
        output<<id2Name[*siteP]<<", ";            
      }
    }
    output<<"word"<<wordID<<"_out);"<<endl;
    int idx = 0;
    for(int i = 0; i < outputs.size(); ++i){
      if(outputs[i]!= 0 ){
        if(id2Name.find(outputs[i]) == id2Name.end()){
          ostringstream Convert;
          Convert<<"w"<<outputs[i];
          id2Name[outputs[i]] = Convert.str();
          output<<"wire "<<id2Name[outputs[i]]<<";"<<endl;
        }
        output<<"assign "<<id2Name[outputs[i]];
        output<<" = word"<<wordID<<"_out["<<idx<<"];"<<endl;
        idx++;
      }
    }
    // assign transName 
  }
  // we need internal words
  // connect!i
  for(int i = 0; i < circuits.size(); ++i){
    // find fanins
    for(int j = 0; j < cirFanins[i]->size(); ++j){
      if(id2Name.find((*cirFanins[i])[j])== id2Name.end()){
        ostringstream Convert;
        Convert<<"w"<<(*cirFanins[i])[j];
        output<<"wire "<<Convert.str()<<";"<<endl;
        id2Name[(*cirFanins[i])[j]] = Convert.str();
      }
    }
    for(int j = 0; j < cirFanouts[i]->size(); ++j){
      if(id2Name.find((*cirFanouts[i])[j])== id2Name.end()){
        ostringstream Convert;
        Convert<<"w"<<(*cirFanouts[i])[j];
        output<<"wire "<<Convert.str()<<";"<<endl;
        id2Name[(*cirFanouts[i])[j]] = Convert.str();
      }
    }
    output<<"sub"<<i<<" m"<<i<<"(";
    for(int j = 0; j < cirFanins[i]->size(); ++j)
      output<<id2Name[(*cirFanins[i])[j]]<<", ";
    
    for(int j = 0; j < cirFanouts[i]->size(); ++j){
      output<< id2Name[(*cirFanouts[i])[j]];
      if(j != cirFanouts[i]->size()-1)
        output<<", ";
    }
    output<<");"<<endl;

    // connect to the module!
  }
  // finally assign POs
  Gia_ManForEachPo(_cir, pObj, idx){
    int gateID = Gia_ObjId(_cir, pObj);
    int faninID0 = Gia_ObjFaninId0(pObj, gateID);
    int bubble0 = Gia_ObjFaninC0(pObj); 
    output<<"assign "<<id2Name[gateID]<<" = ";
    if(bubble0)
      output<<"~";
    if(id2Name.find(faninID0) == id2Name.end())
      cerr<<"missing ports!"<<id2Name[gateID]<<": "<<faninID0<<endl;
    output<<id2Name[faninID0]<<";"<<endl;
  }
  output<<"endmodule"<<endl;
  // 

  // write top module
  for(int i = 0; i < cirFanins.size(); ++i){
    delete cirFanins[i];
    delete cirFanouts[i];
    Gia_ManStop(circuits[i]);
  }

}
void meowBound2::writeTransModule(ofstream& output, meowNode* node, set<int>& extraPOs){
  int wordID = node->getWordID();
  output<<"module trans"<<wordID<<"(";
  output<<"c"<<wordID<<", ";
  map<int, string> id2Name;
  for(int i = 0; i < node->getInputNum(); ++i )
    output<<"word"<<wordID<<"_"<<i<<", ";

  set<int>::iterator site = extraPOs.begin();
  for(; site!= extraPOs.end(); ++site)
    output<<"extra"<<wordID<<"_"<<(*site)<<", ";
  output<<"word"<<wordID<<"_out);"<<endl;
 
  vector<vector<int> >& inIDs = node->getInIDs();
  vector<int>& outIDs = node->getOutIDs(); 
  vector<int>& controls = node->getControlIDs();
 // if(controls.size() > 1) 
  output<<"input ["<<controls.size()-1<<":0]";
//  else
  //  output<<"input ";
  output<<" c"<<wordID<<";"<<endl;
  for(int i = 0; i < controls.size(); ++i){
    ostringstream Convert;
    Convert<<"c"<<wordID<<"["<<i<<"]";
    id2Name[controls[i]] = Convert.str();
  }
  for(int i = 0; i < inIDs.size(); ++i){ 
    output<<"input ["<<node->getWidth()-1<<":0] word"<<wordID<<"_"<<i<<";"<<endl;
    int idx = 0;
    for(int j = 0; j < inIDs[i].size(); ++j){
      if( (outIDs[j]!= 0) ){
        if (id2Name.find(abs(inIDs[i][j])) == id2Name.end()){
          ostringstream Convert;
          Convert<<"word"<<wordID<<"_"<<i<<"["<<idx<<"]";
          //idx++;
          //if(abs(inIDs[i][j]) == 1139)
          //  cerr<<"got 1139!"<<endl;
          id2Name[abs(inIDs[i][j])] = Convert.str();
        }
        idx++;
      }
    }
  }
  output<<" output ["<<node->getWidth()-1<<":0]";
  output<<" word"<<wordID<<"_out;"<<endl;
  site = extraPOs.begin();
  for(; site!= extraPOs.end(); ++site)
    output<<"output extra"<<wordID<<"_"<<(*site)<<";"<<endl;


  int idx = 0;
  for(int i = 0; i < outIDs.size(); ++i){
    if(outIDs[i]!= 0){
      writeTransBitRecur(output, outIDs[i], id2Name);
      output<<"assign word"<<wordID<<"_out["<<idx<<"] = ";
      output<<id2Name[outIDs[i]]<<";"<<endl;
      idx++;
    }
  }
  site = extraPOs.begin();
  for(; site!= extraPOs.end(); ++site){
    output<<"assign extra"<<wordID<<"_"<<(*site)<<" = ";
    output<<id2Name[*site]<<";"<<endl;
  }
  output<<"endmodule"<<endl; 
}
void meowBound2::writeTransBitRecur(ofstream& output, int gateID, 
                                  map<int, string>& id2Name){
  if(id2Name.find(gateID)!= id2Name.end())
    return;
  if(gateID == 0){
    id2Name[0] = "(1'b0)";
    return;
  }

  Gia_Obj_t* pObj = Gia_ManObj(_cir, gateID);
  if(Gia_ObjIsPi(_cir, pObj)){
    //cerr<<"Warning: PI here"<<endl;
    return;
  }
  int faninID0 = Gia_ObjFaninId0(pObj, gateID);
  int faninID1 = Gia_ObjFaninId1(pObj, gateID); 
  int bubble0 = Gia_ObjFaninC0(pObj); 
  int bubble1 = Gia_ObjFaninC1(pObj); 
  writeTransBitRecur(output, faninID0, id2Name);
  writeTransBitRecur(output, faninID1, id2Name);

  ostringstream Convert;
  Convert<<"w"<<gateID;
  id2Name[gateID] = Convert.str();
  output<<"wire "<<Convert.str()<<" = ";
  if(bubble0)
    output<<"~";
  output<<id2Name[faninID0]<<"&";
  if(bubble1)
    output<<"~";
  output<<id2Name[faninID1]<<";"<<endl;


}
void meowBound2::writeSubCircuits(char* fileHead){
  vector<Gia_Man_t*> circuits;
  vector<vector<int>* > cirFanins;
  vector<vector<int>* > cirFanouts;
  set<int> controls; // here we don't need "controls" to be out!
  createSubCircuits(circuits, cirFanins, cirFanouts, controls);
  for(int i = 0; i < circuits.size(); ++i){
    //cerr<<"Hello? we have circuits "<<i;
    ostringstream fileName;
    fileName<<string(fileHead)<<"_"<<i<<".aig";    
    string nameStr = fileName.str();
    cerr<<"circuit File:"<<nameStr<<endl; 
    Gia_AigerWrite(circuits[i], const_cast<char*>(nameStr.c_str()),
                   0, 0);
    
  }
  // write out
  for(int i = 0; i < cirFanins.size(); ++i){
    delete cirFanins[i];
    delete cirFanouts[i];
    Gia_ManStop(circuits[i]);
  }
  
}
void meowBound2::createCG(){


}
ABC_NAMESPACE_IMPL_END
