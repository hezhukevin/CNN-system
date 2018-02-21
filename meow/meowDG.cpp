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
#include "ext/meow/meowDG.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START
meowDG::meowDG(){


}
meowDG::~meowDG(){
  for(unsigned i = 0; i < _nodeList.size(); ++i)
    delete _nodeList[i];
}
meowDGNode* meowDG::addNode(NODE_TYPE type, vector<int>& gateList){
  // false: error!
   
  meowDGNode* newNode = NULL;
  switch(type){
    case NODE_PI:
      newNode = new meowDGPI(_nodeList.size(), gateList);
      break;
    case NODE_CONST:
      newNode = new meowDGConst(_nodeList.size(), gateList);
      break;
    case NODE_PO:
      newNode = new meowDGPO(_nodeList.size(), gateList);
      break;
    case NODE_FF:
      newNode = new meowDGFF(_nodeList.size(), gateList);
      break;
    case NODE_TRANS:
      newNode = new meowDGTransBlock(_nodeList.size(), gateList);
      break; 
    case NODE_GATED:
      newNode = new meowDGGatedFF(_nodeList.size(), gateList);
      break;
    case NODE_INTERNAL:
      newNode = new meowDGInternal(_nodeList.size(), gateList);
      break;
    default:
      break;
  }
  if(newNode){
    _nodeList.push_back(newNode);
    if(!addGate2Node(newNode, gateList))
      cerr<<"ERROR! something repeated! type = "<<newNode->getType()<<endl; 
  }
  return newNode;
}
bool meowDG::addGate2Node(meowDGNode* newNode, vector<int>& gateList){
 
  bool returnValue = true; 
  meowDGNode* visitedOld = NULL;
  for(int i = 0; i < gateList.size(); ++i){
    if(_gate2Node.find(abs(gateList[i]))!= _gate2Node.end()){
    //  we need to update connection here!
      meowDGNode* oldNode = _gate2Node[abs(gateList[i])];
      if( visitedOld!= NULL && oldNode != visitedOld ){
        cerr<<"ERROR: split wrong?! "<<gateList[i]<<endl;
        returnValue = false;
      }
      if(visitedOld)
        continue;
      visitedOld = oldNode;
      // this old Node is some internal to Gated or Trans
      set<meowDGNode*>& outputNodes = oldNode->getOutput();
      set<meowDGNode*>::iterator site = outputNodes.begin();
      for(; site!= outputNodes.end(); ++site){
        newNode->addOutput(*site);
        (*site)->removeInput(oldNode);
        (*site)->addInput(newNode); 
        if((*site)->getType() == NODE_TRANS){
          dynamic_cast<meowDGTransBlock*>(*site)->replaceInput(oldNode, newNode);
        }
      }    
    }
  }
  if(visitedOld){
    _replaced.insert(visitedOld);
   
  //  cerr<<"replace "<<visitedOld->getID()<<" by "<<newNode->getID()<<endl;
   // visitedOld->printDGNode();
   // newNode->printDGNode();
  }
// add Mux as input nodes first ==> replace directly
  for(int i = 0; i < gateList.size(); ++i)
    _gate2Node[abs(gateList[i])] = newNode; // we have replaced

  return returnValue;
}
bool meowDG::createdBefore(vector<int>& gateList){
  meowDGNode* used = NULL;
  for(int i = 0; i < gateList.size(); ++i){
    if(_gate2Node.find(abs(gateList[i]))!= _gate2Node.end()){
      if(used == NULL)
        used = _gate2Node[abs(gateList[i])];
      else if(used != _gate2Node[abs(gateList[i])])
        cerr<<"Error: issue with split"<<endl;
       
      //return true;

    }
  }
  if(used)
    return true;
  return false;
}
meowDGNode* meowDG::getNode(int gateID){
  if(_gate2Node.find(gateID) == _gate2Node.end())
    return NULL;
  return _gate2Node[gateID];
}
void meowDG::getUpdatingOrder(vector<meowDGNode*>& candidates){
 // set<meowDGNode*> visited;
  // collect and sort by IDs...
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_replaced.find(_nodeList[i])!= _replaced.end())
      continue;
    NODE_TYPE type = _nodeList[i]->getType();
    if(type == NODE_FF || type == NODE_GATED)
      candidates.push_back(_nodeList[i]);
  }
  // topological order from PI to PO
  //updatingOrderRecur(candidates, visited, _nodeList[0]);
}
void meowDG::updatingOrderRecur(vector<meowDGNode*>& candidates,
                                set<meowDGNode*>& visited,
                                meowDGNode* current){
  if(visited.find(current)!=visited.end())
    return;
 /* set<meowDGNode*> inputs = current->getInput();
  set<meowDGNode*>::iterator site = inputs.begin();
  for(; site!= inputs.end(); ++site){
    if(visited.find(*site) == visited.end())
      return; // not finished!
  }*/

  visited.insert(current);
  NODE_TYPE type = current->getType();
  if(type == NODE_FF || type == NODE_GATED)
    candidates.push_back(current);

  set<meowDGNode*>& outputs = current->getOutput();
  set<meowDGNode*>::iterator site = outputs.begin();
  for(; site!= outputs.end(); ++site)
    updatingOrderRecur(candidates, visited, *site ); 

}
void meowDG::getObserveOrder(vector<meowDGNode*>& candidates){
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_replaced.find(_nodeList[i])!= _replaced.end())
      continue;
    NODE_TYPE type = _nodeList[i]->getType();
    if(type == NODE_FF || type == NODE_GATED){ // we accept gated
      if(_nodeList[i]->isGatedU())
        continue;
      candidates.push_back(_nodeList[i]);

    }
  }

 // set<meowDGNode*> visited;
 // observeOrderRecur(candidates, visited, _nodeList[1]);
  // reverse topological order from PO to PI
}
void meowDG::observeOrderRecur(vector<meowDGNode*>& candidates,
                               set<meowDGNode*>& visited,
                               meowDGNode* current){
  if(visited.find(current)!=visited.end())
    return;

  /*set<meowDGNode*>& outputs = current->getOutput();
  set<meowDGNode*>::iterator site = outputs.begin();
  for(; site!= outputs.end(); ++site){
    if(visited.find(*site) == visited.end())
      return; // output not ready
  }*/
  visited.insert(current);
  NODE_TYPE type = current->getType();
  if(type == NODE_FF)
    candidates.push_back(current);

  set<meowDGNode*>& inputs = current->getInput();
  set<meowDGNode*>::iterator site = inputs.begin();
  for(; site!= inputs.end(); ++site)
    observeOrderRecur(candidates, visited, *site ); 
}
void meowDG::reviseNodeReduce(meowDGNode* target, int newControl){
  // use for verification
  if(newControl == 0){
    vector<int>& gateIDs = target->getGates();
    meowDGNode* newNode = new meowDGFF(target->getID(), gateIDs);
    replaceNode(target, newNode);
  } // make it to NODE_FF!
  else{
    dynamic_cast<meowDGGatedFF*>(target)->reduceControlID(newControl);
  }
}
void meowDG::replaceNode(meowDGNode* target, meowDGNode* newNode){
  vector<int>& gateIDs = target->getGates();
    
  for(int i = 0; i < gateIDs.size(); ++i)
    _gate2Node[gateIDs[i]]  = newNode;
    
  set<meowDGNode*>& inputNodes = target->getInput(); 
  set<meowDGNode*>::iterator site = inputNodes.begin();
  for(; site!= inputNodes.end(); ++site){
    newNode->addInput(*site);
    (*site)->removeOutput(target);
    (*site)->addOutput(newNode); 
  }
  set<meowDGNode*>& outputNodes = target->getOutput();
  site = outputNodes.begin();
  for(; site!= outputNodes.end(); ++site){
    newNode->addOutput(*site);
    (*site)->removeInput(target);
    (*site)->addInput(newNode);
    }
  _nodeList[target->getID()] = newNode; 
  delete target;

}
void meowDG::reviseNode(meowDGNode* target, int newControl){ 
 // use for synthesis
  if(target->getType() == NODE_FF){
    vector<int>& gateIDs = target->getGates();
    
    meowDGNode* newNode = new meowDGGatedFF(target->getID(),
                                            gateIDs);
    dynamic_cast<meowDGGatedFF*>(newNode)->addControlID(newControl);
    replaceNode(target, newNode);
    newNode->setGatedU(); 
  } 
  else if(target->getType() == NODE_GATED){
    dynamic_cast<meowDGGatedFF*>(target)->addControlID(newControl);
    target->setGatedU();
  }
  else
    cerr<<"ERROR! no syntheis on this NODE!"<<endl;
}
void meowDG::updateDGIDs(map<int, int>& old2newID){
  _gate2Node.clear();
  for(int i = 0; i < _nodeList.size(); ++i){
    _nodeList[i]->updateID(old2newID);
    vector<int>& gateIDs = _nodeList[i]->getGates();
    for(int j = 0; j < gateIDs.size(); ++j)
      _gate2Node[gateIDs[j]] = _nodeList[i];
  }
}
void meowDG::drawGraph(char* fileName, bool print){
  ofstream output(fileName);
  output<<"digraph graphname{"<<endl; 
  // create Node first;
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_replaced.find(_nodeList[i])!= _replaced.end())
      continue;
    if(print)
      _nodeList[i]->printDGNode();


    int nodeID = _nodeList[i]->getID();
    output<<"n"<<nodeID<<" [";
    NODE_TYPE type = _nodeList[i]->getType();
    switch(type){
      case NODE_PI:
      case NODE_PO:
        output<<" shape=ellipse";
        break;
      case NODE_FF:
        output<<" shape=box";
        break;
      case NODE_GATED:
        output<<" color=red";
        break;
      case NODE_TRANS:
        output<<" shape=trapezium";
        break;
      case NODE_INTERNAL:
        output<<" shape=doublecircle";
        break;
      default:
        break;
    }
    output<<" ];"<<endl;
  } 
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_replaced.find(_nodeList[i])!= _replaced.end())
      continue;

    set<meowDGNode*>& inputNodes = _nodeList[i]->getInput();
    set<meowDGNode*>::iterator site = inputNodes.begin();
    for(; site!= inputNodes.end(); ++ site) {
      output<<"n"<<(*site)->getID()<<" -> n"<<_nodeList[i]->getID();
      output<<";"<<endl;
    }
  }
  output<<"}"<<endl;
  output.close();

} 
ABC_NAMESPACE_IMPL_END
