#include"ext/meow/charGraph.h"
#include<iostream>
#include<set>
#include<vector>
#include<map>
using namespace std;
 

charGraph::charGraph( int num){
 // cout<<"charGraph :)"<<endl;
  _id2CharNode = new vector<charNode*>(num, NULL); 
}
charGraph::~charGraph(){
  delete _id2CharNode;
  for(int i = 0; i < _allNodes.size(); ++i)
    delete _allNodes[i];
}
charNode* charGraph::addNewNode(int selectID){
  charNode* newNode = new charNode(selectID);
  _allNodes.push_back(newNode);
  if(selectID > 0)
    _select2CharNode[selectID] = newNode;
  return newNode;
}
charNode* charGraph::getNodeBySelect(int selectID){
  if(_select2CharNode.find(selectID) != _select2CharNode.end())
    return _select2CharNode[selectID];
  else
    return NULL;
}
void charGraph::addContainForNode(charNode* node, int newID){
  node->addContain(newID);
  (*_id2CharNode)[newID] = node;
}
charNode* charGraph::id2Node(int gateID){
  return (*_id2CharNode)[gateID];
}
void charGraph::getContainID(vector<int>& idList, int nodeIndex){
  //assert(nodeIndex < allNodes.size());
  _allNodes[nodeIndex]->getContain(idList); 
}
void charGraph::setDepend(set<int>& inList, int nodeIndex, int type){
  charNode* current = _allNodes[nodeIndex];
  set<int>::iterator ite = inList.begin();
  for(; ite != inList.end(); ++ite){
    if(type){
      current->addOnInput((*_id2CharNode)[(*ite)]);
      (*_id2CharNode)[(*ite)]->addOnOutput(current);
    }
    else{
      current->addOffInput((*_id2CharNode)[(*ite)]);
      (*_id2CharNode)[(*ite)]->addOffOutput(current);
    }
  } 
}
void charGraph::addBadNode(int realId){
  charNode* badNode= (*_id2CharNode)[realId];
  if(badNode == NULL)
    cerr<<"Bad Wrong!\n";
  _badNode.insert(badNode);
//  cerr<<"Bad "<<badNode<<endl;
}
int charGraph::getTargetByIndex(int index, vector<int> & CoList){
  int select = _propertyOrder[index];
  select = (select > 0)? select : select*(-1);
  charNode* node = _select2CharNode[select];
  node->getContain(CoList); 
  return select;
}
void charGraph::collectSignalID(vector<int>& idForSignal){
  // for each node in bad, collect
  set<charNode*>::iterator ite = _badNode.begin(); 
  vector<int> otherList;
  for(; ite != _badNode.end(); ++ite){ 
  //TODO here we only consider 1-timeframe 
    if(((*ite)->getSelectID()) == 0 )
      continue;
    int currentID = ((*ite)->getSelectID());
    //cerr<<"get badNode select"<<currentID<<endl;
    otherList.clear();
    set<charNode*>* onInput = (*ite)->getOnInput();
    set<charNode*>::iterator ite2 = onInput->begin();
    for(;  ite2 != onInput->end(); ++ite2){
      if((*ite2)->getSelectID() == 0){
        otherList.clear();
        break;
      }
      else
        otherList.push_back((*ite2)->getSelectID());
    }
    if(otherList.size() != 0){ // have good property for forward case
      _propertyMap[currentID] = otherList;
      _propertyOrder.push_back(currentID);
      idForSignal.push_back(currentID);
      for(int k = 0; k < otherList.size(); ++k)
        idForSignal.push_back(otherList[k]);
    }

    otherList.clear();
    set<charNode*>* onOutput = (*ite)->getOnOutput();
    ite2 = onOutput->begin();
    for(; ite2 != onOutput->end(); ++ite2){
      if((*ite2)->getSelectID() == 0){
        otherList.clear();
        break;
      }
      else
        otherList.push_back((*ite2)->getSelectID());

    }
    if(otherList.size() != 0){ // have good property for backward

      _propertyMap[currentID*(-1)] = otherList;
      _propertyOrder.push_back(currentID*(-1));
      idForSignal.push_back(currentID);
      for(int k = 0; k < otherList.size(); ++k)
        idForSignal.push_back(otherList[k]);

    }
    //get on output selection! 
  }
}
void charGraph::printGraph(){
    for(int i = 0; i < _allNodes.size(); ++i){
    if(_allNodes[i]->hasPI())
      cout<<"PI: ";
    if(_allNodes[i]->hasPO())
      cout<<"PO: "; 
    cout<<_allNodes[i]<<" ";
    cout<<"Containing:"<<endl;
    _allNodes[i]->printContain();
    
     //    else{
      cout<<endl;
      cout<<"Node: "<<_allNodes[i]<<" Select:"<<_allNodes[i]->getSelectID()<<endl;
      cout<<"On: "<<endl;
      _allNodes[i]->printOn();
      cout<<endl;
      cout<<"Off: "<<endl;
      _allNodes[i]->printOff();
      cout<<endl;
    //}
  }
}
void charGraph::printProperty(){
  map<int, vector<int> >::iterator mite = _propertyMap.begin();
  for(; mite != _propertyMap.end(); ++mite){
    cout<<"Property: "<<mite->first<<endl;
    for(int i = 0; i < (mite->second).size(); ++i)
      cout<<(mite->second)[i]<<" ";
  }
  cout<<endl;
}
