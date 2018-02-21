#include "ext/meow/meowBlock.h"
#include "ext/meow/meowBound.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START
bool meowBlock::checkFullySupport(vector<int>& inIDs){
  for(int i = 0; i < inIDs.size(); ++i){
    if(_targets.find(inIDs[i])== _targets.end())
      return false;
  }
  return true;
}
bool meowBlock::checkFullyTarget(vector<int>& outIDs){
  for(int i = 0; i < outIDs.size(); ++i){
    if(_supports.find(outIDs[i])== _supports.end())
      return false;
  }
  return true;

}
void meowBlock::addWords(meowBound* boundAPI, vector<wordNode*>& words){
  for(int w = 0; w < words.size(); ++w){ 
    _words.push_back(words[w]);
    vector<int> inIDs;
    vector<int> outIDs;
    vector<int> controls;
    words[w]->getInOutIDs(inIDs, outIDs, controls);
    _controls.insert(controls.begin(), controls.end());
    for(int i = 0; i < inIDs.size(); ++i){
      if(_targets.find(abs(inIDs[i]))!= _targets.end()){
        _targets.erase(abs(inIDs[i])); // internal
        boundAPI->updateTarget2Block(inIDs[i], NULL);
      }
      else{
        _supports.insert(abs(inIDs[i])); // boundary
        boundAPI->updateSupport2Block(inIDs[i], this);
      }
      if(_supports.find(abs(outIDs[i]))!= _supports.end()){

        _supports.erase(abs(outIDs[i]));
        boundAPI->updateSupport2Block(outIDs[i], NULL);
      }
      else{
        _targets.insert(abs(outIDs[i]));
        boundAPI->updateTarget2Block(outIDs[i], this);
      }
    }
  }
  //updateBound(boundAPI);
} 
void meowBlock::addWord(meowBound* boundAPI, vector<int>& inIDs, vector<int>& outIDs, vector<int>& controls, vector<bool>& cofactors){
     //this is fine but we would like to check boundary issue: if support is in other supports' fanin don't do it 
  wordNode* newWord = new wordNode(inIDs, outIDs, controls, cofactors);
  _words.push_back(newWord);
  _controls.insert(controls.begin(), controls.end());
  for(int i = 0; i < inIDs.size(); ++i){
    if(_targets.find(abs(inIDs[i]))!= _targets.end()){
      _targets.erase(abs(inIDs[i])); // internal
      boundAPI->updateTarget2Block(inIDs[i], NULL);
    }
    else{
      _supports.insert(abs(inIDs[i])); // boundary
      boundAPI->updateSupport2Block(inIDs[i], this);
    }
    if(_supports.find(abs(outIDs[i]))!= _supports.end()){
      _supports.erase(abs(outIDs[i]));
      boundAPI->updateSupport2Block(outIDs[i], NULL);
    }
    else{
      _targets.insert(abs(outIDs[i]));
      boundAPI->updateTarget2Block(outIDs[i], this);
    }
  }
//  updateBound(boundAPI);
      //update _target2Block, _support2Block 
}
void meowBlock::updateBound(meowBound* boundAPI){
  // update support TODO
  cerr<<"Start!!"<<endl;
  set<int> supportedList; // stored fully supported IDs;
  set<int> hiddenList;
  set<int>::iterator site = _supports.begin();
  supportedList.insert(_controls.begin(), _controls.end());
  while(site != _supports.end()){
    set<int>::iterator current = site++;
    int gateID = *current;
    if(updateSupportList(boundAPI, supportedList, hiddenList,gateID)){
      _supports.erase(gateID);
      cerr<<"Erase: "<<gateID<<endl;
    }
  }  
  //update target

}
bool meowBlock::updateSupportList(meowBound* boundAPI, set<int>& supportedList, set<int>& hiddenList, int gateID){
  cerr<<"Update?!"<<gateID<<endl;
  if(!fullySupported(boundAPI, supportedList, hiddenList ,gateID)){
    set<int>* currentList = boundAPI->getSupportSet(gateID);
    supportedList.insert(gateID); //  need to keep
    hiddenList.insert(currentList->begin(), currentList->end()); 
    return false;
  }
  else{
    supportedList.insert(gateID);
    return true;

  }
}
bool meowBlock::fullySupported(meowBound* boundAPI, set<int>& supportedList, set<int>& hiddenList, int gateID){
  if (supportedList.find(gateID)!= supportedList.end())
    return true;
  set<int>* currentList = boundAPI->getSupportSet(gateID);
  set<int> remainList;
  set<int>::iterator site = currentList->begin();
  for(; site != currentList->end(); ++site){
    if(hiddenList.find(*site) == hiddenList.end())
      remainList.insert(*site);
  }
  //remainList.insert(gateID);
  if(remainList.size() == 0) // PI?
    return false;
  site = remainList.begin();
  
  bool fullySupport = true;
  for(; site != remainList.end(); ++site){
    if(supportedList.find(*site) != supportedList.end())
      continue;
    else{
      if(fullySupported(boundAPI, supportedList, hiddenList, *site))
        supportedList.insert(*site);
      else{
        fullySupport = false;
      }
    }
  } 
  return fullySupport;
}
ABC_NAMESPACE_IMPL_END
