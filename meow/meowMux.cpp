#include "ext/meow/meowMux.h"
#include<iostream>
#include<fstream>
#include <algorithm> 
using namespace std;
ABC_NAMESPACE_IMPL_START
void meowUsageMux(){
  Abc_Print( -2, "usage: meowMux <cir> [-bdowh] \n" );
  Abc_Print( -2, "\t compute transparent logic of the current Gia by structural approach. \n");
  Abc_Print( -2, "\t -w: toggle to print Proved words and some results\n");
  Abc_Print( -2, "\t-b    : toggle to run backward transparency.\n");

  Abc_Print( -2, "\t-h    : print the command usage\n");

}

meowMux::meowMux(Gia_Man_t* cir){
  _cir = cir;
  int i;
  Gia_Obj_t* pObj; 
  Gia_ManForEachCo(_cir, pObj, i){
    _poList.insert(Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj)));
  }

}
meowMux::~meowMux(){
  for(int i = 0; i < _nodeList.size(); ++i)
    delete _nodeList[i];
}
void meowMux::runAll(bool forward){

  recognizeMux();
  //reportWords();
  collectWords(); // split by orders!
  cleanNodes();
/*  if(forward)
    forwardCheck();
  else
    backwardCheck();
*/
}
void meowMux::sortNodes(vector<int>& nodeOrder){
  vector< pair<int, int> > mux_bigOut;
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badwords.find(_nodeList[i]) == _badwords.end())
      mux_bigOut.push_back(pair<int, int>( _nodeList[i]->getMaxID(),
                                           _nodeList[i]->getNodeID()));

  }
  sort(mux_bigOut.begin(), mux_bigOut.end());
  for(int i = 0; i < mux_bigOut.size(); ++i)
    nodeOrder.push_back(mux_bigOut[i].second);
}
void meowMux::recognizeMux(){
  int i;
  Gia_Obj_t* pObj;
  Gia_Obj_t * pCtrl, * pData0, * pData1;
  int countMux = 0;
  int currentID;
  Gia_ManForEachObj1(_cir, pObj, i){
    if(Gia_ObjIsMuxType(pObj)){
      countMux++;
      currentID = Gia_ObjId(_cir, pObj);
      pCtrl = Gia_ObjRecognizeMux(pObj, &pData1, &pData0);
      int controlID = Gia_ObjId(_cir, pCtrl); // must be positive
      int dataID0 = Gia_ObjId(_cir, pData0);
      int dataID1 = Gia_ObjId(_cir, pData1);
      if(pData1 != Gia_Regular(pData1))
        dataID1 = dataID1*(-1);
      if(pData0 != Gia_Regular(pData0))
        dataID0 = dataID0*(-1);
      if(pCtrl != Gia_Regular(pCtrl)){
        int temp = dataID0;
        dataID0 = dataID1;
        dataID1 = temp; // swap
      }
      addMux(currentID, controlID, dataID0, dataID1);
    }
  }
  //cerr<<"Mux Count "<<countMux<<endl; 
  cleanNodes(); 
}
void meowMux::cleanNodes(){
  // check bitNumi
  //cerr<<"initial words: "<<_nodeList.size() - _badwords.size()<<endl;

  for(int i = 0; i < _nodeList.size(); ++i){
    muxNode* target = _nodeList[i];
    if(target->getBitNum() < 4){
      _badwords.insert(target);
      set<int> fanoutIDs;
      set<int> faninIDs;
      target->getFanoutIDs(fanoutIDs);
      target->getFaninIDs(faninIDs);
      set<int>::iterator site = fanoutIDs.begin();
      for(; site!= fanoutIDs.end(); ++site)
        _mux2Node.erase(*site); // don't count this mux anymore
 
      site = faninIDs.begin();
      for(; site!= faninIDs.end(); ++site)
        _in2Nodes[(*site)].erase(target); 
    }
  }
  //cerr<<"after clean: "<< _nodeList.size() - _badwords.size()<<endl; 

}
void meowMux::addMux(int currentID, int controlID,
                     int dataID0, int dataID1){
  if(_control2Mux.find(controlID) == _control2Mux.end()){
    muxNode* newNode = new muxNode(controlID, _nodeList.size());
    _nodeList.push_back(newNode);
    _control2Mux[controlID] = newNode;
  }
  _mux2Node[currentID] = _control2Mux[controlID];
  _mux2Node[currentID]->addOneMux(currentID, dataID0, dataID1);
  if(_in2Nodes.find(abs(dataID0)) == _in2Nodes.end()){
    set<muxNode*> newList;
    newList.insert(_mux2Node[currentID]);
    _in2Nodes[abs(dataID0)] = newList;
  }
  else
    _in2Nodes[abs(dataID0)].insert(_mux2Node[currentID]);
  if(_in2Nodes.find(abs(dataID1)) == _in2Nodes.end()){
    set<muxNode*> newList;
    newList.insert(_mux2Node[currentID]);
    _in2Nodes[abs(dataID1)] = newList;
  }
  else
    _in2Nodes[abs(dataID1)].insert(_mux2Node[currentID]);

}
void meowMux::collectWords(){
  // step 1 sort orders
  int oldSize = 0;
  while(oldSize != _nodeList.size()){
    oldSize = _nodeList.size();
    vector<int> nodeOrder;
    sortNodes(nodeOrder);// has remove bad nodes... 
    for(int i = 0; i < nodeOrder.size(); ++i){
      splitWords(_nodeList[nodeOrder[i]]);     
    } 
    
  }
  // sort by backward
 // nodeOrder.clear();  
 // sortNodes(nodeOrder);
  
}
muxNode* meowMux::getFaninNode(muxNode* target, bool isFanin0){
  int fanin1;
  int fanin0;
  target->getFaninID(0, fanin1, fanin0);
  muxNode* inputNode = NULL;
  if(!isFanin0){
    if(_mux2Node.find(fanin0)!= _mux2Node.end())
      inputNode = _mux2Node[fanin0];
  }
  else{
    if(_mux2Node.find(fanin1)!= _mux2Node.end())
      inputNode = _mux2Node[fanin1];
  }
  return inputNode;
}
void meowMux::splitForDG(){
  int oldSize = 0; 

  while(_nodeList.size()!= oldSize){
    oldSize = _nodeList.size(); 
    vector<int> nodeOrder;
    sortNodes(nodeOrder);
    for(int i = 0; i < nodeOrder.size(); ++i)
      examForDG(_nodeList[nodeOrder[i]]); // do twice
  }
  collectWords();
}
void meowMux::examForDG(muxNode* currentNode){
  // two cases repeat => split all
  bool repeat = false;
  int bitNum = currentNode->getBitNum();
  if(bitNum == 1)
    return;
  vector<int> faninID0;
  vector<int> faninID1;
  currentNode->getFaninID0(faninID0);
  currentNode->getFaninID1(faninID1);
  set<int> fanin1Set(faninID1.begin(), faninID1.end());
  // check repeat
  for(int i = 0; i < faninID0.size(); ++i){
    if(fanin1Set.find(faninID0[i])!= fanin1Set.end()){
      repeat = true;
      break;
    }
  }
  
  vector<vector<int> > groupList;
  if(!repeat){ // check if we need to decompose
    map<string, vector<int> > usedToken;
    for(int i = 0; i < bitNum; ++i){
      ostringstream Convert;
      set<muxNode*> in2NodeList = _in2Nodes[faninID0[i]];
      set<muxNode*>::iterator site = in2NodeList.begin();
      for(; site!= in2NodeList.end(); ++site)
        Convert<<"&"<<(*site)->getNodeID();
      Convert<<"|";
      
      set<muxNode*> in2NodeList1 = _in2Nodes[faninID1[i]];
      site = in2NodeList1.begin();
      for(; site!= in2NodeList1.end(); ++site)
        Convert<<"&"<<(*site)->getNodeID();
      if(_singleList.find(faninID0[i])!= _singleList.end() ||
         _singleList.find(faninID1[i])!= _singleList.end()){
        vector<int> newList;
        newList.push_back(i);
        groupList.push_back(newList);
        continue; 
      }
      string token = Convert.str();
      if(usedToken.find(token) == usedToken.end()){
        vector<int> newVec;
        usedToken[token] = newVec;
      }
      usedToken[token].push_back(i);
    }
    // 
    if(usedToken.size() >= 2){
      map<string, vector<int> >::iterator mite = usedToken.begin();
      for(; mite!= usedToken.end(); ++mite)
        groupList.push_back(mite->second);
    } // else, do nothing
  }
  else{ // one member for one group
    for(int i = 0; i < bitNum; ++i){
      vector<int> members;
      members.push_back(i);
      groupList.push_back(members);
    }
  }
  if(groupList.size() == 0)
    return;

  _badwords.insert(currentNode);
  int currentControl = currentNode->getControlID();
  for(int i = 0; i < groupList.size(); ++i){
    muxNode* newNode = new muxNode(currentControl, _nodeList.size());
    _nodeList.push_back(newNode);
    for(int j = 0; j <groupList[i].size(); ++j){
      int fanin1;
      int fanin0;
      int gateID;
      
      currentNode->getFaninPhase(groupList[i][j],
                                 fanin1, fanin0, gateID);
      if(groupList[i].size() == 1){
        _singleList.insert(abs(fanin1));
        _singleList.insert(abs(fanin0));
        _singleList.insert(abs(gateID));
      }
      newNode->addOneMux(gateID, fanin0, fanin1);
      _in2Nodes[abs(fanin1)].erase(currentNode);
      _in2Nodes[abs(fanin1)].insert(newNode);
      _in2Nodes[abs(fanin0)].erase(currentNode);
      _in2Nodes[abs(fanin0)].insert(newNode);
      _mux2Node[abs(gateID)] = newNode; // fanout splits

    }
        // currentList groupList[i]
  }

  // different token => split for token

}
void meowMux::splitWords(muxNode* currentNode){
  int bitNum = currentNode->getBitNum();
  //cerr<<"split!"<<endl;
  map<string, vector<int> > usedToken;
  for(int i = 0; i < bitNum; ++i ){
    int fanin1;
    int fanin0;
    int fanout;
    currentNode->getFanoutID(i, fanout);
    currentNode->getFaninID(i, fanin1, fanin0);
    //int token;
    ostringstream Convert;
    if(_mux2Node.find(fanin1) != _mux2Node.end()){ // has fanin
      Convert<<_mux2Node[fanin1]->getNodeID(); 
    }
    else{
      Gia_Obj_t* pInput = Gia_ManObj(_cir, fanin1);
      if(Gia_ObjIsPi(_cir, pInput))
        Convert<<"-1";
      else if(Gia_ObjIsCi(pInput)){ // gated or others?
        Gia_Obj_t* Ri =  Gia_ObjRoToRi(_cir, pInput);
        Gia_Obj_t* sigRi = Gia_ObjFanin0(Ri);
        if(fanout == Gia_ObjId(_cir, sigRi)) 
          Convert<<"-2";
        else
          Convert<<"-3";
      }
      else 
        Convert<<"-P";
    }
    Convert<<"&";
    if(_mux2Node.find(fanin0) != _mux2Node.end()){ // has fanin
      Convert<<_mux2Node[fanin0]->getNodeID(); 
    }
    else{
      Gia_Obj_t* pInput = Gia_ManObj(_cir, fanin0);
      if(Gia_ObjIsPi(_cir, pInput))
        Convert<<"-1";
      else if(Gia_ObjIsCi(pInput)){
        Gia_Obj_t* Ri =  Gia_ObjRoToRi(_cir, pInput);
        Gia_Obj_t* sigRi = Gia_ObjFanin0(Ri);
        if(fanout == Gia_ObjId(_cir, sigRi)) 
          Convert<<"-2";
        else
          Convert<<"-3";
      }
      else
        Convert<<"-P";
    }
    if(_in2Nodes.find(fanout)!= _in2Nodes.end()){
      set<muxNode*> in2NodeList = _in2Nodes[fanout];
      set<muxNode*>::iterator site = in2NodeList.begin();
      for(; site!= in2NodeList.end(); ++site)
        Convert<<"&"<<(*site)->getNodeID();
    }
    if(_poList.find(fanout)!= _poList.end())
      Convert<<"PO"; 


    string token = Convert.str();
  //  cerr<<"token: "<<token<<"; fanin1 "<<fanin1<<"; fanin0 "<<fanin0<<endl;
    if(usedToken.find(token)==usedToken.end()){
      vector<int> newVec;
      usedToken[token] = newVec;
    }
    usedToken[token].push_back(i);
  }
  if(usedToken.size() < 2)// no split
    return;
 // if(currentNode->getControlID()!= 120) 
  _badwords.insert(currentNode);
  // final step: create new node and update _mux2Node
  int currentControl = currentNode->getControlID();
  map<string, vector<int> >::iterator mite = usedToken.begin();
  for(; mite!= usedToken.end(); ++mite){
    vector<int> members = mite->second;
    if(members.size() < 4){
      for(int i = 0; i < members.size(); ++i){
        int fanin1;
        int fanin0;
        int gateID;
        currentNode->getFaninPhase(members[i], fanin1, fanin0, gateID);
        _in2Nodes[abs(fanin1)].erase(currentNode);
        _in2Nodes[abs(fanin0)].erase(currentNode);
        _mux2Node.erase(gateID);
      } 
      continue;

    }
    muxNode* newNode = new muxNode(currentControl, _nodeList.size() );
    _nodeList.push_back(newNode);
    for(int i = 0; i < members.size(); ++i){
      int fanin1;
      int fanin0;
      int gateID;
      currentNode->getFaninPhase(members[i], fanin1, fanin0, gateID);
      newNode->addOneMux(gateID, fanin0, fanin1);
      _in2Nodes[abs(fanin1)].erase(currentNode);
      _in2Nodes[abs(fanin1)].insert(newNode);
      _in2Nodes[abs(fanin0)].erase(currentNode);
      _in2Nodes[abs(fanin0)].insert(newNode);
      _mux2Node[abs(gateID)] = newNode;
    } 
  }
  //cleanNodes(); // TODO check?
}
void meowMux::reportWords(){
  vector<int> nodeOrder;
  sortNodes(nodeOrder); 
  for(int i = 0; i < nodeOrder.size(); ++i){
    muxNode* target = _nodeList[nodeOrder[i]];
    if(target->getBitNum() >= 1
    && _badwords.find(target) == _badwords.end())
      target->printMuxNode();

  }
}
void meowMux::forwardCheck(){
 // check can be reached from PI
  vector<int> nodeOrder;
  sortNodes(nodeOrder);
  set<int> piID;
  Gia_Obj_t* pObj;
  int i;
  Gia_ManForEachPi(_cir, pObj, i){
    piID.insert(Gia_ObjId(_cir, pObj));
  }
  for(int i = 0; i < nodeOrder.size(); ++i){
    muxNode* target = _nodeList[nodeOrder[i]]; 
    set<int> faninIDs;
    target->getFaninIDs(faninIDs); // all
    set<int>::iterator site = faninIDs.begin();
    bool fail = false;
    for(; site != faninIDs.end(); ++site){
      if(piID.find(*site) == piID.end()){
        fail = true;
        break;
      }
    }
    if(fail)
      _badwords.insert(target);
    else{
      set<int> fanoutIDs;
      target->getFanoutIDs(fanoutIDs);
      piID.insert(fanoutIDs.begin(), fanoutIDs.end());  
    } 
  }
}
void meowMux::backwardCheck(){
 // similiar to forward
  vector<int> nodeOrder;
  sortNodes(nodeOrder);
  set<int> poID;
  Gia_Obj_t* pObj;
  int i;
  Gia_ManForEachPo(_cir, pObj, i){
    poID.insert(Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj)));
  }
  for(int i = nodeOrder.size() - 1; i >= 0; --i){
    muxNode* target = _nodeList[nodeOrder[i]]; 
    set<int> fanoutIDs;
    target->getFanoutIDs(fanoutIDs);
    set<int>::iterator site = fanoutIDs.begin();
    bool fail = false;
    for(; site != fanoutIDs.end(); ++site){ // all
      if(poID.find(*site) == poID.end()){
        fail = true;
        break;
      }
    }
    if(fail)
      _badwords.insert(target);
    else{
      set<int> faninIDs;
      target->getFaninIDs(faninIDs);
      poID.insert(faninIDs.begin(), faninIDs.end());  
    } 
  }

}
int meowMux::computeDepth(muxNode* currentNode){
  int fanin1;
  int fanin0;
  currentNode->getFaninID(0, fanin1, fanin0);
  if( _mux2Node.find(fanin1) == _mux2Node.end() 
    && _mux2Node.find(fanin0) == _mux2Node.end() ){
    return 1; //support
  }
  if(_mux2Node.find(fanin0) == _mux2Node.end())
    return computeDepth(_mux2Node[fanin1])+1;

  if(_mux2Node.find(fanin1) == _mux2Node.end())
    return computeDepth(_mux2Node[fanin0])+1;
   
  int depth1 = computeDepth(_mux2Node[fanin1]);
  int depth0 = computeDepth(_mux2Node[fanin0]);
  if(depth1> depth0)
    return depth1+1;
  else
    return depth0+1;
}
void meowMux::getBoundaryList(set<muxNode*>& outputList){
  //for forward check those who are not others' input
  set<int> faninList;
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badwords.find(_nodeList[i])== _badwords.end()){
      set<int> faninIDs;
      _nodeList[i]->getFaninIDs(faninIDs);
      faninList.insert(faninIDs.begin(), faninIDs.end()); 
    }
  }
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badwords.find(_nodeList[i])== _badwords.end()){
      set<int> fanoutIDs;
      _nodeList[i]->getFanoutIDs(fanoutIDs);
      set<int>::iterator site = fanoutIDs.begin();
      for(; site != fanoutIDs.end(); ++site){
        if(faninList.find(*site) == faninList.end()){
          outputList.insert(_nodeList[i]);
          break;
        }
      }
    }
  }

}
void meowMux::reportDepth(){
 // check longest and shortest Muxes numbers
  set<muxNode*> boundaryList;
  getBoundaryList(boundaryList);// new! // output boundary
  int maxDepth = 0;
  int maxBound = 0;
  int minBound = -1;
  int minDepth = -1; 
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badwords.find(_nodeList[i])== _badwords.end()){
      int depth = computeDepth(_nodeList[i]);
      //cerr<<"node "<<i<<"depth "<<depth<<endl;
      if(depth > maxDepth)
        maxDepth = depth;
      if(minDepth == -1 || minDepth > depth)
        minDepth = depth;
      if(boundaryList.find(_nodeList[i])!= boundaryList.end()){
        if(depth > maxBound)
          maxBound = depth;
        if(minBound == -1 || minBound > depth)
          minBound = depth;
      }
    }
  }
  cerr<<"Max Depth: "<< maxDepth<<endl;
  cerr<<"Min Depth: "<< minDepth<<endl;
  cerr<<"Max Bound: "<< maxBound<<endl;
  cerr<<"Min Bound: "<< minBound<<endl;
}
void meowMux::reportCount(){
  set<int> provedBits; 
  int maxWidth = -1;
  int minWidth = -1;
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badwords.find(_nodeList[i])== _badwords.end()){
      muxNode* target = _nodeList[i];
   //   target->printMuxNode();
      if(minWidth == -1)
        minWidth = target->getBitNum();
      if(target->getBitNum() > maxWidth){
        maxWidth = target->getBitNum();
        ///target->printMuxNode();
      }
      else if(target->getBitNum() < minWidth)
        minWidth = target->getBitNum();
      
      set<int> faninIDs;
      set<int> fanoutIDs;
      target->getFaninIDs(faninIDs);
      target->getFanoutIDs(fanoutIDs);
      provedBits.insert(faninIDs.begin(), faninIDs.end());
      //provedBits.insert(fanoutIDs.begin(), fanoutIDs.end());
      set<int>::iterator site = fanoutIDs.begin();
      for(; site!= fanoutIDs.end(); ++site){
        Gia_Obj_t * pObj = Gia_ManObj(_cir, abs(*site));
        provedBits.insert(abs(*site));
        int faninID0 = Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj));
        int faninID1 = Gia_ObjFaninId1(pObj, Gia_ObjId(_cir, pObj));
        provedBits.insert(faninID0);
        provedBits.insert(faninID1);
        
      } 
    }
  } 
 // cerr<<"Done with Mux targets "<<provedBits.size()<<endl;
  Gia_ManStaticFanoutStart(_cir);
//  Gia_Obj_t * pObj;
//  Gia_Obj_t* pFanout;
//  int i;
//  int j;
/*  Gia_ManForEachObj1(_cir, pObj, i){
    if(provedBits.find(Gia_ObjId(_cir, pObj))== provedBits.end()){
      // check its fanout
      int fail = false;
      if(Gia_ObjFanoutNum(_cir, pObj)== 0)
        fail = true;
      if(!Gia_ObjIsAnd(pObj))
        fail = true;
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout,j ){
        if(provedBits.find(Gia_ObjId(_cir, pFanout)) == provedBits.end()){
           fail = true;
           break;
        }
        if(j >= 1)
          fail = true;   
      }
      if(fail)
        continue;
      int faninID0 = Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj));
      int faninID1 = Gia_ObjFaninId1(pObj, Gia_ObjId(_cir, pObj));
      if(provedBits.find(faninID0) == provedBits.end() 
      && provedBits.find(faninID1) == provedBits.end())
        fail = true; 
      
      // check input     
      if(!fail){
        if(_control2Mux.find(Gia_ObjId(_cir, pObj)) == _control2Mux.end()){
          provedBits.insert(Gia_ObjId(_cir, pObj));
        }
      }
    }
  }*/
  set<int> inputWordBits;
  int inputWCount = 0;
  for(int i = 0; i < _nodeList.size(); ++i){
    if(_badwords.find(_nodeList[i])== _badwords.end()){
      muxNode* current = _nodeList[i];
      int fanin1, fanin0;
      current->getFaninID(0, fanin1, fanin0); 
      Gia_Obj_t* pObj0 = Gia_ManObj(_cir, fanin0);
      Gia_Obj_t* pObj1 = Gia_ManObj(_cir, fanin1);
      if(Gia_ObjIsPi(_cir, pObj0)){
        vector<int> fanin0s;
        current->getFaninID0(fanin0s);
        bool newW = false;
        for(int k = 0; k < fanin0s.size(); ++k){
          if(inputWordBits.find(fanin0s[k]) == inputWordBits.end())
            newW = true;
        } 
        inputWordBits.insert(fanin0s.begin(), fanin0s.end());
        if(newW)
          inputWCount++;

      }
      if(Gia_ObjIsPi(_cir, pObj1)){
        vector<int> fanin1s;
        current->getFaninID1(fanin1s);
        bool newW = false;
        for(int k = 0; k < fanin1s.size(); ++k){
          if(inputWordBits.find(fanin1s[k]) == inputWordBits.end())
            newW = true;
        }
        inputWordBits.insert(fanin1s.begin(), fanin1s.end());
        if(newW)
          inputWCount++;

 
      } 
    }
  } 
  Gia_ManStaticFanoutStop(_cir);
  cerr<<"inputWord "<<inputWCount<<endl;
  cerr<<"Bits: "<<provedBits.size()<< "Words num: "<<_nodeList.size()-_badwords.size()<<endl;
  cerr<<"Max Width: "<< maxWidth<<endl;
  cerr<<"Min Width: "<< minWidth<<endl;
  set<int>::iterator test = provedBits.begin();
  //for(; test!= provedBits.end(); ++test)
  //  cerr<<(*test)<<" ";
 // cerr<<endl;
}
ABC_NAMESPACE_IMPL_END
