#ifndef WORD_GRAPH_H
#include"ext/meow/wordGraph.h"
#endif
#include<vector>

using namespace std;
// extern "C" int Gia_QbfSolve( Gia_Man_t * pGia, int nPars, int nIterLimit, int nConfLimit, int nTimeOut, int fVerbose, int*  outValue );
wordGraph::wordGraph(Gia_Man_t* cir){
  _cir = cir;
  _callQBF = 0;
  _wordGroup = 1;
  // initialize PI/PIsupport
  _piNum = Gia_ManPiNum(cir);
  _objNum = Gia_ManObjNum(cir);
  _loadNum = new int[_objNum];
  _provedData = new int[_piNum+1];
//  cerr<<"PI NUM"<<_piNum<<endl;
  for(int j = 1; j <= _piNum; ++j)
    _provedData[j] = 0;
  for(int j = 0; j < _objNum; ++j)
    _loadNum[j] = 0;
  int i = 0;
  int totalID = 0;
 // check const test
  _currentFront.clear();
  Gia_Obj_t* pObj;

  Gia_ManForEachPi(_cir, pObj, i){
    totalID = Gia_ObjId(_cir,pObj);
    set<int>* newSupSet = new set<int>;
    newSupSet->insert(totalID);
    _supportMap[totalID] = newSupSet;

    set<int>* newTarSet = new set<int>;
    newTarSet->insert(totalID);

     _targetMap[totalID] = newTarSet;
     _loadNum[totalID]++;
     _currentFront.insert(totalID);
  }
  /*this part should be useless*/
  set<int>* newSupSet = new set<int>;
  newSupSet->insert(0);
  _supportMap[0] = newSupSet;
  set<int>* newTarSet = new set<int>;
  newTarSet->insert(0);
  _targetMap[0] = newTarSet;
  _loadNum[0]++;
 /* pObj = Gia_ManConst0(_cir);
  totalID = Gia_ObjId(_cir,pObj);*/    
}
wordGraph::~wordGraph(){
  
  delete _loadNum;
  for(unsigned i = 0; i < _totalList.size(); ++i)
    delete _totalList[i];
  map<int, set<int>* >::iterator mite = _supportMap.begin();
  for(; mite != _supportMap.end(); ++mite)
    delete (mite->second);

//  for(mite = _transMap.begin(); mite!= _transMap.end(); ++mite)
//    delete mite->second;
  for(mite = _targetMap.begin(); mite != _targetMap.end(); ++mite)
    delete (mite->second);
}
void wordGraph::getOneNode(int ID){
  // recursive find its support
  map<int, set<int>* >::iterator mite = _supportMap.find(ID);
  if(mite == _supportMap.end()){ // if got => visited
    // 
    set<int>* newSupSet = new set<int>;
    _supportMap[ID] = newSupSet;

    Gia_Obj_t* current = Gia_ManObj(_cir, ID);
    int inID1 = Gia_ObjFaninId0(current, ID);
    int inID2 = Gia_ObjFaninId1(current, ID);

    mite = _supportMap.find(inID1);
    if(mite == _supportMap.end()) // not found
      getOneNode(inID1);
    mite = _supportMap.find(inID1);
    set<int>::iterator site = (mite->second)->begin();
    for(; site != (mite->second)->end(); ++site){
       newSupSet->insert(*site);
       _targetMap[(*site)]->insert(ID);
       _loadNum[(*site)]++;
    }

    mite = _supportMap.find(inID2);
    if(mite == _supportMap.end())
      getOneNode(inID2);
    mite = _supportMap.find(inID2);
    site = (mite->second)->begin();
    for(; site != (mite->second)->end(); ++site){
       newSupSet->insert(*site);
       _targetMap[(*site)]->insert(ID);
       _loadNum[(*site)]++;
    }  
  }
}
void wordGraph::walkOneStep(){
  cerr<<"Walk"<<endl;
  _getNew = false;
  set<int>::iterator site = _currentFront.begin();
  set<int> newFront;
  Gia_Obj_t* pFanout;
  int fanoutID =0;
  int i = 0;
  for(; site != _currentFront.end(); ++site){
   // cerr<<"Front:"<<(*site)<<endl;
    Gia_Obj_t* current = Gia_ManObj(_cir, (*site));
    Gia_ObjForEachFanoutStatic( _cir, current, pFanout, i ){
      fanoutID = Gia_ObjId(_cir,pFanout);
      getOneNode(fanoutID);
      newFront.insert(fanoutID);
    } 
  }
  swap(_currentFront, newFront);
}
bool wordGraph::checkRepeat(vector<int>&inID, vector<int>& outID){
  for(int i = 0; i < _totalList.size(); ++i)
    if(_totalList[i]->same(inID, outID))
      return true;
  return false;
}
bool wordGraph::checkGroup(vector<int>& inID){
  int group = _provedData[(inID[0])];
  for(int i = 1; i < inID.size(); ++i)
    if(_provedData[inID[i]] != group)
      return false;
  return true;
}
bool wordGraph::addNewNode(vector<int>& inID, vector<int>& outID, vector<int>& IDs, vector<int>& values){
  if(checkRepeat(inID,outID))
    return false;
  if(!checkGroup(inID))
    return false;
  wordNode* newNode = new wordNode(inID, outID, IDs, values);
  _totalList.push_back(newNode);
  bool useGroup = false;
  
  for(unsigned i = 0; i < inID.size(); ++i){
    
    if(_provedData[(inID[i])] == 0){
      //cerr<<"group"<<_wordGroup<<" "<<inID[i]<<endl;
      _provedData[(inID[i])] = _wordGroup;
      useGroup = true;
    }
    if(outID[i] < 0)
      outID[i] = (-1)*outID[i];
 /*   map<int, set<int>*>::iterator mite = _transMap.find(outID[i]);
    if(mite==_transMap.end()){
      set<int>* newTrans = new set<int>; 
      newTrans->insert(inID[i]);
      _transMap[outID[i]] = newTrans;
    }
    else{
      _transMap[outID[i]]->insert(inID[i]);
    }*/
  }
  if(useGroup)
    _wordGroup++;
  return true;
}
void wordGraph::printNodes(){
  cerr<<"Word List:"<<_totalList.size()<<" callQbf: "<<_callQBF<<endl;
  set<int> list;
  for(unsigned i = 0; i < _totalList.size(); ++i){
    _totalList[i]->printNode();
    list.insert(_totalList[i]->wordSize());
  }
  cerr<<"bitwidth"<<endl;
  set<int>::iterator site = list.begin();
  for(; site!= list.end(); ++site)
    cerr<<(*site)<<" ";
}
void wordGraph::findCandidate(){
  // go through target and find multi-out
  map<int, set<int>* >::iterator mite = _targetMap.begin();
  vector<int> wordCandidate;
  for(; mite != _targetMap.end(); ++mite){
   // if(_transMap.find(mite->first) != _transMap.end()) // they are not target! they are internal data
   //   continue;
    if((mite->first) >= _piNum)
      continue;
    if((mite->second)->size() <= 4 || (mite->first)== 0 )
      continue;
    if(((mite->first) < _piNum) && (_provedData[(mite->first)] != 0 ))
      continue;
    wordCandidate.clear();

    set<int>::iterator site = (mite->second)->begin(); //candidate
   // bool add = false;
    //cerr<<"Candidate:";
    for(; site!= (mite->second)->end(); ++site ){
      wordCandidate.push_back((*site));
     // cerr<<(*site)<<" "; 
    }
    //cerr<<endl;

    proveWord(wordCandidate); // after that, target will be update
  }  
}
void wordGraph::proveWord( vector<int>& wordCandidate ){ //TODO
  //propagate meow
  //add word
  map<int, int> localGroup;
  for(unsigned i = 0; i < wordCandidate.size(); ++i){
    set<int>* supports = _supportMap[wordCandidate[i]];
    set<int>::iterator site = supports->begin();
    for(; site != supports->end(); ++site){
      if((*site) > _piNum )
        continue;
      if(localGroup.find(*site) == localGroup.end())
        localGroup[*site] = 1;
      else
        localGroup[*site] = localGroup[*site]+1;
    }
  }

  vector<int> highID ; // = false;
  vector<int> lowID; // = false;
  for(unsigned i = 0; i < wordCandidate.size(); ++i){
    highID.clear();
    lowID.clear();
    int currentID = wordCandidate[i];
    if(checkOverlap(currentID))
      continue;
   // cerr<<"current: "<<currentID<<" load:"<<_loadNum[currentID]<<endl;
    if(_loadNum[currentID] > 0) // visited
      continue; 
    map<int, set<int>* >::iterator mite = _supportMap.find(currentID);
    //map<int, set<int>* >::iterator mite2;
    set<int>::iterator site = (mite->second)->begin();
    for(; site!= (mite->second)->end(); ++site){
      if((*site) > _piNum)
        continue;
      if(localGroup[*site] > wordCandidate.size()/4)
        highID.push_back(*site);
      else
        lowID.push_back(*site);

    }
    if((lowID.size() > 0) &&  (highID.size() > 0)){
      //cerr<<"yes, get "<<currentID<<endl;
    
      proveOneNode(currentID, lowID, highID);
    }
    //apply(/* */); // consider MUX case multi-assignment!
  }
// after proved, remove from target??   TODO
 // just update _loadNum
 
}
int wordGraph::recurCopy(Gia_Man_t* pNew, int ID){
  Gia_Obj_t* pObj = Gia_ManObj(_cir, ID);
  if(~pObj->Value)
    return pObj->Value;
  if(Gia_ObjIsAnd(pObj)){
    int id1 = Gia_ObjFaninId0( pObj, ID);
    int id2 = Gia_ObjFaninId1( pObj, ID);
  //cerr<<"Copy"<<ID<<" input:"<<id1<<"and"<<id2<<endl;
    recurCopy(pNew, id1);
    recurCopy(pNew, id2);
    int newLit = Gia_ManHashAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
 //  cerr<<"Copy"<<ID<<" input:"<<Gia_ObjFanin0Copy(pObj)<<"and"<<Gia_ObjFanin1Copy(pObj)<<"get"<<newLit<<endl;

     pObj->Value = newLit;
//  Gia_Obj_t* newObj  = Gia_ManObj(pNew, Abc_Lit2Var(newLit));
//  newObj->Value = ID; // record the mapping back 

    return newLit;
  }
  else {// single Fanin ->Co
    //cerr<<"ReachCo?"<<endl;
    int id1 = Gia_ObjFaninId0( pObj, ID);
   // int id2 = Gia_ObjFaninId1( pObj, ID);
  //cerr<<"Copy"<<ID<<" input:"<<id1<<"and"<<id2<<endl;
    recurCopy(pNew, id1);
   // recurCopy(pNew, id2);
    int newLit =  Gia_ObjFanin0Copy(pObj);
 //  cerr<<"Copy"<<ID<<" input:"<<Gia_ObjFanin0Copy(pObj)<<"and"<<Gia_ObjFanin1Copy(pObj)<<"get"<<newLit<<endl;

     pObj->Value = newLit;
//  Gia_Obj_t* newObj  = Gia_ManObj(pNew, Abc_Lit2Var(newLit));
//  newObj->Value = ID; // record the mapping back 

     return newLit;

  }
}
void wordGraph::proveOneNode( int ID, vector<int>& lowID, vector<int>& highID){
  //TODO find an assignment and get a mapping
  // return in -> this id && partial assignment
//  cerr<<"Call proveOneNode:"<<ID<<endl;
  if(ID < _piNum)
    return;
 // vector<int> values;
//  cerr<<"call callObf for "<<ID<<endl;
  callQbf(lowID, highID, ID, false);
//  cerr<<"finishQbf- for"<<ID<<" "<<lowID.size()<<" "<<highID.size()<<endl;

  callQbf(lowID, highID, ID, true);
 // cerr<<"finishQbf+ for"<<ID<<endl;
    // cerr<<"done with PIs"<<ID<<endl;
}
void wordGraph::callQbf(vector<int>& lowID, vector<int>& highID, int ID, bool negate){
  // cerr<<"call Qbf"<<ID<<endl; 
  for(unsigned i = 0; i < lowID.size(); ++i){
    _callQBF++;
    // step 2 model the problem
    Gia_Man_t* pNew, *pTemp;
    Gia_Obj_t* pObj;
//  int i;
  //  cerr<<"prove low"<<lowID[i]<<endl;
    pNew = Gia_ManStart( Gia_ManObjNum(_cir) );
    Gia_ManHashAlloc( pNew );
    Gia_ManFillValue( _cir );
    Gia_ManConst0(_cir)->Value = 0;
    for(unsigned j = 0; j < highID.size(); ++j){ // add parameter
  // step 2-1
      //cerr<<"high"<<highID[j]<<endl; 
      pObj = Gia_ManObj( _cir, (highID)[j] );
      pObj->Value = Gia_ManAppendCi(pNew); 
    }
  //  cerr<<"done with parameters"<<endl;
    int piLit = 0;
    for(unsigned j = 0; j < lowID.size(); ++j){
      pObj = Gia_ManObj( _cir, (lowID)[j] );
      pObj->Value = Gia_ManAppendCi(pNew); 
      if(i == j)
        piLit = pObj->Value; // to create out == in
    }
  //  cerr<<"done with variable"<<endl;
    int tempPo = recurCopy(pNew, ID); // currentID, our po here
   // cerr<<"done with copy"<<endl;
    int xorLit;
    if(negate)
      xorLit = Gia_ManHashXor(pNew, Abc_LitNot(tempPo),piLit );
    else 
      xorLit = Gia_ManHashXor(pNew, tempPo,piLit );

    Gia_ManAppendCo(pNew, Abc_LitNot(xorLit));
  // 3. solve it 
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    assert(Gia_ManPiNum(pNew) == (highID.size() + lowID.size()));
    int* outValue = new int[highID.size()];
 //   (*outValue) = Vec_IntAlloc(Gia_ManPiNum(pNew));
    int result = 0; // Gia_QbfSolve( pNew, highID.size(), 0, 0, 0, 0 , outValue);
    if(result == 0){ // sat
      vector<int> values;
      for(unsigned j = 0; j < highID.size(); ++j)
        values.push_back(outValue[j]);
      apply(highID, values, negate);
    }
  
    delete outValue;
    Gia_ManStop(pNew);
  }
  //cerr<<"Finish"<<ID<<endl;
}
void wordGraph::cleanTarget(vector<int>& IDs){
  for(unsigned i = 0; i < IDs.size(); ++i){
  //  cerr<<"clean target for"<<IDs[i]<<endl; 
    // they are outWord
    if(IDs[i] < 0){
      IDs[i] = -1* IDs[i];
     // cerr<<"Error!"<<endl;
      //return;
    }
    set<int>* supports = _supportMap[IDs[i]];
    set<int>::iterator site = supports->begin();
    for(; site!= supports->end(); ++site){
      set<int>* targets = _targetMap[(*site)];
      if(targets->find(IDs[i])!= targets->end()){
        targets->erase(IDs[i]);
        _loadNum[(*site)]--;
      }
     // cerr<<"--load"<<(*site)<<"for"<<IDs[i]<<endl;
    }

    _loadNum[IDs[i]]++;
 //   cerr<<"run update load of "<<IDs[i]<<" "<<_loadNum[IDs[i]]<<endl;
    _supportMap[IDs[i]]->insert(IDs[i]);
    set<int>* newTarget = new set<int>; 

    _targetMap[IDs[i]] = newTarget;
    newTarget->insert(IDs[i]);

  }
}
void wordGraph::apply(vector<int>& IDs, vector<int>& values, bool negate){ // TODO
  //cerr<<"run apply"<<endl; 
  Gia_Man_t * pNew;
  Gia_Obj_t * pObj; int i;
  pNew = Gia_ManStart( Gia_ManObjNum(_cir) );
  Gia_ManHashAlloc( pNew );
  Gia_ManFillValue( _cir );
  Gia_ManConst0(_cir)->Value = 0;

  int* Big = new int[_piNum+1]; // maxID same as this pi
  map<int, int> litToPi;
  Gia_ManForEachPi( _cir, pObj, i ){
    int thisID =  Gia_ObjId(_cir,pObj);
    Big[thisID] = thisID;
 //   cerr<<"Put Big["<<thisID<<"] as"<<thisID<<endl;
    for(unsigned j = 0; j < IDs.size(); ++j){
      if(thisID == IDs[j]){
        pObj->Value = values[j];
        //piToLit[thisID] = values[j];
        //cerr<<"assign"<<thisID<<" "<<values[j]<<endl;
      }
    }
    if(~pObj->Value) // not empty
      continue;
    else{
      int newLit = Gia_ManAppendCi(pNew);
      pObj->Value = newLit;
      //Big[thisID] = thisID;
      litToPi[newLit] = thisID;
   //    cerr<<"produce"<<newLit<<"for"<<thisID<<endl;
     // Gia_Obj_t* newObj = Gia_ObjCopy(_cir, pObj); 
     // newObj->Value = thisID; // mapping back to the cir ID
    }
  }
  set<int>::iterator site = _currentFront.begin();
  for(; site!= _currentFront.end();++site){
    int outLit = recurCopy(pNew, (*site));
   // cerr<<"Front:"<<(*site)<<" Lit"<<outLit<<endl;
    Gia_ManAppendCo(pNew, outLit);
  }
  Gia_ManForEachObj(_cir, pObj, i){
    int reprLit;
    if(negate)
      reprLit = Abc_LitNot(pObj->Value);
    else
      reprLit = pObj->Value;
   // cerr<<"ID:"<<Gia_ObjId(_cir, pObj)<<" Value"<<pObj->Value<<endl;
    map<int, int>::iterator mite = litToPi.find(reprLit);
    // note consider negate
    if(mite != litToPi.end()){
      if(Gia_ObjId(_cir, pObj) >Big[mite->second] )
        Big[mite->second] = Gia_ObjId(_cir, pObj);
     //   cerr<<"get"<<Gia_ObjId(_cir, pObj)<<"From "<<mite->second<<endl;
      // Value => pi
    }
  }
  vector<int> inID;
  vector<int> outID;

  for(int k = 1; k <= _piNum ;++k ){
    if(Big[k]!= k){
      inID.push_back(k);
      if(negate)
        outID.push_back((-1)*Big[k]);
      else
        outID.push_back(Big[k]);

//      cerr<<"Get"<<k<<"to"<<Big[k]<<endl;
    }
  }
  // for all obj, check! if their Value is the same as some pi 
  // after copy, check their copy 
  Gia_ManStop(pNew);
  // TODO clean target, add Load!
//  cerr<<"Done with Collect"<<outID.size()<<endl;
  if(outID.size() >= 3){
    if(addNewNode(inID, outID,IDs, values )){
//    cerr<<"Done with adding"<<endl;
      cleanTarget(outID);
      _getNew = true;
    }
  }
  // get words, clean target
  // findPI
  delete Big; 
}
bool wordGraph::isProved(int ID){
  // proved internal signal should have load
  if(_loadNum[ID] > 0)
    return true;
  else
    return false;
}
bool wordGraph::stopOneRound(){
  // analyze _targetMap
  return false;
}
bool wordGraph::checkTerminate(){
  // analyze _supportMap
  return (!_getNew);
}
bool wordGraph::checkOverlap(int ID){
 // check front, see if they got dulplicate
  //set<int>::iterator site = _currentFront.begin();
  //for(; site!= _currentFront.end(); ++site){
    set<int> groups;
    set<int>* supports = _supportMap[ID];
    set<int>::iterator site2 = supports->begin();
    for(;  site2!=supports->end(); ++site2){
      if(((*site2)< _piNum )&& (_provedData[(*site2)]!=0)){
        if(groups.find(_provedData[*site2]) != groups.end())
          return true;
        groups.insert( _provedData[*site2]);
      }
    }
  //}
  return false;
}
void wordGraph::printSupport(){
  map<int, set<int>* >::iterator mite =  _supportMap.begin();
  for(; mite!= _supportMap.end(); ++mite){
    cerr<<"Signal:"<<mite->first<<endl;
    set<int>::iterator site = (mite->second)->begin();
    for(; site != (mite->second)->end(); ++site)
      cerr<<(*site)<<" ";
    cerr<<endl;
  }
}
void wordGraph::printTarget(){
  map<int, set<int>* >::iterator mite =  _targetMap.begin();
  for(; mite!= _targetMap.end(); ++mite){
    cerr<<"PI:"<<mite->first<<" Load"<<_loadNum[mite->first]<<endl;
    set<int>::iterator site = (mite->second)->begin();
    for(; site != (mite->second)->end(); ++site)
      cerr<<(*site)<<" ";
    cerr<<endl;
  }


}
