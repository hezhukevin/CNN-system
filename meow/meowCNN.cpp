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
#include "ext/meow/meowCNN.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
extern "C" unsigned * Gia_ManConvertAigToTruth( Gia_Man_t * p, Gia_Obj_t * pRoot, Vec_Int_t * vLeaves, Vec_Int_t * vTruth, Vec_Int_t * vVisited );
extern "C" int Dar_LibReturnClass( unsigned uTruth );

ABC_NAMESPACE_IMPL_START

void meowUsageCNN(){
  Abc_Print( -2, "usage: meowCNN [-F <fileName>][-P <folderName>] [-M <id>] \n" );
  Abc_Print( -2, "\t -h    : print the command usage\n");
  Abc_Print( -2, "\t -F <filename>   : write out matrices to describe the current circuit to <filename>, run after &if -K 4\n");
  Abc_Print( -2, "\t -P <fileFolder> : for locate operator, partition the current circuit, write out matrices for sub-circuits into <folderName>, come with *.group and *.data \n");
  Abc_Print( -2, "\t -M <mode>   : indicate the output mode 1-5, for DFS order, run &dfs first \n");
  Abc_Print( -2, "\t mode 1: singleEV+original order\n");
  Abc_Print( -2, "\t mode 2: doubleEV+original order\n");
  Abc_Print( -2, "\t mode 3: singleEV+BFS order\n");
  Abc_Print( -2, "\t mode 4: doubleEV+BFS order\n");
  Abc_Print( -2, "\t mode 5: naive format, run after &if -K 3\n");





}
meowCNN::meowCNN(Gia_Man_t* cir){
  _cir = cir;
  _aigNum = 20000;
  _lutNum = 4000;
  _lutGroupNum = 40;
  _truthNum = 10; // top 10?
}
Gia_MapLut_Meow* meowCNN::getMapLut( int& lutNum){
  Gia_Obj_t * pObj;
  int i, k, iFan, iLut = 0;
  int LutSizeMax = Gia_ManLutSizeMax(_cir);
  int nUints = Abc_TruthWordNum(LutSizeMax);
  int nLuts = 1 + Gia_ManCiNum(_cir) + Gia_ManCoNum(_cir) + Gia_ManLutNum(_cir);
  Gia_MapLut_Meow* pLuts = ABC_CALLOC( Gia_MapLut_Meow, nLuts );
  Vec_Wrd_t * vTruths = Vec_WrdStart( Gia_ManObjNum(_cir) );
 // assert( LutSizeMax <= 6 );
    // set obj numbers
    // constant
  pLuts->Type = 3;
  memset( pLuts->pTruth, 0xFF, sizeof(unsigned) * nUints );
  Gia_ManFillValue(_cir);
  Gia_ManConst0(_cir)->Value = pLuts[iLut].Out = Abc_Var2Lit( iLut, 0 );
  iLut++;
    // inputs
  Gia_ManForEachCi( _cir, pObj, i )
    {
        pLuts[iLut].Type = 1;
        memset( pLuts[iLut].pTruth, 0xAA, sizeof(unsigned) * nUints );
        pObj->Value = pLuts[iLut].Out = Abc_Var2Lit( iLut, 0 );
        iLut++;
    }
    // nodes
    Gia_ManForEachObj( _cir, pObj, i )
        if ( i && Gia_ObjIsLut(_cir, i) )
        {
            pLuts[iLut].Type = 3;
            Gia_LutForEachFanin( _cir, i, iFan, k )
                pLuts[iLut].pFans[k] = Gia_ManObj(_cir, iFan)->Value;
            pLuts[iLut].nFans = k;
            *(word *)pLuts[iLut].pTruth = Gia_LutComputeTruth6(_cir, i, vTruths);
            pObj->Value = pLuts[iLut].Out = Abc_Var2Lit( iLut, 0 );
            iLut++;
        }
    // outputs
    Gia_ManForEachCo( _cir, pObj, i )
    {
        pLuts[iLut].Type = 2;
        pLuts[iLut].pFans[0] = Gia_ObjFanin0(pObj)->Value;
        if ( Gia_ObjFaninC0(pObj) ^ Gia_ObjIsConst0(Gia_ObjFanin0(pObj)) )
            memset( pLuts[iLut].pTruth, 0x55, sizeof(unsigned) * nUints );
        else
            memset( pLuts[iLut].pTruth, 0xAA, sizeof(unsigned) * nUints );
        pLuts[iLut].nFans = 1;
        pObj->Value = pLuts[iLut].Out = Abc_Var2Lit( iLut, 0 );
        iLut++;
    }
    assert( iLut == nLuts );
    lutNum = nLuts;
  Vec_WrdFree( vTruths );

  return pLuts;

}
/*void meowCNN::simpleReport(){
  int lutNum = 0;
  Gia_MapLut_Meow* pLuts = getMapLut( lutNum);
  int gateNum = Gia_ManObjNum(_cir);
  cerr<<"Obj: "<<gateNum<<", Lut: "<<lutNum<<endl;
  writeLutNpn(std::cerr, 0);
  ABC_FREE(pLuts);

}*/
void meowCNN::writeTruth(Gia_MapLut_Meow* pLuts, ofstream& output, int lutNum){
  int i = 0;
  for(i = 0; i < lutNum; ++i){
    for(int j = 15; j >= 0; --j){
      if((1<<j)&pLuts[i].pTruth[1])
        output<<"1";
      else
        output<<"0";
    }
   /* for(int j = 31; j >= 0; --j){
      if((1<<j)&pLuts[i].pTruth[0])
        output<<"1";
      else
        output<<"0";
    }*/
    output<<endl;
  }
  for(; i < _lutNum; ++i){
    for(int j = 15; j >= 0; --j)
      output<<"0";
    output<<endl;
  }
}
void meowCNN::writeLutConnect2(Gia_MapLut_Meow* pLuts, ofstream& output, int lutNum){
  map<int, int> out2Lut;
  assert(  Gia_ManLutSizeMax( _cir ) <= 4 );
  int i = 0;
  for(; i < lutNum; ++i){
    int outputId = pLuts[i].Out;
    out2Lut[outputId] = i+1;
    //if(pLuts[i].Type == 1){
    //  continue;

    //}
    int j = 0;
    for(; j < pLuts[i].nFans; j++) {
      int faninLut = out2Lut[pLuts[i].pFans[j]];
      output<<faninLut<<" "; 
    }
    for(; j < 4; ++j)
      output<<"0 ";
    output<<endl;
  }
  for( ; i < _lutNum; ++i){
    for(int j = 0; j < 4; ++j)
      output<<"0 ";
    output<<endl;
  }

}
void meowCNN::writeLutConnect(Gia_MapLut_Meow* pLuts, ofstream& output, int lutNum){
  int* table = new int[_lutNum*_lutNum];
  for(int i = 0; i < _lutNum*_lutNum; ++i)
    table[i] = 0;
  map<int, int> out2Lut;
  for(int i = 0; i < lutNum; ++i){
    int outputId = pLuts[i].Out;
    out2Lut[outputId] = i;
    if(pLuts[i].Type == 1)
      continue;
    for(int j = 0; j < pLuts[i].nFans; j++) {
      int faninLut = out2Lut[pLuts[i].pFans[j]];
      table[i*_lutNum+faninLut] = j+1; 
    }
  }
  for(int i = 0; i < _lutNum; ++i){
    for(int j = 0; j < _lutNum; ++j){
      output<<table[_lutNum*i+j];
    }
    output<<endl;
  }
  delete[] table;
}
void meowCNN::writeLutNpn(ostream& output, int mode){
  // only for &if -K 4 (default)
//  extern char ** Kit_DsdNpn4ClassNames();
//  char ** pNames = Kit_DsdNpn4ClassNames();
  //cerr<<"Hello?"<<endl;
  Vec_Int_t * vLeaves, * vTruth, * vVisited;
  int * pLutClass, ClassCounts[222] = {0};
  int i, k, iFan, Class, OtherClasses, OtherClasses2, nTotal, Counter, Counter2;
  unsigned * pTruth;
  map<int, unsigned> id2Truth;
  assert( Gia_ManHasMapping(_cir) );
  assert(  Gia_ManLutSizeMax( _cir ) <= 4 );
  vLeaves   = Vec_IntAlloc( 100 );
  vVisited  = Vec_IntAlloc( 100 );
  vTruth    = Vec_IntAlloc( (1<<16) );
  pLutClass = ABC_CALLOC( int, Gia_ManObjNum(_cir) );
  Gia_ManCleanTruth( _cir );
  Gia_ManForEachLut( _cir, i ){
    if ( Gia_ObjLutSize(_cir,i) > 4 )
      continue;
    Vec_IntClear( vLeaves );
    Gia_LutForEachFanin( _cir, i, iFan, k )
      Vec_IntPush( vLeaves, iFan );
    for ( ; k < 4; k++ )
      Vec_IntPush( vLeaves, 0 );
    pTruth = Gia_ManConvertAigToTruth( _cir, Gia_ManObj(_cir, i), vLeaves, vTruth, vVisited );
    Class = Dar_LibReturnClass( *pTruth );
    ClassCounts[ Class ]++;
    pLutClass[i] = Class;
    id2Truth[Class] = *pTruth;
  }
  Vec_IntFree( vLeaves );
  Vec_IntFree( vTruth );
  Vec_IntFree( vVisited );
  Vec_IntFreeP( &_cir->vTruths );
  
  nTotal = 0;
  for( i = 0; i < 222; i++)
    nTotal+= ClassCounts[i];
  //cerr<<"LUTs?"<<nTotal<<endl; // it does not include PI/CONST
  if(mode == 3){ // report percentages
    output.precision(2);
    for(i = 0; i < 222; ++i){
      double percent = double(ClassCounts[i])/double(nTotal+1);
      output<<percent<<" ";
    }
    output<<endl;
  }
  if(mode == 2){// // sort by Count report top 10?
    //cerr<<"Hello"<<endl; 
    vector< pair<int, int> > count2id;
    for(i = 0; i < 222; ++i){
      if(ClassCounts[i] == 0)
        continue;
      count2id.push_back(pair<int, int>(ClassCounts[i], i));
    }
    sort(count2id.begin(), count2id.end());
    reverse(count2id.begin(), count2id.end());
    for(i = 0; i < 10; ++i){
      if(i >= count2id.size())
        break;
      unsigned truthV = id2Truth[count2id[i].second];
      //output<<"Class: "<<count2id[i].second;
      for(int x = 15; x >= 0; --x){
        if((1<<x)&truthV)
          output<<"1";
        else
          output<<"0";
      }
      output<<endl;
      //output<<count2id[i].second<<endl;
    }
    for(; i < 10; ++i){
      for(int x = 15; x >= 0; --x)
        output<<"0";
      //output<<"-1"<<endl;
      output<<endl;
    }
  }
}
void meowCNN::writeSingleTruth(Gia_MapLut_Meow* pLuts,
                               ofstream& output, int id, int mode){
  if(id < 0){
    if(mode == 5){
      output<<(1<<16)<<" ";
    }
    if(mode == 4){
      for(int j = 15; j >= 0; --j)
        output<<"2";
    }
    return;
  }
  if(mode == 4){
    for(int j = 15; j >= 0; --j){
      if((1<<j)&pLuts[id].pTruth[0])
        output<<"1";
      else
        output<<"0";
    }
  }
  if(mode == 5){
    output<<(((1<<16)-1)&pLuts[id].pTruth[0])<<" ";
  
  }
}
/*bool sortBags(meowBag* bagFirst, meowBag* bagSecond) {
  int countDiff = bagFirst->getCount() - bagSecond->getCount();
  if(countDiff > 0)
    return true; 
  if(countDiff < 0 )
    return false;
  if(bagFirst->getOneSize() > bagSecond->getOneSize())
    return true;

  return false; 
};*/
void meowCNN::assignId2EV( Gia_MapLut_Meow* pLuts, vector<dEV* >& id2dEV, int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs){
  for(int idx = 0; idx < lutNum; ++idx){
    set<int> fanins;
    set<int> fanouts;
    int npnID = Dar_LibReturnClass(pLuts[idx].pTruth[0]);
    fanins.insert(npnID);
    fanouts.insert(npnID);

    for(int j = 0; j < pLuts[idx].nFans; j++){
      int faninLut = out2Lut[pLuts[idx].pFans[j]];
      npnID = Dar_LibReturnClass(pLuts[faninLut].pTruth[0]);
      fanins.insert(npnID); 
    }

    if(id2FanoutIDs.find(idx)!= id2FanoutIDs.end()){
      set<int>* fanoutIDs = id2FanoutIDs[idx];
      set<int>::iterator site = fanoutIDs->begin();
      for(; site != fanoutIDs->end(); ++site){
        npnID = Dar_LibReturnClass(pLuts[(*site)].pTruth[0]);
        fanouts.insert(npnID);
      }
    }
    dEV* newEV = new dEV(fanins, fanouts);
    id2dEV.push_back(newEV);
  }
}
void meowCNN::BFSGrouping( Gia_MapLut_Meow* pLuts, int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs, vector<EVGroup*>& groups ){
  queue<int> todoList;
  vector<int> newOrder;
  set<int> visitedNode;
  int piNum = Gia_ManPiNum(_cir);
  for(int i = 0; i < piNum+1; ++i )
    todoList.push(i);
 
  while(!todoList.empty()){
    int vertex = todoList.front();
    todoList.pop();
    if(visitedNode.find(vertex)!= visitedNode.end()) // ideally never
      continue;
    newOrder.push_back(vertex);
    visitedNode.insert(vertex);
    if(id2FanoutIDs.find(vertex)!= id2FanoutIDs.end()){
      set<int>* fanouts = id2FanoutIDs[vertex];
      set<int>::iterator site = fanouts->begin();
      for(; site!= fanouts->end(); ++site){
        if(visitedNode.find((*site))!= visitedNode.end())// never
          continue;
        bool fully = true;
        for(int k = 0; k < pLuts[(*site)].nFans; k++){
          int faninLut = out2Lut[(pLuts[(*site)].pFans[k])];
          if(visitedNode.find(faninLut) == visitedNode.end()){
            fully = false;
            break;
          }
        }
        if(fully)
          todoList.push((*site));
      }
    }
  }
  if(newOrder.size() != lutNum)
    cerr<<"Error! mismatch!\n";

  int groupSize = lutNum/_lutGroupNum;
  if(groupSize < 1){
    cerr<<"WARN: number of LUTs is too small.\n";
    return;
  }
//  vector<EVGroup* > groups;
  int remain = lutNum%_lutGroupNum;
  int idx = 0;
  for(int i = 0; i < _lutGroupNum; ++i){
    // inside each group perform pooling
    set<int> LUTs;
    int upper = idx+groupSize;
    if(i < remain )
      upper += 1;
    for(; idx < upper; ++idx)
      LUTs.insert(newOrder[idx]);
   
    EVGroup* newGroup = new EVGroup(LUTs);
    groups.push_back(newGroup); 
  } 
} 
void meowCNN::dynamicGrouping( Gia_MapLut_Meow* pLuts, int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs, vector<EVGroup*>& groups ){
  map<int, EVGroup*> id2Group;
  set<EVGroup*> runningGroups;
  int aveGroupSize = lutNum/_lutGroupNum;
  int maxGroupSize = aveGroupSize*1.2;
  int minGroupSize = aveGroupSize*0.5;
  for(int i = 1; i < lutNum; ++i){
    vector< pair<int, int> > size2LUT; 
    for(int j = 0; j < pLuts[i].nFans; j++){
      int faninLut = out2Lut[pLuts[i].pFans[j]];
      int groupSize = id2Group[faninLut]->groupSize();
      //totalNum+=groupSize;
      size2LUT.push_back(pair<int, int>(groupSize,faninLut));
    } // for pi, skip
    EVGroup* newGroup = new EVGroup(i); // 
    id2Group[i] = newGroup;
    runningGroups.insert(newGroup);
    sort(size2LUT.begin(), size2LUT.end());
    for(int j = 0; j < size2LUT.size(); ++j){
      int currentSize = newGroup->groupSize();
      int faninLut = size2LUT[j].second;
      if(currentSize+id2Group[faninLut]->groupSize()< maxGroupSize ){
        // merge in!
        EVGroup* oldGroup = id2Group[faninLut];
        if(oldGroup == newGroup)
          continue;
        set<int>& faninLUTs = id2Group[faninLut]->getLUTs();
        newGroup->addMembers(faninLUTs);
        set<int>::iterator site = faninLUTs.begin();
        for(; site!= faninLUTs.end(); ++site)
          id2Group[(*site)] = newGroup; // update group
        
        delete oldGroup;
        runningGroups.erase(oldGroup);
      }
      else
        break;
    } 
  }
  // merge too small into neighbor
  set<EVGroup*>::iterator site2 = runningGroups.begin(); 
  set<EVGroup*> deleteGroups; 
  for(; site2!= runningGroups.end(); ++site2){
    if((*site2)->groupSize() > minGroupSize)
      continue;
    mergeSmallest(*site2, id2Group, pLuts, out2Lut, id2FanoutIDs);
    deleteGroups.insert((*site2));
    // merge to smallest
  }
  site2 = deleteGroups.begin();
  for(; site2!= deleteGroups.end(); ++site2){
    runningGroups.erase(*site2);
    delete(*site2);
  }

  deleteGroups.clear();
  // merge from smallest 
  if(runningGroups.size() > _lutGroupNum){
    int target = runningGroups.size() - _lutGroupNum;
    vector< pair<int, EVGroup*> > size2Group;
    set<EVGroup*> usedGroups; 
    site2 = runningGroups.begin();
    for(; site2 != runningGroups.end(); ++site2){
      size2Group.push_back(pair<int, EVGroup*>((*site2)->groupSize(),
                                               (*site2)));
    }
    sort(size2Group.begin(), size2Group.end());
    int idx = 0;
    while(deleteGroups.size() < target){
      EVGroup* small = size2Group[idx].second;
      if(usedGroups.find(small)!= usedGroups.end()){
        idx++;
        continue;
      }
      else{
        EVGroup* big = mergeSmallest(small, id2Group, pLuts,
                                     out2Lut, id2FanoutIDs);
        usedGroups.insert(big);
        deleteGroups.insert(small);
        idx++;
      }
    }
  } 
  // first merge ! (if still more than need merge from smallest...)
  site2 = deleteGroups.begin();
  for(; site2!= deleteGroups.end(); ++site2){
    runningGroups.erase(*site2);
    delete (*site2);
  }

  deleteGroups.clear();
 // ideally no need for id2Group, so we don't update it here 
  if(runningGroups.size() < _lutGroupNum){
    int target = _lutGroupNum - runningGroups.size();
    vector< pair<int, EVGroup*> > size2Group;
  //  set<EVGroup*> usedGroups; 
    site2 = runningGroups.begin();
    for(; site2 != runningGroups.end(); ++site2){
      size2Group.push_back(pair<int, EVGroup*>((*site2)->groupSize(),
                                               (*site2)));
    }
    sort(size2Group.begin(), size2Group.end());
    for(int k = 0; k < target; ++k){ // gtom big to small
      int idx = size2Group.size()-1-k;
      EVGroup* old = size2Group[idx].second;
      old->split(runningGroups);
      runningGroups.erase(old);
      delete old;
    } 
  }
  // split done


  vector< pair<int, EVGroup*> > order2Group;
  //  set<EVGroup*> usedGroups; 
  site2 = runningGroups.begin();
  for(; site2 != runningGroups.end(); ++site2){
    order2Group.push_back(pair<int, EVGroup*>((*site2)->order(),
                                              (*site2)));
  }
  sort(order2Group.begin(), order2Group.end());
  for(int k = 0; k < order2Group.size(); ++k )
    groups.push_back(order2Group[k].second);
  // finally, put into groups

}

EVGroup* meowCNN::mergeSmallest(EVGroup* current, map<int, EVGroup*>& id2Group, Gia_MapLut_Meow* pLuts, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs){
  set<int>& currentLUTs = (current)->getLUTs();
  set<int>::iterator site = currentLUTs.begin();
  EVGroup* smallest = NULL;
  for(; site!= currentLUTs.end(); ++site){
    for(int j = 0; j < pLuts[*site].nFans; ++j){
      int faninLut = out2Lut[pLuts[*site].pFans[j]];
      if(id2Group[faninLut] == current)
        continue;
      int groupSize = id2Group[faninLut]->groupSize();
      if(smallest == NULL || groupSize < smallest->groupSize())
        smallest = id2Group[faninLut];
    } // check fanin
    if(id2FanoutIDs.find(*site)!= id2FanoutIDs.end()){
      set<int>* fanoutIDs = id2FanoutIDs[(*site)];
      set<int>::iterator site3 = fanoutIDs->begin();
      for(; site3 != fanoutIDs->end(); ++site3){
        if(id2Group[(*site3)] == current)
          continue;
        int groupSize = id2Group[(*site3)]->groupSize();
        if(smallest == NULL || groupSize < smallest->groupSize())
          smallest = id2Group[(*site3)];
      }
    } // check fanout 
  } // done of sweep
  if(smallest){
    smallest->addMembers(currentLUTs);
    site = currentLUTs.begin();
    for(; site!= currentLUTs.end(); ++site)
      id2Group[*site] = smallest;

  } // if fail ,just silently delete
/*  else{
    site = currentLUTs.begin();
    for(; site!= currentLUTs.end(); ++site)
      cerr<<(*site)<<",";
    cerr<<endl;
  }*/
  return smallest;
}
void meowCNN::writeGroups(vector<EVGroup*>& groups, vector<dEV* >& id2dEV, ofstream& output, int mode){

  if(groups.size() != _lutGroupNum){
    cerr<<"ERROR: mismatch group number\n";
    return;
  }
  for(int i = 0; i < groups.size(); ++i){
    map<string, dEVBag*> key2Bags;
    vector<dEVBag*> possibleBags;
    set<int>& LUTs = groups[i]->getLUTs();
    set<int>::iterator site = LUTs.begin();
    for(; site!= LUTs.end(); ++site){
      string key;
      if(mode%2 == 1) // single
        key = id2dEV[(*site)]->getSingleKey();
      else // double
        key = id2dEV[(*site)]->getDoubleKey();
      if(key2Bags.find(key) == key2Bags.end()){
        dEVBag* newBag;
        if(mode%2 == 1) // single
          newBag = new dEVBag(id2dEV[(*site)]->getSingleCount(), (*site));
        else // double
          newBag = new dEVBag(id2dEV[(*site)]->getDoubleCount(), (*site));

        key2Bags[key] = newBag;
        possibleBags.push_back(newBag);
      }
      else
        key2Bags[key]->addCount();
    }
    sort(possibleBags.begin(), possibleBags.end(), sortDouble);
    if(possibleBags.size() >=3){
      //if(possibleBags[0]->getCount() > 1)
      id2dEV[possibleBags[0]->getLut()]->outputBag(output, mode);
      id2dEV[possibleBags[1]->getLut()]->outputBag(output, mode);
      id2dEV[possibleBags[2]->getLut()]->outputBag(output, mode);

    }
    else if(possibleBags.size() == 2){
      id2dEV[possibleBags[0]->getLut()]->outputBag(output, mode);
      id2dEV[possibleBags[0]->getLut()]->outputBag(output, mode);
      id2dEV[possibleBags[1]->getLut()]->outputBag(output, mode);
    }
    else if(possibleBags.size() == 1){
      id2dEV[possibleBags[0]->getLut()]->outputBag(output, mode);
      id2dEV[possibleBags[0]->getLut()]->outputBag(output, mode);
      id2dEV[possibleBags[0]->getLut()]->outputBag(output, mode);
    }
    else
      cerr<<"Zero bag?!"<<endl;
    for(int k = 0; k < possibleBags.size(); ++k)
      delete(possibleBags[k]); 


  } 
}
void meowCNN::evenlyGrouping(int lutNum, vector<EVGroup* >& groups){
  int groupSize = lutNum/_lutGroupNum;
  if(groupSize < 1){
    cerr<<"WARN: number of LUTs is too small.\n";
    return;
  }
//  vector<EVGroup* > groups;
  int remain = lutNum%_lutGroupNum;
  int idx = 0;
  for(int i = 0; i < _lutGroupNum; ++i){
    // inside each group perform pooling
    set<int> LUTs;
    int upper = idx+groupSize;
    if(i < remain )
      upper += 1;
    for(; idx < upper; ++idx)
      LUTs.insert(idx);
   
    EVGroup* newGroup = new EVGroup(LUTs);
    groups.push_back(newGroup); 
  } 
}


void meowCNN::buildLutGraph(Gia_MapLut_Meow* pLuts,
                            int lutNum,
                            map<int, int>& out2Lut,
                            map<int, set<int>* >& id2FanoutIDs ){
  for(int i = 0; i < lutNum; ++i){
    int outputId = pLuts[i].Out;
    out2Lut[outputId] = i;
    for(int j = 0; j < pLuts[i].nFans; j++){
      int faninLut = out2Lut[pLuts[i].pFans[j]];
      if(id2FanoutIDs.find(faninLut)== id2FanoutIDs.end()){
        set<int>* newList = new set<int>;
        id2FanoutIDs[faninLut] = newList;
      }
      id2FanoutIDs[faninLut]->insert(i);
    }
  }
}
void meowCNN::writeLutTable(Gia_MapLut_Meow* pLuts,
                            ofstream& output, int lutNum,
                            map<int, int>& out2Lut,
                            map<int, set<int>* >& id2FanoutIDs,
                            int mode ){
    int i = 0;
    int counter = 0;
    for(i = 1; i < lutNum; ++i){
    //if(pLuts[i].Type == 1)
    //  continue;
    //if()
      counter++;
      writeSingleTruth(pLuts, output, i, mode);
      int j = 0;
      for(; j < pLuts[i].nFans; j++){
        int faninLut = out2Lut[pLuts[i].pFans[j]];
        writeSingleTruth(pLuts, output, faninLut, mode);
      }
      for(; j < 4; ++j)
        writeSingleTruth(pLuts, output, -1, mode);
      if(id2FanoutIDs.find(i)==id2FanoutIDs.end())
        writeSingleTruth(pLuts, output, -1, mode);
      else{
        int fanoutID = *((id2FanoutIDs[i])->begin()); // only one
        writeSingleTruth(pLuts, output, fanoutID, mode);
      }
    // finally, one fanouti
      output<<endl;
    }
    for(; counter < _lutNum; ++counter){
      for(int k = 0; k < 6; ++k)
        writeSingleTruth(pLuts, output, -1, mode);
      output<<endl;
    }


}
void meowCNN::writeAlan(Gia_MapLut_Meow* pLuts, int lutNum, map<int, int>& out2Lut, ofstream& output){
  int counter[196];
  for(int i = 0; i < 196; ++i)
    counter[i] = 0;
  int all = 0;
  map<int, int> mapping;
  mapping[0] = 0;
  mapping[2] = 1;
  mapping[5] = 2;
  mapping[13] =  3;
  mapping[15] = 4;
  mapping[21] = 5;
  mapping[83] = 6;
  mapping[103] = 7;
  mapping[105] = 8;
  mapping[109] = 9;
  mapping[120] = 10;
  mapping[180] = 11;
  mapping[220] = 12;
  //mapping[2] = 13;

  //set<int> exist;
  for(int idx = 0; idx < lutNum; ++idx){
    int oldID = Dar_LibReturnClass((pLuts[idx].pTruth[0]));
    int npnID = 0;
    if(mapping.find(oldID)==mapping.end()){
      npnID = 13;
      cerr<<"hey!"<<oldID<<endl;
    }
    else
      npnID = mapping[oldID];
    // exist.insert(npnID);
    /*if(npnID >= 10){
      cerr<<"ERROR!!!"<<npnID<<endl;
      
      //return;
    }*/
    for(int j = 0; j < pLuts[idx].nFans; j++){
      int faninLut = out2Lut[pLuts[idx].pFans[j]];
      int oldID2 = Dar_LibReturnClass(pLuts[faninLut].pTruth[0]);
      int npnID2 = 0;
      if(mapping.find(oldID2)==mapping.end())
        npnID2 = 13;
      else
        npnID2 = mapping[oldID2];
 
      counter[npnID*10+npnID2]++;
      all++; 
    }
  }
/*  set<int>::iterator site = exist.begin();

  for(; site!= exist.end(); ++site)
    cerr<<" "<<(*site);
  cerr<<endl;*/
  for(int i = 0; i < 196; ++i)
    output<<(double)(counter[i])/(double)(all)<<endl;
}
bool meowCNN::writeLUT(ofstream& output, int mode){
  int lutNum = 0;
  Gia_MapLut_Meow* pLuts = getMapLut( lutNum);

  map<int, int> out2Lut;
  map<int, set<int>* > id2FanoutIDs;

  buildLutGraph(pLuts, lutNum, out2Lut, id2FanoutIDs);
  
  if(mode == 5){ // &if -K 3
    writeAlan(pLuts, lutNum, out2Lut, output);
  }
  else{
      // step 1 assgin EV
    vector<dEV* > id2dEV;
    assignId2EV(pLuts, id2dEV, lutNum, out2Lut, id2FanoutIDs);
    vector<EVGroup* > groups;
    if(mode == 1 || mode == 2) // current order
      evenlyGrouping(lutNum, groups);
    else
      BFSGrouping(pLuts, lutNum, out2Lut, id2FanoutIDs, groups);
 
    writeGroups(groups, id2dEV, output, mode); // evenly distributed
      //or non
    for(int i = 0; i < groups.size(); ++i)
      delete groups[i];
  
    for(int i = 0; i < id2dEV.size(); ++i)
      delete id2dEV[i];

  }
    
 
  map<int, set<int>* >::iterator mite = id2FanoutIDs.begin();
  for(; mite!= id2FanoutIDs.end(); ++mite)
    delete mite->second; 

   
  ABC_FREE( pLuts );
  return true;
}
void meowCNN::getOneWindow(Gia_MapLut_Meow* pLuts, int targetLut,
                           int targetSize, map<int, int>& out2Lut,
                           map<int, set<int>* >& id2FanoutIDs,
                           set<int>* members){
  set<int> explored;
  set<int> newMember;

  members->insert(targetLut);
  newMember.insert(targetLut);
    //cerr<<"sub: "<<i<<endl; 
    // flow: output + input
  while(members->size() < targetSize ){
    if(newMember.size() == 0)
      break;
    set<int> nextNew;
    set<int>::iterator site = newMember.begin();
    for(; site!= newMember.end(); ++site){
      if(explored.find(*site)!= explored.end())
        continue;
    //  if(members->size() > targetSize*2)
    //    break; // too big
        // get outputs 
      if(id2FanoutIDs.find(*site)!= id2FanoutIDs.end()){
        set<int>* thisFanouts = id2FanoutIDs[*site];
        members->insert(thisFanouts->begin(), thisFanouts->end());
        nextNew.insert(thisFanouts->begin(), thisFanouts->end());
      }
      for(int j = 0; j < pLuts[(*site)].nFans; j++ ){
        int faninLut = out2Lut[pLuts[(*site)].pFans[j]];
        members->insert(faninLut);
        nextNew.insert(faninLut);
      }
      explored.insert(*site);
    }
    newMember.swap(nextNew);
  }

}
void meowCNN::getSubCircuits3(int lutNum,
                              vector<vector<int>* >& subCircuits,
                              int num){
  int groupSize = lutNum/num*2;
 // int begin = 1;
  for(int i = 0; i < num; ++i){
    int begin = (i*lutNum/num)+1;  
    int upper = begin+groupSize;
    if(upper > lutNum)
      upper = lutNum;
    vector<int>* newGroup = new vector<int>;
    for(; begin < upper; ++begin)
      newGroup->push_back(begin);

    subCircuits.push_back(newGroup); 
  }

}
void meowCNN::getSubCircuits2(Gia_MapLut_Meow* pLuts,
                        int lutNum, map<int, int>& out2Lut,
                        map<int, set<int>* >& id2FanoutIDs,
                        vector<vector<int>* >& subCircuits, int num){
  // num max number of groups
  set<int> coveredLUT;
  vector<set<int>* > initialGroups;
  int jump = lutNum/num;
  for(int i = 1; i < lutNum; i+=jump){
    set<int>* members = new set<int>;
    set<int>* members2 = new set<int>;
    if(coveredLUT.find(i)!=coveredLUT.end())
      continue; // jump
    int size = (_lutGroupNum*10 > lutNum/num*5)? _lutGroupNum*10: lutNum/num*6;
    getOneWindow(pLuts, i, size, out2Lut,
                 id2FanoutIDs, members);

    getOneWindow(pLuts, i, size/2, out2Lut, id2FanoutIDs, members2);
    if(members->size() < _lutGroupNum*2){
      delete members;
      continue;
    }
    if(members2->size() < _lutGroupNum*2){
      delete members2;
      continue;
    }
    coveredLUT.insert(members->begin(), members->end());
    initialGroups.push_back(members);
    initialGroups.push_back(members2);
 /*   vector<int>* newGroup = new vector<int>;
    set<int>::iterator site3 = members.begin();
    for(; site3!= members.end(); ++site3)
      newGroup->push_back((*site3));
    subCircuits.push_back(newGroup);*/
  }
/*  if(initialGroups.size() > num){
    cerr<<"initial Groups: "<<initialGroups.size()<<endl; 
    int remain = initialGroups.size()%num;
    int idx = 0;
    int groupSize = initialGroups.size()/num;
    for(int k = 0; k < num; ++k){
      set<int> unionSet;
      int upper = idx+groupSize;
      if(k < remain)
        upper+=1;
      for(; idx < upper; idx++){
        unionSet.insert(initialGroups[idx]->begin(),
                        initialGroups[idx]->end());
        delete initialGroups[idx];
      }
      vector<int>* newGroup = new vector<int>;
      set<int>::iterator site3 = unionSet.begin();
      for(; site3!= unionSet.end(); ++site3)
        newGroup->push_back((*site3));
      subCircuits.push_back(newGroup);
    }
 
  }
  else{*/
    for(int i = 0; i < initialGroups.size(); ++i){
      set<int>* currentGroup = initialGroups[i];
      vector<int>* newGroup = new vector<int>;
      set<int>::iterator site3 = currentGroup->begin();
      for(; site3!= currentGroup->end(); ++site3)
        newGroup->push_back((*site3));
      subCircuits.push_back(newGroup);
      delete currentGroup;
    }
 // }
} 
void meowCNN::getSubCircuits(Gia_MapLut_Meow* pLuts,
                        int lutNum, map<int, int>& out2Lut,
                        map<int, set<int>* >& id2FanoutIDs,
                        vector<vector<int>* >& subCircuits){
  set<string> usedKey;
  for(int i = 1; i < lutNum; i+=3){
    //int size = 1;
    //while(size < 2){
    set<int>* members = new set<int>;
    getOneWindow(pLuts, i, 8*_lutGroupNum, out2Lut,
                 id2FanoutIDs, members);
     // done with one group!
     // size+=1;
    if(members->size() < _lutGroupNum*2){
      delete members;
      continue; 
    }
    ostringstream convert;
    set<int>::iterator site2 = members->begin();
    for(; site2 != members->end(); ++site2)
        convert<<(*site2)<<"&";
      
    string key = convert.str();
    if(usedKey.find(key) == usedKey.end()){
      usedKey.insert(key);
      vector<int>* newGroup = new vector<int>;
      set<int>::iterator site3 = members->begin();
      for(; site3!= members->end(); ++site3)
        newGroup->push_back((*site3));
      subCircuits.push_back(newGroup);
    }
    delete members; 
  }
}

bool meowCNN:: writeCNNPartition(char* pFolderSpec, int mode, int num){
  // file name : ostringstream convert;
  //  convert<<pFolderSpec<<"_"<<iter<<".v";
  int lutNum = 0;
  Gia_MapLut_Meow* pLuts = getMapLut( lutNum);
  if(lutNum/_lutGroupNum == 0)
    return false;
  map<int, int> out2Lut;
  map<int, set<int>* > id2FanoutIDs;

  ostringstream graphName;
  graphName<<pFolderSpec<<"_graph"<<".g";
  string graphStr = graphName.str();
  ofstream outputGraph(graphStr.c_str());
  // record graph
 
  buildLutGraph(pLuts, lutNum, out2Lut, id2FanoutIDs);
  for(int k = 0; k < lutNum; ++k){
    outputGraph<<k<<" ";
    for(int l = 0; l < pLuts[k].nFans; l++){
      outputGraph<<out2Lut[pLuts[k].pFans[l]]<<" ";
    }
    outputGraph<<endl;
  }
  outputGraph.close();

  vector<dEV* > id2dEV;
  assignId2EV(pLuts, id2dEV, lutNum, out2Lut, id2FanoutIDs);
  //set<string> existGroups;
  vector<vector<int>* > subCircuits;
  if(num < 0)// locate
    getSubCircuits(pLuts, lutNum, out2Lut, id2FanoutIDs, subCircuits);
  else{
    getSubCircuits2(pLuts, lutNum, out2Lut, id2FanoutIDs,
                    subCircuits, num);
  }
//  vector<EVGroup* > groups;
  //cerr<<"Start to write!"<<subCircuits.size()<<endl;
  for(int i = 0; i < subCircuits.size(); ++i){
    // generate groups
    ostringstream dataName;
    dataName<<pFolderSpec<<"_"<<i<<".data";
    string dataStr = dataName.str();
    ofstream outputData(dataStr.c_str());
    ostringstream lutName;
    lutName<<pFolderSpec<<"_"<<i<<".lut";
    string lutStr = lutName.str();
    ofstream outputLut(lutStr.c_str());

    vector<EVGroup* > groups;
    int groupSize = (subCircuits[i]->size())/_lutGroupNum;
    int remain = (subCircuits[i]->size())%_lutGroupNum;
    int idx = 0;
    for(int j = 0; j < _lutGroupNum; ++j){
      set<int> LUTs;
      int upper = idx+groupSize;
      if(j < remain)
        upper+=1;
      for(; idx < upper; ++idx){
        LUTs.insert((*(subCircuits[i]))[idx]);
        outputLut<<(*(subCircuits[i]))[idx]<<" ";
      }
      EVGroup* newGroup = new EVGroup(LUTs);
      groups.push_back(newGroup);
    } 
    writeGroups(groups, id2dEV, outputData, mode); // ideally we use mode 7 onlyi
    outputLut.close();
    outputData.close();
    for(int k = 0; k < groups.size(); ++k)
      delete groups[k];
    delete subCircuits[i];
  }
  return true;
}
bool meowCNN:: writeCNNData( char* pFileSpec , int mode){
  ofstream output(pFileSpec);
  return writeLUT(output, mode);
}
ABC_NAMESPACE_IMPL_END
