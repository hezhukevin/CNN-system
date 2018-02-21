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
#include "ext/meow/meowBound.h"
//#include "ext/meow/meowBlock.h"
#include<iostream>
#include<fstream>
#include <algorithm>
#include <cmath>  
using namespace std;
ABC_NAMESPACE_IMPL_START
void meowUsageBound(){
  Abc_Print( -2, "usage: meowBound [-bwhJ] \n" );
  Abc_Print( -2, "\t compute transparent logic of the current Gia. \n");
  Abc_Print( -2, "\t -b: toggle report the target boundary of transparent blocks.\n ");
  Abc_Print( -2, "\t -w: toggle to print Proved words\n");
  Abc_Print( -2, "\t -r: toggle to print width and depths\n");
  Abc_Print( -2, "\t -h    : print the command usage\n");
  Abc_Print( -2, "\t -J <filename>   : write out words and boundaries in Json into <filename>\n");

}
meowBound::meowBound(Gia_Man_t* cir){
  _cir = cir;
  //int objNum = Gia_ManObjNum(_cir);
  Gia_ManStaticFanoutStart(_cir);
  //
  _counter = 0;
  int i;
  Gia_Obj_t* pObj; 
  Gia_ManForEachPo(_cir, pObj, i){
    _poIDs.insert(Gia_ObjFaninId0(pObj, Gia_ObjId(_cir, pObj)));
  }

 // _gate2Word = new wordNode*[objNum];
 // _gate2Width = new int[objNum];
 /* for(int i = 0; i < objNum; ++i){
    _gate2Word[i] = NULL;
    _gate2Width[i] = 0;
  }*/
//  addSupportTable();
}
meowBound::~meowBound(){
  Gia_ManStaticFanoutStop(_cir);
 // delete[] _gate2Word;
 // delete[] _gate2Width;
/*  delete[] _target2Block;
  delete[] _support2Block;
  set<meowBlock*>::iterator site = _foundBlocks.begin();
  for(; site != _foundBlocks.end(); ++site)
    delete (*site);*/
  for(int i = 0; i < _foundWords.size(); ++i)
    delete _foundWords[i];

  map<int, set<int>* >::iterator mite3 = _gate2Supports.begin();
  for(; mite3 != _gate2Supports.end(); ++mite3)
    delete (mite3->second);

  map<int, vector<int>* >::iterator mite2 = _control2Fanouts.begin();
  for(; mite2 != _control2Fanouts.end(); ++mite2)
    delete (mite2->second);
//  map<int, set<int>* >::iterator mite = _gate2Support.begin(); 
//  for(; mite != _gate2Support.end(); ++mite)
//    delete (mite->second);
//  mite = _gate2Control.begin();
//  for(; mite != _gate2Control.end(); ++mite)
//    delete (mite->second);

  /*set<set<int>* >::iterator site = _pureWords.begin();
  for(; site != _pureWords.end(); ++site){
    delete (*site);
  }*/ 
  map<int, set<wordNode*>* >::iterator mite = _gate2WordList.begin();
  for(; mite != _gate2WordList.end(); ++mite)
    delete (mite->second);
 
  mite = _in2WordList.begin();
  for(; mite!= _in2WordList.end(); ++mite)
    delete (mite->second);
}
void meowBound::reportEquivalence(Gia_Man_t* cir){ // phase0
  cerr<<"Hello Bound!"<<endl;
  Dch_Pars_t Pars, * pPars = &Pars;
  Dch_ManSetDefaultParams( pPars );

  Aig_Man_t * pAig;
  pAig = Gia_ManToAigSimple( cir );
  Dch_ComputeEquivalences( pAig, (Dch_Pars_t *)pPars );
  Gia_ManReprFromAigRepr( pAig, cir );
  Aig_ManStop( pAig );
  int i;
  
  Gia_Obj_t* pObj;
  Gia_ManForEachObj1(cir, pObj, i){
    Gia_Obj_t* representObj;  
    int Id = Gia_ObjId(cir, pObj);
    cerr<<"ID = "<<Id<<endl;
    representObj = Gia_ObjReprObj(cir, Id );
    if(representObj!= NULL){
      if(representObj != Gia_Regular(representObj)){
        representObj = Gia_Regular(representObj);
        cerr<<"Negate!";
      } 
      int reprId = Gia_ObjId(cir, representObj);
      cerr<<"ID = "<<reprId<<endl;
    }
  }
}
int meowBound::addAnd(int Lit0, int Lit1){

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
void meowBound::updateHashTable3(vector<int>& gateIDs, vector<bool>& phases, vector<vector<int> >& eqList){
  vector<vector<int> > tempEqList;
  set<int> deletePos;
  map<int, int> gate2prev;
  map<int, int> tail2Pos;
  map<int, int> new2oldID; // ? 
 
  Gia_Obj_t * pObj;
  int i;
  Gia_ManFillValue( _cir );
  Gia_ManConst0(_cir)->Value = 0;
  // step 1 assign
  for(int k = 0; k < gateIDs.size(); ++k){ // assign control
    pObj = Gia_ManObj(_cir, gateIDs[k]);
    if(phases[k]) // True->1
      pObj->Value = 1;
    else
      pObj->Value = 0;
  }
  _currentID = 1;
  set<int> fanouts;
   // step 2 work on the fanouts and sides
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
  int sideBound = _currentID; 
  set<int>::iterator site = fanouts.begin();
  set<int> currentFront;
  // step3, handle fanouts
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
          //cerr<<(pObj->Value>>1)<<" prev of "<<Gia_ObjId(_cir, pFanout)<<": "<< oldID<<endl;
        }
      }
    } // successfully move forward
  } // for each fanout
  //step4: deeper
  while(currentFront.size() != 0){
    set<int> nextFront;
    site = currentFront.begin();
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
           /* cerr<<oldID<<"from "<< prevG<<endl;
            cerr<<mapID<<" vs "<< ((Gia_ManObj(_cir, prevG)->Value)) <<endl;
            cerr<<"what? Wrong3"<<endl;*/
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
            //cerr<<"prev of"<< Gia_ObjId(_cir, pFanout)<<": "<< oldID<<endl;

          }
        }
      }

    } 
    currentFront.swap(nextFront); 
  }
  // final step
  for(int i = 0; i < tempEqList.size(); ++i){
    if(deletePos.find(i) == deletePos.end()){
      eqList.push_back(tempEqList[i]);
    }
  }
}
void meowBound::updateHashTable2(vector<int>& gateIDs, vector<bool>& phases, map<int, vector<int> >& value2List){ // only consider fanouts
  // update _currentID
  Gia_Obj_t * pObj;
  int i;
  map<int, int> new2oldID; 
  Gia_ManFillValue( _cir );
  Gia_ManConst0(_cir)->Value = 0;
  // step 1 controls
  for(int k = 0; k < gateIDs.size(); ++k){ // assign control
    pObj = Gia_ManObj(_cir, gateIDs[k]);
    if(phases[k]) // True->1
      pObj->Value = 1;
    else
      pObj->Value = 0;
  }
  _currentID = 1;
  set<int> currentFront;
  // step 2 work on the fanouts and sides
  for(int k = 0; k < gateIDs.size(); ++k){ // for all controls
    vector<int>* fanoutList = _control2Fanouts[gateIDs[k]];
    currentFront.insert(fanoutList->begin(), fanoutList->end());

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
      // set up side fanin first  
    }
  }
  int sideBound = _currentID;
  // step 3: work on fanouts
  while(currentFront.size() != 0){
    set<int> nextFront;
    set<int>::iterator site = currentFront.begin();
    for(; site!= currentFront.end(); ++site){
      pObj = Gia_ManObj(_cir, (*site));
      if(~pObj->Value){ // not empty
        if((pObj->Value)>>1 >= sideBound)
          continue;
      }
      if(Gia_ObjFanin0(pObj)->Value == ~0 
      || Gia_ObjFanin1(pObj)->Value == ~0){
        continue;// unknown side
      }
      int oldCurrent = _currentID;
      pObj->Value = addAnd(Gia_ObjFanin0Copy(pObj),
                           Gia_ObjFanin1Copy(pObj) );
      if(oldCurrent < _currentID){ // new variable give up!
        new2oldID[(_currentID-1)] = Gia_ObjId(_cir,pObj);
        int x;
        Gia_Obj_t* pFanout;
        Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, x){
          if(Gia_ObjIsPo(_cir, pFanout))
            continue;
          nextFront.insert(Gia_ObjId(_cir, pFanout));
        }
      } 
      else{ //transparent!
        int oldID = Gia_ObjId(_cir, pObj);
        int mapID = (pObj->Value) >> 1;
        if(Abc_LitIsCompl(pObj->Value))
          oldID = -1*oldID;
        if(mapID != 0){
          if(value2List.find(mapID)!= value2List.end()){
            value2List[mapID].push_back(oldID);
            //if(gateIDs[0] == 2216)
            //  cerr<<mapID<<": "<<oldID<<endl;
          }
          else{
            vector<int> newList;
            //if(gateIDs[0] == 2216){
            //  cerr<<mapID<<": "<<oldID<<", "<<new2oldID[mapID]<<endl;
           // }
            newList.push_back(new2oldID[mapID]);
            newList.push_back(oldID);
            value2List[mapID] = newList;
          }
        }
        // add fanoutsi into nextFront!
        int x;
        Gia_Obj_t* pFanout;
        Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, x){
          if(Gia_ObjIsPo(_cir, pFanout))
            continue;
          nextFront.insert(Gia_ObjId(_cir, pFanout));
        }
      }
    }
    currentFront.swap(nextFront); 
  }
} 
void meowBound::updateHashTable(vector<int>& gateIDs, vector<bool>& phases, map<int, vector<int> >& value2List){
  // update _currentID
  Gia_Obj_t * pObj;
  int i;

  Gia_ManFillValue( _cir );
  Gia_ManConst0(_cir)->Value = 0;
  int min = -1;
  int* singleValue = new int[Gia_ManObjNum(_cir)];
  for(int k = 0; k <  Gia_ManObjNum(_cir); ++k )
    singleValue[k] = 0;

  for(int k = 0; k < gateIDs.size(); ++k){ // assign const
    pObj = Gia_ManObj(_cir, gateIDs[k]);
    if(min == -1 || gateIDs[k] < min)
      min = gateIDs[k]; 
    if(phases[k]) // True->1
      pObj->Value = 1;
    else
      pObj->Value = 0;
  }
  _currentID = 1;
  Gia_ManForEachPi(_cir, pObj, i){
    if(~pObj->Value) // not empty
      continue;

    singleValue[_currentID] = Gia_ObjId(_cir, pObj);

    pObj->Value = _currentID << 1;
    _currentID++;
  }
  Gia_ManForEachAnd( _cir, pObj, i ){
    if(~pObj->Value) // not empty
      continue;
    if(i < min){// should not in the fan in
      singleValue[_currentID] = Gia_ObjId(_cir,pObj);
      pObj->Value = _currentID<<1; // take them as constant
      _currentID++;
      continue;
    } 
    int oldCurrent = _currentID;
    pObj->Value = addAnd(Gia_ObjFanin0Copy(pObj),
                         Gia_ObjFanin1Copy(pObj) );
    if(oldCurrent < _currentID){
      singleValue[(_currentID-1)] = Gia_ObjId(_cir,pObj);
    }
    else{ // Eq candidate!
      int oldID = Gia_ObjId(_cir, pObj);
      int mapID = (pObj->Value) >> 1;
      if(Abc_LitIsCompl(pObj->Value))
        oldID = -1*oldID;
      if(mapID != 0){
        if(value2List.find(mapID)!= value2List.end()){
          value2List[mapID].push_back(oldID);
         // if(gateIDs[0] == 2216)
         //   cerr<<mapID<<": "<<oldID<<endl;
        }
        else{
          vector<int> newList;
         // if(gateIDs[0] == 2216){
         //     cerr<<mapID<<": "<<oldID<<", "<<singleValue[mapID]<<endl;
         //   }

          newList.push_back(singleValue[mapID]);
          newList.push_back(oldID);
          value2List[mapID] = newList;
        }
      }
    }
  } // Step 2: finish copy
  delete[] singleValue;
}
void meowBound::findEquivalence(vector<int>& gateIDs, vector<bool>& phases, vector<vector<int> >& eqList){
  // gateIDs: control, phases: assignment
  //new: take eqList
  updateHashTable3(gateIDs, phases, eqList);
  // old: take value2List
/*  map<int, vector<int> > value2List;
  updateHashTable(gateIDs, phases, value2List);
  
  map<int, vector<int> >::iterator mite = value2List.begin();
  for(; mite!= value2List.end(); ++mite)
    eqList.push_back(mite->second);*/
}
void meowBound::analyzeWords(vector<int>& gateIDs,
                             vector<bool>& phases, 
                             vector<vector<int> >& eqList){
  // step 4: getLevels
  //int level = 0;
 // int count = 0;
 // int weird = 1;
 // vector<int> pos2ListPos;
/*  if(gateIDs[0] == 120){
    set<int> collects;
    for(int i = 0; i < eqList.size(); ++i){
        for(int j = 0; j < eqList[i].size(); ++j)
          collects.insert(eqList[i][j]);
        
    }
    set<int>::iterator site = collects.begin();
    for(; site!= collects.end(); ++site)
      cerr<<(*site)<<endl;
    cerr<<"Done"<<endl;
  }*/

  vector<int> inIDs;
  vector<int> outIDs;
  vector<int> levels;
  vector< vector<int> > eqList2;
 // set<int> transBits;
  for(int i = 0; i < eqList.size(); ++i){
    //pos2Value.push_back((mite->first));
    bool getSide = false;
    bool getSupp = true;
    int weird = 1;
    int targetID = abs((eqList[i][1])); // ?
      
    Gia_Obj_t* target = Gia_ManObj(_cir, targetID);
    int faninID0 = Gia_ObjFaninId0(target, targetID); 
    int faninID1 = Gia_ObjFaninId1(target, targetID);
    int thisOut = abs(eqList[i].back());
    set<int>* suppSet = _gate2Supports[thisOut];
    for(int m = 0; m < gateIDs.size(); ++m){
      if(faninID0 == gateIDs[m] || faninID1 == gateIDs[m]){
        getSide = true;
      }
      if(gateIDs.size() > 1){
        if(suppSet->find(gateIDs[m]) == suppSet->end()){
          getSupp = false;
          break;
        }
      }
    } // TODO
    if(!getSide || !getSupp){
      weird = -1;
    //  continue;
   //   cerr<<"weird?"<<endl<<endl;;
    }
    inIDs.push_back(eqList[i].front());
    outIDs.push_back(eqList[i].back());
    //eqList2.push_back(eqList[i]);
    int thisLevel = eqList[i].size()-1; // could be wrong
    levels.push_back(thisLevel*weird); // we need this!!!!
  }
  vector<int> transPos;
  vector<int> provedBits;
  addNewWord(gateIDs, phases, inIDs, outIDs, levels,
             transPos, provedBits, eqList);
  //cerr<<"finish!"<<endl;
  for(int i = 0; i < transPos.size(); ++i){
    vector<int>& sigList = eqList[transPos[i]];
    for(int j = 0; j < sigList.size(); ++j)
      _transBits.insert(abs(sigList[j]));
  }
   for(int i = 0; i < provedBits.size(); ++i){
    vector<int>& sigList = eqList[provedBits[i]];
    for(int j = 0; j < sigList.size(); ++j)
      _provedBits.insert(abs(sigList[j]));
  }
}
    
void meowBound::applyCofactor(vector<int>& gateIDs, vector<bool>& phases){
  _counter++;
  vector<vector<int> > eqList;
//  int oldSize = _transBits.size();
  findEquivalence(gateIDs, phases, eqList);
  if(eqList.size() > 3)
    analyzeWords(gateIDs, phases, eqList);
  //cerr<<"gateID: "<< gateIDs[0]<<" add _transBits Size"<<_transBits.size()-oldSize<<endl;
}
void meowBound::collectFanouts(set<int>& fanouts, vector<int>& current){
  Gia_Obj_t* pCurrent;
  Gia_Obj_t* pFanout;
  int j;
  for(int i = 0; i < current.size(); ++i){
    pCurrent = Gia_ManObj(_cir, abs(current[i]));
    Gia_ObjForEachFanoutStatic(_cir, pCurrent, pFanout, j){
      int fanoutID = Gia_ObjId(_cir, pFanout);
      if(_transBits.find(fanoutID)== _transBits.end())
        fanouts.insert(fanoutID);
    }
  }
}
void meowBound::findPossibleCombine(set<int>& fanouts, vector<int>& current, vector<wordNode*>& possibleCombine, wordNode* currentNode){
  map<wordNode*, int> hitWords;
  map<wordNode*, set<int> > side2Bits;
  set<int> currentSignals;
  currentSignals.insert(current.begin(), current.end());
  
  set<int>::iterator site = fanouts.begin();
  for(; site!= fanouts.end(); ++site){
    Gia_Obj_t* target = Gia_ManObj(_cir, (*site));
    if(Gia_ObjIsPo(_cir, target)) 
      continue; 

    int c0 = Gia_ObjFaninC0( target);
    int c1 = Gia_ObjFaninC1( target);
 //   if(c0 == 0 || c1 == 0)
 //     continue; // not OR
    // only consider "OR"
    int faninID0 = Gia_ObjFaninId0(target, (*site)); 
    int faninID1 = Gia_ObjFaninId1(target, (*site));
    if(currentSignals.find(faninID0)!= currentSignals.end()){
      if(currentSignals.find(faninID1)== currentSignals.end()){
        if(_gate2WordList.find(faninID1)!= _gate2WordList.end()){
          set<wordNode*>* list1 = _gate2WordList[faninID1];
          set<wordNode*>::iterator w = list1->begin();
          for( ; w != list1->end(); ++w){
            if(_muxWords.find((*w))!= _muxWords.end())
              continue;
            if(_middleWords.find((*w))!= _middleWords.end())
              continue;
            if((*w) == currentNode)
              continue;
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
    }
    else{ // ID0 is new
      if(_gate2WordList.find(faninID0)!= _gate2WordList.end()){
        set<wordNode*>* list0 = _gate2WordList[faninID0];
        set<wordNode*>::iterator w = list0->begin();
        for(; w != list0->end(); ++w){
          if(_muxWords.find((*w))!= _muxWords.end())
            continue;
          if(_middleWords.find((*w))!= _middleWords.end())
            continue;
          if((*w)  == currentNode)
            continue;
          if(hitWords.find((*w))!= hitWords.end()){
            hitWords[(*w)]+=1;
            side2Bits[(*w)].insert(faninID1);
          }
          else{
            hitWords[(*w)] =1;
            set<int> newList;
            newList.insert(faninID1);
            side2Bits[(*w)] = newList;

          }
        }
      } 
    }
  }
  map<wordNode*, int>::iterator mite =  hitWords.begin();
  for(; mite!= hitWords.end(); ++mite){
    if(mite->second == current.size() ){ // TODO
      if((mite->first)->getLevel() > 0){
        if(side2Bits[mite->first].size() >= 4)
          possibleCombine.push_back(mite->first);
      }
    }
  }
   // hit rate should be greater than 4
}
void meowBound::moveForward(wordNode* frontWord){
   vector<int>& outIDs = frontWord->getOutIDs();

   set<int> oneStepFanout;
   collectFanouts(oneStepFanout, outIDs);
   // step 1 collect 1-step fanouts
   vector<wordNode*> possibleCombine; // other wordNodes 
   findPossibleCombine(oneStepFanout, outIDs, possibleCombine,
                       frontWord);
   // step2 find connected words
   vector<int>& control1 = frontWord->getControlIDs();
   for(int i = 0; i < possibleCombine.size(); ++i){
     vector<int>& control2 = possibleCombine[i]->getControlIDs();
     set<int> controls;
     controls.insert(control1.begin(), control1.end());
     controls.insert(control2.begin(), control2.end());
     if(newCombine(controls))
       enumerateControl(&controls); 
     //enumerateCombine(frontWord, possibleCombine[i]);
   }   
}
bool meowBound::newCombine(set<int>& controls){
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
    //cerr<<"key: "<<token<<endl;
    return true;
  }
  else
    return false;
}
void meowBound::enumerateCombine(wordNode* node1, wordNode* node2){
  //cerr<<"combine:"<<endl;
//  node1->printNode();
//  node2->printNode();
  vector<int> gateID;
  vector<bool> phase;
  vector<int>& control1 = node1->getControlIDs();
  vector<bool> value1;
  vector<int>& control2 = node2->getControlIDs();
  vector<bool> value2;
  
  node1->getValues(value1);
  node2->getValues(value2);
  for(int i = 0; i < control1.size(); ++i){
    gateID.push_back(control1[i]);
    phase.push_back(value1[i]);
  }
  for(int i = 0; i < control2.size(); ++i){
    gateID.push_back(control2[i]);
    phase.push_back(value2[i]);
  }
  int upperBound = 1<<(control2.size()); // only modify control2
  for(int i = 0; i < upperBound; ++i){
    for(int j = 0; j < control2.size(); ++j){
      if(i&(1<<j))
        phase[j+control1.size()] = true;
      else
        phase[j+control1.size()] = false;
    }
    applyCofactor(gateID, phase);
  }
  upperBound = 1<<(control1.size()); // only modify control1
  for(int i = 0; i < control2.size(); ++i)
    phase[control1.size()+i] = value2[i];

  for(int i = 0; i < upperBound; ++i){
    for(int j = 0; j < control1.size(); ++j){
      if(i&(1<<j))
        phase[j] = true;
      else
        phase[j] = false;
    }
    applyCofactor(gateID, phase);
  }

}
void meowBound::proceedBlock2(){
  for(int i = 0; i < _foundWords.size(); ++i){ 
    // notice that the size will be modified... on the fly
   // if(_foundWords[i]->getLevel() < 0) // weird guy..
   //   continue;
    if(_muxWords.find(_foundWords[i])!= _muxWords.end())
      continue;
    if(_middleWords.find(_foundWords[i])!= _middleWords.end())
      continue; // proved all bits are in the middle
    if(isMiddleWord(_foundWords[i])){
      _middleWords.insert(_foundWords[i]);
      continue;
    } 
    moveForward(_foundWords[i]);
  }
}
void meowBound::collectLevelRecur(wordNode* current, 
                                  map<int, int>& gate2Level, set<wordNode*>& visitedWords){
  if(visitedWords.find(current)!= visitedWords.end())
    return;
  if(current->getLevel() <= 1)
    return;
  visitedWords.insert(current);
  vector<int>& inIDs = current->getInIDs();
  vector<int>& outIDs = current->getOutIDs();
  vector<int>& levels = current->getLevels();
  for(int i = 0; i < inIDs.size(); ++i){
    if(_gate2WordList.find(abs(inIDs[i])) == _gate2WordList.end()){
      gate2Level[abs(inIDs[i])] = 0;
      int newLevel = gate2Level[abs(inIDs[i])]+levels[i];
      if(gate2Level.find(abs(outIDs[i])) == gate2Level.end())
        gate2Level[abs(outIDs[i])] = newLevel;
      else if(gate2Level[abs(outIDs[i])] < newLevel)
        gate2Level[abs(outIDs[i])] = newLevel;
    //  cerr<<"newLevel: "<<outIDs[i]<<", "<<newLevel<<endl;
      continue;
    }
    set<wordNode*>* faninList = _gate2WordList[abs(inIDs[i])];
    set<wordNode*>::iterator j = faninList->begin();
    for(; j != faninList->end(); ++j){
      collectLevelRecur((*j), gate2Level, visitedWords);
    }
    int newLevel = gate2Level[abs(inIDs[i])]+levels[i];
    if(gate2Level.find(abs(outIDs[i]))== gate2Level.end())
      gate2Level[abs(outIDs[i])] = newLevel;
    else if(gate2Level[abs(outIDs[i])] < newLevel)
      gate2Level[abs(outIDs[i])] = newLevel;
  //  cerr<<"newLevel: "<<outIDs[i]<<", "<<newLevel<<endl;

  }
}
void meowBound::collectLevel(){
  // find words on Target Boundary Level 
  map<int, int> gate2Level;
  set<wordNode*> visitedWords;
  for(int i = 0; i < _foundWords.size(); ++i){
    if(visitedWords.find(_foundWords[i])!= visitedWords.end())
      continue;
    if(_foundWords[i]->getLevel() <= 1)
      continue;
    collectLevelRecur(_foundWords[i], gate2Level, visitedWords);
    //visitedWords.insert(_foundWords[i]); 
  }
  int maxDepth = 0;
  int minDepth = -1;
  for(int i = 0; i < _foundWords.size(); ++i){
    if(_foundWords[i]->getLevel() <= 1)
      continue;
    if(_middleWords.find(_foundWords[i]) != _middleWords.end())
      continue;

    if(isMiddleWord(_foundWords[i])){
      _middleWords.insert(_foundWords[i]);
      continue;
    }

       vector<int>& outIDs = _foundWords[i]->getOutIDs();
    for(int j = 0; j < outIDs.size(); ++j){
      if(gate2Level[abs(outIDs[j])]> maxDepth)
        maxDepth = gate2Level[abs(outIDs[j])];
      if(gate2Level[abs(outIDs[j])]< minDepth || minDepth == -1)
        minDepth = gate2Level[abs(outIDs[j])];
      //if( gate2Level[abs(outIDs[j])]> 60)
      //  cerr<<"Deep Out "<<outIDs[j]<<endl;
    }
  }
  cerr<<"maxDepth: "<<maxDepth<<" minDepth: "<<minDepth<<endl;
}
void meowBound::collectLevel2Recur(int currentID, map<int, int>& gate2Level){
  if(gate2Level.find(currentID) != gate2Level.end())
    return;
  Gia_Obj_t* pObj = Gia_ManObj(_cir, currentID);
  if(Gia_ObjIsPi(_cir, pObj)){
    gate2Level[currentID] = 0;
    return;
  }
  if(_gate2WordList.find(currentID) == _gate2WordList.end()){
    gate2Level[currentID] = 0;
    return;
  }
  set<wordNode*>* nodeList = _gate2WordList[currentID];
  set<wordNode*>::iterator i = nodeList->begin();
  int maxDepth = 0;
  for(; i != nodeList->end(); ++i){
    int level;
    int inID;
    //if((*nodeList)[i]->getLevel() < 2)
    //  continue; // could we allow ?
    (*i)->getCorresIn(currentID, level, inID);
    if(level){
      collectLevel2Recur(abs(inID), gate2Level);
      if((level + gate2Level[abs(inID)])> maxDepth)
        maxDepth = level + gate2Level[abs(inID)];
    }
  }
  gate2Level[currentID] = maxDepth;
 // int id1 = Gia_ObjFaninId0(pObj, abs(inIDs[j]));
 // int id2 = Gia_ObjFaninId1(pObj, abs(inIDs[j]));

}
void meowBound::collectLevel2(){
  map<int, int> gate2Level;
  int maxDepth = 0;
  int minDepth = -1;
  for(int i = 0; i < _foundWords.size(); ++i){
    //if(_foundWords[i]->getLevel() <= 1)
    //  continue;
    if(_middleWords.find(_foundWords[i]) != _middleWords.end())
      continue;

    if(isMiddleWord(_foundWords[i])){
      _middleWords.insert(_foundWords[i]);
      continue;
    }

    vector<int>& outIDs = _foundWords[i]->getOutIDs();
    for(int j = 0; j < outIDs.size(); ++j){
      collectLevel2Recur(abs(outIDs[j]), gate2Level);
      if(gate2Level[abs(outIDs[j])] > maxDepth)
        maxDepth = gate2Level[abs(outIDs[j])];
      if(minDepth == -1 || gate2Level[abs(outIDs[j])] < minDepth)
        minDepth = gate2Level[abs(outIDs[j])];
    }
    
  }
  cerr<<"maxDepth "<<maxDepth<<", minDepth "<<minDepth<<endl; 
}
void meowBound::simpleReport(){
  cerr<<"control Num: "<<_control_bigOut.size()<<endl;
  cerr<<"applyCofactor: "<<_counter<<endl;
  cerr<<"totalWords: "<<_foundWords.size()<<endl;
  cerr<<"transBits"<<_transBits.size()<<endl;
  int minWidth = -1;
  int maxWidth = 4;
  collectLevel2();
  map<int, int> levelCounter;
  for(int i = 0; i < _foundWords.size(); ++i){
    vector<int>& inIDs = _foundWords[i]->getInIDs();
    vector<int>& outIDs = _foundWords[i]->getOutIDs() ;
    int thisLevel = _foundWords[i]->getLevel();
    if(levelCounter.find(thisLevel)!= levelCounter.end())
      levelCounter[thisLevel]++;
    else
      levelCounter[thisLevel] = 1;
    if(_foundWords[i]->getLevel() == 1){
      if(isMiddleWord(_foundWords[i])){
        for(int j = 0; j < inIDs.size(); ++j){
          _transBits.insert(abs(inIDs[j]));
          _transBits.insert(abs(outIDs[j]));
        }
      }
    }
    if(_foundWords[i]->getLevel() > 1){
      if(inIDs.size() > maxWidth) 
        maxWidth = inIDs.size();
      if(minWidth == -1 || inIDs.size() < minWidth)
        minWidth = inIDs.size();
    }
  }
  map<int, int>::iterator mite = levelCounter.begin();
  for(; mite!= levelCounter.end(); ++mite)
    cerr<<"Level: "<<mite->first<<", num = "<<mite->second<<endl; 
  cerr<<"new transBits: "<< _transBits.size()<<endl;
  cerr<<"Width "<<minWidth<<" to "<<maxWidth<<endl;
//  collectLevel();
  forwardReport();
}
void meowBound::forwardReport(){
  int counter = 0;
  set<int> forwardList;
  int i;
  Gia_Obj_t* pObj;
  Gia_ManForEachObj1(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    // if PI and in trans -> add
    if(_transBits.find(gateID) == _transBits.end())
      continue;
    if(Gia_ObjIsPi(_cir, pObj)){
      forwardList.insert(gateID);
      continue;
    }
    if(Gia_ObjIsPo(_cir, pObj))
      continue;
    int faninID0 = Gia_ObjFaninId0(pObj, gateID);
    int faninID1 = Gia_ObjFaninId1(pObj, gateID); 
    if(forwardList.find(faninID0)!= forwardList.end() 
     ||forwardList.find(faninID1)!= forwardList.end())
      forwardList.insert(gateID);
  }
  cerr<<"Forward signals number: "<<forwardList.size()<<endl;
}
void meowBound::splitWord( wordNode* current ){
  vector<int>& outIDs = current->getOutIDs();
  vector<int>& inIDs = current->getInIDs();
  map<string, vector<int> > usedToken; 
  for(int i = 0; i < outIDs.size(); ++i){
    ostringstream Convert;
    if(_gate2WordList.find(abs(inIDs[i]))!= _gate2WordList.end()){
       
    }
    if(_in2WordList.find(abs(outIDs[i]))!= _in2WordList.end()){
      set<wordNode*>* outNodes = _in2WordList[abs(outIDs[i])];
      set<wordNode*>::iterator site = outNodes->begin();
      for(; site!= outNodes->end(); ++site){
        Convert<<size_t(*site)<<"&"; 
      }
    }
    string token = Convert.str();

  //  cerr<<token<<endl;
    if(usedToken.find(token) == usedToken.end()){
      vector<int> newVec;
      usedToken[token] = newVec;
    }
    usedToken[token].push_back(i);
  }
  if(usedToken.size() > 1 && outIDs.size() > 50){
    map<string, vector<int> >::iterator mite = usedToken.begin();
    cerr<<"Current Width: "<<outIDs.size()<<"To:";

    for(; mite!= usedToken.end();++mite)
      cerr<<(mite->second).size()<<" ";
    cerr<<endl;
  } 
}
void meowBound::splitWords(){
  // split by fanins and fanouts
  vector<int> orders;
  decideSplitOrders(orders);
  for(int i = 0; i < orders.size(); ++i)
    splitWord(_foundWords[orders[i]]);
}
void meowBound::decideSplitOrders(vector<int>& orders){
  vector< pair<int, int> > node_bigOut;

  for(int i = 0; i < _foundWords.size(); ++i){
    if(_badNodes.find(_foundWords[i]) == _badNodes.end()){
      node_bigOut.push_back(pair<int, int>(_foundWords[i]->getMaxID(),
                                           i)); 
    }
  }
  sort(node_bigOut.begin(),node_bigOut.end());
  for(int i = 0; i < node_bigOut.size(); ++i)
    orders.push_back(node_bigOut[i].second);
}
void meowBound::analyzeWords(){
  vector<int> orders;
  decideSplitOrders(orders); 
  set<wordNode*> visitedNodes; 
  for(int i = orders.size() -1; i >= 0; --i){
    // put words into "Groups"
    if(visitedNodes.find(_foundWords[orders[i]])!= visitedNodes.end())
      continue;
    vector<int> outIDs = _foundWords[orders[i]]->getOutIDs();
    int middleCount = 0;
    map<wordNode*, int> node2Count;
    for(int j = 0; j < outIDs.size(); ++j){
      if(_middleBits.find(outIDs[j])!= _middleBits.end())
        continue;
      set<wordNode*>* wordList = _gate2WordList[abs(outIDs[j])];
      set<wordNode*>::iterator w = wordList->begin();
      for(; w != wordList->end(); ++w){
        if((*w) == _foundWords[orders[i]] )
          continue;
        if(visitedNodes.find((*w))!= visitedNodes.end())
          continue;
        if(node2Count.find((*w))!= node2Count.end())
          node2Count[(*w)] += 1;
        else
          node2Count[(*w)] = 1;
      }
    }
    map<wordNode*, int>::iterator mite = node2Count.begin();
    wordGroup* newGroup = new wordGroup(_foundGroups.size());
    _foundGroups.push_back(newGroup);
    newGroup->addNode(_foundWords[orders[i]]); 
    for(; mite!= node2Count.end(); ++mite){
      if((mite->second)>= 4){
        newGroup->addNode(mite->first);
        visitedNodes.insert(mite->first);
        // case1: perfect
        // case2 has a lot of diff?
      }
    }
  }
  // make sure all output words are unique
}
void meowBound::splitGroups(){

}
void meowBound::runAll(){ // 
                 // phase 0 SAT sweeping

                 // phase 0.5 structural
  decideOrder(); // OK
  computeEachBlock(); // phase1 almost Ok,
 // cerr<<"finishPhase1 Counter: "<<_counter<<endl;
  proceedBlock2();
}

void meowBound::printWord(bool printAllWords){
  for(int i = 0; i < _foundWords.size(); ++i)
    if(_foundWords[i]->getLevel() > 1)
      _foundWords[i]->printNode();
  cerr<<"Weird Words:"<<endl;
  for(int i = 0; i < _foundWords.size(); ++i){
    if(_foundWords[i]->getLevel() <= 1 && printAllWords){
      _foundWords[i]->printNode();
    }
  }
}
bool meowBound::isMiddleWord(wordNode* node){
  if (_middleWords.find(node)!= _middleWords.end())
    return true;
  vector<int>& outIDs = node->getOutIDs();
  for(int j = 0; j < outIDs.size(); ++j){
    Gia_Obj_t* pObj = Gia_ManObj(_cir, abs(outIDs[j]));
    Gia_Obj_t* pFanout;
    int k;
     // bool getBound = false;
    Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, k){
      int fanoutID = Gia_ObjId(_cir, pFanout);
      if(_transBits.find(fanoutID) == _transBits.end()){
        return false;
      }
    }
  }
  return true;
}
void meowBound::collectSupportBoundary(vector< vector<int> >& supportWords){
  set<int> usedBound;
  set<int> visitedBound;
  //bool first = true;
  for(int i = 0; i < _foundWords.size(); ++i){
    if(_foundWords[i]->getLevel() <= 1)
      continue;
    vector<int>& inIDs = _foundWords[i]->getInIDs();
    vector<int> inBound; 
    for(int j = 0; j < inIDs.size(); ++j){
      if(visitedBound.find(abs(inIDs[j])) != visitedBound.end())
        continue;
      visitedBound.insert(abs(inIDs[j]));
      Gia_Obj_t* pObj = Gia_ManObj(_cir, abs(inIDs[j]));
      if(Gia_ObjIsPi(_cir, pObj)){
        inBound.push_back(inIDs[j]);
        continue;
      }
      int id1 = Gia_ObjFaninId0(pObj, abs(inIDs[j]));
      int id2 = Gia_ObjFaninId1(pObj, abs(inIDs[j]));
      if(_transBits.find(id1) == _transBits.end() 
       &&_transBits.find(id2) == _transBits.end())
        inBound.push_back(inIDs[j]);
    }
    if(inBound.size() != 0){
      /*if(!first)
        output<<","<<endl;
      first = false;
      output<<"    [";
      for(int j = 0; j < inBound.size(); ++j){
        if(j!=0)
          output<<", ";
        output<<inBound[j];
      }
      output<<"]";*/
      supportWords.push_back(inBound);
    }
  }
}
void meowBound::collectTargetBoundary(vector<vector<int> >& outputWords){
  set<int> usedBound;
  //bool first = true;

  for(int i = 0; i < _foundWords.size(); ++i){
    if(_foundWords[i]->getLevel() < 1)
      continue;
    if(_foundWords[i]->getLevel() == 1)
      continue;
    if(_middleWords.find(_foundWords[i])!= _middleWords.end())
      continue;
    vector<int>& outIDs = _foundWords[i]->getOutIDs();
   // bool someTrans = false;
    vector<int> outBound;
    for(int j = 0; j < outIDs.size(); ++j){//for each bit of word
      int k;
      if(usedBound.find(abs(outIDs[j]))!= usedBound.end())
        continue;
      usedBound.insert(abs(outIDs[j]));
      Gia_Obj_t* pObj = Gia_ManObj(_cir, abs(outIDs[j]));
      Gia_Obj_t* pFanout;
      
     // bool getBound = false;
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, k){
        int fanoutID = Gia_ObjId(_cir, pFanout);
        if(_transBits.find(fanoutID)== _transBits.end() ){
          outBound.push_back(outIDs[j]);
          break;
        }
      }
    }// finish for each bit
    if(outBound.size() != 0){
      outputWords.push_back(outBound);
    }
    else{
      _middleWords.insert(_foundWords[i]);
    }
 
  }
//  output<<endl; 
}  
void meowBound::drawCircuit(){
  ofstream output("transGraph.dot");
  output<<"digraph graphname{"<<endl;
  // step 1
  int i;
  Gia_Obj_t* pObj;
 // Gia_Obj_t* pFanout;
  Gia_ManForEachObj(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    output<<"g"<<gateID<<" [";
    if(Gia_ObjIsPi(_cir, pObj)||Gia_ObjIsPo(_cir, pObj) )
      output<<" shape=box, ";
    else 
      output<<" shape=diamond, ";

    if(_transBits.find(gateID)!= _transBits.end())
      output<<" color=red style=filled ]";
    else if(_goodControls.find(gateID)!= _goodControls.end())
      output<<" color=blue style=filled ]";
    else
      output<<" fillcolor=white ]";
    output<<endl;
    if(Gia_ObjIsPi(_cir, pObj)||i == 0)
      continue;
    if(Gia_ObjIsAnd(pObj)){
      int id1 = Gia_ObjFaninId0(pObj, gateID);
      int id2 = Gia_ObjFaninId1(pObj, gateID);
      int bubble1 = Gia_ObjFaninC0(pObj); 
      int bubble2 = Gia_ObjFaninC1(pObj); 
      
      output<<"g"<<id1<<" -> g"<<gateID;
      if(bubble1)
        output<<"[style=dotted]";
       output<<";"<<endl;

      output<<"g"<<id2<<" -> g"<<gateID;
      if(bubble2)
        output<<"[style=dotted]";
 
      output<<";"<<endl;
 

    }
    else{
      int id1 = Gia_ObjFaninId0(pObj, gateID);
      int bubble1 = Gia_ObjFaninC0(pObj); 

      output<<"g"<<id1<<" -> g"<<gateID;
      if(bubble1)
        output<<"[style=dotted]";
 
      output<<";"<<endl;

    }
  }
  // step 2
  
  output<<"}"<<endl;
  output.close();
}
void meowBound::addNewWord( vector<int>& gateIDs, vector<bool>& phases, vector<int>& inIDs, vector<int>& outIDs, 
 vector<int>& levels,vector<int> & transPos,
 vector<int>& provedBits, vector<vector<int> >& eqList){
 // cerr<<"add New Word!"<<endl; 
  // try to split by ...
  map<string, vector<int> > key2Pos;
  map<string, set<int> > usedLevels;
  bool gotBig = false;
  bool gotBad = false;
  for(int i = 0; i < inIDs.size(); ++i){
     // input == PI output == PO 3
     // input == PI output == internal 2
     // input == internal output == PO 1
     // input == internal output ==  internal 0
     // combine with sign of level ?
    ostringstream Convert;
    Gia_Obj_t* pInput = Gia_ManObj(_cir, abs(inIDs[i]));
  //  Gia_Obj_t* pOutput = Gia_ManObj(_cir, abs(outIDs[i]));
   // int key = 0; //levels[i] == 1? 2: levels[i];
    if(Gia_ObjIsPi(_cir, pInput))
      Convert<<"PI&";
 /*   else if(_out2WideWord.find(abs(inIDs[i]))!= _out2WideWord.end()){
        Convert<<size_t(_out2WideWord[abs(inIDs[i])])<<"&";
    }*/
    if(_poIDs.find(abs(outIDs[i]))!= _poIDs.end()) 
      Convert<<"PO";

  /* if(gateIDs[0] == 1128)
     cerr<<"key "<<key<<", "<<inIDs[i]<<", "<<outIDs[i]<<", "<<levels[i]<<endl;
    */
    if(levels[i] < 0){
      gotBad = true;
      continue;
    }
    if(levels[i] > 1)
      gotBig = true;

    string key = Convert.str();
    if(key2Pos.find(key)!= key2Pos.end()){
      key2Pos[key].push_back(i);
      usedLevels[key].insert(levels[i]);
    }
    else{
      vector<int> newList;
      set<int> newSet;
      newList.push_back(i);
      newSet.insert(levels[i]);
      key2Pos[key] = newList;
      usedLevels[key] = newSet;
    } 
  }
//  cerr<<"finish Step 1"<<endl;
  if(!gotBig && gotBad){
  //  cerr<<"Bad?"<<endl;
    return;

  }
//  if(gateIDs[0] == 1128)
//    cerr<<"finish Step 1"<<endl;

  // step 2 seperate by level
  vector<vector<int> > finalList;
  map<string, vector<int> >::iterator mite = key2Pos.begin();
  for(; mite!= key2Pos.end(); ++mite){ // regroup!
   /* if(gateIDs[0] == 1128){
      for(int l = 0; l < mite->second.size(); ++l)
         cerr<<inIDs[(mite->second)[l]]<<" ";
      cerr<<endl;
    }*/ 
    if((mite->second).size() < 4)
      continue;
    //if(levels[(mite->second)[0]] < 0)
    //  continue;
       
    if((usedLevels[mite->first].size() == 1)){
      finalList.push_back(mite->second);
      continue;
    }
   // else if(gateIDs.size() > 1) // TODO
   //   continue;
    // below will not happen, try simple one
    map<int, vector<int> > level2Pos;
    for(int l = 0; l <( mite->second).size(); ++l){
    /*  if(gateIDs[0] == 1128){
        cerr<<inIDs[(mite->second)[l]]<<" ";
      }*/
      int level = levels[(mite->second)[l]];
      if(level2Pos.find(level)!= level2Pos.end())
        level2Pos[level].push_back((mite->second)[l]);
      else{
        vector<int> newLevel;
        newLevel.push_back( (mite->second)[l]);
        level2Pos[level] = newLevel;
      }
    }
    //cerr<<endl;
    bool merge1 = false;
    bool merge2 = false;
    if(level2Pos.find(1) != level2Pos.end()
    && level2Pos.find(2) != level2Pos.end()){
      if((level2Pos[1].size() < 4) && (level2Pos[2].size() > 4)){
        vector<int> mergedList;
        for(int x = 0; x < level2Pos[1].size(); ++x)
          mergedList.push_back(level2Pos[1][x]);
        for(int x = 0; x < level2Pos[2].size(); ++x)
          mergedList.push_back(level2Pos[2][x]);
        finalList.push_back(mergedList);
        merge1 = true;
      }
      else if(level2Pos[1].size() > 3 && level2Pos[2].size() < 3){
        merge1 = true; // but give up
        vector<int> mergedList;
        for(int x = 0; x < level2Pos[1].size(); ++x)
          mergedList.push_back(level2Pos[1][x]);
        for(int x = 0; x < level2Pos[2].size(); ++x)
          mergedList.push_back(level2Pos[2][x]);
        finalList.push_back(mergedList);

      }
    } //TODO merge?
    if(level2Pos.find(2)!= level2Pos.end()
    && level2Pos.find(3)!= level2Pos.end()){
      if((level2Pos[2].size() < 3) &&(level2Pos[3].size() > 4) ){
        
        vector<int> mergedList;
        for(int x = 0; x < level2Pos[2].size(); ++x)
          mergedList.push_back(level2Pos[2][x]);
        for(int x = 0; x < level2Pos[3].size(); ++x){
          mergedList.push_back(level2Pos[3][x]);
        }
        finalList.push_back(mergedList);
        merge2 = true;

      }
    }
    map<int, vector<int> >::iterator mite2 = level2Pos.begin();
    for(;mite2 != level2Pos.end(); ++mite2){
      if(merge1 && ((mite2->first == 1)) ) // TODO
        continue;
      if(merge2 && ((mite2->first == 2)))
        continue;
      if((mite2->first == 1) && (mite2->second).size()< 6)
        continue;
      if(gateIDs.size() > 1 && mite2->first  == 1)
        continue;
      if((mite2->second).size() > 3)
        finalList.push_back(mite2->second);
    }
  }

  for(int v = 0; v < finalList.size(); ++v){
   
    vector<int> subInIDs;
    vector<int> subOutIDs;
    vector<int> subLevels;
    int subLevel = 0;
    int count = 0;
    int nonProved = false;
    //cerr<<"small word"<<endl; 
    for(int j = 0; j < (finalList[v]).size(); ++j){
      if(_provedBits.find(outIDs[finalList[v][j]]) == _provedBits.end()       &&_transBits.find(outIDs[finalList[v][j]]) == _transBits.end() ){
        nonProved = true;
      }
      subInIDs.push_back(inIDs[finalList[v][j]]);
      subOutIDs.push_back(outIDs[finalList[v][j]]);
      subLevels.push_back(levels[finalList[v][j]]);
     // if(gateIDs[0] == 1814)
     //   cerr<<inIDs[finalList[v][j]]<<" to "<<outIDs[finalList[v][j]]<<" level "<<levels[finalList[v][j]]<<endl;
     // cerr<<" "<< levels[finalList[v][j]];
      if(subLevel  == 0 || subLevel < levels[finalList[v][j]])
        subLevel = levels[finalList[v][j]];
      if( levels[finalList[v][j]] == 1)
        count++;
    }
    if(!nonProved && gateIDs.size() > 1)
      continue;
    //cerr<<endl;
    if(count > 3)
      subLevel = 1;
    if(subLevel > 1){ // TODO
      for(int j = 0; j < finalList[v].size(); ++j)
        transPos.push_back(finalList[v][j]);
    }
   // else{
    for(int j = 0; j < finalList[v].size(); ++j)
      provedBits.push_back(finalList[v][j]);
   // }
    wordNode* newWord = new wordNode(subInIDs, subOutIDs,
                                     gateIDs, phases, subLevels);
    newWord->setLevel(subLevel);
    if(subLevel > 1 && gateIDs.size() == 1)
      _muxWords.insert(newWord);

    _foundWords.push_back(newWord);
    int currentWidth= subOutIDs.size();
    for(int k = 0; k < currentWidth; ++k){
      if(_gate2WordList.find(abs(subOutIDs[k]))== _gate2WordList.end()){
        _out2WideWord[abs(subOutIDs[k])] = newWord;
        set<wordNode*>* newList = new set<wordNode*>;
        newList->insert(newWord);
        _gate2WordList[abs(subOutIDs[k])] = newList;
      }
      else{
        _gate2WordList[abs(subOutIDs[k])]->insert(newWord);
        if(_out2WideWord[abs(subOutIDs[k])]->wordSize() < currentWidth)
          _out2WideWord[abs(subOutIDs[k])] = newWord;
      }
      if(_in2WordList.find(abs(subInIDs[k]))== _in2WordList.end()){
        set<wordNode*>* newList = new set<wordNode*>;
        newList->insert(newWord);
        _in2WordList[abs(subInIDs[k])] = newList;
      }
      else
        _in2WordList[abs(subInIDs[k])]->insert(newWord);
        //_gate2Word[abs(outIDs[i])] = newWord; 
    } 
  } 

  if(transPos.size() > 0)
    _goodControls.insert(gateIDs.begin(), gateIDs.end());  

}
/*meowBlock* meowBound::addNewBlock( vector<int>& gateIDs, vector<bool>& phases, vector<int>& inIDs, vector<int>& outIDs){
  // add new words
  meowBlock* newBlock = new meowBlock; 
  _foundBlocks.insert(newBlock);
  newBlock->addWord(this, inIDs, outIDs, gateIDs, phases);
  return newBlock;
}*/
void meowBound::decideOrder(){
  int i, j;
  Gia_Obj_t* pObj;
  Gia_Obj_t* pFanout;
  Gia_ManForEachObj1(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    if(Gia_ObjFanoutNum(_cir, pObj) > 3){
           // cerr<<"gateID "<<gateID<<": ";
      int bigOne = 0;
      vector<int>* newList = new vector<int>; 
      Gia_ObjForEachFanoutStatic(_cir, pObj, pFanout, j){
        int fanoutID = Gia_ObjId(_cir, pFanout);
        if(Gia_ObjIsPo(_cir, pFanout))
          continue;
        if(_gate2Supports.find(fanoutID)== _gate2Supports.end()){
          set<int>* newSet = new set<int>;
          newSet->insert(gateID);
          _gate2Supports[fanoutID] = newSet;
        }
        else
          _gate2Supports[fanoutID]->insert(gateID);


        newList->push_back(fanoutID);
        if(fanoutID > bigOne)
          bigOne = fanoutID;
      }
      _control2Fanouts[gateID] = newList;
      //cerr<<endl;
      _control_bigOut.push_back(pair<int, int>(bigOne, gateID));
      
    }
    if(Gia_ObjIsPi(_cir, pObj) || Gia_ObjIsPo(_cir, pObj))
      continue;
    set<int>* supportSet = NULL;
    if(_gate2Supports.find(gateID) == _gate2Supports.end()){
      supportSet = new set<int>;
      _gate2Supports[gateID] = supportSet;
    }
    else
      supportSet = _gate2Supports[gateID];
    int faninID0 = Gia_ObjFaninId0(pObj, gateID);
    if(_gate2Supports.find(faninID0) != _gate2Supports.end()){
      supportSet->insert(_gate2Supports[faninID0]->begin(),
                         _gate2Supports[faninID0]->end());
    }
    int faninID1 = Gia_ObjFaninId1(pObj, gateID);
    if(_gate2Supports.find(faninID1) != _gate2Supports.end()){
      supportSet->insert(_gate2Supports[faninID1]->begin(),
                         _gate2Supports[faninID1]->end());
    }

  }
  sort(_control_bigOut.begin(), _control_bigOut.end());
}
/*set<int>* meowBound::getSupportSet(int gateID){
  return _gate2Support[gateID];
}
void meowBound::addSupportTable(){
  int i;
  Gia_Obj_t* pObj;
  set<int>* newList = new set<int>;
 // newList->insert(0);
  _gate2Support.push_back(newList);
  Gia_ManForEachPi(_cir, pObj, i){
    int gateID = Gia_ObjId(_cir, pObj);
    set<int>* newList = new set<int>;
   // newList->insert(gateID);
    _gate2Support.push_back(newList); 
  }
  Gia_ManForEachObj1(_cir, pObj, i){
    if(Gia_ObjIsPi(_cir, pObj ))
      continue;
    int gateID = Gia_ObjId(_cir, pObj);
    if(gateID != _gate2Support.size())
      cerr<<"ERROR!!!"<<endl;
    set<int>* newList = new set<int>;
    int faninID0 = Gia_ObjFaninId0p(_cir, pObj);
    set<int>* list0 = _gate2Support[faninID0];
    newList->insert(list0->begin(), list0->end());
    newList->insert(faninID0);
    if(Gia_ObjIsAnd(pObj)){
      int faninID1 = Gia_ObjFaninId1p(_cir, pObj);
      set<int>* list1 = _gate2Support[faninID1];
      newList->insert(list1->begin(), list1->end());
      newList->insert(faninID1);
    }
  //  newList->insert(gateID);
    _gate2Support.push_back(newList);
  }
}
void meowBound::updateBlock(  vector<int>& gateIDs, vector<bool>& phases, vector<int>& inIDs, vector<int>& outIDs, set<meowBlock*>& connectedBlocks){

  // TODO check dependency and then update 
  meowBlock* newBlock = addNewBlock(gateIDs, phases, inIDs, outIDs);
  set<meowBlock*>::iterator site = connectedBlocks.begin();
  for(; site!= connectedBlocks.end(); ++site){
    vector<wordNode*> words;
    (*site)->popWords(words);
    newBlock->addWords(this, words);
  }
}*/
void meowBound::computeEachBlock(){
  for(int k = 0; k < _control_bigOut.size(); ++k){
    int targetControl = _control_bigOut[k].second;// target ID
    vector<int> gateID;
    vector<bool> phase;
    gateID.push_back(targetControl);
    phase.clear(); 
    
    phase.push_back(true); 
   
    applyCofactor(gateID, phase);
    
    phase.clear(); 
    
    phase.push_back(false); 

    applyCofactor(gateID, phase);
    
  }
}
/*void meowBound::proceedBlock(){
  // now we have had several words, what should we do now?...
  //1. label supports and targets
  colorTargets();
  proceedWords();  // get more words  
  
}*/
/*void meowBound::proceedWords(){
  set<int> usedKeys;
  vector<set<int>* > usedLists; 
  map<int, set<int>* >::iterator mite = _gate2Control.begin();
  for(; mite != _gate2Control.end(); ++mite){
    if((mite->second)->size() == 1)
      continue;
    // check if existing combination 
    // note: we might have too many controls
    if(checkControlSet(usedKeys, usedLists, mite->second, mite->first)){
      enumerateControl(mite->second);
    } // else: repeated control or bad support, just skip
    // check if more than one support from the same word 
  }

}*/
void meowBound::enumerateControl(set<int>* controls){
  //cerr<<"Try control!";
  
 // if(controls->size() > 6)
 //   return;
  vector<int> gateID;
  set<int>::iterator site = controls->begin();
  for(; site != controls->end(); site++){
    //cerr<<(*site)<<" ";
    gateID.push_back(*site);
  }
  //cerr<<endl;
  vector<bool> phase;
  int upperBound = 1<<(gateID.size());
  for(int i = 0; i < upperBound; ++i){
    phase.clear();
    for(int j = 0; j < gateID.size(); ++j){
      if(i&(1<<j))
        phase.push_back(true);
      else
        phase.push_back(false);
    }
    applyCofactor(gateID, phase);
  }  
}
/*bool meowBound::checkSupportSet(int gateID){
  Gia_Obj_t* target = Gia_ManObj(_cir, gateID);
  int faninID0 = Gia_ObjFaninId0(target, gateID); 
  int faninID1 = Gia_ObjFaninId1(target, gateID);
  if(_badNodes.find(faninID0)!= _badNodes.end() 
   ||_badNodes.find(faninID1)!= _badNodes.end()){
     _badNodes.insert(gateID);
     return false;
  }
  // check if its supports are in _badNodes
  set<int>* supports = _gate2Support[gateID];
  set<int>::iterator site = supports->begin();
  set<wordNode*> touchedWords;
  for(; site!= supports->end(); ++site){
    wordNode* thisWord = _gate2Word[(*site)];
    if(touchedWords.find(thisWord)!= touchedWords.end()){
      _badNodes.insert(gateID); // different bits from the same word
      return false;
    }
    touchedWords.insert(thisWord);
  }
  return true; // TODO 
}
*/
/*bool meowBound::checkControlSet(set<int>& usedKeys, vector<set<int>* >& usedLists, set<int>* newList, int gateID){
  // TODO: how to handle the crazy case?!
  int newKey = 0;
  set<int>::iterator site = newList->begin();
  for(; site!= newList->end(); ++site){
    newKey = newKey<<1;
    newKey = newKey^(*site);
  }
  if(usedKeys.find(newKey)== usedKeys.end()){ //new!!
    if(checkSupportSet(gateID)){
      usedKeys.insert(newKey);
      usedLists.push_back(newList);
      return true;
    }
    return false;
  }
  else{
    for(int i = 0; i < usedLists.size(); ++i){
      if((*newList) == *(usedLists[i]) )
        return false;
    }
    //here, same key but different lists;
    if(checkSupportSet(gateID)){
      usedLists.push_back(newList);
      return true;
    }
    else
      return false;
  }
} */
    
/*void meowBound::colorTargets(){
  // step 1 for all "not so bad words, store their ..."
  for(int i = 0; i < _foundWords.size(); ++i){
    if(_foundWords[i]->getLevel() < 0) // bad guy
      continue;
    if(_middleWords.find(_foundWords[i])!= _middleWords.end() ) 
      continue; // middle, hide it
    // we rule out those within transparent boundary.
    vector<int> outIDs;
    vector<int> controls;
    _foundWords[i]->getOutIDs(outIDs);
    _foundWords[i]->getControlIDs(controls);
    for(int j = 0; j < outIDs.size(); ++j){
      if(_gate2Support.find(abs(outIDs[j]))!= _gate2Support.end()){
        _gate2Control[abs(outIDs[j])]->insert(controls.begin(), controls.end());
        //for repeating cases
      }
      else{ // TODO how about the crazy AND?
        set<int>* newSupportList = new set<int>;
        newSupportList->insert(abs(outIDs[j]));
         
        set<int>* newControlList = new set<int>;
        newControlList->insert(controls.begin(), controls.end());
      //  we should track both control and new supports.
        _gate2Support[abs(outIDs[j])] = newSupportList;
        _gate2Control[abs(outIDs[j])] = newControlList;
      }
      //_gate2Word[abs(outIDs[j])] = _foundWords[i]; // keep the newest
    }
  } 
  // step 2, start from all objects, if fanin is ready, keep going.
  int i;
  Gia_Obj_t* pObj;
  Gia_ManForEachObj1(_cir, pObj, i){
    if(Gia_ObjIsPi(_cir, pObj))
      continue;
    if(Gia_ObjIsPo(_cir, pObj))
      continue;
    int gateID = Gia_ObjId(_cir, pObj);
    if(_gate2Control.find(gateID) != _gate2Control.end()){
      continue; 

    }
    int faninID0 = Gia_ObjFaninId0(pObj, gateID); 
    int faninID1 = Gia_ObjFaninId1(pObj, gateID);
    if(Gia_ObjIsAnd(pObj)){
      if( _gate2Control.find(faninID0) != _gate2Control.end()
       && _gate2Control.find(faninID1) != _gate2Control.end()){
        set<int>* support0 = _gate2Support[faninID0]; 
        set<int>* support1 = _gate2Support[faninID1];
        set<int>* control0 = _gate2Control[faninID0];
        set<int>* control1 = _gate2Control[faninID1];
        set<int>* newSupportList = new set<int>;
        newSupportList->insert(support0->begin(), support0->end());
        newSupportList->insert(support1->begin(), support1->end());
         
        set<int>* newControlList = new set<int>;
        newControlList->insert(control0->begin(), control0->end());
        newControlList->insert(control1->begin(), control1->end());
         // should we track both control and support at the same time?
        _gate2Support[gateID] = newSupportList;
        _gate2Control[gateID] = newControlList;

      }
    }
    else{
      //ideally never happen
    }
  }
}*/
void meowBound::writeNetList(char* pFileSpec){

}
void meowBound::arrangeBoundaries(vector<vector<int> >& supports, vector<vector<int> >& targets){
  for(int i = 0; i < targets.size(); ++i){


  }
}
void meowBound::printBoundaries(ostream& output){
  vector< vector<int> > suppBoundaries;
  collectSupportBoundary(suppBoundaries);
  vector< vector<int> > targetBoundaries;
  collectTargetBoundary(targetBoundaries);
 // arrangeBoundaries(suppBoundaries, targetBoundaries);  
  output<<"  \"outputs\": ["<<endl;
  for(int i = 0; i < targetBoundaries.size(); ++i){
    if( i!= 0)
      output<<","<<endl;
    output<<"    [";
    for(int j = 0; j < targetBoundaries[i].size(); ++j){
      if(j!=0)
        output<<", ";
      output<<targetBoundaries[i][j];
    }
    output<<"]";
  }
  
  output<<"  ],"<<endl;

  output<<"  \"supports\": ["<<endl;
  for(int i = 0; i < suppBoundaries.size(); ++i){
    if( i!= 0)
      output<<","<<endl;
    output<<"    [";
    for(int j = 0; j < suppBoundaries[i].size(); ++j){
      if(j!=0)
        output<<", ";
      output<<suppBoundaries[i][j];
    }
    output<<"]";
  }
  output<<"  ]"<<endl;
}
void meowBound::printJson(char* pFileSpec, bool printAll){
  ofstream output(pFileSpec);
  output<<"{"<<endl;
  // Words...
  output<<"  \"words\": ["<<endl;
  bool first = true;
  for(int i = 0; i < _foundWords.size(); ++i){
    if(_foundWords[i]->getLevel() > 1){
      if(!first)
        output<<","<<endl;

      first = false;
      _foundWords[i]->printNode(output);
    } 
  }
  output<<endl<<"  ],"<<endl;
  if(printAll){
    output<<"  \"Single words\": ["<<endl;
    bool first = true;
    for(int i = 0; i < _foundWords.size(); ++i){
      if(_foundWords[i]->getLevel() == 1){
        if(!first)
          output<<","<<endl;

        first = false;
        _foundWords[i]->printNode(output);
      } 
    }
    output<<endl<<"  ],"<<endl;
  }
  
  //Boundaries..
  printBoundaries(output); 
    output<<"}"<<endl;
  output.close();    
}
ABC_NAMESPACE_IMPL_END
