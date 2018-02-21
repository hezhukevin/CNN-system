#ifndef MEOW_CNN_H
#define MEOW_CNN_H
#include<iostream>
#include<fstream>
#include <sstream>
#include<cstring>
#include<set>
#include<vector>
#include<map>
#include<queue>
#include <stdlib.h>
#include <bitset> 
#include <time.h>  
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "misc/extra/extra.h"
#include <algorithm> 
using namespace std;
#define MEOW_MAX_LUT_SIZE 6

class dEVBag{
  public:
    dEVBag(int ones, int lutID){
      _ones = ones;
      _count = 1;
      _lut = lutID;
    }
    void addCount(){
      _count+=1;
    }
    int getCount(){
      return _count;
    }
    int getLut(){
      return _lut;
    }
    int getOnes(){
      return _ones;
    }

  private:
    int _lut;
    int _count;
    int _ones;
};
static bool sortDouble(dEVBag* bagFirst, dEVBag* bagSecond ){
  int countDiff = bagFirst->getCount() - bagSecond->getCount();
  if(countDiff > 0)
    return true; 
  if(countDiff < 0 )
    return false;
  if(bagFirst->getOnes() > bagSecond->getOnes())
    return true;
  return false; 
}
class EVGroup{
  public:
    EVGroup( set<int>& initial){
      _LUTs.insert(initial.begin(), initial.end());
    }
    EVGroup(int first){
      _LUTs.insert(first);
    }
/*    ~EVGroup(){
      cerr<<"delete"<<this<<endl;

    }*/
    void split(set<EVGroup*>& runningGroups){
      set<int> new1;
      set<int> new2;
      set<int>::iterator site = _LUTs.begin();
      for(; site != _LUTs.end(); ++site){
        if(new1.size() >= _LUTs.size()/2)
          new2.insert((*site));
        else
          new1.insert((*site));
      }
      EVGroup* newG1 = new EVGroup(new1);
      EVGroup* newG2 = new EVGroup(new2);
      runningGroups.insert(newG1);
      runningGroups.insert(newG2);
    }
    int order(){
      int size = _LUTs.size();
      double ave = 0.0;
      set<int>::iterator site = _LUTs.begin();
      for(; site!= _LUTs.end(); ++site)
        ave += (double)(*site)/size;

     // cerr<<"order"<<(int)(ave)<<endl;
      return (int)(ave);
    }
    int groupSize(){
      return _LUTs.size();
    }
    void addMembers(set<int>& newLUTs){
      _LUTs.insert(newLUTs.begin(), newLUTs.end());
    }
    set<int>& getLUTs(){
      return _LUTs;
    }
   /* void getOutputMember(vector<int>& outputLUTs){
      sort(_possibleBags.begin(), _possibleBags.end(), sortDouble);
      if(_possibleBags.size() >= 3){
        outputLUTs.push_back(_possibleBags[0]->getLut());
        outputLUTs.push_back(_possibleBags[1]->getLut());
        outputLUTs.push_back(_possibleBags[2]->getLut());
      }
      else if(_possibleBags.size() == 2){
        outputLUTs.push_back(_possibleBags[0]->getLut());
        outputLUTs.push_back(_possibleBags[0]->getLut());
        outputLUTs.push_back(_possibleBags[1]->getLut());
      }
      else if(_possibleBags.size() == 1){
        outputLUTs.push_back(_possibleBags[0]->getLut());
        outputLUTs.push_back(_possibleBags[0]->getLut());
        outputLUTs.push_back(_possibleBags[0]->getLut());
      }
      else
        cerr<<"zero bags!"<<endl;
    }*/
  private:
    set<int> _LUTs;
   // vector<dEVBag*> _possibleBags;
};

class dEV{
  public:
    dEV(set<int>& fanins, set<int>& fanouts){
      _fanins = fanins;
      _fanouts = fanouts;
    }
    string getDoubleKey(){
      ostringstream convert;
      set<int>::iterator site = _fanins.begin();
      for(; site!= _fanins.end(); ++site)
        convert<<(*site)<<"&";
      convert<<"||";
      site = _fanouts.begin();
      for(; site!= _fanouts.end(); ++site)
        convert<<(*site)<<"&";
      return convert.str();
    }
    string getSingleKey(){
      set<int> total;
      total.insert(_fanins.begin(), _fanins.end());
      total.insert(_fanouts.begin(), _fanouts.end());
      ostringstream convert;
      set<int>::iterator site = total.begin();
      for(; site!= total.end(); ++site)
        convert<<(*site)<<"&";
      return convert.str();
    }
    int getSingleCount(){
      set<int> total;
      total.insert(_fanins.begin(), _fanins.end());
      total.insert(_fanouts.begin(), _fanouts.end());
      return total.size();
    }
    int getDoubleCount(){
      return _fanins.size()+_fanouts.size();
    }
  void outputSingle(ofstream& output){
    int out[222];
    for(int i = 0; i < 222; ++i)
      out[i] = 0;

    set<int>::iterator site = _fanins.begin();
    for(; site!= _fanins.end(); ++site)
      out[(*site)] = 1;

    site = _fanouts.begin();
    for(; site!= _fanouts.end(); ++site)
      out[(*site)] = 1;

    for(int i = 0; i < 222; ++i)
      output<<out[i];

    output<<endl;
  }
  void outputDouble(ofstream& output){
    int out[444];
    for(int i = 0; i < 444; ++i)
      out[i] = 0; 
    
    set<int>::iterator site = _fanins.begin();
    for(; site!= _fanins.end(); ++site)
      out[(*site)] = 1;

    site = _fanouts.begin();
    for(; site!= _fanouts.end(); ++site)
      out[(*site)+222] = 1;

    for(int i = 0; i < 444; ++i)
      output<<out[i];

    output<<endl;

  }
  void outputBag(ofstream& output, int mode){
    if(mode%2 == 1) // single
      outputSingle(output);
    else // double
      outputDouble(output);
  } 
  private:
    set<int> _fanins;
    set<int> _fanouts;
};
struct Gia_MapLut_Meow
{
    int        Type;          // node type: PI=1, PO=2, LUT=3^M
    int        Out;           // ID^M
    int        StartId;       // -1^M
    int        nFans;         // fanin count^M
    float      Delay;         // 0.0^M
    int        pFans[MEOW_MAX_LUT_SIZE];  // fanin IDs^M
    unsigned   pTruth[MEOW_MAX_LUT_SIZE<6?1:(1<<(MEOW_MAX_LUT_SIZE-5))]; // the truth table^M
};

class meowCNN{ // this class is for print bad guy
  public:
    meowCNN(Gia_Man_t* cir);
    bool writeCNNData(char* pFileSpec, int mode);
    bool writeCNNPartition(char* pFolderSpec, int mode, int num);
    void getSubCircuits(Gia_MapLut_Meow* pLuts,
                        int lutNum, map<int, int>& out2Lut,
                        map<int, set<int>* >& id2FanoutIDs,
                        vector<vector<int>* >& subCircuits);
    void getSubCircuits2(Gia_MapLut_Meow* pLuts,
                        int lutNum, map<int, int>& out2Lut,
                        map<int, set<int>* >& id2FanoutIDs,
                        vector<vector<int>* >& subCircuits,
                        int num);
    void getSubCircuits3(int lutNum, 
                        vector<vector<int>* >& subCircuits,
                        int num);




    void getOneWindow(Gia_MapLut_Meow* pLuts, int targetLut,
                      int targetSize, map<int, int>& out2Lut,
                      map<int, set<int>* >& id2FanoutIDs,
                      set<int>* members);
  //  bool writeCNNPartition(char* pFolderSpec, int mode);
    bool writeLUT(ofstream& output, int mode);
    void writeTruth(Gia_MapLut_Meow* pLuts, ofstream& output,
                    int lutNum);
    void writeLutNpn(ostream& output, int mode);
    void writeLutConnect(Gia_MapLut_Meow* pLuts, ofstream& output,
                         int lutNum);
    void writeLutConnect2(Gia_MapLut_Meow* pLuts, ofstream& output,
                          int lutNum);
    void buildLutGraph(Gia_MapLut_Meow* pLuts,
                       int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs); // 

    //void writeLutSingleEV(Gia_MapLut_Meow* pLuts, ofstream& output, int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs);
    void assignId2EV( Gia_MapLut_Meow* pLuts, vector<dEV* >& id2dEV, int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs);
    void dynamicGrouping( Gia_MapLut_Meow* pLuts, int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs, vector<EVGroup*>& groups );


    EVGroup* mergeSmallest(EVGroup* current, map<int, EVGroup*>& id2Group, Gia_MapLut_Meow* pLuts, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs);
   // void dynamicPooling(  Gia_MapLut_Meow* pLuts, int lutNum, vector<dEV* >& id2dEV, ofstream& output, int mode, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs);
    void evenlyGrouping(int lutNum, vector<EVGroup* >& groups);
    void BFSGrouping( Gia_MapLut_Meow* pLuts, int lutNum, map<int, int>& out2Lut, map<int, set<int>* >& id2FanoutIDs, vector<EVGroup*>& groups);
    void writeGroups(vector<EVGroup*>& groups, vector<dEV* >& id2dEV, ofstream& output, int mode);
    void writeAlan( Gia_MapLut_Meow* pLuts, int lutNum, map<int, int>& out2Lut,
ofstream& output);
    void writeLutTable( Gia_MapLut_Meow* pLuts,
                        ofstream& output, int lutNum,
                        map<int, int>& out2Lut,
                        map<int, set<int>* >& id2FanoutIDs,
                        int mode); 
    void writeSingleTruth(Gia_MapLut_Meow* pLuts,
                          ofstream& output, int id, int mode);
    Gia_MapLut_Meow* getMapLut(int& lutNum);
  private:
    Gia_Man_t* _cir;
    int _aigNum;
    int _lutNum;
    int _lutGroupNum;
    int _truthNum;
};

#endif
