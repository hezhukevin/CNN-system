#ifndef MEOW_NODE_H
#define MEOW_NODE_H
#include<iostream>
#include<fstream>
#include <sstream>
#include<cstring>
#include<set>
#include<vector>
#include<map>
#include <stdlib.h>  
#include "aig/gia/gia.h"
#include "aig/gia/giaAig.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satStore.h"
#include "misc/extra/extra.h"
#include <algorithm> 

using namespace std;
class meowNode{
  public:
    meowNode(int wordID, vector<int>& controls, vector<int>& outIDs){
      _wordID = wordID;
      for(int i = 0; i < controls.size(); ++i)
        _controls.push_back(controls[i]);
      for(int i = 0; i < outIDs.size(); ++i)
        _outIDs.push_back(outIDs[i]); 
      // outIDs must be positive
      _zero = 0;
    }
    void addFaninWord(vector<bool>& assignment, vector<int>& inIDs, vector<vector<int> >& eqList){
      _assignments.push_back(assignment);
      _inIDs.push_back(inIDs);
     // cerr<<"From "<<_eqLists.size();
      _eqLists.push_back(eqList);
      //cerr<<" TO "<<_eqLists.size()<<endl;
    }
    
    //void addOuts()
    void removeOuts(vector<int>& removeIDs){ // maybe no?
      int removeIdx = 0;
      for(int i = 0; i < _outIDs.size(); ++i){
        if(removeIDs[removeIdx] == _outIDs[i]){
          _outIDs[i] = 0;
          //for(int j = 0; j < _inIDs.size(); ++j)
          //  _inIDs[j][i] = 0;
          removeIdx++;
          if(removeIdx >= removeIDs.size())
            break;
        }
      }
    }
    void removeOut(int outID){
      for(int i = 0; i < _outIDs.size(); ++i){
        if(outID == _outIDs[i]){
          _outIDs[i] = 0;
          _zero++;
          break;
         // _zero++;
        }
      }
    }
    void printNode(){
       cerr<<"Output word: \t"<<_wordID<<endl;
       for(int i = 0; i < _outIDs.size(); ++i){
         if(_outIDs[i]!= 0)
           cerr<<_outIDs[i]<<"\t";
       }
       cerr<<endl;
       cerr<<"\tControl Supports:\n\t";
       for(int i = 0; i < _controls.size(); ++i)
         cerr<<_controls[i]<<"\t";
       cerr<<endl;
 
       for(int i = 0; i < _inIDs.size(); ++i){
         cerr<<"\t Input Word: \t";
         for(int j = 0; j < _outIDs.size(); ++j){
           if(_outIDs[j]!=0)
             cerr<<_inIDs[i][j]<<"\t"; 
         }
         
         cerr<<endl;
         cerr<<"\t Levels: \t";
         for(int j = 0; j < _outIDs.size(); ++j){
          if(_outIDs[j]!=0)
            cerr<<_eqLists[i][j].size()<<"\t";
         }
         cerr<<endl;
         cerr<<"\tControl assignment: \t";
         for(int j = 0; j < _controls.size(); ++j)
           cerr<<_assignments[i][j]<<"\t";
         cerr<<endl;
       }
    }
    int getWordID(){
      return _wordID;
    }
    int getWidth(){
      return _outIDs.size() - _zero; // consider zero?
    }
    void getInputs(set<int>& inputs){
      for(int i = 0; i < _inIDs.size(); ++i){
        for(int j = 0; j < _inIDs[i].size(); ++j){
          if(_outIDs[j] != 0)
            inputs.insert(abs(_inIDs[i][j]));
        }
      } 
    }
    void getInputsByPos(set<int>& inputs, int pos){
      for(int i = 0; i < _inIDs.size(); ++i){
        inputs.insert(abs(_inIDs[i][pos]));
      }
    }
    void getLevels(vector<int>& levels){
      //printNode();
      for(int i = 0; i < _eqLists.size(); ++i){
        levels.push_back(_eqLists[i][0].size()-1);
      }
    }
    int getLevel(){
      int maxLevel = 0;
      for(int i = 0; i < _eqLists.size(); ++i){ // i is each word
        int level = -1;
        for(int j = 1; j < _eqLists[i].size(); ++j )
          if((_outIDs[j]!= 0) 
          &&(level >  _eqLists[i][j].size() || level == -1)){
            level = _eqLists[i][j].size();}

        if(level > maxLevel)
          maxLevel = level;
      }
      return maxLevel;
    }
    int getInputNum(){
      return _inIDs.size();
    }
    int getMaxOut(){
      int maxOut = 0;
      for(int i = 0; i < _outIDs.size(); ++i){
        if(maxOut < _outIDs[i])
          maxOut = _outIDs[i];
      }
      return maxOut;
    }
    vector<int>& getOutIDs(){
      return _outIDs;
    }
    vector<int>& getControlIDs(){
      return _controls;
    }
    void getFanins(int pos, vector<int>& fanins){
      for(int i = 0; i < _inIDs.size(); ++i)
        fanins.push_back(abs(_inIDs[i][pos]));
    }
    bool isMux(){
      if(_controls.size() == 1 && _inIDs.size() == 2)
        return true;

      return false;
    }
    void addMiddleBits(set<int>& provedBits){
      for(int i = 0; i < _eqLists.size(); ++i){
        for(int j = 0; j < _eqLists[i].size(); ++j){
          if(_outIDs[j] == 0)
            continue;

          for(int k = 1; k < _eqLists[i][j].size(); ++k)
            provedBits.insert(abs(_eqLists[i][j][k]));
        }
      }
    }
    void addGoodControl(set<int>& goodControls){
      goodControls.insert(_controls.begin(), _controls.end());
    }
    void addInternal(set<int>& internalBits){
      for(int i = 0; i < _eqLists.size(); ++i){
        for(int j = 0; j < _eqLists[i].size(); ++j){
          if(_outIDs[j] == 0)
            continue;

          for(int k = 1; k < _eqLists[i][j].size()-1; ++k)
            internalBits.insert(abs(_eqLists[i][j][k]));
        }
      }
    }
    bool fixInternal(int pos, set<int>& internalBits){
      if(_inIDs.size() > 1)
        return false;
      if(_eqLists[0][pos].size() < 3)
        return false;
      int newIndex = -1;
      for(int i = _eqLists[0][pos].size() -2; i >= 1; --i){
        if(internalBits.find(abs(_eqLists[0][pos][i])) == internalBits.end()){
            
          newIndex = i;
          break;
        }
      }
      if(newIndex == -1)
        return false; // fail

      //1. replace outs
      if((_eqLists[0][pos].back())*(_eqLists[0][pos][newIndex]) < 0) 
        _inIDs[0][pos] = (-1)*(_inIDs[0][pos]);
      _outIDs[pos] = abs(_eqLists[0][pos][newIndex]);
      //2. remove eqLists
      while(_eqLists[0][pos].size() > (newIndex+1))
        _eqLists[0][pos].pop_back();
      return true;
    }
    bool isBetter(meowNode* old){
      if(this->getWidth() > old->getWidth())
        return true;
      if(this->getLevel() > old->getLevel())
        return true;
      return false;
      // compare width or depth?
    }
    void addProvedBitsPos(int pos, set<int>& provedBits){

    }
    void addProvedBits(set<int>& provedBits){
      for(int i = 0; i < _eqLists.size(); ++i){
        for(int j = 0; j < _eqLists[i].size(); ++j){
          if(_outIDs[j] == 0)
            continue;
          for(int k = 0; k < _eqLists[i][j].size(); ++k)
            provedBits.insert(abs(_eqLists[i][j][k]));
        }
      }
    }
    bool isGoodNode(bool hateSingle){ // early
      int maxLevel = 0;
      for(int i = 0; i < _eqLists.size(); ++i){
        int level = _eqLists[i][0].size();
        for(int j = 0; j < _eqLists[i].size(); ++j )
          if(level != _eqLists[i][j].size())
            return false; // different! no npn iso
        if(level > maxLevel)
          maxLevel = level;
      }
      if(maxLevel < 3 && hateSingle) // singleLevel
        return false;
      //updateLevel();
      if(maxLevel < 3 && _controls.size() > 1)
        return false;
      if(maxLevel >= 3 && _controls.size() == 1 && _inIDs.size() == 1)
        return false;
      return true;
    }
    meowNode* splitNode(int nodeID, vector<int>* pos){
      vector<int> outIDs;
      //cerr<<"Old width"<<_outIDs.size()<<endl;
      //cerr<<"Input Num "<<_inIDs.size()<<endl;
      for(int i = 0; i < pos->size(); ++i)
        outIDs.push_back(_outIDs[(*pos)[i]]);
      meowNode* newNode = new meowNode(nodeID, _controls, outIDs);
      for(int i = 0; i < _inIDs.size(); ++i){
        vector<int> inIDs;
        vector<vector<int> > eqList;
       // cerr<<"_eqList[i].size(): "<<i<<"size: "<<_eqLists[i].size();
        for(int j = 0; j < pos->size(); ++j){
          inIDs.push_back(_inIDs[i][(*pos)[j]]);
         // cerr<<"What?"<<_eqLists[i][(*pos)[j]].size()<<endl;
          eqList.push_back(_eqLists[i][(*pos)[j]]);
        }
        newNode->addFaninWord(_assignments[i],inIDs, eqList);
      }
      return newNode; 
    }
    void writeVerilog(ofstream& output){
     // if(isMux())
     //   output<<"module mux"<<_wordID<<"(";
     // else 
        output<<"module trans"<<_wordID<<"(";
      output<<"c"<<_wordID<<", ";
      for(int i = 0; i < _inIDs.size(); ++i)
        output<<"word"<<_wordID<<"_"<<i<<", ";
      output<<"word"<<_wordID<<"_out);"<<endl;

      for(int i = 0; i < _inIDs.size(); ++i)
        output<<"input ["<<getWidth()-1<<":0] word"<<_wordID<<"_"<<i<<";"<<endl;

     // if(_controls.size() > 1)
     //   output<<"input ["<<_controls.size()-1<<":0]";
    //  else
      output<<"input ";
      output<<" c"<<_wordID<<";"<<endl;
      
      if(isMux()){ // single MUX
       
        output<<" output ["<<getWidth()-1<<":0]";
        output<<" word"<<_wordID<<"_out;"<<endl;
        output<<" assign word"<<_wordID<<"_out = ";
        if(!_assignments[0][0])
          output<<"~";
        output<<"c"<<_wordID<<"?";
        output<<"word"<<_wordID<<"_0 : word"<<_wordID<<"_1;"<<endl;
        output<<"endmodule"<<endl;
      }
     /* else{ 
        for(int i = 0; i < _inIDs.size(); ++i){
          output<<"wire word"<<_wordID<<"_s"<<i<<" = ";
          for(int j = 0; j < _assignments[i].size(); ++j){
            if(j != 0)
              output<<"&";
            output<<"(";
            if(!_assignments[i][j])
              output<<"~";
            output<<"c"<<_wordID<<"["<<j<<"])";
 
          } 
          output<<";"<<endl;
        } // decide control condition first
        output<<"output ["<<getWidth()-1<<":0] word"<<_wordID<<"_out;"<<endl;
        output<<"assign word"<<_wordID<<"_out = ";

        for(int i = 0; i < _inIDs.size(); ++i){
          if(i != 0)
            output<<"|";
          output<<"({"<<getWidth()<<"{word"<<_wordID<<"_s"<<i<<"}}&"<<"word"<<_wordID<<"_"<<i<<")";
   
        }
        output<<";"<<endl;
        output<<"endmodule"<<endl;
      }*/
    }
    vector<vector<int> >& getInIDs(){
      return _inIDs; 
    } 
  private:
    vector<int> _outIDs;
    vector<vector<int> > _inIDs; // maybe literal?
    vector<int> _controls;
    vector<vector<bool> > _assignments;
    vector< vector<vector<int> > > _eqLists;
    int _wordID;
    int _zero;
};

#endif
