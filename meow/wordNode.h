#ifndef WORD_NODE_H
#define WORD_NODE_H
#include<iostream>
#include<fstream>
#include <sstream>

#include <algorithm> 

#include<set>
#include<vector>
using namespace std;

class wordNode{
  public:
    wordNode(vector<int>& inID, vector<int>& outID, vector<int>& IDs, vector<int>& values){
       _maxID = 0;
       for(unsigned i = 0; i <inID.size(); ++i){
         _inID.push_back(inID[i]);
         _outID.push_back(outID[i]);
         if(abs(outID[i]) > _maxID)
           _maxID = abs(outID[i]);
       }
       for(unsigned i = 0; i < IDs.size(); ++i){
         _IDs.push_back(IDs[i]);
         _values.push_back( values[i]);

      }
      _level = 0;
    }
    wordNode(vector<int>& inID, vector<int>& outID, vector<int>& IDs, vector<bool>& values, vector<int>& levels){ // TODO add middle?
      // cerr<<"Hello?"<<endl;
        _maxID = 0;
       for(unsigned i = 0; i <inID.size(); ++i){
         _inID.push_back(inID[i]);
         _outID.push_back(outID[i]);
         _levels.push_back(levels[i]);
         if(abs(outID[i]) > _maxID)
           _maxID = abs(outID[i]);
       }
       for(unsigned i = 0; i < IDs.size(); ++i){
         _IDs.push_back(IDs[i]);
         if(values[i])
           _values.push_back(1);
         else
           _values.push_back(0);
      }
      _level = 0;
    }
    int getMaxID(){
       return _maxID;
    }
    void getCorresIn(int outID, int& level, int& inID){
      for(unsigned i = 0; i < _outID.size(); ++i){
        if(outID == _outID[i] || outID*(-1) == _outID[i]){
          inID = _inID[i];
          level = _levels[i];
          return;
        }
      }
      level = 0;
      inID = 0;
    }
    void setLevel(int level){
      _level = level;
    }
    int& getLevel(){
      return _level;
    }
    void printNode(ofstream& output){
      output<<"    {"<<endl;
      output<<"      \"level\": "<<_level<<","<<endl;
      output<<"      \"control\":{"<<endl;
      output<<"        \"nodes\":[";
      for(unsigned i = 0; i < _IDs.size(); ++i){
        if(i != 0)
          output<<", ";
        output<<_IDs[i];
      }
      output<<"],"<<endl;
      output<<"        \"assignment\":[";
      for(unsigned i = 0; i < _values.size(); ++i){
        if(i != 0)
          output<<", ";
        output<<_values[i];
      }

      output<<"]"<<endl;

      output<<"      },"<<endl;
      output<<"      \"inputs\":[";
      for(unsigned i = 0; i < _inID.size(); ++i){
        if(i != 0)
          output<<", ";
        output<<_inID[i];
      }

      output<<"],"<<endl;
      output<<"      \"outputs\":[";
      for(unsigned i = 0; i < _outID.size(); ++i){
        if(i != 0)
          output<<", ";
        output<<_outID[i];
      }

      output<<"]"<<endl;
      output<<"    }";
    }
    void printNode(){
      cerr<<"Transparent Word: Level = "<<_level<<endl;
      cerr<<"condition:"<<endl;
      for(unsigned i = 0; i < _IDs.size(); ++i)
        cerr<<_IDs[i]<<":"<<_values[i]<<"\t";
      cerr<<endl<<"From:"<<endl;
      for(unsigned i = 0; i < _inID.size(); ++i)
        cerr<<_inID[i]<<" ";
      cerr<<endl<<"To:"<<endl;
      for(unsigned i = 0; i < _outID.size(); ++i)
        cerr<<_outID[i]<<" ";
      cerr<<endl<<"Level: "<<endl;
      for(unsigned i = 0; i < _levels.size(); ++i)
        cerr<<_levels[i]<<" ";

      cerr<<endl;
    }
    int wordSize(){
      return _outID.size();
    }
    bool same(vector<int>& inID, vector<int>& outID){
      if(inID.size() != _inID.size())
        return false;
      for(int i = 0; i < outID.size(); ++i)
        if((inID[i] != _inID[i]) || (outID[i] != _outID[i]))
          return false;
      return true;
    }
    vector<int>& getOutIDs(){
      return _outID;
    }
    vector<int>& getInIDs(){
      return _inID;
    }
    vector<int>& getControlIDs(){
      return _IDs;
    }
    void getValues(vector<bool>& values){
      for(int i = 0; i < _values.size(); ++i){
        if(_values[i] == 1)
          values.push_back(true);
        else
          values.push_back(false);
      }
    }
    vector<int>& getLevels(){
      return _levels;
    }
    void getInOutIDs(vector<int>& inIDs, vector<int>& outIDs, vector<int>& controls){
      for(int i = 0; i < _inID.size(); ++i){
        inIDs.push_back(_inID[i]);
        outIDs.push_back(_outID[i]);
      }
      for(int i = 0; i < _IDs.size(); ++i)
        controls.push_back(_IDs[i]);
    }
  private:
   // vector<wordNode*> _inputs;
    vector<int> _inID;
    vector<int> _outID;
    vector<int> _IDs;
    vector<int> _values;
    vector<int> _levels;
    int _maxID;
    int _level; 

    // TODO: save eqList...
};
#endif
