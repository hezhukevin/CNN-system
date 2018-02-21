#ifndef DEP_GRAPH_H
#define DEP_GRAPH_H
#include<iostream>
#include<vector>
#include<map>
using namespace std;

class depGraph{
  public:
    depGraph(vector<int> & signals, bool forward){
      _forward = forward;
      _signals = signals;
      _sigNum = _signals.size();
      _depMapping = new char*[_sigNum];
      for(int i = 0; i < _sigNum; ++i){
        _depMapping[i] = new char[_sigNum];
        _cirID2GraphID[_signals[i]] = i;
      }
      for(int i = 0; i < _sigNum; ++i){
        for(int j = 0; j < _sigNum; ++j){
          _depMapping[i][j] = 0;
        }
      }
      _workingIndex = 0;
    }
    ~depGraph(){
      for(int i = 0; i < _sigNum; ++i)
        delete[] _depMapping[i];
      delete[] _depMapping;
    }
    void addDependency(int sourceID, int targetID){
      int sourceGID = _cirID2GraphID[sourceID];
      int targetGID = _cirID2GraphID[targetID];
      _depMapping[sourceGID][targetGID] = 1;
    }
    void getDescends(int sourceID, vector<int>& targets){
      int sourceGID = _cirID2GraphID[sourceID];
      for(int i = 0; i < _sigNum; ++i){
        if(_depMapping[sourceGID][i] == 1)
          targets.push_back(_signals[i]);
      }
    }
    void getAncestors(int sinkID, vector<int>& targets){
      int sinkGID = _cirID2GraphID[sinkID];
      for(int i = 0; i < _sigNum; ++i){
        if(_depMapping[i][sinkGID] == 1)
          targets.push_back(_signals[i]);
      }
    }
    vector<int> getSources(){
      vector<int> sourceIDs;
      for(int i = 0; i < _sigNum; ++i){
        bool hasFanin = false;
        for(int j = 0; j < _sigNum; ++j){
          if(_depMapping[j][i] == 1){
            hasFanin = true;
            break;
          }
        }
        if(!hasFanin)
          sourceIDs.push_back(_signals[i]);
      }
      return sourceIDs;
    }
    vector<int> getSinks(){
      vector<int> sinkIDs;
      for(int i = 0; i < _sigNum; ++i){
        bool hasFanout = false;
        for(int j = 0; j < _sigNum; ++j){
          if(_depMapping[i][j] == 1){
            hasFanout = true;
            break;
          }
        }
        if(!hasFanout)
          sinkIDs.push_back(_signals[i]);
      }
      return sinkIDs;
    }
    void printDepGraph(){
      for(int i = 0; i < _sigNum; ++i){
        cerr<<"From "<<_signals[i]<<" To: \n";
        for(int j = 0; j < _sigNum; ++j){
          if(_depMapping[i][j] == 1)
            cerr<<_signals[j]<<"\t";
        }
        cerr<<endl;
      }
    }
    void getNewSignals(vector<int> & newSignals){
      if(_visited.size() == 0){
        if(_forward){
          newSignals = getSources();
        }
        else{
          newSignals = getSinks();
        }
      }
      else{
        set<int>::iterator site = _visited.begin();
        for(; site != _visited.end(); ++site){
          vector<int> targets;
          if(_forward)
            getDescends(*site, targets);
          else
            getAncestors(*site, targets);
          for(int i = 0; i < targets.size(); ++i){
            if(_visited.find(targets[i]) == _visited.end())
              newSignals.push_back(targets[i]);
          }
        }
      }
      for(int i = 0; i < newSignals.size() ; ++i)
        _visited.insert(newSignals[i]);
    }
  private:
    map<int, int> _cirID2GraphID;
    set<int> _visited;
    set<int> _provedWordBits;
    vector<int> _last;
    vector<int> _signals; // gateID of control signals.
    int _sigNum;
    char** _depMapping;
    int _workingIndex;
    bool _forward; 
   // int _gateID2wordID;
};

#endif
