#ifndef MEOW_BLOCK_H
#define MEOW_BLOCK_H
#include<iostream>
#include<set>
#include<map>
#include<vector>
#include<cmath>
#include"ext/meow/wordNode.h"
class meowBound;

using namespace std;

class meowBlock{
  public:
    meowBlock(){

    }
    ~meowBlock(){
     // for(int i = 0; i < _words.size(); ++i)
     //   delete _words[i];
      
    }
    bool checkFullySupport(vector<int>& inIDs);
    bool checkFullyTarget(vector<int>& outIDs);
    void addWord(meowBound* boundAPI, vector<int>& inIDs, vector<int>& outIDs, vector<int>& controls, vector<bool>& cofactors);
    void addWords(meowBound* boundAPI, vector<wordNode*>& words);
    void updateBound(meowBound* boundAPI);
    bool updateSupportList(meowBound* boundAPI, set<int>& supportedList, set<int>& hiddenList ,int gateID);
    bool fullySupported(meowBound* boundAPI, set<int>& supportedList, set<int>& hiddenList, int gateID);
    void popWords(vector<wordNode*>& words){
      for(int i = 0; i < _words.size(); ++i)
        words.push_back(_words[i]);

      _words.clear();
      _targets.clear();
      _supports.clear();
    }
    void printBlock(bool printAllWords){
      if(_words.size() == 0)
        return;
      cerr<<"Transparent Block:"<<endl;
      cerr<<"Supports: ";
      set<int>::iterator site = _supports.begin();
      for(; site!= _supports.end(); ++site)
        cerr<<(*site)<<"\t";

      cerr<<endl;
      cerr<<"Targets: ";
      site = _targets.begin();
      for(; site!= _targets.end(); ++site)
        cerr<<(*site)<<"\t";

      cerr<<endl;
      if(printAllWords){
        for(int i = 0; i < _words.size(); ++i)
          _words[i]->printNode();
      }
    } 
  private:
    vector<wordNode*> _words;
    set<int> _targets;
    set<int> _supports;
    set<int> _controls;
    
};
#endif
