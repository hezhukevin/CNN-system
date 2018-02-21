#ifndef CHAR_NODE_H
#define CHAR_NODE_H
#include<iostream>
#include<set>
#include<vector>
using namespace std;

class charNode{
  public:
    charNode(int id){
      _selectID = id;
      _flag = 0;
    }
    void addContain(int id){
      _containID.insert(id);

    }
    int getSelectID(){
      return _selectID;
    }
    void getContain(vector<int>& idList){
      set<int>::iterator ite = _containID.begin();
      for(; ite != _containID.end(); ++ite)
        idList.push_back(*ite);
    }
    void setPI(){
      _flag|=1;
    }
    void setPO(){
      _flag|=2;
    }
    void setDouble(){
      _flag|=4;
    }
    bool hasDouble(){
      return(_flag&4)!=0;
    }
    bool hasPI(){
      return (_flag&1)!= 0;
    }
    bool hasPO(){
      return (_flag&2)!= 0;
    }
    void addOnInput(charNode* onInput){
      _onInput.insert(onInput);
    }
    void addOffInput(charNode* offInput){
      _offInput.insert(offInput);
    }
     void addOnOutput(charNode* onOutput){
      _onOutput.insert(onOutput);
    }
    void addOffOutput(charNode* offOutput){
      _offOutput.insert(offOutput);
    }
    void printOn(){
      cout<<"\ninput: ";
      set<charNode*>::iterator ite = _onInput.begin();
      for(; ite != _onInput.end(); ++ite)
        cout<<(*ite)<<" ";
      cout<<endl;

      cout<<"\noutput:";
      ite = _onOutput.begin();
      for(; ite != _onOutput.end(); ++ite)
        cout<<(*ite)<<" ";
      cout<<endl;
    }
    void printContain(){
      set<int>::iterator ite = _containID.begin();
      for(; ite != _containID.end(); ++ite)
        cout<<(*ite)<<" ";
      cout<<endl;



    }
    void printOff(){
      cout<<"\ninput: ";
      set<charNode*>::iterator ite = _offInput.begin();
      for(; ite != _offInput.end(); ++ite)
        cout<<(*ite)<<" ";
      cout<<endl;

      cout<<"\noutput:";
      ite = _offOutput.begin();
      for(; ite != _offOutput.end(); ++ite)
        cout<<(*ite)<<" ";
      cout<<endl;

    }
    set<charNode*>* getOnInput(){
      return &_onInput;
    }    
    set<charNode*>* getOnOutput(){
      return &_onOutput;
    }
  private:
    set<int> _containID;
    set<charNode*> _onInput;
    set<charNode*> _offInput;
    set<charNode*> _onOutput;
    set<charNode*> _offOutput;
    int _selectID;
    int _flag;
};

#endif
