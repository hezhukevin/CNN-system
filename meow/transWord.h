#ifndef TRANS_WORD_H
#define TRANS_WORD_H
#include<iostream>
#include<set>
#include<vector>
#include<cstring>
using namespace std;

class transWord{
  public:
    transWord(int bitNum, int inputWordNum, int controlNum){
      _bitNum = bitNum;
      _inputWordNum = inputWordNum;
      _controlNum = controlNum;
      if(inputWordNum != 0 && controlNum != 0){
        _inputWords = new int*[_inputWordNum];
        _assignments = new char*[_inputWordNum]; 
        for(int i = 0; i < inputWordNum; ++i){
          _inputWords[i] = new int[_bitNum];
          _assignments[i] = new char[_controlNum];
          for(int j = 0; j < _controlNum; ++j)
          _assignments[i][j] = 'X';
        }
      }
      else{
        _inputWords =NULL;
        _assignments = NULL;
      }
      _outputWord = new int[bitNum];
      if(controlNum != 0)
        _controls = new int[controlNum];
      else
        _controls = NULL;
    }
    ~transWord(){
      delete[] _outputWord;
      if(_inputWordNum != 0 && _controlNum != 0){
        for(int i = 0; i < _inputWordNum; ++i){
          delete[] _inputWords[i];
          delete[] _assignments[i];
        }
      
        delete[] _inputWords;
        delete[] _assignments;
        delete[] _controls;
      }
    }
    void setWordNSupp(vector<int>& outputs, vector<int>& controls, int* inputWords ){
      for(int i = 0; i < outputs.size(); ++i)
        _outputWord[i] = outputs[i];
      for(int i = 0; i < controls.size(); ++i){
        _controls[i] = controls[i];
        _control2pos[_controls[i]] = i;
      }
      for(int i = 0; i < _inputWordNum; ++i){
        for(int j = 0; j < _bitNum; ++j){
          _inputWords[i][j] = inputWords[i*_bitNum+j];
        }
      }
    }
    void putAssignment(vector<int>& controls, int wordIndex, int* values ){
      for(int i = 0; i < controls.size(); ++i){
        if(values[i] == 0)
          _assignments[wordIndex][_control2pos[controls[i]]] = '0';
        else
          _assignments[wordIndex][_control2pos[controls[i]]] = '1';

      }
    }
    void putAssignment2(vector<int>& controls, int wordIndex, vector<char>& values){
      for(int i = 0; i < controls.size(); ++i){
        _assignments[wordIndex][_control2pos[controls[i]]] = values[i];

      }

    }
    void setFaninWords(vector<transWord*>& faninWords){
      for(int i = 0; i < faninWords.size(); ++i)
        _faninWords.push_back(faninWords[i]);
    }
    void addFaninWord(transWord* faninWord){
      _faninWords.push_back(faninWord);
    }
    int getInputWordNum(){
      return _inputWordNum;
    }
    int getProvedInputWordNum(){
      return _faninWords.size();
    }
    void getInputWordByIndex(int i, vector<int>& ids ){
      for(int j = 0; j < _bitNum; ++j){
          ids.push_back(_inputWords[i][j]);
      }
    }
    void getOutputWordIds(vector<int>& ids){
       for(int i = 0; i < _bitNum; ++i)
        ids.push_back(_outputWord[i]);
    }
    int getWidth(){
       return _bitNum;
 
    }
    void printTransWord(){
      cerr<<"Output word: \t";
      for(int i = 0; i < _bitNum; ++i)
        cerr<<_outputWord[i]<<"\t";
      cerr<<endl;
      cerr<<"\tControl Supports:\n\t";
      for(int i = 0; i < _controlNum; ++i)
        cerr<<_controls[i]<<"\t";
      cerr<<endl;
      for(int i = 0; i < _inputWordNum; ++i){
        cerr<<"\t\tInput word: \t";
        for(int j = 0; j < _bitNum; ++j)
          cerr<<_inputWords[i][j]<<"\t";
        cerr<<endl;
        cerr<<"\t\tControl assignment: \t";
        for(int j = 0; j < _controlNum; ++j)
          cerr<<_assignments[i][j]<<"\t";
        cerr<<endl;
      }
      if(_faninWords.size() > 0){
        cerr<<"Input Words: \n";
        for(int i = 0; i < _faninWords.size() ;++i)
          _faninWords[i]->printWordID();
      }
    }
    int provedFaninWordNum(){
      return _faninWords.size();
    }
    transWord* getFaninWord(int index){
      return _faninWords[index];
    }
    void setWordID(int id){
      _wordID = id;
    }
    int getWordID(){
      return _wordID;
    }
    void setNonInheritControls(set<int>& nonInheritControls){
      _nonInheritControls.assign(nonInheritControls.begin(),
                                 nonInheritControls.end());
    }
    void getAllControls(vector<int>& controls){
      for(int i = 0; i < _controlNum ; ++i)
        controls.push_back(_controls[i]);
    }
    void getNonInheritControls(vector<int>& controls){
      for(int i = 0; i < _nonInheritControls.size(); ++i)
        controls.push_back(_nonInheritControls[i]);
    }
    void getNonInheritAssignment(vector<int>& controls, vector<char>& assignments){
      for(int i = 0; i < _nonInheritControls.size(); ++i){
        controls.push_back(_nonInheritControls[i]);
        int pos = _control2pos[_nonInheritControls[i]];
        assignments.push_back(_assignments[0][pos]);
//        cerr<<"get Non inherit "<<_assignments[0][pos];
//        cerr<<" for ID"<<_nonInheritControls[i]<<endl;
      }

    }
    void printWordID(){
      cerr<<"Word ID = "<< _wordID<<endl;
    }
    int* getControls(){
      return _controls;
    }
    int getControlNum(){
      return _controlNum;
    }
    transWord* getFaninWordByIndex(int i){
      return _faninWords[i];
    }
    char* getAssignments(int index){
      return _assignments[index];
    }
    int getPosFromControl(int controlID){
      return _control2pos[controlID];
    }
    //do we need control ID to pos?
  private:
    map<int, int> _control2pos;
    int _bitNum;
    int _inputWordNum;
    int _controlNum;
    int** _inputWords; // this could include input words ID
    int* _outputWord; 
    int* _controls; // appear in this level only
    char** _assignments;
    vector<int> _nonInheritControls;
    vector<transWord*> _faninWords;
    int _wordID; 
};
#endif
