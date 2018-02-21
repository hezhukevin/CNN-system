#ifndef CHAR_GRAPH_H
#define CHAR_GRAPH_H
#include"ext/meow/charNode.h"
#include<iostream>
#include<set>
#include<vector>
#include<map>
using namespace std;
class charGraph{
  public:
    charGraph(int num); // record id to node
    ~charGraph();
    charNode* addNewNode(int selectID);
    charNode* getNodeBySelect(int selectID);
    charNode* id2Node(int gateID);
    void addContainForNode(charNode* node, int newID); 
    void getContainID(vector<int>& idList, int nodeIndex );
    int selectIdByNodeIndex(int nodeIndex){
      return _allNodes[nodeIndex]->getSelectID();
    }
    void printGraph();
    int nodeNum(){ return _allNodes.size(); }
    void setDepend(set<int>& inList, int nodeIndex, int type);
    void addBadNode(int giaId);
    void collectSignalID(vector<int>& idForSignal);
    void printProperty();
    int getTargetByIndex(int index, vector<int> & CoList);
    map<int, vector<int> >* getProperty(){
      return &_propertyMap;
    }
    int propertyTarget(int index){
      return _propertyOrder[index];
    }
    int propertyNum(){
      return _propertyOrder.size();
    }
    //bool collectProperty(); 
  private:
    vector<charNode*> _allNodes;
    vector<charNode*>* _id2CharNode;// position(id) => node
    map<int, charNode*> _select2CharNode;
    set<charNode*> _badNode;
    vector<int> _propertyOrder;
    map<int, vector<int> > _propertyMap; // property in order to selector
};
#endif
