#ifndef CONTROLREGIONS_H
#define CONTROLREGIONS_H

#include<unordered_map>
#include <functional> 
#include <vector>
#include <string>
#include <memory>
#include <map>

class ControlTreeNode{
public:
    size_t id;
    std::string predicate;
    ControlTreeNode *parent;
    std::vector<ControlTreeNode*> children;

    ControlTreeNode(std::string predicate, size_t id): predicate(predicate), id(id){}

};

class ControlTree{
public:
    ControlTreeNode *root;
    ControlTree(ControlTreeNode *root): root(root){}

    ControlTreeNode* findNodeByID(const size_t id);
    ControlTreeNode* DFS(const size_t id, ControlTreeNode* node);
};

class ControlRegions{
public:
    ControlTree *ct;
    ControlTreeNode* lastSeen;
    
    //needed to track the common ancestors of different control statements
    std::map<ControlTreeNode*, ControlTreeNode*> lastSeenHeirarchy; //(child, parent)
    std::map<size_t, ControlTreeNode*> predicateMap;

    ControlRegions(){
        //root is sentinel
        this->lastSeen = std::make_unique<ControlTreeNode>("GLOBAL_REGION",0).get();
        lastSeenHeirarchy[lastSeen] = NULL;
        ct = std::make_unique<ControlTree>(this->lastSeen).get();
    }

};


#endif 