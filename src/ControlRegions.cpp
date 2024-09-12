#include "ControlRegions.h"

ControlTreeNode* ControlTree::findNodeByID(const size_t id){
    //Do a DFS on the tree
    return this->DFS(id,this->root); 
}

//DFS to search the tree
ControlTreeNode* ControlTree::DFS(const size_t id, ControlTreeNode* node){
    //if(this->root->id == id)return this->root; 
    //root is a sentinel, so it should not match with any node

    ControlTreeNode* ret = NULL;
    for(ControlTreeNode* ctn : node->children){
        if(ctn->id == id){
            return ctn;
        }
        ret = this->DFS(id,ctn);
    }
    return ret;
 }