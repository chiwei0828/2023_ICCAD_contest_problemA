#include "hashmap.h"
#include <stdio.h>
#include <stdlib.h>


HashMap * map_init(int size) {
    HashMap *hashmap = (HashMap *)malloc(sizeof(HashMap));
    hashmap->size = size;
    hashmap->table = (HashNode **)malloc(sizeof(HashNode*) * hashmap->size);
    for (int i = 0; i < hashmap->size; i++)
        hashmap->table[i] = NULL;
    return hashmap;
}

int map_get(HashMap *hashmap, ll key, int vsign) {
    int pos = 1ll * key % hashmap->size;
    HashNode *pointer = hashmap->table[pos];
    while (pointer != NULL) {
        if (pointer->data.key == key)
            return pointer->data.val;
        else
            pointer = pointer->next;
    }
    return vsign;
}

void map_delete(HashMap *hashmap, ll key) {
    int pos = 1ll * key % hashmap->size;
    HashNode *pointer = hashmap->table[pos];
    if (pointer == NULL) return;
    if (pointer->data.key == key) {
        hashmap->table[pos] = pointer->next;
        free(pointer);
        return;
    }
    HashNode *prev = pointer;
    pointer = pointer->next;
    while (pointer != NULL) {
        if (pointer->data.key == key) {
            prev->next = pointer->next;
            free(pointer);
            return;
        }
        prev = pointer;
        pointer = pointer->next;    
    };
}

void map_insert(HashMap *hashmap, ll key, int value) {
    HashNode *hnode = (HashNode *)malloc(sizeof(HashNode));
    hnode->data.key = key;
    hnode->data.val = value;
    hnode->next = NULL;

    int pos = 1ll * key % hashmap->size;
    if (hashmap->table[pos] == NULL) {
        hashmap->table[pos] = hnode;
        return;
    }
    HashNode *pointer = hashmap->table[pos];
    HashNode *prev = pointer;
    while (pointer != NULL) {
        if (pointer->data.key == key) {
            pointer->data.val = value;
            free(hnode);
            return;
        } 
        prev = pointer;
        pointer = pointer->next; 
    } 
    prev->next = hnode;
}

void map_free(HashMap *hashmap){
    for (int i = 0; i > hashmap->size; i++) {
        HashNode *pointer = hashmap->table[i];
        HashNode *prev = pointer;
        while (pointer != NULL){    
            prev = pointer;
            pointer = pointer->next;
            free(prev);
        }
    }
    free(hashmap->table);
    free(hashmap);
    hashmap->table = NULL;
    hashmap = NULL;
}