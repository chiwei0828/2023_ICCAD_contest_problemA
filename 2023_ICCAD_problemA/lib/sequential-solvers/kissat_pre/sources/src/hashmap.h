#ifndef _hashmap_h_INCLUDED
#define _hashmap_h_INCLUDED
typedef long long ll;

typedef struct DataType DataType;
struct DataType{
	ll key;  
	int val;  
};

typedef struct HashNode HashNode;
struct HashNode{
	struct DataType data;
	HashNode *next; 
};

typedef struct HashMap HashMap;
struct HashMap{
	int size;
	HashNode **table;
}*hashmap;

HashMap * map_init(int size);
int map_get(HashMap *hashmap, ll key, int vsign);
void map_delete(HashMap *hashmap, ll key);
void map_insert(HashMap *hashmap, ll key, int value);
void map_free(HashMap *hashmap);

#endif