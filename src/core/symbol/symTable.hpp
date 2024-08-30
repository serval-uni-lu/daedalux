#ifndef SYMBOL_TABLE_H
#define SYMBOL_TABLE_H
/*
 * SYMBOL TABLE
 * * * * * * * * * * * * * * * * * * * * * * * */

#include <cassert>
#include <string>
#include <map>
#include <list>
#include <unordered_set>
#include <fstream>

#include "symbol.hpp"

class astNode;
class stmnt;
class expr;
class exprVar;
class exprVarRef;
class exprVarRefName;

class fsm;
class fsmNode;
class fsmTrans;

class varSymNode;
class sysSymNode;

class symTabVisitor;
class symTabConstVisitor;

//symbolTable?
class symTable {
public:

	symTable(const std::string& name, symTable* prev = nullptr);

	symTable* createSubTable(const std::string& name = "");

	virtual ~symTable();

	std::string getNameSpace(void) const;

	void setNameSpace(const std::string& name);

	void print(int tab = 0) const;

	symbol* lookup(const std::string& name) const;

	symbol* lookupGlobal(const std::string& name) const;

	std::unordered_set<symbol*> getSymbols(const symbol* left) const;

	std::unordered_set<symbol*> getSymbols(void) const;

	template <typename T> std::unordered_set<T> getSymbols(void) const {
		std::unordered_set<T> res;
		for(auto sym : syms) {
			if(dynamic_cast<T>(sym.second) != nullptr)
				res.insert(dynamic_cast<T>(sym.second));
		}
		return res;
	}

	template <typename T> std::unordered_set<T> getGlobalSymbols(void) const {
		std::unordered_set<T> res = prev? prev->getGlobalSymbols<T>() : std::unordered_set<T>();

		for(auto sym : syms) {
			if(dynamic_cast<T>(sym.second) != nullptr)
				res.insert(dynamic_cast<T>(sym.second));
		}

		return res;
	}

	void insert(symbol* sym);
	
	void remove(const std::string& name);

	void remove(const symbol* sym);

	void clear(void);

	void setBlock(stmnt* block);

	stmnt* getBlock(void) const;

	void setPrevSymTab(symTable* symTab);

	void addNextSymTab(symTable* symTab);
	
	symTable* prevSymTab(void) const;

	symTable* getSubSymTab(const std::string& name) const;
	
	void printSymTab(int level, const std::string& title) const;

	bool isGlobal(void) const;

	bool isMultiSystems(void) const;

	operator std::string(void) const;

	static void addPredefinedSym(symTable* tab);

	void acceptVisitor(symTabVisitor* visitor);

	void acceptVisitor(symTabConstVisitor* visitor) const;

	void printGraphViz(std::ofstream& file) const;

protected:

	std::string name;
	std::string parentNameSpace;
	stmnt* block;
	symTable* prev;
	std::list<symTable*> nexts;
	std::map<std::string, symbol*> syms;
};

#endif
