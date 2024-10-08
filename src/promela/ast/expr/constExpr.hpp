#ifndef CONST_EXPR_H
#define CONST_EXPR_H

#include <limits>

#include "expr.hpp"

//E_EXPR_CONST,		// iVal = the value
class exprConst : public expr
{
public:
	exprConst(int constant, int lineNb);

	int getCstValue(void) const;
	
	//void setCstValue(int constant);

	operator std::string() const override;

	bool operator==(const astNode* other) const override;

	std::string getTypeDescr(void) const override;

	symbol::Type getExprType(void) const override;

	bool castToExprType(symbol::Type type) const override;

	std::vector<astNode*> getMutations(void) const override ;

	astNode* deepCopy(void) const override;

	void acceptVisitor(ASTConstVisitor* visitor) const override;

	void acceptVisitor(ASTVisitor* visitor) override;

protected:
	exprConst(astNode::Type type, int constant, int lineNb);

private:
	bool exceed_limits(int add) const;

private:
	int constant;
};

//E_EXPR_TRUE,		// iVal = 1
class exprTrue : public exprConst
{
public:
	exprTrue(int lineNb);

	operator std::string() const override;

	std::string getTypeDescr(void) const override;

	symbol::Type getExprType(void) const override;

	std::vector<astNode*> getMutations(void) const override;

	astNode* deepCopy(void) const override;

	void acceptVisitor(ASTConstVisitor* visitor) const override;

	void acceptVisitor(ASTVisitor* visitor) override;

};

//E_EXPR_FALSE,		// iVal = 0
class exprFalse : public exprConst
{
public:
	exprFalse(int lineNb);

	operator std::string() const override;

	std::string getTypeDescr(void) const override;

	symbol::Type getExprType(void) const override;

	std::vector<astNode*> getMutations(void) const override;

	astNode* deepCopy(void) const override;

	void acceptVisitor(ASTConstVisitor* visitor) const override;

	void acceptVisitor(ASTVisitor* visitor) override;
	
};

#endif