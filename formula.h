#ifndef  __FORMULA_H__
#define __FORMULA_H__
#include<iostream>
#include<utility>
#include<vector>
using namespace std;

enum Status{sat,unsat,unknown,done};

struct Node{
	Node(){};
	Node(int x,int v,int lev,int c)
	{
		literal = x;value = v;level = lev;
		antecedent = c;
	}

	Node(int x,int v,int lev)
	{
		literal = x;value = v;level = lev;
		antecedent = -1;
	}

        int literal;
        int value;                           // 1-true -1-false
        int level;
        int antecedent;                 // it is a clause
};

class Formula{
public:
	static int initSize;
        vector<int> literals;			// -1:false 0:unknown 1:true
	Status status;
	static vector<vector<int> > clauses;
	vector<int> clauseStatus;
	int resolveNum;
	static vector<Formula> formulaStack;	
	static int currentLevel;
	int preAssign;
	int curDec;
	int curValue;
	void setDecision(int x,int v){curDec=x;curValue=v;}

        // for conflict graph
        int level;
	int conflicting;
        static vector<Node> conflictGraph;             // it is a stack
	static vector<int> conflictClause;
	int conflictx,conflictv;

        // for 2-lit watching
        static vector<pair<int,int> > watchingList;    	// record two watch lit 
                                                	// for each clauses
        static vector<vector<int> > posWatched;
        static vector<vector<int> > negWatched;

        // for decision making
        vector<double> counterList;             // record freq of literals
        static vector<double> VSIDS;                   // will update counter when 
                                                // conflict occur
	vector<int> literalsPolar;		// record which polar of lit
						// occur more freq

	static int targetLevel;
	int backtrackingTime;

	//function
//	outputFile(FILE*);

	Formula();
	Formula(const vector<vector<int> >&);
	Formula(const Formula *);	

	~Formula();

	void setOriginClauses(const vector<vector<int> >&);

	int init();
	
	int BCP(int);				// for unit propagation
	int assign(int,int);
	void firstUIP();			// return conflict clause

	int updateWatchingList(int,int);	// which clause & one to replace

	void showResult();
	void showClauses();
	void showInfo();

	int checkSat();
	void addClause(vector<int>);
	bool checkUIP(vector<int>,int*);

	void zero();

	void showConflictGraph();

	int conflictResolve(int);	
};
#endif
