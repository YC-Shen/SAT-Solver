#include<iostream>
#include "parser.h"
#include<vector>
#include "formula.h"
#include<stdlib.h>
#include<stdio.h>
#include<string>
using namespace std;

void output(vector<int> );

int DPLL(Formula &);
int recurseTime=0;
FILE* out;

int main(int arg,char* argv[])
{
	srand(time(NULL));

	vector<vector<int> > clauses;
	int maxVarIndex;

	string s(argv[1]);
	int l = s.length();

	parse_DIMACS_CNF(clauses, maxVarIndex, argv[1]);

	s[l-1] = 't';
	s[l-2] = 'a';
	s[l-3] = 's';

	const char *c1 = s.c_str();
	out = fopen(c1,"w+");

	Formula formula(clauses);
	int r = formula.init();
	if(r == unsat){
		cout<<endl<<"UNSAT"<<endl;
		return 0;
	}
//	formula.showInfo();
//	cin>>r;	
//	formula.showInfo();
//	formula.assign(1,1);

//	formula.showClauses();
//	cin>>r;
	int result = DPLL(formula);
	if(result == unsat)
		fprintf(out,"UNSAT\n");
//	cout<<"Time : "<<recurseTime<<endl;
	return 0;
}

void output(vector<int> c)
{
	fprintf(out,"SAT\n");
	for(int i=1;i<c.size();i++)
	{
		int j=i;
		if(c[i]<0)
			j*=-1;

		fprintf(out,"%d ",j);
	}
}

int maxy(Formula);
void showStack(vector<Formula>);

int timeTrack = 0;
int timeNode = 0;

bool showDetail = true;
int flag = 0;
int DPLL(Formula &f) 			// -1:false 0:unknown 1:true
{
	f.zero();	
	vector<Formula> fv;
	fv.push_back(new Formula(f));
	fv.back().level=Formula::currentLevel=1;
	int blevel=-1,x=0,value=0,antedent = -1;
	while(true)
	{
		timeNode++;
		if(timeNode % 100 == 0)
			cout<<".";
		//decide next branch
		x = maxy(fv.back());
		
		value = fv.back().literalsPolar[abs(x)];
	
		if(value >=0)
			value = 1;
		else
			value = -1;

		while(true)
		{
			Formula *newf=new Formula(fv.back());	
			newf->level = Formula::currentLevel;

//			if(newf->level == 1)
//			{
//				int r;cin>>r;
//			}

			Formula::conflictGraph.push_back(Node(x,value,newf->level,antedent));
			antedent = -1;				

			newf->curDec = x;newf->curValue=value;
			//cout<<newf->curDec<<",,"<<newf->curValue;
//			cout<<"//level: "<<newf->level<<" x"<<newf->curDec<<" = "<<value;
			int result = newf->assign(x,value);
//			cout<<endl;

			if(result == unsat)
			{
				timeTrack++;

				blevel = newf->conflictResolve(newf->conflicting);
//				cout<<"Return to level "<<blevel<<endl;

				if(blevel<0)
				{
					int c;cin>>c;
					return unsat;
				}
				else
				{	

					if(timeTrack%128 == 0)
					{
						for(int i=0;i<Formula::VSIDS.size();i++)
						{
							Formula::VSIDS[i] /= 2.0;
						}
					}

					//backtracking
					while(fv.size()>0 && fv.back().level != blevel)
					{
						fv.pop_back();
					}
					int l = Formula::conflictGraph.size();
					while(l>0 && Formula::conflictGraph[l-1].level > blevel)
					{
						Formula::conflictGraph.pop_back();
						l--;
					}
					
					x = newf->conflictx;

					value = newf->conflictv;
					Formula::currentLevel = blevel;

					newf->addClause(newf->conflictClause);
					antedent = newf->clauses.size()-1;

					if(blevel == 0)
					{
						Formula *nf = new Formula(f);
						Formula::currentLevel++;
						nf->level = 1;
					
						antedent = -1;
						//Formula::conflictGraph.push_back(Node(x,value,1,antedent));
						
						//Formula::conflictGraph.push_back(Node(x,value,1,antedent));
//						cout<<Formula::conflictGraph.size();
//						cout<<"//level: "<<nf->level<<" x"<<x<<" = "<<value;
//						cout<<" ";
						Formula::conflictGraph.push_back(Node(x,value,1,-1));

						result = nf->assign(x,value);
//						cout<<endl;

						if(result == unsat)
							return unsat;

						fv.push_back(nf);
						Formula::currentLevel++;
		
//						nf->showConflictGraph();
				//		int r;cin>>r;
						break;
					}
				}
			//	int e;cin>>e;	
			}
			else if(result == sat)
			{
				newf->showResult();
				output(newf->literals);
				return sat;
			}
			else
			{
				Formula::currentLevel++;
				fv.push_back(new Formula((*newf)));
				break;
			}
		}
	}
}

int maxy(Formula f)
{
	double max=0,j=1;
	for(int i=1;i<f.counterList.size();i++)
	{
		if(f.counterList[i] == -1)
			continue;
		if(max<f.counterList[i]+f.VSIDS[i])
		{
			max = f.counterList[i]+f.VSIDS[i];
			j = i;
		}
	}
	return j;
}

void showStack(vector<Formula> fs)
{
	cout<<"show stack"<<endl;
	for(int i=0;i<fs.size();i++)
	{
		cout<<fs[i].level<<" ";
		cout<<"x"<<fs[i].curDec<<"= "<<fs[i].curValue<<endl;
	}
	cout<<endl;
}





