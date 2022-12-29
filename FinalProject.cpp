#include<bits/stdc++.h>
#define pb push_back
using namespace std;

string eps = "‘‘";

//this function removes spaces from string
string removeSpace(string s){
    string ret;
    for(auto e:s){
        if(e == ' ')    continue;
        ret += e;
    }
    return ret;
}

//function that convert string to vector of strings
vector<string> stovecofs(string str){
    vector<string> ret;
    string tmp;
    for(auto &let : str){
        if(let == ' '){
            if(tmp.size())  ret.push_back(tmp);
            tmp.clear();
        }
        else    tmp += let;
    }
    if(tmp.size())  ret.push_back(tmp);
    return ret;
}

//function to print stack
void printStk(stack<string> stk){
    int sz = 0;
    stack<string> tmp;
    while(stk.size())   tmp.push(stk.top()), sz += stk.top().size(), sz++, stk.pop();
    while(tmp.size())   cout<<tmp.top()<<" ",   tmp.pop();
    for(int i=sz;i<16;i++) cout<<" ";
}

//function to print queue
void printQ(queue<string> q){
    while(q.size())   cout<<q.front()<<" ", q.pop();
    cout<<"\n";
}

//class for production rules
class prod{
    public:
        vector<string> rule;
        set<string>trmnls;
        string nonTrmnl;

        prod(string rule){
//            rule = removeSpace(rule);

            //fill the non-terminal string and the terminals set of string
            //1. append the non-terminal part
            string str;
            for(int i=0;i<rule.size();i++){
                if(rule[i] == ' ' && nonTrmnl.size()==0)  continue;
                if(rule[i] == '-' && rule[i+1] == '>'){
                    i++;
                    nonTrmnl = str;
                    this->rule.push_back(str);
                    str.clear();
                    continue;
                }
                str += rule[i];
            }
            //2. append the terminals part
            for(int i=0;i<str.size();i++){
                if(str[i] == ' ')   continue;
                if(str[i] == '|'){
                    this->rule.push_back("|");
                    continue;
                }
                string tmp; tmp += str[i];
                while(i+1<str.size() && str[i+1]!=' ') i++, tmp += str[i];
//                if(i+1<str.size() && str[i+1]=='\''){
//                    tmp = str[i];   tmp += '\'';
//                    trmnls.insert(tmp), i++;
//                }
//                else if(str[i] == '‘')  trmnls.insert("‘‘"), tmp = "‘‘", i++;
//                else{
//                    tmp = str[i];
//                    trmnls.insert(tmp);
//                }
                trmnls.insert(tmp);
                this->rule.push_back(tmp);
            }
        }
};

//class for context-free grammars
class cfg{
    public:
        vector<prod> prods;
        set<string> trmnls;
        set<string> nonTrmnls;
        vector<vector<string>> rules;
        map<string,set<string>> firsts, follows;
        vector<vector<string>> parseTable;
        vector<vector<string>> parseAns;


        cfg(vector<string> &prodRules){

            //convert all production rules from string to "prod" class and push them all to prods vector
            for(auto &rule:prodRules){
                prod prodRule(rule);
                prods.push_back(prodRule);

                //for each production rule insert its non-terminal and terminals to "trmnls" set and
                //"nonTrmnls" set
                for(auto &trm:prodRule.trmnls)  this->trmnls.insert(trm);
                this->nonTrmnls.insert(prodRule.nonTrmnl);

                //push each production rule to the "rules" vector
                this->rules.push_back(prodRule.rule);
            }

            //remove redundant non-terminals from the terminal st
            for(auto trm : nonTrmnls)  trmnls.erase(trm);
        }

        //Check if non-terminal has an epsilon in its first
        bool hasEps(set<string>first){
            for(auto term : first) if(term == "‘‘")  return true;
            return false;
        }

        //left factoring function
        void lefFactoring(){
            vector<vector<string>> lftFacRules;
            map<string, bool> done;
            for(int i=0;i<rules.size();i++){
                if(done[rules[i][0]])   continue;
                vector<string> rule;
                rule.push_back(rules[i][0]);
                for(int j=i;j<rules.size();j++){
                    if(rules[i][0] != rules[j][0])  continue;
                    if(i!=j)    rule.push_back("|");
                    for(int k=1;k<rules[j].size();k++)  rule.push_back(rules[j][k]);
                }
                lftFacRules.push_back(rule);
                done[rules[i][0]] = 1;
            }
            rules = lftFacRules;
        }

        //eliminate left recurrsion
        void elimLeftRec(){
            vector<vector<string>> lftRecRules;
            queue<vector<string>> q;
            for(auto rule: rules)   q.push(rule);

            while(q.size()){
                if(q.front()[0] != q.front()[1]){
                    lftRecRules.push_back(q.front());
                    q.pop();
                    continue;
                }
                vector<string> rule = q.front();
                q.pop();
                string nwTrm = rule[0];
                nwTrm += '\'';

                vector<string> rule1, rule2;
                rule1.push_back(rule[0]);
                rule2.push_back(nwTrm);

                for(int i=1;i<rule.size();i++){
                    if(rule[i] == "|")  continue;
                    vector<string> tmp;
                    tmp.push_back(rule[i]);
                    while(i+1< rule.size() && rule[i+1] != "|"){
                        i++;
                        tmp.push_back(rule[i]);
                    }
//                    for(auto e: tmp)    cout<<e<<" ";   cout<<"\n";

                    if(tmp[0] == rule[0]){
                        if(rule2.size()>1)  rule2.push_back("|");
                        for(int j=1;j<tmp.size();j++)   rule2.push_back(tmp[j]);
                        rule2.push_back(nwTrm);
                    }
                    else{
                        if(rule1.size()>1)  rule1.push_back("|");
                        for(int j=0;j<tmp.size();j++){
                            if(tmp[j] == eps)   continue;
                            rule1.push_back(tmp[j]);
                        }
                        rule1.push_back(nwTrm);
                    }
                }
                if(rule2.size() != 1)   rule2.push_back("|");
                rule2.pb(eps);
                lftRecRules.push_back(rule1);
                lftRecRules.push_back(rule2);
            }

            rules = lftRecRules;
        }

        void findFirst(string term){
            //If firsts of the term are already calculated then return
            if(firsts[term].size()>0)   return;
            for(auto rule: rules){
                //if this is not the rule of the non-terminal then skip it
                if(term != rule[0]) continue;
                // I found the rule of the non-terminal
                bool nxtIsFirst = 1;
                for(int trm = 1; trm<rule.size();trm++){
                    if(rule[trm] == "|"){
                        if(nxtIsFirst)  firsts[term].insert(eps);
                        nxtIsFirst = 1;
                    }
                    if(!nxtIsFirst || rule[trm] == "|")   continue;
                    // if it's terminal then add it to the first of the non-terminal
                    if(trmnls.find(rule[trm]) != trmnls.end()){
                        firsts[term].insert(rule[trm]);
                    }
                    //if it's non-terminal calculate its firsts then add them also
                    else{
                        if(firsts[rule[trm]].size() == 0)     findFirst(rule[trm]);
                        for(auto frst : firsts[rule[trm]]){
                            if(frst == eps) continue;
                            firsts[term].insert(frst);
                        }
                        if(hasEps(firsts[rule[trm]]))     continue;
                    }
                    nxtIsFirst = 0;
                }
                if(nxtIsFirst)  firsts[term].insert("‘‘");
            }
        }

        void findFollow(string term){
            //Follow of the term is already calculated
            if(follows[term].size()>0)  return;
            if(rules[0][0] == term) follows[term].insert("$");
            for(auto rule : rules){
                bool nxtIsFollow = 0;
                bool flag = 0;
                for(int i=1;i<rule.size();i++){
                    if(rule[i] == term){
                        nxtIsFollow = 1;
                        continue;
                    }
                    if(!nxtIsFollow)  continue;
                    if(rule[i] == "|")  flag = 1;
                    for(auto frst : firsts[rule[i]]){
                        if(frst == eps) continue;
                        follows[term].insert(frst);
                    }
                    if(hasEps(firsts[rule[i]]))   continue;
                    nxtIsFollow = 0;
                }
                if(!nxtIsFollow && !flag) continue;
                findFollow(rule[0]);
                for(auto fllw : follows[rule[0]]){
                    follows[term].insert(fllw);
                }
            }
        }

        void constructTable(){
            vector<string>columns, row;
            columns.push_back(" ");
            for(auto trm : trmnls){
                if(trm == eps)  continue;
                columns.pb(trm);
            }

            parseTable.pb(columns);

            string rowCnt;
            for(auto rule: rules){
                row.assign(columns.size(), "0");
                bool takeFirst = 1;
                for(int i=0;i<rule.size();i++){
                    if(i == 0){
                        row[0] = rule[0];
                        continue;
                    }
                    if(takeFirst){
                        int idx = i;
                        rowCnt += rule[i];
                        while(idx+1<rule.size() && rule[idx+1] != "|") idx++, rowCnt += ' ', rowCnt += rule[idx];
                        if(hasEps(firsts[rule[i]])){
                            for(int trm = 0;trm<columns.size();trm++){
                                if(follows[rule[0]].find(columns[trm]) != follows[rule[0]].end()){
                                    row[trm] = rowCnt;
                                }
                            }
                        }
                        for(int trm = 0;trm<columns.size();trm++){
                            if(firsts[rule[i]].find(columns[trm]) != firsts[rule[i]].end()){
                                row[trm] = rowCnt;
                            }
                        }
                        takeFirst = 0;
                        rowCnt = "";
                    }
                    if(rule[i] == "|")  takeFirst = 1;
                }
                parseTable.pb(row);
                rowCnt = "";
            }
        }

        void solve(){
            lefFactoring();
            elimLeftRec();

            puts("Grammar parsed:");
            for(int i=0;i<rules.size();i++){
                cout<<i+1<<". ";
                for(int j=0;j<rules[i].size();j++){
                    cout<<rules[i][j]<<" ";
                    if(j == 0)  cout<<"-> ";
                }
                cout<<"\n";
            }
            puts("");

            cout<<"The non terminals in the grammar are: ";
            for(auto trm: nonTrmnls)    cout<<trm<<" ";     cout<<"\n\n";

            cout<<"The terminals in the grammar are: ";
            for(auto trm : trmnls)      cout<<trm<<" ";     cout<<"\n\n";

            for(auto trm : trmnls) firsts[trm].insert(trm);
            trmnls.insert("$");

            puts("Firsts list:");
            for(auto nonTrm : nonTrmnls){
                findFirst(nonTrm);
                cout<<nonTrm<<": ";
                for(auto str : firsts[nonTrm])  cout<<str<<" ";     cout<<"\n";
            }

            puts("");

            puts("Follows list:");
            for(auto rule:rules){
                cout<<rule[0]<<": ";
                findFollow(rule[0]);
                for(auto str : follows[rule[0]])  cout<<str<<" ";     cout<<"\n";
            }

            puts("");

            constructTable();
            puts("Parse Table:");
            for(auto row:parseTable){
                for(auto cell : row){
                    cout<<cell<<" ";
                    for(int i=cell.size();i<7;i++)  cout<<" ";
                }
                cout<<"\n";
            }

            puts("");
        }

        void parse(string str){
            vector<string> input = stovecofs(str);
            reverse(input.begin(), input.end());

            stack<string>parseStk, inputStk;
            parseStk.push("$");
            parseStk.push(rules[0][0]);

            inputStk.push("$");
            for(auto trm : input)   inputStk.push(trm);

            cout<<"Tracing for sample parsing: \""<<str<<"\"\n";

            string prvRule = " ";
            while(parseStk.size() && inputStk.size()){
                printStk(parseStk);         printStk(inputStk);     cout<<prvRule<<"\n";
                string stktp = parseStk.top();
                string inpttp = inputStk.top();
                parseStk.pop();

                for(auto row : parseTable){
                    if(row[0] == stktp){
                        for(int i=1;i<row.size();i++){
                            if(parseTable[0][i] == inpttp){
                                prvRule = row[0];       prvRule += " -> ";
                                prvRule += row[i];
                                if(row[i] == eps)   continue;
                                vector<string>trms = stovecofs(row[i]);
                                reverse(trms.begin(), trms.end());
                                for(auto trm : trms) parseStk.push(trm);
                            }
                        }
                    }
                }
                if(inpttp == parseStk.top()){
                    printStk(parseStk);         printStk(inputStk);     cout<<prvRule<<"\n";
                    prvRule = " ";
                    inputStk.pop();       parseStk.pop();
                }
                if(parseStk.top() == "$" && inputStk.top() == "$")  break;
            }
        }


};

vector<string> vecs{"E -> T E'",
                    "E' -> + T E'",
                    "E' -> ‘‘",
                    "T -> F T'",
                    "T' -> * F T'",
                    "T' -> ‘‘",
                    "F -> ( E )",
                    "F -> id"
};

int main(){
    cfg grammar(vecs);
    grammar.solve();
    grammar.parse("id + id");
    return 0;
}

