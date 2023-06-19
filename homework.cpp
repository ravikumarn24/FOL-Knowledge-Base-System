#include<bits/stdc++.h>

using namespace std;

void printIntVector(vector<int> &list){
    for(int i=0;i<list.size();i++){
        cout<<list[i]<<", ";
    }
}

void printStringVector(vector<string> &list){
    for(int i=0;i<list.size();i++){
        cout<<list[i]<<", ";
    }
}

void printStringVectorIntMap(map<string, vector<int> > &mp){
    map<string, vector<int> >::iterator itr;
    for(itr = mp.begin(); itr != mp.end();itr++){
            cout<<itr->first<<" / ";
            for(int i=0;i<itr->second.size();i++){
                cout<<itr->second[i]<<",";
            }
            cout<<" :: ";
     }
}

struct FunctionData {
    string function;
    vector<string> args;

    void printFunctionData(){
        cout<<endl;
        cout<<"------Function : "<<function<<endl;
        cout<<"------Args : ";
        printStringVector(args);
        cout<<endl;
    }
};

struct ORData{
    vector<string> orLiterals;
    vector<FunctionData> orFuncs;
    map<string, vector<int> > literalPos; // literal label to literal pos mapping
    map<string, vector<int> > funcPos;
    map<string, vector<int> > literalNeg;
    map<string, vector<int> > funcNeg;
    bool tautology;

    ORData(){
        tautology = false;
    }

    void printORData(){
        cout<<endl;
        cout<<"---OrLiterals : ";
        printStringVector(orLiterals);
        cout<<endl;
        cout<<"---OrFuncs : ";
        for(int i=0;i<orFuncs.size();i++){
            orFuncs[i].printFunctionData();
            cout<<endl;
        }
        cout<<endl;
        cout<<"---LiteralPos : ";
        printStringVectorIntMap(literalPos);
        cout<<"---FuncPos : ";
        printStringVectorIntMap(funcPos);
        cout<<"---LiteralNeg : ";
        printStringVectorIntMap(literalNeg);
        cout<<"---FuncNeg : ";
        printStringVectorIntMap(funcNeg);
        cout<<endl;

    }
};



struct KBInput {
    int size;
    string query;
    vector<ORData> stmts;
    map<string,vector<int> > literalPositive; // Literal label to stmt mapping 
    map<string,vector<int> > literalNegative;
    map<string,vector<int> > funcPositive;
    map<string,vector<int> > funcNegative;

    void printInput(){
        cout<<"Size : "<<size<<endl;
        cout<<"Query : "<<query<<endl;
        for(int i=0;i<stmts.size();i++){
            stmts[i].printORData();
            cout<<endl;
        }
        cout<<endl;
        cout<<"LiteralPositive : ";
        printStringVectorIntMap(literalPositive);
        cout<<"FuncPositive : ";
        printStringVectorIntMap(funcPositive);
        cout<<"LiteralNegative : ";
        printStringVectorIntMap(literalNegative);
        cout<<"FuncNegative : ";
        printStringVectorIntMap(funcNegative);
        cout<<endl;

    }
};

vector<string> splitBasedOnChar(string &stmt, char splitChar){
    string tmp = "";
    vector<string> result;

    for(int i=0;i<stmt.size();i++){
        char c = stmt[i];
        if(c == splitChar){
            result.push_back(tmp);
            tmp = "";
        }
        else if(c == ' '){
            // Ignore Space
            continue;
        }
        else{
            tmp += c;
        }
    }
    if(tmp != ""){
        result.push_back(tmp);
    }
    return result;

}


vector<string> dedupeList(vector<string> &literals){
    vector<string> result;
    set<string> literalNames;
    for(int i=0;i<literals.size();i++){
        if(literalNames.find(literals[i]) != literalNames.end()){
            continue;
        }
        if(literalNames.find("~"+literals[i]) != literalNames.end() ||
            (literals[i][0] == '~' && literalNames.find(literals[i].substr(1, string::npos)) != literalNames.end())){
                // Overall True scenario as it has both negated and non-negated component as ORs
                // So no use in going ahead with this OR List - Returning empty list
                vector<string> tmp;
                return tmp;
        }
        result.push_back(literals[i]);
        literalNames.insert(literals[i]);
    }
    return result;
}

vector<string> convertORListToCNF(vector<string> &orList){
    vector<string> cnfList;
    for(int t=0;t < orList.size();t++){
            string orLiteral = orList[t];
            vector<string> andList =splitBasedOnChar(orLiteral, '&');
            
            if(andList.size() == 1){
                if(cnfList.size() == 0){
                    cnfList.push_back(andList[0]);
                    continue;
                }
                for(int i=0;i<cnfList.size();i++){
                    cnfList[i] += " | " + andList[0];
                }
            }
            else{
                if(cnfList.size() == 0){
                    for(int i=0;i<andList.size();i++){
                        string andLiteral = andList[i];
                        cnfList.push_back(andLiteral);
                    }
                    continue;
                }
                vector<string> tmpList = cnfList;
                for(int i=0;i<tmpList.size();i++){
                    cnfList[i] += " | " + andList[0];
                }
                for(int i=0;i<tmpList.size();i++){
                    for(int j=1;j<andList.size();j++){
                        cnfList.push_back(tmpList[i] + " | " + andList[j]);
                    }
                }
            }
         }
    return cnfList;

}

// start - inclusive , end - exclusive
/*
    A ^ B V C = (A V C) ^ (B V C) ^ D 
*/
vector<string> convertLogicToCNF(string &statement, int start, int end){
    int leftIdx = -1, rightIdx = -1;
    string stmt = statement.substr(start,end - start); // statement in focus;
    for(int i=0;i+1<stmt.length();i++){
        // Taking the last implies , working backwards 
         if(stmt[i] == '=' && stmt[i+1] == '>'){
              leftIdx = i;
              rightIdx = i+2;
         }
    }
    if(leftIdx != -1){
         vector<string> finalList;
         vector<string> leftHalf = convertLogicToCNF(stmt,0,leftIdx);
         vector<string> rightHalf = convertLogicToCNF(stmt, rightIdx, end); 
         // ~(leftHalf) | (rightHalf)
         vector<string> orList;
         for(int i=0;i<leftHalf.size();i++){
           // each string part of CNF
            vector<string> literals = splitBasedOnChar(leftHalf[i],'|');
            string negatedClause = "";
            for(int j=0;j<literals.size();j++){
                if(negatedClause != ""){
                    negatedClause += " & ";
                }
                negatedClause += "~"+literals[j];
                
            }
            orList.push_back(negatedClause);
         }
         // (LeftHalf | ((A | B | C) & (D | E))) 
         // leftHalf OR List = X 
         // X | ((A | B | C) & (D| E))
         // (X| A| B| C) & (X | D| E)
         for(int i=0;i<rightHalf.size();i++){
            vector<string> tmpList = orList;
            vector<string> rightHalfLiterals = splitBasedOnChar(rightHalf[i], '|');
            for(int j=0;j<rightHalfLiterals.size();j++){
                tmpList.push_back(rightHalfLiterals[j]);
            }
            vector<string> clauseCnfList = convertORListToCNF(tmpList);
            for(int j=0;j<clauseCnfList.size();j++){
                finalList.push_back(clauseCnfList[j]);
            }
         }
         finalList = dedupeList(finalList);
         return finalList;
    }
    else{
         vector<string> orList = splitBasedOnChar(stmt, '|');
         vector<string> cnfList = convertORListToCNF(orList);
         cnfList = dedupeList(cnfList);
         return cnfList;
    }
    
}

vector<string> simplifyLiterals(vector<string> &literals){
    vector<string> result;
    for(int i=0;i<literals.size();i++){
        int negationCount = 0;
        for(int j=0;j<literals[i].size();j++){
            if(literals[i][j] != '~'){
                break;
            }
            negationCount++;
        }
        
        if(negationCount & 1){
            result.push_back(literals[i].substr(negationCount-1,string::npos)); 
        }
        else{
            result.push_back(literals[i].substr(negationCount,string::npos));
        }
    }
    return result;
}

string getLiteralLabel(string &literal){
    string label = "";
    for(int i=0;i<literal.length();i++){
        if(literal[i] == '~'){
            continue;
        }
        if(literal[i] == '('){
            break;
        }
        label += literal[i];
    }
    return label;
}

// This assumes that all the literals have been simplified with respect to negation
bool isLiteralNegative(string &queryLiteral){
    return queryLiteral[0] == '~';
}

// If literal length is same as label, its not a func, else its a func
bool isLiteralFunc(string &queryLiteral, string &literalLabel){
    int skipChar = literalLabel.length();
    if(queryLiteral[0] == '~'){
        skipChar++;
    }
    return queryLiteral.length() > skipChar;
}

vector<string> extractArgs(string &literal){
    bool openBraces = false;
    vector<string> args;
    string arg = "";
    for(int i=0;i<literal.length();i++){
        if(literal[i] == '('){
            openBraces = true;
        }
        else if(literal[i] ==')'){
            args.push_back(arg);
            arg = "";
            openBraces = false;
        }
        else if(openBraces){
            if(literal[i] == ','){
                args.push_back(arg);
                arg = "";
            }
            else if(literal[i] == ' '){
                // skip 
                continue;
            }
            else{
                arg += literal[i];
            }

        }
    }
    return args;
}

FunctionData getFunctionData(string &literal){
    FunctionData funcData;
    funcData.function = literal;
    funcData.args = extractArgs(literal);
    return funcData;
}

KBInput readInput(){
    ifstream f("input.txt");
    KBInput inputData;
    if(!f.is_open()){
        cout<<"UNABLE TO OPEN input.txt file, Aborting\n";
        exit(1);
    }
    // Added Get line here
    getline(f,inputData.query);
    // cout<<inputData.query<<endl;
    f >> inputData.size;
    string tmp;
    getline(f,tmp); // Get new line after token based extraction
    for(int i=0;i<inputData.size;i++){

         getline(f,tmp);  
         vector<string> cnf = convertLogicToCNF(tmp, 0, tmp.length());
         for(int t=0;t<cnf.size();t++){
            vector<string> temp = splitBasedOnChar(cnf[t], '|');
            vector<string> orLiterals = simplifyLiterals(temp);
            orLiterals = dedupeList(orLiterals);
            if(orLiterals.size() == 0){
                continue;
            }
            printStringVector(orLiterals);
            
            cout<<" :: \n";
            ORData orData;

            for(int j=0;j<orLiterals.size();j++){

                string literalLabel = getLiteralLabel(orLiterals[j]);
                bool isNegative = isLiteralNegative(orLiterals[j]);
                bool isFunc = isLiteralFunc(orLiterals[j], literalLabel);
                if(isFunc){
                    orData.orFuncs.push_back(getFunctionData(orLiterals[j]));
                }
                else{
                    orData.orLiterals.push_back(orLiterals[j]);
                }
                if(isNegative){
                    if(isFunc){
                        inputData.funcNegative[literalLabel].push_back(inputData.stmts.size());
                        orData.funcNeg[literalLabel].push_back(orData.orFuncs.size()-1);
                    }
                    else{
                        inputData.literalNegative[literalLabel].push_back(inputData.stmts.size());
                        orData.literalNeg[literalLabel].push_back(orData.orLiterals.size()-1);
                    }
                }
                else{
                    if(isFunc){
                        inputData.funcPositive[literalLabel].push_back(inputData.stmts.size());
                        orData.funcPos[literalLabel].push_back(orData.orFuncs.size()-1);
                    }
                    else{
                        inputData.literalPositive[literalLabel].push_back(inputData.stmts.size());
                        orData.literalPos[literalLabel].push_back(orData.orLiterals.size()-1);
                    }
                }
            }

            inputData.stmts.push_back(orData);
            
         }
         //cout<<endl;
    }
    
    f.close();
    return inputData;
}

void writeOutput(bool result){
    ofstream f("output.txt");
     if(!f.is_open()){
         cout<<"UNABLE TO OPEN output.txt file, Aborting\n";
         exit(1);    
     }
     if(result){
         f <<"TRUE";
          
     }
     else{
      f <<"FALSE"; 
        
     }
     f.close();
} 

vector<FunctionData> dedupeFuncList(vector<FunctionData> &functions){
    vector<FunctionData> result;
    set<string> funcNames;
    for(int i=0;i<functions.size();i++){
        string name = functions[i].function;
        if(funcNames.find(name) != funcNames.end()){
            continue;
        }
        if(funcNames.find("~"+name) != funcNames.end() ||
            (name[0] == '~' && funcNames.find(name.substr(1, string::npos)) != funcNames.end())){
                // Overall True scenario as it has both negated and non-negated component as ORs
                // So no use in going ahead with this OR List - Returning empty list
                vector<FunctionData> tmp;
                return tmp;
        }
        result.push_back(functions[i]);
        funcNames.insert(name);
    }
    return result;
}

void updateMapsBasedOnLists(ORData &orData){
    int prevLiteralsSize = orData.orLiterals.size();
    int prevFuncsSize = orData.orFuncs.size();
    orData.orLiterals = dedupeList(orData.orLiterals);
    orData.orFuncs = dedupeFuncList(orData.orFuncs);
    if((prevLiteralsSize >0 && orData.orLiterals.size() == 0) || (prevFuncsSize > 0 && orData.orFuncs.size() == 0)){
        orData.tautology = true;
    }
    for(int i=0;i<orData.orLiterals.size();i++){
        string literalLabel = getLiteralLabel(orData.orLiterals[i]);
        bool isNegative = isLiteralNegative(orData.orLiterals[i]);
        if(isNegative){
            orData.literalNeg[literalLabel].push_back(i);
        }
        else{
            orData.literalPos[literalLabel].push_back(i);
        }
    }
    for(int i=0;i<orData.orFuncs.size();i++){
        string funcLabel = getLiteralLabel(orData.orFuncs[i].function);
        bool isNegative = isLiteralNegative(orData.orFuncs[i].function);
        if(isNegative){
            orData.funcNeg[funcLabel].push_back(i);
        }
        else{
            orData.funcPos[funcLabel].push_back(i);
        }
    }
}

ORData convertLiteralToORData(string &literal){
    ORData orData;
    string literalLabel = getLiteralLabel(literal);
    bool isNegative = isLiteralNegative(literal);
    bool isFunc = isLiteralFunc(literal, literalLabel);
    if(isNegative && isFunc){
        // negative func;
        orData.orFuncs.push_back(getFunctionData(literal));
        orData.funcNeg[literalLabel].push_back(0);
    }
    else if(isNegative){
        // negative literal;
        orData.orLiterals.push_back(literal);
        orData.literalNeg[literalLabel].push_back(0);
    }
    else if(isFunc){
        // positive func;
        orData.orFuncs.push_back(getFunctionData(literal));
        orData.funcPos[literalLabel].push_back(0);
    }
    else{
        // positive literal;
        orData.orLiterals.push_back(literal);
        orData.literalPos[literalLabel].push_back(0);
    }
    return orData;
}

bool areArgsUnifiable(vector<string> &a, vector<string> &b){
    bool unifiable = true;
    if(a.size() != b.size()){
        return false;
    }
    map<string,string> assignment;
    for(int l=0;l<a.size();l++){
        bool noAddition = true;
        for(int i=0;i<a.size();i++){
            string currA = a[i];
            string currB = b[i];
            if(assignment.find("a_"+currA) != assignment.end()){
                currA = assignment["a_"+currA];
            }
            if(assignment.find("b_"+currB) != assignment.end()){
                currB = assignment["b_"+currB];
            }
            bool upperA = currA[0] >= 'A' && currA[0] <= 'Z';
            bool upperB = currB[0] >= 'A' && currB[0] <= 'Z';
            if(upperA && upperB && currA != currB){
                return false;
            }
            if(upperA && !upperB){
                assignment["b_"+currB] = currA;
                noAddition = false;
            }
            if(!upperA && upperB){
                assignment["a_"+currA] = currB;
                noAddition = false;
            }
        }
        if(noAddition){
            return true;
        }
    }

    return unifiable;
}

// Eg: Func1(a,b,a), Func1(c,d,d)
map<string,string> unifyArgs(vector<string> &a, vector<string> &b){
    map<string,string> assignment;
    for(int l=0;l<a.size();l++){
        bool noAddition = true;
        for(int i=0;i<a.size();i++){
            string currA = a[i];
            string currB = b[i];
            if(assignment.find("a_"+currA) != assignment.end()){
                currA = assignment["a_"+currA];
            }
            if(assignment.find("b_"+currB) != assignment.end()){
                currB = assignment["b_"+currB];
            }
            bool upperA = currA[0] >= 'A' && currA[0] <= 'Z';
            bool upperB = currB[0] >= 'A' && currB[0] <= 'Z';
            if(upperA && !upperB){
                assignment["b_"+currB] = currA;
                noAddition = false;
            }
            if(!upperA && upperB){
                assignment["a_"+currA] = currB;
                noAddition = false;
            }
        }
        if(noAddition){
            break;
        }
    }

    vector< set<string> > disjointSet;
    for(int i=0;i<a.size();i++){
        string currA = a[i];
        string currB = b[i];
        if(assignment.find("a_"+currA) != assignment.end()){
            currA = assignment["a_"+currA];
        }
        if(assignment.find("b_"+currB) != assignment.end()){
            currB = assignment["b_"+currB];
        }
        bool upperA = currA[0] >= 'A' && currA[0] <= 'Z';
        bool upperB = currB[0] >= 'A' && currB[0] <= 'Z';
        int aPos = -1, bPos = -1;
        if(!upperA && !upperB){
            for(int j=0;j<disjointSet.size();j++){
                if(disjointSet[j].find("a_"+currA) != disjointSet[j].end()){
                    aPos = j;
                }
                if(disjointSet[j].find("b_"+currB) != disjointSet[j].end()){
                    bPos = j;
                }
            }
            if( aPos ==-1 && bPos == -1){
                set<string> strSet;
                strSet.insert("a_"+currA);
                strSet.insert("b_"+currB);
                disjointSet.push_back(strSet);
            }
            else if(aPos == -1){
                disjointSet[bPos].insert("a_"+currA);
            }
            else if(bPos == -1){
                disjointSet[aPos].insert("b_"+currB);
            }
            else{
                disjointSet[aPos].insert(disjointSet[bPos].begin(), disjointSet[bPos].end());
                disjointSet.erase(disjointSet.begin() + bPos);
            }
        }
    }
    for(int i=0;i<disjointSet.size();i++){
        set<string>::iterator itr;
        for(itr = disjointSet[i].begin(); itr != disjointSet[i].end();itr++){
            assignment[*itr] = (char)('a' + i);
        }
    }

    return assignment;
}

string constructFunctionString(string &oldFunc, vector<string> &args){
    string newVal = "";
    for(int i=0;i<oldFunc.length();i++){
        if(oldFunc[i] == '('){
            break;
        }
        newVal += oldFunc[i];
    }
    newVal += "(";
    for(int i=0;i<args.size();i++){
        newVal += args[i];
        if(i+1 < args.size()){
            newVal += ",";
        }
    }
    newVal += ")";
    return newVal;

}

vector< pair<int,int> > findFunctionMatches(KBInput &input, vector<int> &stmtsWithOppositeLiteral, FunctionData &queryFunc, string &funcLabel, bool isNegative){
    vector<pair<int,int> > matches;
    for(int i=0;i<stmtsWithOppositeLiteral.size();i++){
        int idx = stmtsWithOppositeLiteral[i];
        ORData orData = input.stmts[idx];
        vector<int> orFuncIdxs;
        if(isNegative){
            orFuncIdxs =  orData.funcPos[funcLabel];
        }
        else{
            orFuncIdxs = orData.funcNeg[funcLabel];
        }
        bool unifiable = false;
        int second = -1;
        for(int j=0;j<orFuncIdxs.size();j++){
            int idx = orFuncIdxs[j];
            FunctionData funcData = orData.orFuncs[idx]; 
            unifiable |= areArgsUnifiable(queryFunc.args, funcData.args);
            if(unifiable){
                second = idx;
                break;
            }
        }
        if(unifiable){
            pair<int,int> posPair;
            posPair.first = idx; 
            posPair.second = second;
            matches.push_back(posPair);
        }
    }
    return matches;
}

ORData applyUnitResolutionForFuncs(ORData &queryStmt, ORData &inputStmt, int queryIdx, string &funcLabel, bool isNegative, int candidateIdx){
    ORData newStmt;
    string oppLabel = funcLabel;
    FunctionData inputFunc = inputStmt.orFuncs[candidateIdx];
    FunctionData queryFunc = queryStmt.orFuncs[queryIdx];

    map<string,string> assignments = unifyArgs(queryFunc.args, inputFunc.args); // unifyArgs(a,b);

    // Literals are not affected by Function Arg Assignments
    for(int i=0;i<queryStmt.orLiterals.size();i++){
        newStmt.orLiterals.push_back(queryStmt.orLiterals[i]);
    }
    for(int i=0;i<inputStmt.orLiterals.size();i++){
        newStmt.orLiterals.push_back(inputStmt.orLiterals[i]);
    }
    for(int i=0;i<queryStmt.orFuncs.size();i++){
        if(i == queryIdx){ 
            continue;
        }
        FunctionData newFunc;
        vector<string> funcArgs = queryStmt.orFuncs[i].args; 
        for(int j=0;j<funcArgs.size();j++){
            string arg = funcArgs[j];
            if(assignments.find("a_"+funcArgs[j]) != assignments.end()){
                arg = assignments["a_"+funcArgs[j]];
            }
            newFunc.args.push_back(arg);
        }
        newFunc.function = constructFunctionString(queryStmt.orFuncs[i].function,newFunc.args);
        newStmt.orFuncs.push_back(newFunc);
    }

    for(int i=0;i<inputStmt.orFuncs.size();i++){
        if(i == candidateIdx){
            continue;
        }
        FunctionData newFunc;
        vector<string> funcArgs = inputStmt.orFuncs[i].args; 
        for(int j=0;j<funcArgs.size();j++){
            string arg = funcArgs[j];
            if(assignments.find("b_"+funcArgs[j]) != assignments.end()){
                arg = assignments["b_"+funcArgs[j]];
            }
            newFunc.args.push_back(arg);
        }
        newFunc.function = constructFunctionString(inputStmt.orFuncs[i].function,newFunc.args);
        newStmt.orFuncs.push_back(newFunc);
    }

    updateMapsBasedOnLists(newStmt);
    
    return newStmt;
}

ORData applyUnitResolutionForLiterals(ORData &queryStmt, ORData &inputStmt, string &queryLiteral, string &literalLabel, bool isNegative){
    ORData newStmt;
    string oppLiteral = "~"+queryLiteral;
    if(isNegative){
        oppLiteral = queryLiteral.substr(1,string::npos);
    }
    // Functions are not affected by Literal Unit Resolution
    for(int i=0;i<queryStmt.orFuncs.size();i++){
        newStmt.orFuncs.push_back(queryStmt.orFuncs[i]);
    }
    for(int i=0;i<inputStmt.orFuncs.size();i++){
        newStmt.orFuncs.push_back(inputStmt.orFuncs[i]);
    }
    for(int i=0;i<queryStmt.orLiterals.size();i++){
        if(queryLiteral == queryStmt.orLiterals[i]){ 
            continue;
        }
        newStmt.orLiterals.push_back(queryStmt.orLiterals[i]);
    }

    for(int i=0;i<inputStmt.orLiterals.size();i++){
        if(oppLiteral == inputStmt.orLiterals[i]){
            continue;
        }
        newStmt.orLiterals.push_back(inputStmt.orLiterals[i]);
    }

    updateMapsBasedOnLists(newStmt);
    
    return newStmt;

}


map<string,bool> visited;
long long dfsCount = 0;

string constructORDataString(ORData &queryStmt){
    string stringifiedORData = "";
    vector<string> orLiterals = queryStmt.orLiterals;
    sort(orLiterals.begin(), orLiterals.end());
    for(int i=0;i<orLiterals.size();i++){
        stringifiedORData += "l_"+orLiterals[i]+",";
    }
    vector<string> funcNames;
    for(int i=0;i<queryStmt.orFuncs.size();i++){
        funcNames.push_back(queryStmt.orFuncs[i].function);
    }
    sort(funcNames.begin(),funcNames.end());
    for(int i=0;i<funcNames.size();i++){
        stringifiedORData += "f_"+funcNames[i]+",";
    }
    return stringifiedORData;
}

void addORDataToKB(ORData &orData, KBInput &input){
    input.stmts.push_back(orData);
    int idx = input.stmts.size() -1;
    map<string, vector<int> >:: iterator itr;
    for(itr = orData.funcNeg.begin(); itr != orData.funcNeg.end();itr++){
        input.funcNegative[itr->first].push_back(idx);
    }
    for(itr = orData.funcPos.begin(); itr != orData.funcPos.end();itr++){
        input.funcPositive[itr->first].push_back(idx);
    }
    for(itr = orData.literalNeg.begin(); itr != orData.literalNeg.end();itr++){
        input.literalNegative[itr->first].push_back(idx);
    }
    for(itr = orData.literalPos.begin(); itr != orData.literalPos.end();itr++){
        input.literalPositive[itr->first].push_back(idx);
    }
}

pair<bool,vector<ORData> >  performOp(ORData &queryStmt, KBInput &input){
    pair<bool,vector<ORData> > finalRes;
    // Stop DFS after using all the input stmts;
    dfsCount++;
    if(queryStmt.orLiterals.size() == 0 && queryStmt.orFuncs.size() == 0){
        finalRes.first = true;
        return finalRes;
    }


    // Find matches for queryStmt;
    for(int i=0;i<queryStmt.orLiterals.size();i++){
        string queryLiteral = queryStmt.orLiterals[i];
        string literalLabel = getLiteralLabel(queryLiteral);
        
        bool isNegative = isLiteralNegative(queryLiteral);

        vector<int> stmtsWithOppositeLiteral;
        if(isNegative){
            stmtsWithOppositeLiteral = input.literalPositive[literalLabel];
        }
        else{
            stmtsWithOppositeLiteral = input.literalNegative[literalLabel];
        }

        vector<int> candidates = stmtsWithOppositeLiteral;
        for(int j=0;j<candidates.size();j++){
            ORData newQueryStmt = applyUnitResolutionForLiterals(queryStmt,input.stmts[candidates[j]], queryLiteral, literalLabel, isNegative);
            if(newQueryStmt.tautology){
                // Skipping if the query stmt is itself a tautology
                continue;
            }
            string stringifiedORData = constructORDataString(newQueryStmt);
            if(visited[stringifiedORData]){
                continue;
            }
            visited[stringifiedORData] = true;
            
            if(newQueryStmt.orLiterals.size() == 0 && newQueryStmt.orFuncs.size() == 0){
                finalRes.first = true;
                return finalRes;
            }
            finalRes.second.push_back(newQueryStmt);
        }
    }

    // Find func matches for queryStmt;
    for(int i=0;i<queryStmt.orFuncs.size();i++){
        string queryFunc = queryStmt.orFuncs[i].function;
        string funcLabel = getLiteralLabel(queryFunc);
        
        bool isNegative = isLiteralNegative(queryFunc);

        vector<int> stmtsWithOppositeLiteral;
        if(isNegative){
            stmtsWithOppositeLiteral = input.funcPositive[funcLabel];
        }
        else{
            stmtsWithOppositeLiteral = input.funcNegative[funcLabel];
        }

        
        vector< pair<int,int> > candidates = findFunctionMatches(input, stmtsWithOppositeLiteral, queryStmt.orFuncs[i], funcLabel, isNegative);
        //cout<<"Level "<<currDepth<<" = candidate count : "<<candidates.size()<<endl;
        for(int j=0;j<candidates.size();j++){
            ORData newQueryStmt = applyUnitResolutionForFuncs(queryStmt,input.stmts[candidates[j].first], i, funcLabel, isNegative, candidates[j].second);
            if(newQueryStmt.tautology){
                // Skipping if the query stmt is itself a tautology
                continue;
            }
            string stringifiedORData = constructORDataString(newQueryStmt);
            if(visited[stringifiedORData]){
                continue;
            }
            visited[stringifiedORData] = true;

            if(newQueryStmt.orLiterals.size() == 0 && newQueryStmt.orFuncs.size() == 0){
                finalRes.first = true;
                return finalRes;
            }

            finalRes.second.push_back(newQueryStmt);
        }
    }
   
    return finalRes;
}

class CustomComparator {
 
    public:
     bool operator()(ORData &a, ORData &b){
           if(a.orFuncs.size() + a.orLiterals.size() == b.orFuncs.size() + b.orLiterals.size()){
                return a.orFuncs.size() > b.orFuncs.size();
           }
           return a.orFuncs.size() + a.orLiterals.size() > b.orFuncs.size() + b.orLiterals.size() ;
     }
};

bool query(KBInput &input){
    bool result = false;
    vector<string> tmp;
    int skipSpace = 0;
    for(int i=0;i<input.query.length();i++){
        if(input.query[i] != ' '){
            break;
        }
        skipSpace++;
    }

    string q = input.query.substr(skipSpace,string::npos);
    input.query = q;
    tmp.push_back("~" + input.query);
    tmp = simplifyLiterals(tmp);
    ORData queryStmt = convertLiteralToORData(tmp[0]);
    int maxDepth = 1;
    dfsCount = 0;
    priority_queue<ORData, vector<ORData>, CustomComparator> pq;
    pq.push(queryStmt);
    int maxLimit = 5000000;
    int currSize = 0;
    addORDataToKB(queryStmt,input);
    for(int i=0;i<input.stmts.size();i++){
        string stringifiedORData = constructORDataString(input.stmts[i]);
        visited[stringifiedORData] = true;
    }
    while(!pq.empty()){
       currSize++;
       ORData stmt = pq.top(); 
       pq.pop();
       pair<bool, vector<ORData> > childrenPair = performOp(stmt, input);
       if(childrenPair.first){
        return true;
       }
       for(int i=0;i<childrenPair.second.size();i++){
        pq.push(childrenPair.second[i]);
        int unitClause = childrenPair.second[i].orFuncs.size() + childrenPair.second[i].orLiterals.size();
        if(unitClause == 1){ // Add to the Knowledge base
            addORDataToKB(childrenPair.second[i], input);
        }
       }
       if(pq.size() > maxLimit){
         break;
       }
    }
    return result; 
        
}

int main(){
     KBInput input = readInput();
    //  input.printInput();
     bool result = query(input);
    //  cout<<result<<endl;
     writeOutput(result);
}