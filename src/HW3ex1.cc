#include <errno.h>
#include <signal.h>
#include <sstream>
#include <fstream>
#include <algorithm>
#include <stdio.h>
#include <iostream>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <cstring>   // for strcmp
#include "hcm.h"
#include "flat.h"
#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"

using namespace std;
using namespace Minisat;

// globals
bool verbose = false;

// Extract primary ports from a top-level cell (PIs and POs)
void extractPorts(hcmCell* cell, vector<string>& inputs, vector<string>& outputs) {
    for (auto port : cell->getPorts()) {
        if (port->getDirection() == IN)
            inputs.push_back(port->getName());
        else if (port->getDirection() == OUT)
            outputs.push_back(port->getName());
    }
}

// Extract instportports from an instance
void extractPorts(hcmInstance* instance, vector<string>& inputs, vector<string>& outputs) {
    for (auto instport : instance->getInstPorts()) {
        if (instport.second->getPort()->getDirection() == IN)
            inputs.push_back(instport.second->getNode()->getName());
        else if (instport.second->getPort()->getDirection() == OUT)
            outputs.push_back(instport.second->getNode()->getName());
    }
}

// A helper function to obtain the variable for a given signal name.
// If the signal is "VDD" or "VSS", we create a variable and then add
// a unit clause forcing it to 1 or 0 respectively.
Var getOrCreateVar(const string& sig,
                   Solver& solver,
                   map<string, Var>& varMap) {
    // If already present, return it.
    if (varMap.find(sig) != varMap.end())
        return varMap[sig];

    // For constant nets, create the variable and force its value.
    if (sig == "VDD") {
        Var v = solver.newVar();
        varMap[sig] = v;
        // Force v to be true: add clause (v)
        solver.addClause(mkLit(v));
        return v;
    }
    if (sig == "VSS") {
        Var v = solver.newVar();
        varMap[sig] = v;
        // Force v to be false: add clause (~v)
        solver.addClause(~mkLit(v));
        return v;
    }
    // Otherwise, create a new variable.
    Var v = solver.newVar();
    varMap[sig] = v;
    return v;
}

//--------------------------------------------------------------------
// This function generates CNF clauses for the circuit in 'cell'.
// Primary inputs (if their names are in the set primaryInputs) 
// are shared using the globalInputMap.
// Function to generate CNF from circuit logic
void generateCNF(hcmCell* cell, Solver& solver, map<string, Var>& varMap,
                 const set<string>& primaryInputs, map<string, Var>& globalInputMap) {
    for (auto gate : cell->getInstances()) {
        vec<Lit> clause;
        clause.clear();
        string gateType = gate.second->masterCell()->getName();
        vector<string> inputs, outputs;
        extractPorts(gate.second, inputs, outputs);
        if (inputs.empty() || outputs.empty())
            continue;

        // Create variables for inputs and outputs.
        for (const auto& input : inputs){
            if (primaryInputs.count(input)) {
                if (globalInputMap.find(input) == globalInputMap.end())
                    globalInputMap[input] = getOrCreateVar(input, solver, varMap);
                varMap[input] = globalInputMap[input];
            } else {
                getOrCreateVar(input, solver, varMap);
            }
        }
        for (const auto& output : outputs) {
            getOrCreateVar(output, solver, varMap);
        }

        // Apply CNF encoding for different gate types.
        if (gateType == "buffer") {
            // Buffer: Z = A
            solver.addClause(mkLit(varMap[inputs[0]]), ~mkLit(varMap[outputs[0]]));
            solver.addClause(~mkLit(varMap[inputs[0]]), mkLit(varMap[outputs[0]]));
        } else if (gateType == "inv" || gateType == "not") {
            // NOT: Z = ~A
            solver.addClause(~mkLit(varMap[inputs[0]]), ~mkLit(varMap[outputs[0]]));
            solver.addClause(mkLit(varMap[inputs[0]]), mkLit(varMap[outputs[0]]));
        } else if (gateType.rfind("nor", 0) == 0) {
            // NOR: Z = ~(A | B | ...)
            clause.push(mkLit(varMap[outputs[0]]));
            for (const auto& input : inputs) {
                clause.push(mkLit(varMap[input]));
                solver.addClause(~mkLit(varMap[input]), ~mkLit(varMap[outputs[0]]));
            }
            solver.addClause(clause);
        } else if (gateType.rfind("or", 0) == 0) {
            // OR: Z = A | B | ...
            clause.clear();
            clause.push(~mkLit(varMap[outputs[0]]));
            for (const auto& input : inputs) {
                clause.push(mkLit(varMap[input]));
                solver.addClause(~mkLit(varMap[input]), mkLit(varMap[outputs[0]]));
            }
            solver.addClause(clause);
        } else if (gateType.rfind("nand", 0) == 0) {
            // NAND: Z = ~(A & B & ...)
            clause.clear();
            clause.push(~mkLit(varMap[outputs[0]]));
            for (const auto& input : inputs) {
                clause.push(~mkLit(varMap[input]));
                solver.addClause(mkLit(varMap[input]), mkLit(varMap[outputs[0]]));
            }
            solver.addClause(clause);
        } else if (gateType.rfind("and", 0) == 0) {
            // AND: Z = A & B & ...
            clause.clear();
            clause.push(mkLit(varMap[outputs[0]]));
            for (const auto& input : inputs) {
                clause.push(~mkLit(varMap[input]));
                solver.addClause(mkLit(varMap[input]), ~mkLit(varMap[outputs[0]]));
            }
            solver.addClause(clause);
        } else if (gateType == "xor" || gateType == "xor2") {
            // XOR: Z = A ^ B (assumes exactly 2 inputs)
            solver.addClause(~mkLit(varMap[inputs[0]]), ~mkLit(varMap[inputs[1]]), ~mkLit(varMap[outputs[0]]));
            solver.addClause(mkLit(varMap[inputs[0]]), mkLit(varMap[inputs[1]]), ~mkLit(varMap[outputs[0]]));
            solver.addClause(mkLit(varMap[inputs[0]]), ~mkLit(varMap[inputs[1]]), mkLit(varMap[outputs[0]]));
            solver.addClause(~mkLit(varMap[inputs[0]]), mkLit(varMap[inputs[1]]), mkLit(varMap[outputs[0]]));
        } else if (gateType == "dff") {
            // D Flip-Flop: We *Do not add any constraint* so that the sequential behavior does not mask differences.
            // (Alternatively, add a fixed initial state, e.g., force Q = false.)
            // For now, we do nothing so that the combinational differences are visible.
            // If you want a fixed initial state, uncomment one of the lines below:
            // solver.addClause(~mkLit(varMap[outputs[0]]));  // forces Q = 0
            // or
            // solver.addClause(mkLit(varMap[outputs[0]]));   // forces Q = 1

        } else {
            cerr << "-E- Unsupported gate type: " << gateType << endl;
        }
    }
}

//--------------------------------------------------------------------
// For each output pair, create a new difference variable d that is true
// if and only if the spec and impl outputs differ. Then add a clause
// requiring that at least one difference is true.
// If SAT, print a counter-example (the primary input assignments).
bool checkEquivalence(Solver& solver, 
                      const vector<string>& primaryInputs,
                      const vector<string>& outputsSpec, const vector<string>& outputsImp,
                      const map<string, Var>& varMapSpec, const map<string, Var>& varMapImp) {
    vector<Var> diffVars;
    for (size_t i = 0; i < outputsSpec.size(); i++) {
        // Create a new variable for the difference between this pair.
        Var d = solver.newVar();
        diffVars.push_back(d);
        Lit s = mkLit(varMapSpec.at(outputsSpec[i]));
        Lit t = mkLit(varMapImp.at(outputsImp[i]));
        Lit dLit = mkLit(d);
        // Encode: d is true iff s XOR t is true.
        solver.addClause(~s, t, dLit);
        solver.addClause(s, ~t, dLit);
        solver.addClause(s, t, ~dLit);
        solver.addClause(~s, ~t, ~dLit);
    }
    // Force at least one difference to be true.
    vec<Lit> miterClause;
    for (Var d : diffVars)
        miterClause.push(mkLit(d));
    solver.addClause(miterClause);

    // Check for satisfiability.
    if (solver.solve()) {
        cout << "\nA counterexample was found:" << endl;
        cout << "Primary input assignment:" << endl;
        // For each primary input, print its assigned value.
        for (const auto& in : primaryInputs) {
            // We assume that the primary input is shared in varMapSpec.
            Var v = varMapSpec.at(in);
            lbool val = solver.modelValue(v);
            cout << in << " = " << (val == l_True ? "1" : (val == l_False ? "0" : "undef")) << endl;
        }
        cout << endl;
        return false;
    } else{
        cout << endl;
        return true;
    }
}

///////////////////////////////////////////////////////////////////////////
int main(int argc, char **argv) {
    int argIdx = 1;
    int anyErr = 0;
    unsigned int i;
    vector<string> specVlgFiles;
    vector<string> implementationVlgFiles;
    string specCellName;
    string implementationCellName;
    Solver solver;

    if (argc < 8) { 
        anyErr++;
    } else {
        if (!strcmp(argv[argIdx], "-v")) {
            argIdx++;
            verbose = true;
        }
        if (!strcmp(argv[argIdx], "-s")) {
            argIdx++;
            specCellName = argv[argIdx++];
            while (strcmp(argv[argIdx], "-i") != 0) {
                specVlgFiles.push_back(argv[argIdx++]);
            }
        }
        argIdx++;
        implementationCellName = argv[argIdx++];
        for (; argIdx < argc; argIdx++) {
            implementationVlgFiles.push_back(argv[argIdx]);
        }
        if (implementationVlgFiles.size() < 2 || specVlgFiles.size() < 2) {
            cerr << "-E- At least top-level and one verilog file are required for each model" << endl;
            anyErr++;
        }
    }
    if (anyErr) {
        cerr << "Usage: " << argv[0] << " [-v] -s top-cell spec_file1.v spec_file2.v -i top-cell impl_file1.v impl_file2.v ... \n";
        exit(1);
    }

    string fileName = specCellName + ".cnf";
    set<string> globalNodes;
    globalNodes.insert("VDD");
    globalNodes.insert("VSS");

    // spec hcm
    hcmDesign* specDesign = new hcmDesign("specDesign");
    for (i = 0; i < specVlgFiles.size(); i++) {
        printf("-I- Parsing verilog %s ...\n", specVlgFiles[i].c_str());
        if (!specDesign->parseStructuralVerilog(specVlgFiles[i].c_str())) {
            cerr << "-E- Could not parse: " << specVlgFiles[i] << " aborting." << endl;
            exit(1);
        }
    }
    hcmCell *topSpecCell = specDesign->getCell(specCellName);
    if (!topSpecCell) {
        printf("-E- could not find cell %s\n", specCellName.c_str());
		exit(1);
    }

    hcmCell *flatSpecCell = hcmFlatten(specCellName + string("_flat"), topSpecCell, globalNodes);

    // implementation hcm
    hcmDesign* impDesign = new hcmDesign("impDesign");
    for (i = 0; i < implementationVlgFiles.size(); i++) {
        printf("-I- Parsing verilog %s ...\n", implementationVlgFiles[i].c_str());
        if (!impDesign->parseStructuralVerilog(implementationVlgFiles[i].c_str())) {
            printf("-E- could not find cell %s\n", implementationCellName.c_str());
		    exit(1);
        }
    }

    hcmCell *topImpCell = impDesign->getCell(implementationCellName);
    if (!topImpCell) {
        cerr << "-E- Could not find cell " << implementationCellName << endl;
        exit(1);
    }

    hcmCell *flatImpCell = hcmFlatten(implementationCellName + string("_flat"), topImpCell, globalNodes);

  	//---------------------------------------------------------------------------------//
	//enter your code below

    // --- Extract primary inputs and outputs from both circuits ---
    vector<string> inputsSpec, outputsSpec, inputsImp, outputsImp;
    extractPorts(flatSpecCell, inputsSpec, outputsSpec);
    extractPorts(flatImpCell, inputsImp, outputsImp);

    sort(inputsSpec.begin(), inputsSpec.end());
    sort(inputsImp.begin(), inputsImp.end());
    sort(outputsSpec.begin(), outputsSpec.end());
    sort(outputsImp.begin(), outputsImp.end());
    if (inputsSpec != inputsImp || outputsSpec != outputsImp) {
        cout<< "Primary inputs/outputs do not match between spec and implementation! any input would be a counter example" << endl;
        return 1;
    }
    // For convenience, create a set of primary inputs.
    set<string> primaryInputs(inputsSpec.begin(), inputsSpec.end());

    // --- Prepare variable mappings ---
    map<string, Var> globalInputMap;   // Shared primary inputs.
    map<string, Var> varMapSpec, varMapImp; // Internal signals for each circuit.

    // Generate CNF for both circuits.
    generateCNF(flatSpecCell, solver, varMapSpec, primaryInputs, globalInputMap);
    generateCNF(flatImpCell, solver, varMapImp, primaryInputs, globalInputMap);

    // --- Perform equivalence check ---
    checkEquivalence(solver, inputsSpec, outputsSpec, outputsImp, varMapSpec, varMapImp);

 	//---------------------------------------------------------------------------------//
    solver.toDimacs(fileName.c_str());
    solver.simplify();
    bool sat = solver.solve();
    if (sat) {
        cout << "SATISFIABLE!" << endl;
    }
    else {
        cout << "NOT SATISFIABLE!" << endl;
    }
    return 0;
}
