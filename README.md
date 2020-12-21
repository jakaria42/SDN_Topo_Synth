# SDN_Topo_Synth
This project uses satisfiability modulo theories (SMT) to model a framework that creates a topology of hybrid network of traditional and SDN-enabled switches.
Microsoft Z3 library is used as an efficient SMT solver.

## Programming Language
This project is written in C# .net. For Z3 library, it uses the *Microsoft.Z3* package, which is freely available from Microsoft. See https://github.com/Z3Prover/z3/releases and https://github.com/Z3Prover/z3 for more info. See https://rise4fun.com/z3 for tutorials on Z3.

### Description
This project creates the Z3 clauses required for generating an efficient SDN topology for a synthetic SCADA network and solves them using the Z3 library. It takes inputs from a text file where the user can specify the network scenario along with the requirements and constraints. The output is printed in another text file where the user can see which traditional switches should be replaced with SDN-enabled switches to meet the requirements specified by the user.

This project basically creates Boolean SMT variables that corresponds to whether a switch should be replaced. There are other Boolean and Number variables that correspond to whether a link should be deployed or not given the budget constraints, etc. The solution, if available, assigns either True or False values to the Boolean variables which can then be mapped to the ultimate network topology.
