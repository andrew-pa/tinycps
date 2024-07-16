# Tiny-CPS

## Pipeline
- Input: "traditional" CPS IR

- Preprocess phase: trad-CPS → expanded CPS
    In this phase, all literal values are made explicit, so that terms only refer to bound variables.
    For instance, rather than having a "record literal term" that constructs a record, the record is constructed in a "create record" expression first, and then the expression containing the term is the continuation. Same with lambdas, integers.
    This obivates the creation of temporary register assignments in code generation.
    This phase should also do alphabetization so that each unique variable has a unique id.

- Closure conversion phase: expanded CPS → expanded CPS where no "create lambda" expressions exist
    This is a traditional closure conversion phase. All "create lambda" expressions are mapped to a "create record" expression that captures the free variables of the lambda. Lambda bodies are moved into a top-level function.

- Variable spill phase: closure converted xCPS → closure converted xCPS
    In this phase, the invariant that the number of bindings active at any point in a function is less than or equal to the number of machine registers. This is accomplished by introducing a "spill record" which stores the remaining variables, if any. Only one record is maintained in any function.

- Code generation phase: closure converted, expanded CPS → abstract instructions
    The codegen phase converts the continuation based control flow into a linear sequence of abstract instructions. It also assigns variables to registers, and implements the calling convention for the target architecture.

- Assembly phase: abstract instructions -> machine code
    The assembly phase translates abstract instructions into machine code for the target architecture. The bulk of this is the process of instruction selection. Additionally, the assembly phase calculates jumps to labels and deals with very low level details like manipulating the stack, allocating memory for records etc.

- Output: an object file containing the machine code for all functions in the module, ready for linking with the runtime/other modules

## Runtime
### The Stack

### The Heap
