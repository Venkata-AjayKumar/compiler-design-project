%{
    /*definitions*/
    #include <stdio.h>
    #include<string.h>
    #include<stdlib.h>
    #include<ctype.h>
    #include <limits.h>
    // #include"lex.yy.c"  // this is creating multiple definitions

    // Declaration of tree
    struct node {
        int num_children;       // Number of children
        struct node **children; // Array of pointers to child nodes
        char *token;            // Token associated with the node
    };

    struct node *head;
    struct node* mknode(int num_children, struct node **children, char *token) ;
    void printtree(struct node* tree);
    void printInorder(struct node *tree);
    void add(char);
    void insert_type();
    int search(char *);

    void check_declaration(char *);
	void check_return_type(char *);
	char *get_type(char *);
    char *get_datatype(char *);

    struct dataType {
        char * id_name;
        int used;   // for optimization stage - to check if the declared variable is used anywhere else in the program
        char * data_type;
        char * type;
        int line_no;
        int thisscope;
        int num_params;
        int range[10][2];  // [start index of first computation in icg,end index of assignment in icg for that chunk]
        int range_count;
    } symbol_table[10000];

    int count=0;
    int q;
    char type[10];
    extern int countn;
    extern int scope;
    int curr_num_params=0;
    int curr_num_args=0;
    extern char* yy_text;
    char exp_type[30];  // will be empty if no expression is there
    int sem_errors=0;
	char buff[10000];
	char errors[10][10000];
    int oldscope=-1;
    int performedConstantFolding=0;

    int firstexpvalue=-1000000,secondexpvalue=-1000000;

    // Intermediate code generation
    int ic_idx=0;    // used to index the intermediate 3 address codes to show them together later in output
	int label[10000];     // label stack to store the order of labels in the intermediate code
                        // label number in the intermediate code -> GOTO L4
                        // LABEL L4: ....
    int ifelsetracker=-1;  // used to store the ending label for an if-elseLadder
    int jumpcorrection[10000]; // jumpcorrection[instruction number] = label number after a if-else Ladder
    int lastjumps[10000];
    int lastjumpstackpointer=0;
    int laddercounts[10000];
    int laddercountstackpointer=0;

    int stackpointer=0; // used to index the label stack
    int labelsused=0;   // used to keep track of the number of labels used in the intermediate code
    int looplabel[10000]; // another stack
    int looplabelstackpointer=0; // another stack pointer
    int insNumOfLabel[10000]; // used to store the instruction number of each label

    int gotolabel[10000]; // another stack
    int gotolabelstackpointer=0; // another stack pointer
    
    int rangestart=-1,rangeend=-1;  // used to store the range of instructions for a chunk of variable declaration/assignment code temperorily
    int uselessranges[10000][2];  // used to store the range of instructions for a chunk of useless variable declaration/assignment code overall
    int uselessrangescount=0;

    char icg[10000][20];  // stores the intermediate code instructions themselves as strings
    int isleader[10000];  // stores whether the instruction is a leader or not
    int registerIndex=0;  // used to index the registers used in the intermediate code
    int registers[10000];   // stores the registers used in the intermediate code
    int regstackpointer=0; // used to index the register stack
    int firstreg=-1,secondreg=-1,thirdreg=-1; // used to track regIndices in exp*exp 

    //finish writing the reserved words,there are more reserved words
    const int reserved_count = 13;   // why is this not working for reserved[reserved_count][20]???
	char reserved[13][20] = {"int", "float", "char", "fun", "if", "elseif",
    "else", "while", "return", "thechko","cin>>","printf","string"};

    int stringToInt(const char *str) {
        int result = 0;
        int sign = 1;
        int i = 0;
        
        // Handling negative numbers
        if (str[0] == '-') {
            sign = -1;
            i = 1;
        }
        
        // Iterate through each character of the string
        for (; str[i] != '\0'; ++i) {
            // Ignore if it's a negative sign (already handled) or positive sign
            if (str[i] == '-' || str[i] == '+') {
                continue;
            }
            
            // Check if character is a digit
            if (str[i] >= '0' && str[i] <= '9') {
                // Update result by multiplying it by 10 and adding the digit
                result = result * 10 + (str[i] - '0');
            } else {
                // If non-digit character encountered, return 0 (or handle error as required)
                return 0;
            }
        }
        
        // Apply sign to the result
        return sign * result;
    }

    // Function to mark a variable as used if found in the symbol table
        void markVariableAsUsed(const char *id_name) {
            for (int i = 0; i < 10000; ++i) {
                if (symbol_table[i].id_name != NULL && strcmp(symbol_table[i].id_name, id_name) == 0) {
                    symbol_table[i].used = 1;
                    return;
                }
            }
        }

    // Function to search for an identifier in the symbol table and return its index if found
    int findIdentifierIndex(char *id_name) {
        for (int i = 0; i < 10000; i++) {
            if (symbol_table[i].id_name != NULL && strcmp(symbol_table[i].id_name, id_name) == 0) {
                return i; // Return the index if found
            }
        }
        return -1; // Return -1 if not found
    }

    // Function to swap two ranges
    void swapRanges(int range1[], int range2[]) {
        int tempStart = range1[0];
        int tempEnd = range1[1];
        range1[0] = range2[0];
        range1[1] = range2[1];
        range2[0] = tempStart;
        range2[1] = tempEnd;
    }

    // Function to sort the 2D array of ranges
    void sortRanges(int ranges[][2], int rangeCount) {
        for (int i = 0; i < rangeCount - 1; i++) {
            for (int j = 0; j < rangeCount - i - 1; j++) {
                if (ranges[j][0] > ranges[j + 1][0]) {
                    swapRanges(ranges[j], ranges[j + 1]);
                }
            }
        }
    }
    

%}

%error-verbose

%union { 
	struct var_name { 
		char name[10000]; 
		struct node* nd;
	} nd_obj; 
} 



%token<nd_obj> EOL cpp_INT cpp_FLOAT cpp_ARITHMETIC_OPERATOR cpp_COMPARISON_OPERATOR cpp_ASSIGNMENT_OPERATOR cpp_LOGICAL_OPERATOR 
%token<nd_obj> cpp_DATATYPE cpp_IF cpp_ELIF cpp_ELSE cpp_WHILE cpp_OPEN_FLOOR_BRACKET cpp_CLOSED_FLOOR_BRACKET
%token<nd_obj> cpp_IDENTIFIER cpp_STRING cpp_OPEN_CURLY_BRACKET cpp_CLOSED_CURLY_BRACKET cpp_OPEN_SQUARE_BRACKET cpp_CLOSED_SQUARE_BRACKET  
%token<nd_obj> cpp_PUNCTUATION_COMMA cpp_NEWLINE cpp_FINISH cpp_FUNCTION cpp_RETURN cpp_CHARACTER cpp_PRINT cpp_IMPORT cpp_INPUT

%type<nd_obj> program,input,exp,condition,if_statement,while_loop,variable_declaration,parameters_repeat,equation,parameters_line,function_declaration,function_content,bunch_of_statements,elif_repeat,
                else_statement,if_else_ladder,empty_lines,function_call,identifiers_line,identifiers_repeat,cpp_print,print_content,print_statement,cpp_constant
%type<nd_obj> cpp_identifier_declaring,eol,cpp_int, cpp_float, cpp_arithmetic_operator, cpp_comparison_operator, cpp_assignment_operator, cpp_logical_operator, cpp_datatype, cpp_if, cpp_elif, cpp_else,
                 cpp_while, cpp_identifier, cpp_string, cpp_open_curly_bracket, cpp_closed_curly_bracket, cpp_open_square_bracket, cpp_closed_square_bracket, cpp_open_floor_bracket, 
                 cpp_function_name,cpp_function_name_call,cpp_closed_floor_bracket, cpp_punctuation_comma, cpp_newline, cpp_finish, cpp_function, cpp_return, cpp_character,cpp_import,cpp_input,cpp_imported_library

%%
program:
    input {int num_children = 1;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        
        // Assigning children nodes
        children[0] = $1.nd;  // Assuming $1 represents the parse tree node for symbol1
        // Assign more children if needed
        
        // Create the parse tree node for the production rule
        $$.nd = mknode(num_children, children, "program");
         head = $$.nd;}


eol:
    EOL {$$.nd = mknode(NULL, NULL, "newline");}
cpp_identifier:
    cpp_IDENTIFIER {printf("CHECKING FOR %s\n",$1.name);check_declaration($1.name); printf("saw pure id2");$$.nd = mknode(NULL, NULL, $1.name);}

cpp_function_name:   // only for functions being declared
    cpp_IDENTIFIER {printf("parser saw cppFuncNamex");
    $$.nd = mknode(NULL, NULL, $1.name);}

cpp_function_name_call:   // only for functions being called
    cpp_IDENTIFIER {printf("parser saw cppFuncNameCall");
    $$.nd = mknode(NULL, NULL, $1.name);}

cpp_identifier_declaring:   // only for identifiers being declared
    cpp_IDENTIFIER { printf("saw varDeclareid");add('V');$$.nd = mknode(NULL, NULL, $1.name);}


cpp_imported_library:   // only for identifiers being declared
    cpp_IDENTIFIER { add('L');$$.nd = mknode(NULL, NULL, $1.name);}
cpp_print:
    cpp_PRINT {add('K');$$.nd = mknode(NULL, NULL, $1.name);}

cpp_int:
    cpp_INT {$$.nd = mknode(NULL, NULL, $1.name);add('i');}
cpp_input:  // cin>>   , scanf()
    cpp_INPUT {add('K');$$.nd = mknode(NULL, NULL, $1.name);}
cpp_float:
    cpp_FLOAT {add('f');$$.nd = mknode(NULL, NULL, $1.name);}

cpp_import:
    cpp_IMPORT {$$.nd = mknode(NULL, NULL, $1.name);}
cpp_constant:
    cpp_INT {$$.nd = mknode(NULL, NULL, $1.name);add('i');}
    | cpp_FLOAT {$$.nd = mknode(NULL, NULL, $1.name);add('f');}
    | cpp_STRING {$$.nd = mknode(NULL, NULL, $1.name);add('s');}
    | cpp_CHARACTER {$$.nd = mknode(NULL, NULL, $1.name);add('c');}


cpp_arithmetic_operator:
    cpp_ARITHMETIC_OPERATOR {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_comparison_operator:
    cpp_COMPARISON_OPERATOR {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_assignment_operator:
    cpp_ASSIGNMENT_OPERATOR {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_logical_operator:
    cpp_LOGICAL_OPERATOR {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_datatype:
    cpp_DATATYPE {insert_type();$$.nd = mknode(NULL, NULL, $1.name);}

cpp_if:
    cpp_IF {add('K');$$.nd = mknode(NULL, NULL, "if");}

cpp_elif:
    cpp_ELIF {add('K');$$.nd = mknode(NULL, NULL, "elif");}

cpp_else:
    cpp_ELSE {add('K');$$.nd = mknode(NULL, NULL, "else");}

cpp_while:
    cpp_WHILE {add('K');$$.nd = mknode(NULL, NULL,"while");}

cpp_string:
    cpp_STRING {add('s');$$.nd = mknode(NULL, NULL, $1.name);}

cpp_open_curly_bracket:
    cpp_OPEN_CURLY_BRACKET {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_closed_curly_bracket:
    cpp_CLOSED_CURLY_BRACKET {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_open_square_bracket:
    cpp_OPEN_SQUARE_BRACKET {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_closed_square_bracket:
    cpp_CLOSED_SQUARE_BRACKET {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_open_floor_bracket:
    cpp_OPEN_FLOOR_BRACKET {$$.nd = mknode(NULL, NULL, $1.name);scope++;} // increase scope for variables

cpp_closed_floor_bracket:
    cpp_CLOSED_FLOOR_BRACKET {$$.nd = mknode(NULL, NULL, $1.name);
        //here we need to remove all the variables declared in this scope
        // change all of their scope to INT_MAX
            int i;
            for(i=count-1; i>=0; i--) {
                if(symbol_table[i].thisscope == scope && 
                        strcmp(symbol_table[i].type, "Variable")==0) {
                    symbol_table[i].thisscope = INT_MAX;
                    printf("\nERASING %s from symbol table as its CURRENT SCOPE is FINISHED\n", symbol_table[i].id_name);
                }
            }
        scope--;
    }  // decrease scope for variables

cpp_punctuation_comma:
    cpp_PUNCTUATION_COMMA {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_newline:
    cpp_NEWLINE {$$.nd = mknode(NULL, NULL, $1.name);}

cpp_finish:
    cpp_FINISH {$$.nd = mknode(NULL, NULL, $1.name); 
        strcpy(exp_type," ");
    } // resetting exp_type string

cpp_function:
    cpp_FUNCTION {add('K');$$.nd = mknode(NULL, NULL, $1.name);}

cpp_return:
    cpp_RETURN {add('K');$$.nd = mknode(NULL, NULL, $1.name);}

cpp_character:
    cpp_CHARACTER {add('c');$$.nd = mknode(NULL, NULL, $1.name);}




input:  // input can be empty also
    { $$.nd = mknode(NULL, NULL, "empty"); }
|   input eol { 
        printf("Parser found input-eol\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        $$.nd = mknode(num_children, children, "input-eol");
    }
|   eol input { 
        printf("Parser found eol-input\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        $$.nd = mknode(num_children, children, "eol-input");
    }
|   input cpp_import cpp_imported_library cpp_finish { 
        //add('H');
        printf("Parser found input-import-lib-;\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "input-import-lib-;");
    }
|   cpp_import cpp_imported_library cpp_finish input { 
        //add('H');
        printf("Parser found import-lib-;-input\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "import-lib-;-input");
    }
|   input bunch_of_statements input { 
        printf("Parser found input-bunch_of_stmts-input\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        $$.nd = mknode(num_children, children, "input-bunch-input");
    }
|   input {insNumOfLabel[labelsused]=ic_idx; sprintf(icg[ic_idx++], "LABEL L%d:\n", labelsused++);} function_declaration input { 
        //add('F');
        printf("Parser found input-functionDec-input\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $3.nd; 
        children[2] = $4.nd;
        $$.nd = mknode(num_children, children, "input-funDec-input");
    }
;


empty_lines:
    EOL
|   empty_lines EOL

exp:   // empty not allowed

    cpp_int {    
                    if(strcmp(exp_type," ")==0) {
                        strcpy(exp_type, "int");
                    }
                    else if(strcmp(exp_type, "string")==0) {
                        sprintf(errors[sem_errors], "Line %d: operation among int and string in expression not allowed\n", countn+1);
                        sem_errors++;
                    }
                    printf("Parser found int\n");
                    int num_children = 1;  // Number of children
                    struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
                    children[0] = $1.nd;  
                    $$.nd = mknode(num_children, children, "INT");

                    // if(firstreg == -1){
                    //     firstreg = registerIndex++;
                    //     sprintf(icg[ic_idx++], "R%d = %s\n", firstreg, $1.name);
                    // }
                    // else{
                    //     secondreg = registerIndex++;
                    //     sprintf(icg[ic_idx++], "R%d = %s\n", secondreg, $1.name);
                    // }
                    registers[regstackpointer++]=registerIndex;
                    sprintf(icg[ic_idx++], "MOV R%d , %s\n", (registerIndex++)-1, $1.name);

                }
|   cpp_float {
                    if(strcmp(exp_type," ")==0) {
                        strcpy(exp_type, "float");
                    }
                    else if(strcmp(exp_type, "string")==0) {
                        sprintf(errors[sem_errors], "Line %d: operation among float and string in expression not allowed\n", countn+1);
                        sem_errors++;
                    }
                    printf("Parser found float\n");
                    int num_children = 1;  // Number of children
                    struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
                    children[0] = $1.nd;  
                    $$.nd = mknode(num_children, children, "FLOAT");
                    registers[regstackpointer++]=registerIndex;
                    sprintf(icg[ic_idx++], "MOV R%d , %s\n",( registerIndex++)-1, $1.name);
                }
|   cpp_character {
                    printf("Parser found character\n");
                    int num_children = 1;  // Number of children
                    struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
                    children[0] = $1.nd;  
                    $$.nd = mknode(num_children, children, "CHAR");
                    registers[regstackpointer++]=registerIndex;
                    sprintf(icg[ic_idx++], "MOV R%d , %s\n", (registerIndex++)-1, $1.name);
                }
|   cpp_string {
                    if(strcmp(exp_type," ")==0) {
                        strcpy(exp_type, "string");
                    }
                    else if(strcmp(exp_type, "int")==0 || strcmp(exp_type, "float")==0) {
                        sprintf(errors[sem_errors], "Line %d: operation among string and int/float in expression not allowed\n", countn+1);
                        sem_errors++;
                    }
                    printf("Parser found string\n");
                    int num_children = 1;  // Number of children
                    struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
                    children[0] = $1.nd;  
                    $$.nd = mknode(num_children, children, "STRING");
                    registers[regstackpointer++]=registerIndex;
                    sprintf(icg[ic_idx++], "MOV R%d , %s\n", (registerIndex++)-1, $1.name);
                }
|   cpp_identifier {
                    printf("Parser found identifier\n");
                    int num_children = 1;  // Number of children
                    struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
                    children[0] = $1.nd;  
                    $$.nd = mknode(num_children, children, "ID");
                    registers[regstackpointer++]=registerIndex;
                    sprintf(icg[ic_idx++], "MOV R%d , %s\n", (registerIndex++)-1, $1.name);
                    markVariableAsUsed($1.name);  // optimization stage
                }
|   function_call {
                    printf("Parser found funcCall\n");
                    int num_children = 1;  // Number of children
                    struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
                    children[0] = $1.nd;  
                    $$.nd = mknode(num_children, children, "funcCall");
                }
|   cpp_identifier cpp_open_square_bracket exp cpp_closed_square_bracket {
                    printf("Parser found id[exp]\n");
                    int num_children = 4;  // Number of children
                    struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
                    children[0] = $1.nd;  
                    children[1] = $2.nd; 
                    children[2] = $3.nd; 
                    children[3] = $4.nd; 
                    $$.nd = mknode(num_children, children, "ID[exp]");
                    //registers[regstackpointer++]=registerIndex;
                    sprintf(icg[ic_idx++], "MOV R%d , %s+R%d\n", registerIndex , $1.name,registerIndex-1);
                }
|   cpp_open_curly_bracket exp cpp_closed_curly_bracket { 
        printf("Parser found (exp)\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        
        // Assigning children nodes
        children[0] = $1.nd;  // Assuming $1 represents the parse tree node for symbol1
        children[1] = $2.nd;  // Assuming $2 represents the parse tree node for symbol2
        children[2] = $3.nd;
        $$.nd = mknode(num_children, children, "(exp)");
        
        // Free the memory allocated for the array of children
        //free(children);
    }
// |   cpp_int cpp_arithmetic_operator cpp_int {
//         printf("Parser found int-arithmeticOp-exp\n");      
//         int num_children = 3;  // Number of children
//         struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
//         children[0] = $1.nd;  // Assuming $1 represents the parse tree node for symbol1
//         children[1] = $2.nd;  // Assuming $2 represents the parse tree node for symbol2
//         children[2] = $3.nd;
//         if(($2.name)[0] == '+')
//             sprintf(icg[ic_idx++], "MOV R%d , %d\n", registers[regstackpointer++], stringToInt($1.name)+stringToInt($3.name));
//         else if(($2.name)[0] == '%')
//             sprintf(icg[ic_idx++], "MOV R%d , %d\n", registers[regstackpointer++], stringToInt($1.name)%stringToInt($3.name));
//         else if(($2.name)[0] == '-')
//             sprintf(icg[ic_idx++], "MOV R%d , %d\n", registers[regstackpointer++], stringToInt($1.name)-stringToInt($3.name));
//         else if(($2.name)[0] == '*')
//             sprintf(icg[ic_idx++], "MOV R%d , %d\n", registers[regstackpointer++], stringToInt($1.name)*stringToInt($3.name));
//         else if(($2.name)[0] == '/')
//             sprintf(icg[ic_idx++], "MOV R%d , %d\n", registers[regstackpointer++], stringToInt($1.name)/stringToInt($3.name));
//         else{
//             sprintf(icg[ic_idx++], "MOV R%d , %d\n", registers[regstackpointer++], stringToInt($1.name)+stringToInt($3.name));
//         }
//         performedConstantFolding=1;
            
    
// }
|   exp {firstreg = registerIndex-1;registers[registerIndex-1]=firstreg;} cpp_arithmetic_operator exp 
    {secondreg = registerIndex-1;registers[registerIndex-1]=secondreg;} { 
        printf("Parser found exp-arithmeticOp-exp\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        
        // Assigning children nodes
        children[0] = $1.nd;  // Assuming $1 represents the parse tree node for symbol1
        children[1] = $3.nd;  // Assuming $2 represents the parse tree node for symbol2
        children[2] = $4.nd;
        // Assign more children if needed
        
        // Create the parse tree node for the production rule
        $$.nd = mknode(num_children, children, "AthematicOp");
        
        // Free the memory allocated for the array of children
        //free(children);
        regstackpointer--;
        if(($3.name)[0] == '+')
            sprintf(icg[ic_idx++], "ADD R%d , R%d\n", secondreg , registers[--regstackpointer]-1);
        else if(($3.name)[0] == '-')
            sprintf(icg[ic_idx++], "SUB R%d , R%d\n", secondreg-1 , registers[--regstackpointer]-1);
        else if(($3.name)[0] == '*')
            sprintf(icg[ic_idx++], "MUL R%d , R%d\n", secondreg , registers[--regstackpointer]-1);
        else if(($3.name)[0] == '/')
            sprintf(icg[ic_idx++], "DIV R%d , R%d\n", secondreg , registers[--regstackpointer]-1);
        else if(($3.name)[0] == '%')
            sprintf(icg[ic_idx++], "MOD R%d , R%d\n", secondreg , registers[--regstackpointer]-1);
        else{
            sprintf(icg[ic_idx++], "R%d = R%d %c R%d\n", secondreg , registers[--regstackpointer]-1, ($3.name)[0],secondreg);
        }

        // // CONSTANT FOLDING
        // if(($3.name)[0] == '+')
        //     sprintf(icg[ic_idx++], "MOV R%d , %d\n", secondreg , registers[--regstackpointer]-1);

        //secondreg = firstreg;
        //first = registers[regstackpointer];
      
    }
|   exp {firstreg = registerIndex-1;} cpp_logical_operator exp {secondreg = registerIndex-1;} { 
        printf("Parser found exp-logicalOp-exp\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $3.nd; 
        children[2] = $4.nd;
        $$.nd = mknode(num_children, children, "LogicalOp");
        //sprintf(icg[ic_idx++], "R%d = R%d %s R%d\n", secondreg , firstreg, $3.name, secondreg);
        if (strcmp($3.name, "and") == 0) {
            sprintf(icg[ic_idx++], "AND R%d , R%d\n", secondreg , firstreg);
        }
        else if (strcmp($3.name, "or") == 0) {
            sprintf(icg[ic_idx++], "OR R%d , R%d\n", secondreg , firstreg);
        }  
        // else if (strcmp($3.name, "!") == 0) {
        //     sprintf(icg[ic_idx++], "NOT R%d , R%d\n", secondreg , firstreg);
        // }  
        else if (strcmp($3.name, "^") == 0) {
            sprintf(icg[ic_idx++], "XOR R%d , R%d\n", secondreg , firstreg);
        }
        else{
            sprintf(icg[ic_idx++], "R%d = R%d %s R%d\n", secondreg , firstreg, $3.name,secondreg);
        }  


    }
|   exp {firstreg = registerIndex-1;} cpp_comparison_operator exp {secondreg = registerIndex-1;} { 
        printf("Parser found exp-compOp-exp\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $3.nd; 
        children[2] = $4.nd;
        $$.nd = mknode(num_children, children, "CompOp");
        //sprintf(icg[ic_idx++], "R%d = R%d %s R%d\n", secondreg , firstreg, $3.name, secondreg);
        if (strcmp($3.name, "<") == 0) {
            sprintf(icg[ic_idx++], "LT R%d , R%d\n", secondreg , firstreg);
        }
        else if (strcmp($3.name, ">") == 0) {
            sprintf(icg[ic_idx++], "GT R%d , R%d\n", secondreg , firstreg);
        }  
        // else if (strcmp($3.name, "kaadu") == 0) {
        //     sprintf(icg[ic_idx++], "NOT R%d , R%d\n", secondreg , firstreg);
        // }  
        else if (strcmp($3.name, ">=") == 0) {
            sprintf(icg[ic_idx++], "GE R%d , R%d\n", secondreg , firstreg);
        }  
        else if (strcmp($3.name, "<=") == 0) {
            sprintf(icg[ic_idx++], "LE R%d , R%d\n", secondreg , firstreg);
        }  
        else if (strcmp($3.name, "==") == 0) {
            sprintf(icg[ic_idx++], "EQ R%d , R%d\n", secondreg , firstreg);
        }  
        else if (strcmp($3.name, "!=") == 0) {
            sprintf(icg[ic_idx++], "NE R%d , R%d\n", secondreg , firstreg);
        }  
        else{
            sprintf(icg[ic_idx++], "R%d = R%d %s R%d\n", secondreg , firstreg, $3.name,secondreg);
        }  


    }
|   cpp_identifier cpp_open_square_bracket exp {registers[regstackpointer++]=registerIndex;
        sprintf(icg[ic_idx++], "MOV R%d , %s + R%d\n", registerIndex , $1.name, registerIndex-1);} cpp_closed_square_bracket { 
        printf("Parser found id[exp]\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        children[3] = $5.nd;
        $$.nd = mknode(num_children, children, "id[exp]");
        //sprintf(icg[ic_idx++], "MOV R%d , %s + R%d\n", firstreg , $1.name, firstreg);
    }
;


bunch_of_statements:  //can be empty
    { $$.nd = mknode(NULL, NULL, "empty"); }
|   eol bunch_of_statements { 
        printf("Parser found EOL-bunch\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        $$.nd = mknode(num_children, children, "eol-bunch");
    }
|   bunch_of_statements eol { 
        printf("Parser found bunch-EOL\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        $$.nd = mknode(num_children, children, "bunch-eol");
    }
|   bunch_of_statements if_else_ladder {
            insNumOfLabel[labelsused]=ic_idx; 
            sprintf(icg[ic_idx++], "LABEL L%d:\n", labelsused++);
            //lastjumps[lastjumpstackpointer++] = label[stackpointer-2];
            int index = ic_idx - 1;
            int count = laddercounts[laddercountstackpointer-1]; // Number of iterations

            for (int i = index; i >= 0 && count > 0; i--) {
                printf("icg[%d] = %s\n", i, icg[i]);
                if (strncmp(icg[i], "JUMP ", 5) == 0) { // Check if the prefix matches "JUMP "
                    printf("...................\n");
                    char jump_str[20]; // Assuming the number won't exceed 20 digits
                    sprintf(jump_str, "%d", labelsused-1); // Convert number to string
                    snprintf(icg[i], 20, "JUMPx L%s\n", jump_str); // Set icg[i] to "JUMP" followed by the number
                    count--;
                }
            }
            lastjumpstackpointer--;  // forgetting the current ifelseLadder's lastjump and counts
            laddercountstackpointer--;
        
        } bunch_of_statements {

        } { 
        printf("Parser found bunch_of_statement if_else_ladder bunch\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $4.nd; 
        $$.nd = mknode(num_children, children, "bunch-IfElse-bunch");
    }
|   bunch_of_statements cpp_input cpp_open_curly_bracket cpp_identifier cpp_closed_curly_bracket cpp_finish bunch_of_statements { 
        printf("Parser found bunch_of_statement-inputscan-bunch\n");
        int num_children = 7;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        children[3] = $4.nd;
        children[4] = $5.nd;
        children[5] = $6.nd;
        children[6] = $7.nd;
        $$.nd = mknode(num_children, children, "bunch-inputScan-bunch");
    }
|   bunch_of_statements while_loop bunch_of_statements { 
        printf("Parser found bunch_of_statement while_loop bunch\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        $$.nd = mknode(num_children, children, "bunch-while-bunch");
    }
|   bunch_of_statements print_statement cpp_finish bunch_of_statements { 
        printf("Parser found bunch-printStmt-finish\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "bunch-printStmt-;-bunch");
    }
|   bunch_of_statements variable_declaration cpp_finish bunch_of_statements { 
        printf("Parser found bunch-varDeclare-finish\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "bunch-varDeclare-;-bunch");
    }
|   bunch_of_statements cpp_open_floor_bracket bunch_of_statements cpp_closed_floor_bracket bunch_of_statements {
        printf("parser found bunch {bunch}\n");
        int num_children = 5;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        children[3] = $4.nd;
        children[4] = $5.nd;
        $$.nd = mknode(num_children, children, "bunch-{bunch}-bunch");
    }
|   bunch_of_statements function_call cpp_finish bunch_of_statements { 
        printf("Parser found bunch-functionCall-;\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd; 
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "bunch-functionCall-;-bunch");
    }
|   bunch_of_statements equation cpp_finish bunch_of_statements { 
        printf("Parser found bunch-equation-finish\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd; 
        children[2] = $3.nd;
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "bunch-equation-;-bunch");
    }
|   error cpp_finish {
        printf("PARSER ERROR: syntax error \n");
        int num_children = 0;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        $$.nd = mknode(num_children, children, "error-;");
}

condition:  // for if_statement and while loop, empty not allowed
    exp { 
        printf("Parser found exp as condition\n");
        int num_children = 1;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        $$.nd = mknode(num_children, children, "condition");
    }
|   exp {firstreg = registerIndex-1;} cpp_comparison_operator exp {secondreg = registerIndex-1;} { 
        printf("Parser found exp-compareOp-exp\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $3.nd; 
        children[2] = $4.nd;
        $$.nd = mknode(num_children, children, "condition");
        
        //sprintf(icg[ic_idx++], "R%d = R%d %s R%d\n", secondreg , firstreg, $3.name, secondreg);
        if (strcmp($3.name, "<") == 0) {
            sprintf(icg[ic_idx++], "LT R%d R%d R%d\n", registerIndex++ , firstreg, secondreg);
        }
        else if (strcmp($3.name, ">") == 0) {
            sprintf(icg[ic_idx++], "GT R%d R%d R%d\n", registerIndex++ , firstreg, secondreg);
        }
        else if (strcmp($3.name, "<=") == 0) {
            sprintf(icg[ic_idx++], "LTE R%d R%d R%d\n", registerIndex++ , firstreg, secondreg);
        }
        else if (strcmp($3.name, ">=") == 0) {
            sprintf(icg[ic_idx++], "GTE R%d R%d R%d\n", registerIndex++ , firstreg, secondreg);
        }
        else if (strcmp($3.name, "==") == 0) {
            sprintf(icg[ic_idx++], "EQ R%d R%d R%d\n", registerIndex++ , firstreg, secondreg);
        }
        else{
            sprintf(icg[ic_idx++], "R%d = R%d %s R%d\n", secondreg , firstreg, $3.name, secondreg);
            registerIndex++;   // is this needed?
        }
         
    }
|   exp {firstreg = registerIndex-1;} cpp_logical_operator exp {secondreg = registerIndex-1;} { 
        printf("Parser found exp-logicalOp-exp\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $3.nd; 
        children[2] = $4.nd;
        $$.nd = mknode(num_children, children, "condition");
        sprintf(icg[ic_idx++], "R%d = R%d %s R%d\n", secondreg , firstreg, $3.name, secondreg);
    }

if_statement:
    cpp_if cpp_open_curly_bracket condition {
        sprintf(icg[ic_idx++], "if NOT (R%d) GOTO L%d\n",registerIndex-1,labelsused);isleader[insNumOfLabel[labelsused]]=1;isleader[ic_idx]=1; label[stackpointer++]=labelsused++;} cpp_closed_curly_bracket cpp_open_floor_bracket bunch_of_statements {sprintf(icg[ic_idx++], "JUMP L%d\n",label[stackpointer-1]);} cpp_closed_floor_bracket { 
        printf("Parser found if(cond){bunch}\n");
        int num_children = 7;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $5.nd;
        children[4] = $6.nd;
        children[5] = $7.nd;
        children[6] = $9.nd;
        $$.nd = mknode(num_children, children, "if(cond){bunch}");
        insNumOfLabel[label[stackpointer-1]]=ic_idx; 
        sprintf(icg[ic_idx++], "LABEL L%d:\n", label[--stackpointer]);
        laddercounts[laddercountstackpointer++]=1;

    }

elif_repeat: //can be empty
    { $$.nd = mknode(NULL, NULL, "empty"); }
|   eol elif_repeat { 
        printf("Parser found eol elif_repeat\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "EOL-elifrepeat");
    }
|   elif_repeat cpp_elif cpp_open_curly_bracket condition 
    {sprintf(icg[ic_idx++], "if NOT (R%d) GOTO L%d\n",registerIndex-1,labelsused);isleader[insNumOfLabel[labelsused]]=1;isleader[ic_idx]=1;label[stackpointer++]=labelsused++;} 
    cpp_closed_curly_bracket cpp_open_floor_bracket bunch_of_statements 
    {sprintf(icg[ic_idx++], "JUMP L%d\n",label[stackpointer-1]);} cpp_closed_floor_bracket 
    {insNumOfLabel[label[stackpointer-1]]=ic_idx;  sprintf(icg[ic_idx++], "LABEL L%d:\n", label[--stackpointer]);} elif_repeat { 
        printf("Parser found elif(cond){bunch}\n");
        int num_children = 9;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $4.nd;
        children[4] = $6.nd;
        children[5] = $7.nd;
        children[6] = $8.nd;
        children[7] = $10.nd;
        children[8] = $12.nd;
        $$.nd = mknode(num_children, children, "elif(cond){bunch}");
        laddercounts[laddercountstackpointer-1]++;
       
    }

else_statement:  //can be empty   
    { $$.nd = mknode(NULL, NULL, "empty"); }
|   eol else_statement { 
        printf("Parser found EOL-else\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "EOL-else");
    }
|   cpp_else cpp_open_floor_bracket bunch_of_statements cpp_closed_floor_bracket { 
        printf("Parser found else{bunch}\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "else{bunch}");
    }

if_else_ladder:
    if_statement elif_repeat 
    {
             lastjumps[lastjumpstackpointer++] = label[stackpointer-1];

        }
         else_statement { 
        printf("Parser found ifElseLadder\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $4.nd; 
        $$.nd = mknode(num_children, children, "ifElseLadder");
        // lastjumpstackpointer--;  // forgetting the current ifelseLadder's lastjump and counts
        // laddercountstackpointer--;
    }
|   if_statement elif_repeat 
        {
             lastjumps[lastjumpstackpointer++] = label[stackpointer-1];
            // int index = ic_idx - 1;
            // int count = laddercounts[laddercountstackpointer-1]; // Number of iterations

            // for (int i = index; i >= 0 && count > 0; i--) {
            //     if (strncmp(icg[i], "JUMP ", 5) == 0) { // Check if the prefix matches "JUMP "
            //         char jump_str[20]; // Assuming the number won't exceed 20 digits
            //         sprintf(jump_str, "%d", lastjumps[lastjumpstackpointer-1]); // Convert number to string
            //         snprintf(icg[i], 20, "JUMPx L%s\n", jump_str); // Set icg[i] to "JUMP" followed by the number
            //         count--;
            //     }
            // }

        }
        {    // without the else statement
        printf("Parser found ifElseLadder\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "ifElseLadder");
    }

while_loop:
    cpp_while cpp_open_curly_bracket condition { looplabel[looplabelstackpointer++] = labelsused; insNumOfLabel[labelsused]=ic_idx;  sprintf(icg[ic_idx++], "LABEL L%d:\n", labelsused++);
        gotolabel[gotolabelstackpointer++]=labelsused;  sprintf(icg[ic_idx++], "if NOT (R%d) GOTO L%d\n",registerIndex-1,labelsused++);isleader[insNumOfLabel[labelsused-1]]=1;isleader[ic_idx]=1;
    } cpp_closed_curly_bracket cpp_open_floor_bracket bunch_of_statements { sprintf(icg[ic_idx++], "JUMPtoLOOP L%d\n",looplabel[--looplabelstackpointer]);
    } cpp_closed_floor_bracket {insNumOfLabel[gotolabel[gotolabelstackpointer-1]]=ic_idx;  sprintf(icg[ic_idx++], "LABEL L%d:\n", gotolabel[--gotolabelstackpointer]);} { 
        printf("Parser found while(cond){bunch}\n");
        int num_children = 7;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $5.nd;
        children[4] = $6.nd;
        children[5] = $7.nd;
        children[6] = $9.nd;
        $$.nd = mknode(num_children, children, "while(cond){bunch}");
    }

variable_declaration:
    cpp_datatype cpp_identifier_declaring cpp_assignment_operator {rangestart = ic_idx;} exp {
        //add('V');   // this is taking ';' as a variable
        printf("Parser found datatypeId=exp\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $5.nd;
        $$.nd = mknode(num_children, children, "datatypeId=exp");
        if(strcmp(exp_type,$1.name)!=0 && strcmp(exp_type, " ")!=0){
            sprintf("$1name=%s and exp_type=%s\n", $1.name,exp_type);
            sprintf(errors[sem_errors], "Line %d: Data type casting not allowed in declaration\n", countn);
            sem_errors++;
        }
        rangeend = ic_idx;
        printf("QQQQQQQQQQQQQQQQQQQQQ rangestart=%d rangeend=%d\n",rangestart,rangeend);
        int idIndexinSymbolTable = findIdentifierIndex($2.name);
        symbol_table[idIndexinSymbolTable].range[symbol_table[idIndexinSymbolTable].range_count][0] = rangestart;
        symbol_table[idIndexinSymbolTable].range[symbol_table[idIndexinSymbolTable].range_count++][1] = rangeend;  //stack counter is increased
        if(performedConstantFolding) registerIndex++;
            sprintf(icg[ic_idx++], "MOVe %s , R%d\n", $2.name, registerIndex-1);
        performedConstantFolding=0;
    }
|   cpp_datatype cpp_identifier_declaring {
        
        printf("Parser found datatype Id\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "datatypeId");

        //// not needed here
        // rangestart = ic_idx;
        // rangeend = ic_idx;
        // int idIndexinSymbolTable = findIdentifierIndex($2.name);
        // symbol_table[idIndexinSymbolTable].range[symbol_table[idIndexinSymbolTable].range_count][0] = rangestart;
        // symbol_table[idIndexinSymbolTable].range[symbol_table[idIndexinSymbolTable].range_count++][1] = rangeend;  //stack counter is increased
    }
|   cpp_datatype cpp_identifier_declaring cpp_open_square_bracket exp cpp_closed_square_bracket {
        
        printf("Parser found datatype Id\n");
        int num_children = 5;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        children[3] = $4.nd;
        children[4] = $5.nd;
        $$.nd = mknode(num_children, children, "datatype Id[exp]");
    }


parameters_repeat: // can be empty 0 or more occurences
    { $$.nd = mknode(NULL, NULL, "empty"); }
|   parameters_repeat cpp_datatype cpp_identifier_declaring cpp_punctuation_comma { 
        printf("Parser found paramRepDatatypeIdComma\n");
        curr_num_params++;
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "paramRepDatatypeIdComma");
    }

parameters_line: // can be empty
    { $$.nd = mknode(NULL, NULL, "empty"); }
|   {scope++;} parameters_repeat cpp_datatype cpp_identifier_declaring {scope--;} { 
        printf("Parser found parameters_line\n");
        curr_num_params++;
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $2.nd;
        children[1] = $3.nd;
        children[2] = $4.nd; 
        $$.nd = mknode(num_children, children, "paramLine");
    }

identifiers_repeat: // abc,x,y,p  can be empty
     { $$.nd = mknode(NULL, NULL, "empty"); }
|   cpp_identifier { 
        curr_num_args++;
        printf("Parser found lastparam\n");
        int num_children = 1;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        $$.nd = mknode(num_children, children, "paramEnd");
        sprintf(icg[ic_idx++], "PARAM %s\n", $1.name);
    }
|   cpp_constant { 
        curr_num_args++;
        printf("Parser found lastparam\n");
        int num_children = 1;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        $$.nd = mknode(num_children, children, "paramEnd");
        sprintf(icg[ic_idx++], "PARAM %s\n", $1.name);
    } 
|   exp { 
        curr_num_args++;
        printf("Parser found lastparam\n");
        int num_children = 1;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        $$.nd = mknode(num_children, children, "paramEnd");
        sprintf(icg[ic_idx++], "PARAM R%d\n", registers[regstackpointer-1]+1);
    }
|   identifiers_repeat cpp_punctuation_comma identifiers_repeat { 
        curr_num_args++;
        printf("Parser found id-comma-prep\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        $$.nd = mknode(num_children, children, "paramRep");
        sprintf(icg[ic_idx++], "PARAM %s\n", $1.name);
    }

identifiers_line: // for function call,can be empty
    identifiers_repeat {
        printf("Parser found idLine\n");
        int num_children = 1;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd; 
        $$.nd = mknode(num_children, children, "idline");
    }

equation:
    cpp_identifier cpp_assignment_operator { strcpy(exp_type," "); } {rangestart = ic_idx;} exp { 
        printf("Parser found equation\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $5.nd; 
        $$.nd = mknode(num_children, children, "id=exp");
        //check if identifier type and exp_type mismatch -> if yes then typecast is happening
        printf("type of identifier: %s XXXXXXXXXXXXXXXXX exp_type=%s\n\n", get_type($1.name),exp_type);
        if(strcmp(get_datatype($1.name) , exp_type) && strcmp(exp_type, " ")){
            sprintf(errors[sem_errors], "Line %d: Data type casting not allowed in equation\n", countn);
            sem_errors++;
        }
        // a = exp   ---> t1=exp, a=t1
        rangeend = ic_idx;
        printf("ZZZZZZZZZZ      rangestart=%d rangeend=%d\n",rangestart,rangeend);
        int idIndexinSymbolTable = findIdentifierIndex($1.name);
        symbol_table[idIndexinSymbolTable].range[symbol_table[idIndexinSymbolTable].range_count][0] = rangestart;
        symbol_table[idIndexinSymbolTable].range[symbol_table[idIndexinSymbolTable].range_count++][1] = rangeend;  //stack counter is increased

        sprintf(icg[ic_idx++], "%s = R%d\n", $1.name, registerIndex-1);
    }
|   cpp_identifier cpp_open_square_bracket exp {thirdreg = registerIndex-1;} cpp_closed_square_bracket cpp_assignment_operator exp { 
        printf("Parser found id[exp]=exp\n");
        int num_children = 6;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd; 
        children[3] = $5.nd;
        children[4] = $6.nd;
        children[5] = $7.nd;
        $$.nd = mknode(num_children, children, "id[exp]=exp");
        sprintf(icg[ic_idx++], "MOV %s+R%d , R%d\n", $1.name,thirdreg ,registerIndex-1);
    }

function_content:  // can be empty also, return not needed
    function_content eol { 
        printf("Parser found funContentEOL\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "funContentEOL");
    }
|   eol function_content { 
        printf("Parser found EOL-funContent\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "EOL-funContent");
    }
|    bunch_of_statements function_content bunch_of_statements { 
        printf("Parser found bunch_function_content_bunch\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        $$.nd = mknode(num_children, children, "bunch-content-bunch");
    }
|    bunch_of_statements { 
        printf("Parser found bunch_function_content_bunch\n");
        int num_children = 1;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        $$.nd = mknode(num_children, children, "bunch-content-bunch");
    }
|   bunch_of_statements cpp_return cpp_finish bunch_of_statements { 
        printf("Parser found bunchReturnFinish\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        children[3] = $4.nd; 
        $$.nd = mknode(num_children, children, "bunchReturnFinish");
    }
|   bunch_of_statements cpp_return exp cpp_finish bunch_of_statements { 
        printf("Parser found bunchReturnExpFinish\n");
        int num_children = 5;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        children[3] = $4.nd;
        children[4] = $5.nd; 
        $$.nd = mknode(num_children, children, "bunchReturnExpFinish");
    }
|   bunch_of_statements function_call cpp_finish bunch_of_statements { 
        printf("Parser found bunchReturnExpFinish\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "bunchFunCallFinish");
    }


print_content:  // can be empty also
|   print_content eol { 
        printf("Parser found print_contentEOL\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "print_content-EOL");
    }
|   eol print_content {    // take care of infinite loop
        printf("Parser found EOL-print_content\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "EOL-printContent");
    }
|   print_content cpp_string { 
        printf("Parser found print_content-String\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "printContent-String");
    }
|   print_content exp { 
        printf("Parser found print_content-exp\n");
        int num_children = 2;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        $$.nd = mknode(num_children, children, "printContent-exp");
    }
|   print_content cpp_punctuation_comma cpp_string { 
        printf("Parser found print_content-comma-String\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        $$.nd = mknode(num_children, children, "print_content-comma-String");
    }
|   print_content cpp_punctuation_comma exp { 
        printf("Parser found print_content-comma-exp\n");
        int num_children = 3;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        $$.nd = mknode(num_children, children, "print_content-comma-exp");
    }

print_statement:
    cpp_print cpp_open_curly_bracket print_content cpp_closed_curly_bracket { 
        printf("Parser found printStatement\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $2.nd;
        children[2] = $3.nd;
        children[3] = $4.nd;
        $$.nd = mknode(num_children, children, "printStatement");
    }

function_declaration:
    cpp_function {oldscope=scope;scope=0;} cpp_function_name {add('F');scope=oldscope;} cpp_open_curly_bracket parameters_line cpp_closed_curly_bracket cpp_open_floor_bracket function_content cpp_closed_floor_bracket { 
        printf("Parser found equation\n");
        int num_children = 8;  // Number of childrenfunction_call
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $3.nd;
        children[2] = $5.nd; 
        children[3] = $6.nd;
        children[4] = $7.nd;
        children[5] = $8.nd;
        children[6] = $9.nd;
        children[7] = $10.nd;
        $$.nd = mknode(num_children, children, "func-id-(param){content}");
        symbol_table[count-curr_num_params-3].num_params= curr_num_params;
        if(symbol_table[count-curr_num_params-3].num_params>=0){
            printf("XXXX changed num_params of %s to %d\n",symbol_table[count-curr_num_params-3].id_name,symbol_table[count-curr_num_params-3].num_params);
            curr_num_params=0;
        }
    }

function_call:
    cpp_identifier { check_declaration($1.name); } cpp_open_curly_bracket identifiers_line cpp_closed_curly_bracket { 
        printf("Parser found id(idLine)Finish\n");
        int num_children = 4;  // Number of children
        struct node **children = (struct node **)malloc(num_children * sizeof(struct node *));
        children[0] = $1.nd;
        children[1] = $3.nd;
        children[2] = $4.nd; 
        children[3] = $5.nd;
        $$.nd = mknode(num_children, children, "id(idLine)Finish");

        for(int i=0;i<count;i++){
            if(strcmp(symbol_table[i].id_name,$1.name)==0){  // found the corresponding function
            if(symbol_table[i].num_params==-1){
                printf("ERROR:  %s is not a function\n",$1.name);
                sprintf(errors[sem_errors], "Line %d:  %s is not a function\n", countn+1,$1.name);
                sem_errors++;
                break;
            }
                // if(symbol_table[i].num_params!=curr_num_args){
                //     printf("ERROR: Number of parameters do not match\n");
                //     sprintf(errors[sem_errors], "Line %d: need %d arguments but found %d args\n", countn+1,symbol_table[i].num_params,curr_num_args);
                //     sem_errors++;
                //     break;
                // }
            }
        }

        curr_num_args=0;
        sprintf(icg[ic_idx++], "CALL %s\n", $1.name);
    }
%%

int main(){
    for(int i=0;i<10000;i++){
        laddercounts[i]=0;
        isleader[i]=0;
        insNumOfLabel[i]=-1;
    }
    isleader[0]=1;
    strcpy(exp_type," ");
    printf("\n\n");
	printf("\t\t\t\t\t\t\t\t PHASE 1: LEXICAL ANALYSIS \n\n");
    for(int i=0;i<10000;i++){
        symbol_table[i].used = 0;
        symbol_table[i].range_count = 0;   
        // for(int j=0;j<10000;j++){
        //     symbol_table[i].range[j][0]=-1;
        //     symbol_table[i].range[j][1]=-1;   // dummy values
        // }
    }
    yyparse();
	printf("\nSYMBOL   DATATYPE   TYPE   LineNUMBER  SCOPE  numParams\n");
	printf("_______________________________________\n\n");
	int i=0;
	// for(i=0; i<count; i++) {

	// 	printf("%s\t%s\t%s\t%d\t%d\t%d\n", symbol_table[i].id_name, symbol_table[i].data_type, symbol_table[i].type, symbol_table[i].line_no,symbol_table[i].thisscope,symbol_table[i].num_params);
	// }
    for (i = 0; i < count; i++) {
        printf("%s\t%s\t%s\t%d\t%d\t%d\t%s\n", symbol_table[i].id_name, symbol_table[i].data_type, symbol_table[i].type, symbol_table[i].line_no, symbol_table[i].thisscope, symbol_table[i].num_params, symbol_table[i].used ? "Used" : "unUsed");
    }

	
	printf("\n\n");
	printf("\t\t\t\t\t\t\t\t PHASE 2: SYNTAX ANALYSIS \n\n");
	printtree(head); 
	printf("\n\n\n\n");
	printf("\t\t\t\t\t\t\t\t PHASE 3: SEMANTIC ANALYSIS \n\n");
	if(sem_errors>0) {
		printf("Semantic analysis completed with %d errors\n", sem_errors);
		for(int i=0; i<sem_errors; i++){
			printf("\t - %s", errors[i]);
		}
	} else {
		printf("Semantic analysis completed with no errors");
	}
	printf("\n\n");
    printf("\t\t\t\t\t\t\t   PHASE 4: INTERMEDIATE CODE GENERATION \n\n");
	for(int i=0; i<ic_idx; i++){
        if(icg[i][0]=='L' && icg[i][0]=='A'){
            printf("\n");
        }
		printf("%d  %s", i,icg[i]);
	}
	printf("\n\n");

    // Assuming icg[] contains the strings "LABEL L15", "LABEL L20", etc.
    for (int i = 0; i < ic_idx; i++) {
        // Check if the string starts with "LABEL L"
        if (strncmp(icg[i], "LABEL L", 7) == 0) {
            // Extract the label number from the string
            int labelNumber = atoi(icg[i] + 7); // Skip "LABEL L" and convert the rest to integer
            
            // Use the label number to index into insNumOfLabel array
            insNumOfLabel[labelNumber] = i;
        }
    }

    for(int i=0;i<ic_idx;i++){
        if (strncmp(icg[i], "if NOT (", 8) == 0) {
            char *ptr = strstr(icg[i], "L"); // Find the first occurrence of "L" in the string
            int labelNumber = atoi(ptr + 1); // Convert the substring after "L" to integer
            //printf("Extracted label number: %d\n", labelNumber);
            isleader[insNumOfLabel[labelNumber]] = 1;
            if(i+1<10000)
                isleader[i+1]=1;
        }
    }

    printf("\t\t\tBLOCKS:\n\n");
    int prev=-1,blockcount=0;
    for(int i=0;i<10000;i++){
        // if(insNumOfLabel[i]!=-1){
        //     printf("Label %d is at %d\n",i,insNumOfLabel[i]);
        // }
        if(isleader[i]){
            if(prev!=-1)
            printf("block %d: %d to %d\n",blockcount++,prev,i-1);
            //printf("Leader %d\n",i);
            prev=i;
        }
    }
    
    printf("\n\n");

    // Iterate over the symbol table to print ranges for unused variables
    for (int i = 0; i < count; i++) {
        if (symbol_table[i].used <= 0 && strcmp(symbol_table[i].type, "Variable") == 0) {
             printf("Variable %s declared but not used\n", symbol_table[i].id_name);
             printf("Ranges for %s:\n", symbol_table[i].id_name);
            for (int j = 0; j < symbol_table[i].range_count; j++) {
                printf("[%d, %d]\n", symbol_table[i].range[j][0], symbol_table[i].range[j][1]);
                uselessranges[uselessrangescount][0] = symbol_table[i].range[j][0];
                uselessranges[uselessrangescount++][1] = symbol_table[i].range[j][1];
            }
            printf("\n");
        }
    }
    for(i=0;i<count;i++) {
		free(symbol_table[i].id_name);   // symbol is needed, so dont free yet
		free(symbol_table[i].type);
	}
    //printf("done");

    // Sort uselessranges
    sortRanges(uselessranges, uselessrangescount);
    int uselessrangesidx = 0;
    printf(" uselessrangescount=%d\n", uselessrangescount);
    printf("\t\t\t\t\t\t\t   PHASE 5: OPTIMIZATION \n\n");
	for(int i=0; i<ic_idx; i++){
        if (uselessrangesidx < uselessrangescount && i == uselessranges[uselessrangesidx][0]) {
            uselessrangesidx++;
            i=uselessranges[uselessrangesidx-1][1];
            //printf("skipping from %d to %d\n", uselessranges[uselessrangesidx-1][0], uselessranges[uselessrangesidx-1][1]);
            continue;
        }
        if(icg[i][0]=='L' && icg[i][0]=='A'){
            printf("\n");
        }
		printf("%d %s",i, icg[i]);
	}
	printf("\n\n");

    

    return 0;
}

int yyerror(char *s){
    printf("PARSER ERROR: %s\n",s);
    //return 0;
}

struct node* mknode(int num_children, struct node **children, char *token) {
    struct node *newnode = (struct node *)malloc(sizeof(struct node));
    newnode->num_children = num_children;
    newnode->children = children;
    newnode->token = strdup(token);
    return newnode;
}

void printtree(struct node* tree) {
	printf("\n\n Inorder traversal of the Parse Tree: \n\n");
	printInorder(tree);
	printf("\n\n");
}

void printInorder(struct node *tree) {
	if (tree) {
		printf("%s, ", tree->token);
		for (int i = 0; i < tree->num_children; i++) {
			printInorder(tree->children[i]);
		}
	}
}

/////////////////////////////////////  SYMBOL TABLE & SEMANTIC ANALYSIS PART

int search(char *type) {
	int i;
	for(i=count-1; i>=0; i--) {
		if(strcmp(symbol_table[i].id_name, type)==0) {
			return symbol_table[i].thisscope;
			break;
		}
	}
	return 0;
}

void check_declaration(char *c) {
    q = search(c);
    // if(!q) {
    //     sprintf(errors[sem_errors], "Line %d: Variable \"%s\" not declared before usage!\n", countn+1, c);
	// 	sem_errors++;
    // }
}

char *get_type(char *var){
	for(int i=0; i<count; i++) {
		// Handle case of use before declaration
		if(!strcmp(symbol_table[i].id_name, var)) {
			return symbol_table[i].type;
		}
	}
}
char *get_datatype(char *var){
	for(int i=0; i<count; i++) {
		// Handle case of use before declaration
		if(!strcmp(symbol_table[i].id_name, var)) {
			return symbol_table[i].data_type;
		}
	}
}

void add(char c) {
	if(c == 'V'){ // variable
		for(int i=0; i<reserved_count; i++){
			if(!strcmp(reserved[i], strdup(yy_text))){
        		sprintf(errors[sem_errors], "Line %d: Variable name \"%s\" is a reserved keyword!\n", countn+1, yy_text);
				sem_errors++;
				return;
			}
		}
	}
    q=search(yy_text);
	if(!q) {   // insert into symbol table only if not already present
		if(c == 'H') {  //header
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup(type);
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Header");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1; 
			count++;
		}
		else if(c == 'K') { //keyword
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup("N/A");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Keyword\t");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1;
			count++;
		}
		else if(c == 'V') { //variable
            printf("yytext: %s\n", yy_text);
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup(type);
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Variable");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1;
			count++;
		}
        else if(c == 'C') {  
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup("CONST");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("constantx");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1;
			count++;
		}
		else if(c == 'i') {  
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup("CONST");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("int");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1;
			count++;
		}
        else if(c == 'f') {  
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup("CONST");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("float");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1;
			count++;
		}
        else if(c == 'c') {  
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup("CONST");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("char");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1;
			count++;
		}
        else if(c == 's') {  
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup("CONST");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("string");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=-1;
			count++;
		}
		else if(c == 'F') {
			symbol_table[count].id_name=strdup(yy_text);
			symbol_table[count].data_type=strdup(type);
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Function");
            symbol_table[count].thisscope=scope;
            printf("\nSETTING %s's params to %d\n", symbol_table[count-curr_num_params].id_name, curr_num_params);
            symbol_table[count-curr_num_params].num_params=curr_num_params;
            curr_num_params=0;
			count++;
		}
        else if(c == 'L') {
            symbol_table[count].id_name=strdup(yy_text);
            symbol_table[count].data_type=strdup(type);
            symbol_table[count].line_no=countn;
            symbol_table[count].type=strdup("Library");
            symbol_table[count].thisscope=scope;
            symbol_table[count].num_params=0;
            count++;
        }
               
    }
    else if(c == 'V' && q) {
        if(q != INT_MAX){

            sprintf(errors[sem_errors], "Line %d: Multiple declarations of \"%s\" not allowed!\n", countn+1, yy_text);
            sem_errors++;
        }
        else{ // its scope is already destroyed, now it can be redeclared again into the symbol table with current scope
            // search again for that symbol table value
            int i;
            for(i=count-1; i>=0; i--) {
                if(strcmp(symbol_table[i].id_name, type)==0) {
                    symbol_table[i].thisscope = scope;
                    symbol_table[count].line_no=countn;
                    symbol_table[count].num_params=0;
                    printf("\nReinserted %s because its previous scope is finished\n", type);
                    break;
                }
            }
        }
    }
}

void insert_type() {
	strcpy(type, yy_text);
}



