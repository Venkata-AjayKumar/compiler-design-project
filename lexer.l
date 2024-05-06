%{
#include <stdio.h>
    #include<string.h>
    #include<stdlib.h>
    #include<ctype.h>
    #include <limits.h>
#include "t2parser.tab.h"


extern int col_num;

extern int countn;  // replaced new_line count
extern int scope=1;  // starts from 1
extern char* yy_text = NULL;


char prev='@';
int countn = 1;
int col_num = 1;
const int largest_length_for_yytext_clone=10000;
%}

datatype "int"|"float"|"char"|"string"
cpp_if "if"
cpp_elif "elseif"
cpp_else "else"
cpp_while "while"
cpp_function "fun"
cpp_return "return"
cpp_print "cout"
cpp_import "thechko"
cpp_input "cin>>"

identifier [a-zA-Z_][a-zA-Z0-9_]*
digit [0-9]
int [-+]?{digit}+
float {int}"."({digit}+)
arthematic_operator ("+")|("-")|("*")|("/")|("%")
comparision_operator ("==")|("!=")|(">=")|("<=")|("<")|(">")
logical_operator "and"|"or"|"!"|"^"
assignment_operator "="
space [ \t]
newline [\n]
finish ";"
string \"(\\.|[^\\"])*\"
invalidIdentifier (({digit}+{identifier}))

%%
{int} {
    // HANDLE THIS CASE PROPERLY
    if(prev != '=') {
        if(yytext[0]!='+' && yytext[0]!='-'){ // will this case be reached?
            printf("%s is an  integer1 (line: %d, column: %d)\n",yytext, countn, col_num);
            //yylval.num=atoi(yytext);
            prev='@';
            yy_text = strdup(yytext);
            strcpy(yylval.nd_obj.name,(yytext));
            return cpp_INT; // unsigned needed?
        }
        else{
            //printf("total yytext = %s\n",yytext);
            printf(" %c is an arithmetic operator(line: %d, column: %d)\n", yytext[0], countn, col_num + 1);
            int i = 1;
            int textlen=strlen(yytext)-1;
            //printf("textlen=%d\n",textlen);
            char dummy[largest_length_for_yytext_clone]; // Declaration of dummy array
            strcpy(dummy, yytext); 
            i=1;
            for (i = textlen; i >= 1; i--) {
                //printf("i=%d\n", i);
                //printf(" unputting %c\n", dummy[i]);
                unput(dummy[i]); // Put back each digit into the input stream
            }
            //printf("length=%d for unput\n",i-1);
            //unxput(yytext, 1, i-1);
            //printf("after unput yytext=%s\n",yytext);
            prev = '@';
            //colnum +=1-yyleng;  // to balance the next +yyleng because we only saw one operation character
            yy_text = strdup(yytext);
            strcpy(yylval.nd_obj.name,(yytext));
            return cpp_ARITHMETIC_OPERATOR;
        }
    } 
    else {
        printf("%s is a  integer3 (line: %d, column: %d)\n", yytext, countn, col_num);
        prev='@';
        yy_text = strdup(yytext);
        strcpy(yylval.nd_obj.name,(yytext));
        return cpp_INT;
    }
    col_num += yyleng;
}

{float} {
    if(prev != '=') {
        if(yytext[0]!='+' && yytext[0]!='-'){
            printf("%s is an unsigned float (line: %d, column: %d)\n",yytext, countn, col_num);
            yy_text = strdup(yytext);
            strcpy(yylval.nd_obj.name,(yytext));
            return cpp_FLOAT;
        }
        else{
            printf("%s is arithmatic operator\n%s is a float (line: %d, column: %d)\n", yytext[0],yytext+1, countn, col_num+1);
            unput(yytext[0]); // Put back the arithmatic operator into the input stream
            yy_text = strdup(yytext);
            strcpy(yylval.nd_obj.name,(yytext));
            return cpp_ARITHMETIC_OPERATOR;
        }
    } 
    else {
        printf("%s is a signed float (line: %d, column: %d)\n", yytext, countn, col_num);
        yy_text = strdup(yytext);
        strcpy(yylval.nd_obj.name,(yytext));
        return cpp_FLOAT;
    }
    prev='@';
    col_num += yyleng;
}

{finish} {
    printf("%s is the end of a statement (line: %d, column: %d)\n", yytext, countn, col_num);
    prev='@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_FINISH;
}

{arthematic_operator} {
    
    if(prev != '='){
        printf("%s is an arithmatic operator (line: %d, column: %d)\n", yytext, countn, col_num);
        prev='@';
        col_num += yyleng;
        yy_text = strdup(yytext);
        strcpy(yylval.nd_obj.name,(yytext));
        return cpp_ARITHMETIC_OPERATOR;
    }
    else if(yytext[0] == '+' || yytext[0] == '-') {
        int c;
        do {
            c = input();
        } while (isspace(c));
        
        if (isdigit(c)) {
            unput(c);
            printf("%c is an arithmetic operator\n%s is an integer (line: %d, column: %d)\n", yytext[0], yytext + 1, countn, col_num + 1);
            yy_text = strdup(yytext);
            strcpy(yylval.nd_obj.name,(yytext));
            return cpp_ARITHMETIC_OPERATOR;
        } else {
            unput(c);
            printf("%s is an arithmatic operator (line: %d, column: %d)\n", yytext, countn, col_num);
            yy_text = strdup(yytext);
            strcpy(yylval.nd_obj.name,(yytext));
            return cpp_ARITHMETIC_OPERATOR;
        }
    } else {
        printf("%s is an arithmatic operator (line: %d, column: %d)\n", yytext, countn, col_num);
        prev = '@';
        col_num += yyleng;
        yy_text = strdup(yytext);
        strcpy(yylval.nd_obj.name,(yytext));
        return cpp_ARITHMETIC_OPERATOR;
    }
}

{logical_operator} {
    printf("%s is a comparison operator (line: %d, column: %d)\n", yytext, countn, col_num);
    prev='@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_LOGICAL_OPERATOR;
}

{comparision_operator} {
    printf("%s is a comparison operator (line: %d, column: %d)\n", yytext, countn, col_num);
    prev='@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_COMPARISON_OPERATOR;
}

{assignment_operator} {
    printf("%s is an assignment operator (line: %d, column: %d)\n", yytext, countn, col_num);
    prev='=';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_ASSIGNMENT_OPERATOR;
}

{cpp_import} {
    printf("%s is import keyword (line: %d, column: %d)\n", yytext, countn, col_num);
    prev='@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_IMPORT;
}

{datatype} {
    printf("%s is a data type (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_DATATYPE;
}

{cpp_if} {
    printf("%s is a cpp_if statement (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_IF;
}

{cpp_elif} {
    printf("%s is a cpp_elif statement (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_ELIF;
}

{cpp_else} {
    printf("%s is a cpp_else statement (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_ELSE;
}

{cpp_while} {
    printf("%s is a cpp_while statement (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_WHILE;
}

{cpp_function} {
    printf("%s is a cpp_function keyword (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_FUNCTION;
}

{cpp_return} {
    printf("%s is a cpp_return keyword (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_RETURN;
}

{cpp_print} {
    printf("%s is a cpp_print keyword (line: %d, column: %d)\n", yytext, countn, col_num);
    prev = '@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_PRINT;
}

{space} {
    col_num += yyleng;
    //return -1; // No token associated with space
}

{newline} {
    printf("%s is a new line (line: %d)\n", yytext, countn);
    countn++;
    col_num = 1;
    yy_text = strdup(yytext);//
    strcpy(yylval.nd_obj.name,(yytext));
    return EOL;
}

{identifier} {
    printf("%s is an identifier (line: %d, column: %d)\n", yytext, countn, col_num);
    prev='i'; 
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return cpp_IDENTIFIER;
}

{invalidIdentifier} {
     printf("%s is an invalid identifier (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return -1; // No specific token for invalid identifier
}

{string} {
     printf("%s is a string (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_STRING;
}

"(" {
    printf("%s is an open curly bracket (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_OPEN_CURLY_BRACKET;
}
")" {
    printf("%s is an closed curly bracket (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_CLOSED_CURLY_BRACKET;
}
"[" {
    printf("%s is an open square bracket (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_OPEN_SQUARE_BRACKET;
}
"]" {
    printf("%s is an closed square bracket (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_CLOSED_SQUARE_BRACKET;
}
"{" {
    printf("%s is an open flower bracket (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_OPEN_FLOOR_BRACKET;
}
"}" {
    printf("%s is an closed flower bracket (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_CLOSED_FLOOR_BRACKET;
}  
"," {
    printf("%s is a punctuation comma (line: %d, column: %d)\n", yytext, countn, col_num);
     prev='@';
     col_num += yyleng;
     yy_text = strdup(yytext);
     strcpy(yylval.nd_obj.name,(yytext));
     return cpp_PUNCTUATION_COMMA;
}

"//"        {
                while (1) {
                    int c = input();
                    if (c == '\n' || c == EOF) {
                        unput(c);
                        break;
                    }
                }
            }

. {
    printf("\nLEXICAL ERROR:%s is not defined for me (line: %d, column: %d)\n\n", yytext, countn, col_num);
    prev='@';
    col_num += yyleng;
    yy_text = strdup(yytext);
    strcpy(yylval.nd_obj.name,(yytext));
    return -1; // No specific token for undefined character
}

%%

int yywrap(){
    //return 1;
}