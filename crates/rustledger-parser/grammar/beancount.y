/*
 * Beancount v3 token-level LALR(1) grammar -- clean-room.
 *
 * SPDX-License-Identifier: MIT
 *
 * This grammar reproduces the *syntax-error behaviour* of beancount 3.2.3's
 * parser: which token each syntax error is reported at, how many errors are
 * reported, and the exact "syntax error, unexpected X, expecting ..." text.
 * It was written without access to beancount's grammar or lexer sources,
 * from documentation and black-box experiments only.  See PROVENANCE.md.
 *
 * Terminals are the token names beancount's lexer reports through
 * beancount.parser.lexer.lex_iter_string (see LEXICAL.md).  There are no
 * semantic actions: checks beancount performs in its actions (too many
 * strings on a transaction, deprecated pipe, invalid options, ...) are not
 * syntax errors and are not modelled.
 *
 * How the parse tables are meant to be driven (and how
 * harness/lalr.py drives them):
 *
 *   - Standard bison yacc.c error recovery.  The only `error` production is
 *     at top level (`declarations : declarations error`), so after any
 *     syntax error the parser unwinds to the top level and discards tokens
 *     until one can start a new declaration.  An error is only reported if
 *     three tokens have been shifted since the previous error.
 *   - A lexer error is delivered as bison's YYerror token: it enters error
 *     recovery directly, without reporting a syntax error.
 *   - End of input is token 0 and is delivered repeatedly, as a flex scanner
 *     does: it may terminate a line (rule `eol`) and is then read again.
 *
 * Token declaration order matters only for the order of the tokens listed
 * in "expecting ..." messages; the order below is consistent with every
 * message observed from beancount.
 */

%define parse.error verbose

%token YYEOF 0 "end of file"
%token EOL INDENT
%token PIPE ATAT AT LCURLCURL RCURLCURL LCURL RCURL COMMA TILDE HASH ASTERISK
%token SLASH COLON PLUS MINUS LPAREN RPAREN
%token FLAG
%token TXN BALANCE OPEN CLOSE COMMODITY PAD EVENT PRICE NOTE DOCUMENT QUERY CUSTOM
%token PUSHTAG POPTAG PUSHMETA POPMETA OPTION INCLUDE PLUGIN
%token DATE ACCOUNT CAPITAL CURRENCY STRING NUMBER BOOL NONE TAG LINK KEY

%left MINUS PLUS
%left ASTERISK SLASH
%precedence NEGATIVE

/* Two shift/reduce conflicts, both resolved by shifting: in a custom
 * directive, a value list `1 -2` (or `1 +2`) is read as the single
 * expression `1-2`, not as two values.  Observed: `custom "x" 1 -2` yields
 * the one value -1. */
%expect 2

%start file

%%

file : declarations ;

declarations : %empty
             | declarations declaration
             | declarations error
             ;

/* A blank or comment-only line is a bare EOL.  An indented line is never a
 * declaration of its own: INDENT at top level is a syntax error. */
declaration : EOL
            | directive
            | entry
            ;

/* A line may also be ended by the end of the input. */
eol : EOL | YYEOF ;

/* Undated directives take no indented lines. */
directive : OPTION STRING STRING eol
          | INCLUDE STRING eol
          | PLUGIN STRING eol
          | PLUGIN STRING STRING eol
          | PUSHTAG TAG eol
          | POPTAG TAG eol
          | PUSHMETA key_value eol
          | POPMETA KEY COLON eol
          ;

entry : DATE txn_flag txn_strings tags_links eol txn_lines
      | DATE BALANCE ACCOUNT amount_tolerance eol kv_lines
      | DATE OPEN ACCOUNT currency_list opt_booking eol kv_lines
      | DATE CLOSE ACCOUNT eol kv_lines
      | DATE COMMODITY currency eol kv_lines
      | DATE PAD ACCOUNT ACCOUNT eol kv_lines
      | DATE PRICE currency amount eol kv_lines
      | DATE EVENT STRING STRING eol kv_lines
      | DATE QUERY STRING STRING eol kv_lines
      | DATE NOTE ACCOUNT STRING tags_links eol kv_lines
      | DATE DOCUMENT ACCOUNT STRING tags_links eol kv_lines
      | DATE CUSTOM STRING custom_values eol kv_lines
      ;

/* Transactions. */

txn_flag : TXN | ASTERISK | FLAG | HASH | CAPITAL ;

/* Any number of strings (more than two is a semantic error, not a syntax
 * error); the deprecated `|` separator may appear anywhere among them. */
txn_strings : %empty
            | txn_strings STRING
            | txn_strings PIPE
            ;

tags_links : %empty
           | tags_links TAG
           | tags_links LINK
           ;

/* The lines of a transaction.  Postings, metadata and tag/link lines may
 * come in any order (tags after the first posting are a semantic error).
 * `INDENT tags_links eol` with no tags is an indented comment line. */
txn_lines : %empty
          | txn_lines INDENT tags_links eol
          | txn_lines INDENT key_value eol
          | txn_lines posting
          ;

/* The eol belongs to each posting alternative: after the cost, the parser
 * expects "end of file or EOL or ATAT or AT". */
posting : INDENT opt_flag ACCOUNT incomplete_amount cost_spec eol
        | INDENT opt_flag ACCOUNT incomplete_amount cost_spec AT incomplete_amount eol
        | INDENT opt_flag ACCOUNT incomplete_amount cost_spec ATAT incomplete_amount eol
        ;

opt_flag : %empty | ASTERISK | FLAG | HASH | CAPITAL ;

/* Metadata lines of the other dated directives; a bare INDENT eol is an
 * indented comment line.  Tag/link lines are not allowed here. */
kv_lines : %empty
         | kv_lines INDENT eol
         | kv_lines INDENT key_value eol
         ;

key_value : KEY COLON kv_value ;

kv_value : %empty
         | STRING
         | ACCOUNT
         | DATE
         | currency
         | TAG
         | BOOL
         | NONE
         | number_expr
         | amount
         ;

/* A single capital letter (token CAPITAL) is a valid currency. */
currency : CURRENCY | CAPITAL ;

number_expr : NUMBER
            | number_expr PLUS number_expr
            | number_expr MINUS number_expr
            | number_expr ASTERISK number_expr
            | number_expr SLASH number_expr
            | MINUS number_expr %prec NEGATIVE
            | PLUS number_expr %prec NEGATIVE
            | LPAREN number_expr RPAREN
            ;

amount : number_expr currency ;

/* Posting and price amounts may omit the number, the currency, or both. */
incomplete_amount : %empty
                  | number_expr
                  | currency
                  | number_expr currency
                  ;

amount_tolerance : amount
                 | number_expr TILDE number_expr currency
                 ;

/* Costs: {...} per unit or {{...}} total.  Components are separated by
 * commas; the list may be empty, and so (quirk) may the first component
 * only: `{, 1 USD}` is accepted, `{1 USD,}` and `{,}` are syntax errors. */
cost_spec : %empty
          | LCURL cost_comp_list RCURL
          | LCURLCURL cost_comp_list RCURLCURL
          ;

cost_comp_list : %empty
               | cost_comp
               | cost_comp_list COMMA cost_comp
               ;

cost_comp : compound_amount
          | DATE
          | STRING
          | ASTERISK
          ;

/* `per # total CUR` compound costs; either number may be missing. */
compound_amount : maybe_number currency
                | number_expr
                | maybe_number HASH maybe_number currency
                ;

maybe_number : %empty | number_expr ;

currency_list : %empty
              | currency
              | currency_list COMMA currency
              ;

opt_booking : %empty | STRING ;

custom_values : %empty
              | custom_values custom_value
              ;

custom_value : STRING
             | DATE
             | BOOL
             | amount
             | number_expr
             | ACCOUNT
             ;

%%
