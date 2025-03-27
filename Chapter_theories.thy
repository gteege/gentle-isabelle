theory Chapter_theories
  imports Chapter_system
begin
chapter "Isabelle Theories"
text_raw\<open>\label{theory}\<close>

text \<open>
A theory\index{theory} is the content of an Isabelle theory file.
\<close>

section "Theory Notation"
text_raw\<open>\label{theory-notation}\<close>

text\<open>
Theories are written using a notation which follows strict syntax rules, similar to a programming
language. The interactive editor helps using correct notation by immediately signaling syntax
errors upon input. However, it is crucial to also understand the \<^emph>\<open>meaning\<close> of the written text.
This introduction describes both in a systematic stepwise manner.
\<close>

subsection "Languages for Theory Content"
text_raw\<open>\label{theory-notation-lang}\<close>

text \<open>
Isabelle aims at two main goals: Supporting interactive work with mathematical formulas
and proofs, and supporting their presentation together with explanations as nicely typeset text in
the form of an article or a book. For this purpose Isabelle combines three different languages for
writing theory content:

 \<^item> a language for mathematics, called the ``inner syntax'',
 \<^item> a language for textual content, which is an extended form of \LaTeX\ source code,
 \<^item> a language for organizing fragments of the first two languages in a theory, called the ``outer
syntax''.\<close>

subsubsection "Inner Syntax"

text\<open>
For the inner syntax\index{syntax!inner $\sim$} Isabelle tries to be as close as possible to the form how mathematical content
is traditionally presented in books. It supports formulas such as \<open>\<forall>x\<le>100 . x\<in>{y\<^sup>2 | y. y\<le>10}\<close> both
in the interactive editor and the textual presentation. It does not support larger two-dimensional
constructs like matrices or fractions.\<close>

subsubsection "Outer Syntax"

text\<open>
The outer syntax\index{syntax!outer $\sim$} resembles a programming language. It uses keywords to construct larger entities
like definitions and proofs. These entities usually contain mathematical formulas written in inner
syntax. To clearly separate both languages, content in inner syntax must always be surrounded
by double quotes  \<open>"\<dots>"\<close> or by the ``cartouche delimiters'' \<open>\<open>\<dots>\<close>\<close> available in the editor's
Symbols panel in tab ``Punctuation''. The only exception is a single isolated identifier, for it the
quotes or delimiters  may be omitted.

This introduction describes only a selected part of the outer and inner syntax. The full
notation used by Isabelle is described in the Isabelle/Isar reference manual \<^cite>\<open>"isar-ref"\<close> with
some more advanced parts in other documentation \<^cite>\<open>datatypes and corec and eisbach\<close>.\<close>

subsubsection \<open>Embedded \LaTeX\ Code\<close>

text\<open>
Additionally, text written in \LaTeX\ syntax\index{syntax!LaTeX $\sim$} can be embedded into the outer syntax using the form
\<^theory_text>\<open>text\<open> \<dots> \<close>\<close>
and \LaTeX\ sections\index{sections} can be created using
\<^theory_text>\<open>chapter\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>section\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>subsection\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>subsubsection\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>paragraph\<open> \<dots> \<close>\<close>,
\<^theory_text>\<open>subparagraph\<open> \<dots> \<close>\<close>.
 
It is also possible to embed inner and outer syntax in the \LaTeX\ syntax (see Chapter 4 in the 
Isabelle/Isar Reference Manual).\<close>

subsubsection "Comments"

text\<open>
Moreover, comments\index{comments} of the form
\begin{verbatim}
  (* ... *)
\end{verbatim}
can be embedded into the outer syntax. They are only intended for the reader of the theory file
and are not displayed in the session document.

Line breaks\index{line breaks} are ignored as part of the outer and inner syntax and have the same effect as
a space.
\<close>

subsection "Meta Level and Object Level"
text_raw\<open>\label{theory-notation-meta}\<close>

text \<open>
Isabelle consists of a small fixed kernel which is called ``meta-logic''\index{meta-logic}\index{logic!meta-}. It is implemented in the
session \<^verbatim>\<open>Pure/Pure\<close>\index{Pure (session)} (see Section~\ref{system-invoke-theory}) which is the ancestor of all other
sessions. To be useful the meta-logic must be extended by an ``object logic''\index{object logic}\index{logic!object $\sim$}. It may consist of one
or more sessions, all sessions other than \<^verbatim>\<open>Pure/Pure\<close> are parts of an object logic. There are many
object logics available for Isabelle, the most versatile is HOL\index{HOL (object logic)}. Although called a ``logic'' it is
a full extensible representation of mathematics.

This introduction first describes the Isabelle kernel features, followed by a
description of the object logic HOL in Chapters~\ref{holbasic} and subsequent chapters.

Both outer\index{syntax!outer $\sim$} and inner\index{syntax!inner $\sim$} syntax consist of a part for the kernel
(the ``meta-level''\index{meta-level}\index{level!meta-} of the languages)
and a part introduced by and specific for the object logic (the ``object-level''\index{object-level}\index{level!object-} of the languages).
While the meta-level of the inner syntax is extremely small, mainly consisting of only four logical
operators, the meta-level of the outer syntax supports a large set of constructs for specifying
entities like axioms, definitions, proofs, and, finally, whole theories.

This introduction describes the meta-level of the inner syntax mainly in
Sections~\ref{theory-terms} and~\ref{theory-prop}. The rest of the sections about the
Isabelle kernel describe the meta-level of the outer syntax. Chapter~\ref{holbasic} describes basic
parts of the object level of the inner and outer syntax for HOL. Chapter~\ref{holtdefs} describes
a major part of the outer syntax for HOL, whereas Chapter~\ref{holtypes} describes an important part
of the inner syntax for HOL.
\<close>

subsection "Theory Structure"
text_raw\<open>\label{theory-notation-struct}\<close>

text \<open>
The content of a theory file\index{theory!file} has the outer syntax structure
@{theory_text[display]
\<open>theory name
imports name\<^sub>1 \<dots> name\<^sub>n
begin
  \<dots>
end\<close>}\index{theory (keyword)}\index{imports (keyword)}
where \<^theory_text>\<open>name\<close> is the theory name\index{theory!name} and \<^theory_text>\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are the names of the imported theories\index{theories!imported $\sim$}.
The theory name \<^theory_text>\<open>name\<close> must be the same which is used for the theory file, i.e., the file name 
must be \<^verbatim>\<open>name.thy\<close>.\<close>

section "Terms and Types"
text_raw\<open>\label{theory-terms}\<close>

text \<open>
The two main constituents of the inner syntax are terms\index{term} and types\index{type}. 
As usual in formal logics, the basic building blocks of propositions are terms. Terms denote arbitrary
objects like numbers, sets, functions, or boolean values. Isabelle is strongly typed, so every term 
must have a type  which names the type of values denoted by the term. 
However, in most situations Isabelle can derive the type of a term automatically,
so that it needs not be specified explicitly.
\<close>

subsection "Types"
text_raw\<open>\label{theory-terms-types}\<close>

text \<open>
Types are basically specified by type names\index{type!name}\index{name!for type}. In Isabelle HOL (see Chapter~\ref{holbasic}) there are 
predefined types such as \<open>nat\<close>\index{nat (type)} and \<open>bool\<close>\index{bool (type)} for natural numbers and boolean values.  With the
exception of function types, types like these with a mathematical meaning always belong to an object
logic. Chapter~\ref{holtypes} gives a detailed description of several important types of HOL. Due
to the lack of adequate types in the meta-logic this introduction uses a small set of HOL types for
examples to illustrate concepts on the meta-level, assuming an intuitive understanding of the
associated operations and terms.\<close>

subsubsection "Type Declarations"

text\<open>
New type names can be introduced using the outer syntax construct
@{theory_text[display]
\<open>typedecl name\<close>}\index{typedecl (keyword)}
which introduces the \<^theory_text>\<open>name\<close> for a new type for which the values are different from the values of 
all existing types and the set of values is not empty. No other information about the values is 
given, that may be done separately. See Chapter~\ref{holtdefs} for ways of defining types with
specifying more information about their values.\<close>

subsubsection "Parameterized Types and Polymorphic Types"

text\<open>
Types can be parameterized\index{type!parameterized $\sim$}\index{parameterized!type}, then the type
parameters\index{type!parameter} are denoted \<^emph>\<open>before\<close> the type name, such as in
\<open>nat set\<close> which is the  HOL  type of sets of natural numbers. A type name with \<open>n\<close> parameters is declared
in the form
@{theory_text[display]
\<open>typedecl ('name\<^sub>1,\<dots>,'name\<^sub>n) name\<close>}
where the parentheses may be omitted if \<open>n = 1\<close>, such as in \<^theory_text>\<open>typedecl 'a set\<close>.
The type parameters are denoted by ``type variables''\index{type!variables} which always have the 
form \<open>'name\<close> with a leading single quote character.

A type name with parameters is called a ``type constructor''\index{type!constructor} because it is not a type on its own.
Every use where the parameters are replaced by actual types, such
as in \<open>nat set\<close>, is called an ``instance''\index{type!instance} of the parameterized type.

Parameters of a type constructor may again be replaced by parameterized types, such as in \<open>('a set) set\<close>.
In this way arbitrary complex ``type expressions''\index{type!expression} can be built, consisting
of type constructors, type names, type variables, and parentheses. Generally, types in Isabelle may
be specified by arbitrary type expressions.

If a type expression contains type variables, such as in \<open>'a set\<close> or if it consists of a single type
variable such as \<open>'a\<close> the denoted type is called ``polymorphic''\index{type!polymorphic $\sim$}\index{polymorphic}.
A polymorphic type can be used as a type specification, its meaning is that an arbitrary instance
can be used where the type variables are replaced by actual types.\<close>

subsubsection "Type Synonyms"

text\<open>
Alternatively a type name can be introduced as a synonym\index{type!synonym} for an existing type in the form
@{theory_text[display]
\<open>type_synonym name = type\<close>}\index{type-synonym@type$\_$synonym (keyword)}
such as in  \<^theory_text>\<open>type_synonym natset = "nat set"\<close>. Type synonyms can also be parameterized as in
@{theory_text[display]
\<open>type_synonym ('name\<^sub>1,\<dots>,'name\<^sub>n) name = type\<close>}
where \<open>type\<close> may be a polymorphic type which contains atmost the type variables \<open>'name\<^sub>1,\<dots>,'name\<^sub>n\<close>.
\<close>

subsection "Constants and Variables"
text_raw\<open>\label{theory-terms-consts}\<close>

text \<open>
Terms are mainly built as syntactical structures based on constants\index{constant} and variables\index{variable}. Constants are usually
denoted by names\index{constant!name}\index{name!for constant}, using the same namespace as type names. Whether a name denotes a constant or a 
type depends on its position in a term. In HOL predefined constant names of type
\<open>bool\<close> are \<open>True\<close>\index{True (constant)} and \<open>False\<close>\index{False (constant)}.

Constants of number types, such as \<open>nat\<close>, may be denoted by number literals\index{number literal}, such as \<open>6\<close>
or \<open>42\<close>. Nested terms are generally written by using parentheses\index{parentheses} \<open>(\<dots>)\<close>. There are many priority
rules how to nest terms automatically, but if in doubt, it is always safe to use parentheses.
\<close>

subsubsection "Constants Declarations"

text\<open>
A new constant name can be introduced by specifying its type. The outer syntax construct
@{theory_text[display]
\<open>consts name\<^sub>1 :: type\<^sub>1 \<dots> name\<^sub>n :: type\<^sub>n\<close>}\index{consts (keyword)}
introduces \<open>n\<close> constants with their names and types. No information is specified about the 
constant's values, in this respect the constants are ``underspecified''\index{constant!underspecified $\sim$}\index{underspecified!constant}. The information about the
values may be specified separately.

If the constant's type is polymorphic (see Section~\ref{theory-terms-types}) the constant is 
also called polymorphic\index{constant!polymorphic $\sim$}\index{polymorphic}. Thus the declaration
@{theory_text[display]
\<open>consts myset :: "'a set"\<close>}\index{myset (example constant)}
declares the polymorphic constant \<open>myset\<close> which may be a set of elements of arbitrary type.
Note the use of quotes because the type is specified in inner syntax and is not a single
type name.\<close>

subsubsection "Variables"

text\<open>
A (term) variable\index{variable}\index{name!for variable} has the same form as a constant name, but it has not been introduced as a 
constant. Whenever a variable is used in a term it has a specific type which is either derived 
from its context or is explicitly specified\index{type!specification} in inner syntax in the form \<open>varname :: type\<close>.\<close>
 
subsection "Functions"
text_raw\<open>\label{theory-terms-functions}\<close>

text \<open>
A constant name denotes an object, which, according to its type, may also be a function\index{function} of 
arbitrary order. Functions basically have a single argument\index{function!argument}. The type of a function is written
in inner syntax as \<open>argtype \<Rightarrow> restype\<close>\index{function!type}\index{=>@\<open>\<Rightarrow>\<close> (operator)} or equivalently
as \<open>(argtype, restype) fun\<close>\index{fun (type)} (thus \<open>fun\<close> is a type constructor with two arguments). These ways of denoting function
types belongs to the meta-level of the inner syntax and is thus available in all object logics.

Functions in Isabelle are always total, i.e., they map every value of type \<open>argtype\<close> to some value
of type \<open>restype\<close>. However, a function may be ``underspecified''\index{function!underspecified $\sim$}\index{underspecified!function} so that no information is (yet)
available about the result value for some or all argument values. A function defined by
@{theory_text[display]
\<open>consts mystery :: "nat \<Rightarrow> nat"\<close>}\index{mystery (example constant)}
is completely underspecified: although it maps every natural number to a unique other natural number
no information about these numbers is available. Functions may also be partially specified by 
describing the result value only for some argument values. This does not mean that the function is
``partial'' and has no value for the remaining arguments. The information about these values may
always be provided later, this does not ``modify'' the function, it only adds information about it.
\<close>

subsection "Functions with Multiple Arguments"
text_raw\<open>\label{theory-terms-multargs}\<close>

text\<open>
The result type
of a function may again be a function type, then it may be applied to another argument. This is used
to represent functions with more than one argument\index{function!multiple arguments}. Function types are right associative, thus a 
type \<open>argtype\<^sub>1 \<Rightarrow> argtype\<^sub>2 \<Rightarrow> \<cdots> \<Rightarrow> argtype\<^sub>n \<Rightarrow> restype\<close> describes functions which can be applied 
to \<open>n\<close> arguments.\<close>

subsubsection "Function Application"

text\<open>
Function application\index{function!application} terms for a function \<open>f\<close> and an argument \<open>a\<close> are denoted in inner
syntax  by
\<open>f a\<close>, no parentheses are required around the argument. Function application terms are left 
associative, thus a function application to \<open>n\<close> arguments is written \<open>f a\<^sub>1 \<dots> a\<^sub>n\<close>. Note that an
application \<open>f a\<^sub>1 \<dots> a\<^sub>m\<close> where \<open>m < n\<close> (a ``partial application'')\index{function!application!partial $\sim$} is a correct term and denotes a
function taking the remaining \<open>n-m\<close> arguments.\<close>

subsubsection "Infix Function Application"

text\<open>
For every constant alternative syntax forms may be defined for application terms. This is often used
for binary functions to represent application terms in infix notation\index{infix notation} with an operator symbol\index{operator symbol}\index{symbol!operator $\sim$}.
As an example, the name for the addition function in HOL is \<open>plus\<close>, so an application term is denoted
in the form \<open>plus 3 5\<close>. For \<open>plus\<close> the alternative name \<open>(+)\<close> is defined (the parentheses are part
of the name). For functions with such ``operator names''\index{operator name} an application term \<open>(+) 3 5\<close> can also be
denoted in infix form \<open>3 + 5\<close>. Infix notation is supported for many basic functions and predicates
in HOL ,
having operator names such as \<open>(-)\<close>, \<open>(**)\<close>, \<open>(=)\<close>, \<open>(\<noteq>)\<close>, \<open>(\<le>)\<close>, or \<open>(\<in>)\<close>. 
\<close>

subsection "Lambda-Terms"
text_raw\<open>\label{theory-terms-lambda}\<close>

text\<open>
Functions can be denoted in inner syntax by lambda terms\index{lambda term}\index{term!lambda $\sim$} of the form \<open>\<lambda>x. term\<close>\index{/lam@\<open>\<lambda>\<close> (binder)} where \<open>x\<close> is a variable
which may occur in the \<open>term\<close>. The space between the dot and the \<open>term\<close> is often required to
separate both. A function to be applied to \<open>n\<close> arguments can be denoted by the
lambda term \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. term\<close> where \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are distinct variables. As usual, types may be
specified for (some of) the variables in the form \<open>\<lambda>(x\<^sub>1::t\<^sub>1) \<dots> (x\<^sub>n::t\<^sub>n). term\<close>. The parentheses
may be omitted if there is only one argument variable.

A constant function\index{function!constant $\sim$} has a value which does not depend on the argument, thus the variable \<open>x\<close>
does not occur in the \<open>term\<close>. Then its name is irrelevant and it may be replaced by the ``wildcard''\index{wildcard}
\<open>_\<close> (an underscore) as in \<open>\<lambda>_. term\<close>.\<close>

subsubsection "Binding Variables"

text\<open>
If a variable from the \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> occurs in the \<open>term\<close> of \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. term\<close> it is called a
``bound''\index{variable!bound $\sim$} occurrence and denotes the corresponding function argument. If an occurrence of a variable
\<open>x\<close> is not a part of a lambda term \<open>\<lambda>\<dots> x \<dots> . term\<close> the occurrence is called ``free''\index{free occurrence}\index{variable!free occurrence of $\sim$}.

A lambda term is a case of ``binder syntax''\index{syntax!binder $\sim$}\index{binder syntax}. It consists of a ``binder''\index{binder} (here \<open>\<lambda>\<close>)
followed by one or more variables with optional type specifications, followed by a dot and a term
(called ``body''\index{binder syntax!body in $\sim$}\index{body in binder syntax}).
Terms of the inner syntax nearly always have either the form of a function application, possibly
in infix notation, or the form of a binder syntax.
\<close>

subsection "Searching Constants"
text_raw\<open>\label{theory-terms-search}\<close>

text \<open>
Constants may be searched\index{constant!search $\sim$}\index{search!for constants} using the command
@{theory_text[display]
\<open>find_consts criterion\<^sub>1 \<dots> criterion\<^sub>n\<close>}\index{find-consts@find$\_$consts (keyword)}
or using the Query panel\index{panel!query $\sim$} (see Section~\ref{system-jedit-query}) in the ``Find Constants'' tab using
the sequence \<open>criterion\<^sub>1 \<dots> criterion\<^sub>n\<close> as search specification\index{search!specification} in the ``Find:'' input field. The
\<open>criterion\<^sub>i\<close> are combined by conjunction.

The command \<^theory_text>\<open>find_consts\<close> may be entered in the text area between other theory content such as
type or constant declarations. It finds all named constants which have been introduced before the
command position. Searches using the Query panel find all named constants which have been introduced
before the cursor position in the text area.\<close>

subsubsection "Searching by Type"

text\<open>
A \<open>criterion\<^sub>i\<close> may be a type, specified in inner syntax and quoted if not a single type name. Then
the search finds all constants where the type occurs as a part of the constant's type. For example,
it finds all functions which have the specified type as argument or result type.

A \<open>criterion\<^sub>i\<close> may also have the form \<open>strict: "type"\<close>, then the search only finds constants which
have that type. In both cases the specified type may be a function type, then the search finds
corresponding named functions.

If the specified type is polymorphic the search will also find constants which have an instance
of it as their type or as a part of the type, respectively.\<close>

subsubsection "Searching by Name"

text\<open>
A \<open>criterion\<^sub>i\<close> may also have the form \<open>name: strpat\<close> where \<open>strpat\<close> is a string pattern which may
use ``*'' as wildcard (then the pattern must be enclosed in double quotes). Then all constants are
found where the \<open>strpat\<close> matches a substring of their name.
\<close>

section "Definitions and Abbreviations"
text_raw\<open>\label{theory-definition}\<close>

text \<open>
A constant name may be introduced together with information about its associated value by specifying 
a term for the value. There are two forms for introducing constant names in this way, definitions
and abbreviations. Both are constructs of the outer syntax.
\<close>

subsection "Definitions"
text_raw\<open>\label{theory-definition-defs}\<close>

text\<open>
A definition\index{constant!definition}\index{definition!for constant} defines a new constant together with its type and value.
It is denoted in the form
@{theory_text[display]
\<open>definition name where "name \<equiv> term"\<close>}\index{definition (keyword)}\index{where (keyword)}
Note that the ``defining equation'' \<open>name \<equiv> term\<close> is specified in inner syntax and must be
delimited by quotes. The operator \<open>\<equiv>\<close>\index{=@\<open>\<equiv>\<close> (meta-logic operator)} is the equality\index{equality!meta $\sim$} operator of the meta-logic (see
Section~\ref{theory-notation-meta}). The \<open>name\<close> may not occur in the \<open>term\<close>, i.e., this form
of definition
does not support recursion. Also, no free variables may occur in the \<open>term\<close>. In the object logic HOL
(see Chapter~\ref{holbasic}) also the normal equality operator \<open>=\<close>\index{=@\<open>=\<close> (operator)} may be used instead of \<open>\<equiv>\<close>.

The type of the defined constant is the same as that of the \<open>term\<close>. If that type is polymorphic
(see Section~\ref{theory-terms-types}) a more specific type may be specified explicitly in the form
@{theory_text[display]
\<open>definition name :: type where "name \<equiv> term"\<close>}
As usual the type is specified in inner syntax and must be quoted if it is not a single type name.

A short form of a definition is
@{theory_text[display]
\<open>definition "name \<equiv> term"\<close>}

Usually, a constant defined in this way is fully specified, i.e., all information about its value
is available. However, if the term does not provide this information, the constant is still 
underspecified\index{constant!underspecified $\sim$}\index{underspecified!constant}. Consider the definition
@{theory_text[display]
\<open>definition mystery2 where "mystery2 \<equiv> mystery"\<close>}\index{mystery2 (example constant)}
where \<open>mystery\<close> is defined as above. Then it is only known that \<open>mystery2\<close> has type \<open>nat \<Rightarrow> nat\<close> and
is the same total function as \<open>mystery\<close>, but nothing is known about its values.\<close>

subsubsection "Defining Functions"

text\<open>
If the type of the defined constant is a function\index{function!definition}\index{definition!for function} type, the \<open>term\<close> may be a lambda term.
Alternatively, the definition for a function applicable to \<open>n\<close> arguments can be written in the form
@{theory_text[display]
\<open>definition name where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
with variable names \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> which may occur in the \<open>term\<close>. This form is mainly equivalent to
@{theory_text[display]
\<open>definition name where "name \<equiv> \<lambda>x\<^sub>1 \<dots> x\<^sub>n. term"\<close>}\<close>

subsection "Abbreviations"
text_raw\<open>\label{theory-definition-abbrevs}\<close>

text\<open>
An abbreviation\index{abbreviation!for constant}\index{constant!abbreviation} definition does not define a constant, it only introduces the name 
as a synonym for a term\index{term!synonym}. Upon input the name is automatically expanded, and upon output it is used 
whenever a term matches its specification and the term is not too complex. 
An abbreviation definition is denoted in a similar form as a definition:
@{theory_text[display]
\<open>abbreviation name where "name \<equiv> term"\<close>}\index{abbreviation (keyword)}\index{where (keyword)}
As for definitions, recursion is not supported, the \<open>name\<close> may not occur in the \<open>term\<close> and also
no free variables. An explicit type may be specified for \<open>name\<close> and the short form is also available
as for definitions.

The alternative form for functions\index{abbreviation!for function}\index{function!abbreviation} is also available. The abbreviation definition
@{theory_text[display]
\<open>abbreviation name where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
introduces a ``parameterized'' abbreviation. An application term \<open>name term\<^sub>1 \<dots> term\<^sub>n\<close> is replaced
upon input by \<open>term\<close> where all occurrences of \<open>x\<^sub>i\<close> have been substituted by \<open>term\<^sub>i\<close>. Upon output
terms are matched with the structure of \<open>term\<close> and if successful a corresponding application term
is constructed and displayed.
\<close>

section "Overloading"
text_raw\<open>\label{theory-overload}\<close>

subsection "True Overloading"
text_raw\<open>\label{theory-overload-true}\<close>

text \<open>
One way of providing information about the value of an underspecified constant is overloading\index{overloading}.
It provides the information with the help of another constant together with a definition for it.

Overloading depends on the type. Therefore, if a constant is 
polymorphic, different definitions can be associated for different type instances.

Overloading is only possible for constants which do not yet have a definition, i.e., they must
have been defined by \<^theory_text>\<open>consts\<close> (see Section~\ref{theory-terms-consts}).
Such a constant \<open>name\<close> is associated with \<open>n\<close> definitions by the following overloading
specification:
@{theory_text[display]
\<open>overloading
  name\<^sub>1 \<equiv> name
    \<dots>
  name\<^sub>n \<equiv> name
begin
  definition name\<^sub>1 :: type\<^sub>1 where \<dots>
    \<dots>
  definition name\<^sub>n :: type\<^sub>n where \<dots>
end\<close>}\index{overloading (keyword)}
where all \<open>type\<^sub>i\<close> must be instances of the type declared for \<open>name\<close>.

The auxiliary constants \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are only introduced locally and cannot be used outside
of the \<^theory_text>\<open>overloading\<close> specification.
\<close>

subsection "Adhoc Overloading"
text_raw\<open>\label{theory-overload-adhoc}\<close>

text\<open>
There is also a form of overloading\index{overloading!ad-hoc $\sim$} which achieves similar effects although it is implemented
completely differently. It is only performed on the syntactic level, like abbreviations.

A constant name \<open>name\<close> can be defined to be a ``type dependent abbreviation''
for \<open>n\<close> terms of different type instances by
@{theory_text[display]
\<open>adhoc_overloading name \<rightleftharpoons> term\<^sub>1 \<dots> term\<^sub>n\<close>}\index{adhoc-overloading@adhoc$\_$overloading (keyword)}
The syntactic operator \<open>\<rightleftharpoons>\<close>\index{==@\<open>\<rightleftharpoons>\<close> (syntactic operator)} is available for input in the
editor's Symbols panel in tab ``Arrow''. It means that translation between both sides occurs upon
input and output.
Upon input the type of \<open>name\<close> is determined from the context, then it is replaced by the 
corresponding \<open>term\<^sub>i\<close>. Upon output terms are matched with the corresponding \<open>term\<^sub>i\<close> and if 
successful \<open>name\<close> is displayed instead.

Although \<open>name\<close> must be the name of an existing constant, only its type is used. The constant is
not affected by the adhoc overloading, however, it becomes inaccessible because its name is now
used as term abbreviation. 

Several constant names can be overloaded in a common specification:

@{theory_text[display]
\<open>adhoc_overloading name\<^sub>1 \<rightleftharpoons> term\<^sub>1\<^sub>,\<^sub>1 \<dots> term\<^sub>1\<^sub>,\<^sub>n and \<dots> and name\<^sub>k \<rightleftharpoons> \<dots>\<close>}
\<close>

section "Propositions"
text_raw\<open>\label{theory-prop}\<close>

text \<open>
A proposition\index{proposition} denotes an assertion, which can be valid or not. Valid proposition are called
``facts''\index{fact}, they are the main content of a theory. Propositions are specific terms and
are hence written in inner syntax and must be enclosed in quotes.
\<close>

subsection "Formulas"
text_raw\<open>\label{theory-prop-formulas}\<close>

text \<open>
A simple form of a proposition is a single term of type \<open>bool\<close>\index{bool (type)}, such as
@{text[display]
\<open>6 * 7 = 42\<close>}
The \<open>*\<close> is the infix operator for multiplication, it may not be omitted in arithmetic
terms.

Terms of type \<open>bool\<close> are also called ``formulas''\index{formula}.  Since \<open>bool\<close> belongs to the object
logic HOL, formulas are also specific for HOL or another object logic, there are no formulas in
the meta-logic. The simplest form of a proposition on meta-level is a single variable.

A proposition may contain free variables as in
@{text[display]
\<open>2 * x = x + x\<close>}

A formula as proposition is valid if it evaluates to \<open>True\<close>\index{True (constant)} for all possible values substituted
for the free variables\index{free occurrence}\index{variable!free occurrence of $\sim$}.
\<close>

subsection "Derivation Rules"
text_raw\<open>\label{theory-prop-rules}\<close>

text \<open>
More complex propositions on the meta-level can express ``derivation rules''\index{derivation rule}\index{rule!derivation $\sim$} used to derive propositions
from other propositions. Derivation rules are denoted using the meta-logic operator \<open>\<Longrightarrow>\<close>\index{==>@\<open>\<Longrightarrow>\<close> (meta-logic operator)}
and can thus be expressed independent of an object logic.

Derivation rules consist of assumptions\index{assumption} and a conclusion\index{conclusion}. They are written in the form
@{text[display]
\<open>A\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<close>}
where the \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> are the assumptions and \<open>C\<close> is the conclusion.  Since \<open>\<Longrightarrow>\<close> is right-associative
the conclusion can be assumed to be a single variable or a formula. 
The assumptions may be arbitrary propositions. If an
assumption contains meta-logic operators parentheses\index{parentheses} can be used to delimit them from the rest of the
derivation rule.

A derivation rule states that if the assumptions are valid, the conclusion can be derived
as also being valid.  So  \<open>\<Longrightarrow>\<close>  can be viewed as a ``meta implication''\index{implication!meta $\sim$} with a similar meaning as a
boolean implication, but with a different use.

An example for a rule with a single assumption is
@{text[display]
\<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close>}
Note that type \<open>nat\<close> is explicitly specified for variable \<open>x\<close>. This is necessary, because the
constants \<open><\<close>, \<open>*\<close>, and \<open>\<le>\<close> are overloaded and can be applied to other types than only natural
numbers. Therefore the type of \<open>x\<close> cannot be derived automatically. However, when the type of
\<open>x\<close> is known, the types of \<open>c\<close> and \<open>n\<close> can be derived to also be \<open>nat\<close>.

An example for a rule with two assumptions is
@{text[display]
\<open>(x::nat) < c \<Longrightarrow> n > 0 \<Longrightarrow> n*x < n*c\<close>}

In most cases the assumptions are also formulas, as in the example. However, they may also
be again derivation rules. Then the rule is a ``meta rule''\index{rule!meta $\sim$} which derives a proposition from other 
rules.
\<close>

subsection "Binding Free Variables"
text_raw\<open>\label{theory-prop-bind}\<close>

text \<open>
A proposition may contain universally bound variables\index{variable!bound $\sim$}, using the meta-logic quantifier
\<open>\<And>\<close>\index{/@\<open>\<And>\<close> (meta-logic binder)} in the form
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>n. P\<close>}
where the \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> may occur free in the proposition \<open>P\<close>.  This is another case of binder
syntax\index{syntax!binder $\sim$}\index{binder} (see Section~\ref{theory-terms-lambda}). As usual, types may be
specified for (some of) the variables in the form \<open>\<And> (x\<^sub>1::t\<^sub>1) \<dots> (x\<^sub>n::t\<^sub>n). P\<close>. An example for
a valid derivation rule with bound variables is
@{text[display]
\<open>\<And> (x::nat) c n . x < c \<Longrightarrow> n*x \<le> n*c\<close>}
\<close>

subsection "Rules with Multiple Conclusions"
text_raw\<open>\label{theory-prop-multconcl}\<close>

text \<open>
A derivation rule may specify several propositions to be derivable from the same assumptions using
the meta-logic operator \<open>&&&\<close>\index{.and@\<open>&&&\<close> (meta-logic operator)} in the form
@{text[display]
\<open>A\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close>}
Here the \<open>C\<^sub>i\<close> may be arbitrary propositions, like the assumptions. If they contain meta-logic
operators they must be enclosed in parentheses because \<open>&&&\<close> binds stronger than the other
meta-logic operators.

The rule is equivalent to the set of rules deriving each \<open>C\<^sub>i\<close> separately:
@{text[display]
\<open>A\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<^sub>1
  \<dots> 
A\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<^sub>h\<close>}

The rule states that if the assumptions are valid then all conclusions are valid. So  \<open>&&&\<close> can be
viewed as a ``meta conjunction''\index{conjunction!meta $\sim$} with a similar meaning as a boolean conjunction, but with a
different use.

An example for a rule with two conclusions is
@{text[display]
\<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c &&& n+x < n+c\<close>}\<close>

subsection "Alternative Rule Syntax"
text_raw\<open>\label{theory-prop-altsynt}\<close>

text \<open>
An alternative, Isabelle specific syntax\index{syntax!alternative $\sim$!for rules} for derivation rules  with possibly multiple conclusions is
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close>}
which is often considered as more readable, because it better separates the assumptions from the
conclusions. In the interactive editor to switch to this form it may be necessary to set 
\<^verbatim>\<open>Print Mode\<close> to \<^verbatim>\<open>brackets\<close> in \<^verbatim>\<open>Plugin Options\<close> for \<^verbatim>\<open>Isabelle General\<close>. The fat brackets are
available for input in the editor's Symbols panel in tab ``Punctuation''.

Using this syntax the two-assumption example rule from the previous section is denoted by
@{text[display]
\<open>\<And> (x::nat) c n. \<lbrakk>x < c; n > 0\<rbrakk> \<Longrightarrow> n*x < n*c\<close>}
or equivalently without quantifier by
@{text[display]
\<open>\<lbrakk>(x::nat) < c; n > 0\<rbrakk> \<Longrightarrow> n*x < n*c\<close>}

Note that in the literature a derivation rule @{thm conjI[no_vars]} is often denoted in the form
@{thm[display,mode=Rule] conjI[no_vars]}
\<close>

subsection "Structured Rule Syntax"
text_raw\<open>\label{theory-prop-struct}\<close>

text\<open>
Isabelle supports another alternative syntax for derivation rules  with possibly multiple
conclusions. It is called ``structured''\index{syntax!structured $\sim$!for rules}\index{structured form} form, since the rule is not specified by a single
proposition but by several separate propositions for the parts of the rule:
@{theory_text[display]
\<open>"C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m\<close>}\index{if (keyword)}\index{for (keyword)}
Here the conclusions, assumptions and the variables may be grouped or separated for better
\index{conclusion!group}\index{assumption!group}\index{variable!group}
readability by the keyword \<^theory_text>\<open>and\<close>\index{and (keyword)}. For every group of variables (but not for single variables in a
group) a type may be specified\index{type!specification} in the form \<open>x\<^sub>1 \<dots> x\<^sub>m :: "type"\<close>, it applies to all variables in the
group.

The keywords \<^theory_text>\<open>if\<close>, \<^theory_text>\<open>and\<close>, \<^theory_text>\<open>for\<close> belong to the outer syntax. Thus, a rule in structured form
cannot occur nested in another proposition, such as an assumption in another rule. Moreover, the
original rule must be quoted as a whole, whereas in the structured form only the sub-propositions
\<open>C\<^sub>1 \<dots> C\<^sub>h, A\<^sub>1, \<dots>, A\<^sub>n\<close> must be individually quoted. The \<open>x\<^sub>1, \<dots>, x\<^sub>m\<close> need not be quoted, but if a
type is specified for a variable group the type must be quoted, if it is not a single type name.

If written in this form, the two-assumption example rule from the previous section may become
@{theory_text[display]
\<open>"n*x < n*c" if "x < c" and "n > 0" for x::nat and n c\<close>}
and the rule with two conclusions depicted earlier may become
@{theory_text[display]
\<open>"n*x \<le> n*c" and "n+x < n+c" if "x < c" for x::nat and n c\<close>}
The assumptions and the conclusion in a rule in structured form may be arbitrary propositions, in
particular, they may be derivation rules (in unstructured form).  If a conclusion is a derivation
rule the assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> are added to the assumptions present in the conclusion.
\<close>

subsection "Conditional Definitions"
text_raw\<open>\label{theory-prop-conddefs}\<close>

text\<open>
A definition, as described in Section~\ref{theory-definition-defs} may be conditional\index{definition!conditional $\sim$}\index{conditional definition}, then its
defining equation has the form of a derivation rule
@{theory_text[display]
\<open>definition name where "\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> name \<equiv> term"\<close>}
or in structured form:
@{theory_text[display]
\<open>definition name where "name \<equiv> term" if "A\<^sub>1" \<dots> "A\<^sub>n"\<close>}
Since no free variables are allowed in \<open>term\<close> it is not possible to bind variables using \<open>\<And>\<close>.
The meaning of a conditional definition is that the value of \<open>name\<close> is only defined by the \<open>term\<close>
if all assumptions are valid. Otherwise it is underspecified.

For the rule conclusion also the form \<open>name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term\<close> can be used if \<open>name\<close> has a function
type. Then the \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> may occur in the \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> and restrict the specification of function
values to specific function arguments.

As for normal definitions a type may be specified for \<open>name\<close> and the short form may be used where
only the defining rule is given. For the abbreviations described in
Section~\ref{theory-definition-abbrevs} a conditional form is not available.
\<close>

section "Theorems"
text_raw\<open>\label{theory-theorem}\<close>

text \<open>
A theorem\index{theorem} specifies a proposition together with a proof, that the proposition is valid. Thus it
adds a fact\index{fact} to the enclosing theory.\<close>

subsection "Specifying Theorems"
text_raw\<open>\label{theory-theorem-spec}\<close>

text\<open>
A simple form of a theorem is
@{theory_text[display]
\<open>theorem "prop" \<proof>\<close>}\index{theorem (keyword)}
where \<open>prop\<close> is a proposition in inner syntax and \<^theory_text>\<open>\<proof>\<close> is a proof\index{proof} as described in 
Chapter \ref{proof}. The keyword \<^theory_text>\<open>theorem\<close> can be replaced by one of the keywords
\<^theory_text>\<open>lemma\<close>\index{lemma (keyword)}, \<^theory_text>\<open>corollary\<close>\index{corollary (keyword)}, \<^theory_text>\<open>proposition\<close>\index{proposition (keyword)} to give a hint about the use of the  theorem  to
the reader.

The example rule from the previous sections can be stated as a fact by the theorem
@{theory_text[display]
\<open>theorem "\<And> (x::nat) c n . x < c \<Longrightarrow> n*x \<le> n*c" \<proof>\<close>}\<close>

subsubsection "Implicit Variable Bindings"

text\<open>
If the proposition in a theorem contains free variables\index{free occurrence}\index{variable!free occurrence of $\sim$} they are implicitly universally
bound\index{variable!bound $\sim$}. Thus the previous example theorem is equivalent to the theorem
@{theory_text[display]
\<open>theorem "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" \<proof>\<close>}
Explicit binding of variables\index{variable!binding} is only required to avoid name clashes with 
constants of the same name. In the theorem
@{theory_text[display]
\<open>theorem "\<And> (True::nat). True < c \<Longrightarrow> n*True \<le> n*c" \<proof>\<close>}
the name \<open>True\<close> is used locally as a variable of type \<open>nat\<close> instead of the predefined constant
of type \<open>bool\<close>. Of course, using well known constant names as variables is confusing and should
be avoided.

Explicit binding of variables can also be useful to specify the variable types at a common place
in the proposition instead of scattering them over it. Finally, explicit variable binding makes
a difference for the \<open>\<proof>\<close>: it restricts the variables to the proposition so that they are
not available in the \<open>\<proof>\<close> (see Sections~\ref{proof-state-initial} and~\ref{proof-fix}).\<close>

subsubsection "Structured Form"

text\<open>
If the proposition in a theorem is a derivation rule with possibly multiple conclusions  it may also
be specified in structured form (see Section~\ref{theory-prop-struct}):
@{theory_text[display]
\<open>theorem "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
with optional grouping of all components by \<^theory_text>\<open>and\<close>. Remember that the \<open>C\<^sub>i\<close> may be arbitrary
propositions, therefore a theorem in this form may specify several derivation rules with additional
common assumptions and common bound variables. As for the unstructured form the explicit
binding of variables\index{variable!binding} in the \<^theory_text>\<open>for\<close> part is optional. If a theorem has free variables in a \<open>C\<^sub>i\<close> or in
a \<open>A\<^sub>i\<close> a \<^theory_text>\<open>for\<close> part is automatically added for all such variables.\<close>

subsubsection "Multiple Conclusions"

text\<open>
A theorem with multiple conclusions adds a separate fact for every conclusion to the enclosing
theory (copying all assumptions to every such fact), as if there had been a separate theorem for
every conclusion.

In particular, if no variables are explicitly bound and no common assumptions are present this
form allows to specify several propositions in a common theorem of the form
@{theory_text[display]
\<open>theorem "C\<^sub>1" \<dots> "C\<^sub>h" \<proof>\<close>}
where all propositions can be proved together in a single proof.

The example rules from the previous sections can be stated as facts by a common theorem in the form
@{theory_text[display]
\<open>theorem "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
    and "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m"
\<proof>\<close>}
Although the resulting facts are completely independent of each other, the variables are common
to both propositions. This means that it suffices to specify the type \<open>nat\<close> for \<open>x\<close> in one of them.
If different types are specified for \<open>x\<close> in the two propositions an error is signaled.
\<close>

subsection "Unknowns"
text_raw\<open>\label{theory-theorem-unknowns}\<close>

text \<open>
Whenever a theorem turns a proposition to a fact, the free (or universally bound) variables
are replaced by ``unknowns''\index{unknown}. For a variable \<open>name\<close> the corresponding unknown is \<open>?name\<close>.
This is only a technical difference, it signals to Isabelle that the unknowns can be 
consistently substituted by arbitrary terms, as long as the types are preserved.

The result of such a substitution\index{substitution} is always a special case of the fact and therefore also
a fact. In this way a fact with unknowns gives rise to a (usually infinite) number of facts
which are constructed by substituting unknowns by terms.

When turned to a fact, the rule used in the example theorems becomes
@{text[display]
\<open>?x < ?c \<Longrightarrow> ?n*?x \<le> ?n*?c\<close>}
with type \<open>nat\<close> associated to all unknowns.

Propositions specified in a theorem may not contain unknowns, they are only introduced by Isabelle
after proving the proposition.

Isabelle can be configured to suppress the question mark\index{question mark} when displaying unknowns, then
this technical difference becomes invisible.
\<close>

subsection "Named Facts"
text_raw\<open>\label{theory-theorem-named}\<close>

text \<open>
Facts are often used in proofs of other facts. For this purpose they can be named so 
that they can be referenced by name\index{fact!name}\index{name!for fact}. A named fact is specified by a theorem of the form
@{theory_text[display]
\<open>theorem name: "prop" \<proof>\<close>}
The names used for facts have the same form as names for constants and variables (see
Section~\ref{theory-terms-consts}). The same name can be used for a variable and a fact, they can
always be distinguished by the usage context.

The example rule from the previous sections can be turned into a fact named \<open>example1\<close> by
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" \<proof>\<close>}\index{example1 (example fact)}\<close>

subsubsection "Named Fact Collections"

text\<open>
It is also possible to introduce named collections of facts\index{fact!collection}\index{name!for fact collection}. A simple way to introduce
such a named collection is 
@{theory_text[display]
\<open>lemmas name = name\<^sub>1 \<dots> name\<^sub>n\<close>}
where \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are names of existing facts or fact collections.

If there is a second rule stated as a named fact by
@{theory_text[display]
\<open>theorem example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m" \<proof>\<close>}\index{example2 (example fact)}
a named collection can be introduced by
@{theory_text[display]
\<open>lemmas examples = example1 example2\<close>}\index{examples (example fact set)}

If a theorem with multiple conclusions is named in the form
@{theory_text[display]
\<open>theorem name: "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
it introduces the name for the collection of all resulting facts. Moreover, if the conclusions are
grouped by \<^theory_text>\<open>and\<close>, (some of) the groups\index{conclusion!group} may be named separately in the form
@{theory_text[display]
\<open>theorem name\<^sub>1: "C\<^sub>1\<^sub>,\<^sub>1" \<dots> "C\<^latex>\<open>$_{1,g_1}$\<close>" and \<dots> and name\<^sub>h: "C\<^sub>h\<^sub>,\<^sub>1" \<dots> "C\<^latex>\<open>$_{h,g_h}$\<close>"
  if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
which introduces the names for the corresponding collections of facts according to the groups.

In this way the two example facts may be specified and named by the common theorem
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
    and example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m"
\<proof>\<close>}\index{example1 (example fact)}\index{example2 (example fact)}\<close>

subsubsection "Dynamic Fact Sets"

text\<open>
As an alternative to introducing fact names in theorems   a ``dynamic fact set''\index{fact!set}\index{dynamic fact set} can be declared by
@{theory_text[display]
\<open>named_theorems name\<close>}
It can be used as a ``bucket'' where facts can be added afterwards by specifying the bucket
name in the theorem:
@{theory_text[display]
\<open>theorem [name]: "prop" \<proof>\<close>}
or together with specifying a fixed fact name \<^theory_text>\<open>name\<^sub>f\<close> by
@{theory_text[display]
\<open>theorem name\<^sub>f[name]: "prop" \<proof>\<close>}

There are also some predefined ``internal fact sets''\index{internal fact set}. For them the name can only be used to add
facts as described above, the set cannot be used or displayed by referring it by name. Examples
are the internal fact sets \<open>intro\<close> (see Section~\ref{methods-rule-intro}) and \<open>simp\<close> (see
Section~\ref{methods-simp-simp}).
\<close>

subsection "Alternative Theorem Syntax"
text_raw\<open>\label{theory-theorem-altsynt}\<close>

text \<open>
If the proposition of a theorem is a derivation rule  with possibly multiple conclusions  Isabelle
supports an alternative structured form\index{structured form}\index{syntax!alternative $\sim$!for theorems}
\index{syntax!structured $\sim$!for theorems} for it:
@{theory_text[display]
\<open>theorem
  fixes x\<^sub>1 \<dots> x\<^sub>m
  assumes "A\<^sub>1" \<dots> "A\<^sub>n"
  shows "C\<^sub>1" \<dots> "C\<^sub>h"
  \<proof>\<close>}\index{fixes (keyword)}\index{assumes (keyword)}\index{shows (keyword)}
As for the general structured form (see Section~\ref{theory-prop-struct}) the variables,
assumptions, and conclusions  may be grouped by \<^theory_text>\<open>and\<close>, a type may be specified for each variable
group, the keywords belong to the outer syntax and the  \<open>C\<^sub>i\<close> and \<open>A\<^sub>i\<close>  must be individually quoted.
Moreover, the explicit binding of variables\index{variable!binding} in the \<^theory_text>\<open>fixes\<close> part is optional, as in a \<^theory_text>\<open>for\<close> part.

Note that this structured form may only be used if a derivation rule is specified in a theorem.

Using this syntax the two-assumption example rule from Section~\ref{theory-prop} can be
written as
@{theory_text[display]
\<open>theorem 
  fixes x::nat and c n
  assumes "x < c" and "n > 0"
  shows "n*x < n*c"
  \<proof>\<close>}

As for the general structured form of a theorem (some of) the conclusion groups may be named
individually which introduces the names for the corresponding fact collections. A possibly
additional name specified after the \<^theory_text>\<open>theorem\<close> keyword names the collection of the resulting facts
from all groups together:
@{theory_text[display]
\<open>theorem name:
  fixes x\<^sub>1 \<dots> x\<^sub>m
  assumes "A\<^sub>1" \<dots> "A\<^sub>n"
  shows name\<^sub>1: "C\<^sub>1\<^sub>,\<^sub>1" \<dots> "C\<^latex>\<open>$_{1,g_1}$\<close>" and \<dots> and name\<^sub>h: "C\<^sub>h\<^sub>,\<^sub>1" \<dots> "C\<^latex>\<open>$_{h,g_h}$\<close>"
  \<proof>\<close>}\<close>

subsection "Definitions as Facts"
text_raw\<open>\label{theory-theorem-defs}\<close>

text \<open>
The definitions\index{definition!as fact} described in Section~\ref{theory-definition-defs} also introduce facts in
the enclosing theory. Every definition introduces a new constant and specifies a defining
equation of the form \<open>name \<equiv> term\<close> for it. This equation is a proposition. It is the initial information given for
the new constant, thus it is valid ``by definition'' and is a fact in the theory.

These facts are automatically named. If \<open>name\<close> is the name of the defined constant, the 
defining equation\index{name!of defining equation}\index{definition!name} is named \<open>name_def\<close>\index{def@$\_$def (fact name suffix)}. Alternatively an explicit name can be specified in 
the form
@{theory_text[display]
\<open>definition name :: type
where fact_name: "name \<equiv> term"\<close>}

Although the auxiliary constants used in an \<^theory_text>\<open>overloading\<close>\index{overloading} specification (see 
Section~\ref{theory-overload-true}) are not accessible outside the specification, their 
definitions are. So they can be referred by their names and used as information about the 
overloaded constant.
\<close>

subsection "Displaying and Searching Named Facts"
text_raw\<open>\label{theory-theorem-search}\<close>

subsubsection "Fact Display"

text \<open>
A named fact or fact set (but not a dynamic fact set) can be displayed\index{fact!display} in its standard form
as proposition using the command
@{theory_text[display]
\<open>thm name\<close>}\index{thm (keyword)}
and it can be displayed in its structured form with \<^theory_text>\<open>fixes\<close>, \<^theory_text>\<open>assumes\<close>, and \<^theory_text>\<open>shows\<close> using the
command
@{theory_text[display]
\<open>print_statement name\<close>}\index{print-statement@print$\_$statement (keyword)}

In the interactive editor a list of the named facts introduced by an outer syntax construct such as
\<^theory_text>\<open>theorem\<close> can be obtained by positioning the curser after the construct and using the Query panel\index{panel!query $\sim$}
(see Section~\ref{system-jedit-query}) in tab ``Print Context'' by checking ``theorems''. For
theorems the introduced facts are usually apparent, but there are constructs in HOL, such as
inductive or recursive definitions (see Sections~\ref{holbasic-inductive} and~\ref{holbasic-recursive}),
where it may be interesting to look at the introduced facts.
\<close>

subsubsection "Fact Search"

text\<open>
Named facts may be searched\index{fact!search $\sim$}\index{search!for facts} using the command
@{theory_text[display]
\<open>find_theorems criterion\<^sub>1 \<dots> criterion\<^sub>n\<close>}\index{find-theorems@find$\_$theorems (keyword)}
or using the Query panel\index{panel!query $\sim$} (see Section~\ref{system-jedit-query}) in the ``Find Theorems'' tab using
the sequence \<open>criterion\<^sub>1 \<dots> criterion\<^sub>n\<close> as search specification\index{search!specification} in the ``Find:'' input field. The
\<open>criterion\<^sub>i\<close> are combined by conjunction.

A \<open>criterion\<^sub>i\<close> may be a term containing unknowns as subterms (called a ``term pattern''\index{term!pattern}). Then 
all facts are found which contain a matching subterm in their proposition. A term pattern matches
a subterm if the unknowns in the pattern can be consistently replaced by terms so that the result
is syntactically equal to the subterm. The term pattern is specified in inner syntax and must be
quoted. Only named facts can be found in this way.

The example theorems \<open>example1\<close> and \<open>example2\<close> can be found using the term pattern \<open>"?t1 \<le> ?t2"\<close>,
whereas the pattern \<open>"?t1 + ?c \<le> ?t2 + ?c"\<close> will only find \<open>example2\<close>.

A \<open>criterion\<^sub>i\<close> may also have the form \<open>name: strpat\<close> where \<open>strpat\<close> is a string pattern which may
use ``*'' as wildcard (then the pattern must be enclosed in double quotes). Then all facts are found
where the \<open>strpat\<close> matches a substring of the fact name. After naming the example theorems
as above the criterion \<open>name: example\<close> will display the theorems \<open>example1\<close> and \<open>example2\<close>
with their names and propositions.

The commands for display and search may be entered in the text area outside of theorems and at most
positions in a proof. The found facts are displayed with their names in the Output panel\index{panel!output $\sim$} (see
Section~\ref{system-jedit-output}).
\<close>
end