theory Chapter_basic
  imports Chapter_system
  "HOL-Library.Adhoc_Overloading"
begin
chapter "Isabelle Basics"
text_raw\<open>\label{basic}\<close>

text \<open>
The basic mechanisms of Isabelle mainly support defining types, constants, and functions and 
specifying and proving statements about them.
\<close>

section "Isabelle Theories"
text_raw\<open>\label{basic-theory}\<close>

text \<open>
A theory is the content of an Isabelle theory file.
\<close>


subsection "Theory Notation"
text_raw\<open>\label{basic-theory-notation}\<close>

text\<open>
Theories are written using a notation which follows strict syntax rules, similar to a programming
language. The interactive editor helps using correct notation by immediately signaling syntax
errors upon input. However, it is crucial to also understand the \<^emph>\<open>meaning\<close> of the written text.
This introduction describes both in a systematic stepwise manner.
\<close>

subsubsection "Languages for Theory Content"

text \<open>
Isabelle aims at two main goals: Supporting interactive work with mathematical formulas
and proofs, and supporting their presentation together with explanations as nicely typeset text in
the form of an article or a book. For this purpose Isabelle combines three different languages for
writing theory content:

 \<^item> a language for mathematics, called the ``inner syntax'',
 \<^item> a language for textual content, which is an extended form of \LaTeX\ source code,
 \<^item> a language for organizing fragments of the first two languages in a theory, called the ``outer
syntax''.

For the inner syntax Isabelle tries to be as close as possible to the form how mathematical content
is traditionally presented in books. It supports formulas such as \<open>\<forall>x\<le>100 . x\<in>{y\<^sup>2 | y. y\<le>10}\<close> both
in the interactive editor and the textual presentation. It does not support larger two-dimensional
constructs like matrices or fractions.

The outer syntax resembles a programming language. It uses keywords to construct larger entities
like definitions and proofs. These entities usually contain mathematical formulas written in inner
syntax. To clearly separate both languages,  content in inner syntax must always be surrounded
by double quotes  \<open>"\<dots>"\<close> or by the ``cartouche delimiters'' \<open>\<open>\<dots>\<close>\<close> available in the editor's
Symbols panel in tab ``Punctuation''.  The only exception is a single isolated identifier, for it the
quotes  or delimiters  may be omitted.

This introduction describes only a selected part of the outer and  inner syntax. The full
notation used by Isabelle  is described in the Isabelle/Isar Reference Manual and other
documentation.

Additionally, text written in \LaTeX\ syntax can be embedded into the outer syntax using the form
\<^theory_text>\<open>text\<open> \<dots> \<close>\<close>
and \LaTeX\ sections can be created using
\<^theory_text>\<open>chapter\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>section\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>subsection\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>subsubsection\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>paragraph\<open> \<dots> \<close>\<close>,
\<^theory_text>\<open>subparagraph\<open> \<dots> \<close>\<close>.
 

It is also possible to embed inner and outer syntax in the \LaTeX\ syntax (see Chapter 4 in the 
Isabelle/Isar Reference Manual).

Moreover, comments of the form
\begin{verbatim}
  (* ... *)
\end{verbatim}
can be embedded into the outer syntax. They are only intended for the reader of the theory file
and are not displayed in the session document.

Line breaks are ignored as part of the outer and inner syntax and have the same effect as
a space.
\<close>


subsubsection "Meta Level and Object Level"

text \<open>
Isabelle consists of a small fixed kernel which is called ``meta-logic''. It is implemented in the
session \<^verbatim>\<open>Pure/Pure\<close> (see Section~\ref{system-invoke-theory}) which is the ancestor of all other
sessions. To be useful the meta-logic must be extended by an ``object logic''. It may consist of one
or more sessions, all sessions other than \<^verbatim>\<open>Pure/Pure\<close> are parts of an object logic. There are many
object logics available for Isabelle, the most versatile is HOL. Although called a ``logic'' it is
a full extensible representation of mathematics.

This introduction first describes the Isabelle kernel features, followed by a
description of the object logic HOL in Chapters~\ref{holbasic} and subsequent chapters.

Both outer and inner syntax consist of a part for the kernel (the ``meta-level'' of the languages)
and a part introduced by and specific for the object logic (the ``object-level'' of the languages).
While the meta-level of the inner syntax is extremely small, mainly consisting of only four logical
operators, the meta-level of the outer syntax supports a large set of constructs for specifying
entities like axioms, definitions, proofs, and, finally, whole theories.

This introduction describes the meta-level of the inner syntax mainly in
Sections~\ref{basic-theory-terms} and~\ref{basic-theory-prop}. The rest of the sections about the
Isabelle kernel describe the meta-level of the outer syntax. Chapter~\ref{holbasic} describes basic
parts of the object level of the inner and outer syntax for HOL. Chapter~\ref{holtdefs} describes
a major part of the outer syntax for HOL, whereas Chapter~\ref{holtypes} describes an important part
of the inner syntax for HOL.
\<close>


subsubsection "Theory Structure"

text \<open>
The content of a theory file has the  outer syntax  structure
@{theory_text[display]
\<open>theory name
imports name\<^sub>1 \<dots> name\<^sub>n
begin
  \<dots>
end\<close>}
where \<^theory_text>\<open>name\<close> is the theory name and \<^theory_text>\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are the names of the imported theories.
The theory name \<^theory_text>\<open>name\<close> must be the same which is used for the theory file, i.e., the file name 
must be \<^verbatim>\<open>name.thy\<close>.

\<close>

subsection "Terms and Types"
text_raw\<open>\label{basic-theory-terms}\<close>

text \<open>
The two main constituents of the inner syntax are terms and types. 
As usual in formal logics, the basic building blocks of propositions are terms. Terms denote arbitrary
objects like numbers, sets, functions, or boolean values. Isabelle is strongly typed, so every term 
must have a type  which names the type of values denoted by the term. 
However, in most situations Isabelle can derive the type of a term automatically,
so that it needs not be specified explicitly.
\<close>

subsubsection "Types"

text \<open>
Types are usually specified by type names. In Isabelle HOL (see Chapter~\ref{holbasic}) there are 
predefined types such as \<open>nat\<close> and \<open>bool\<close> for natural numbers and boolean values.  With the
exception of function types, types like these with a mathematical meaning always belong to an object
logic. Chapter~\ref{holtypes} gives a detailed description of several important types of HOL. Due
to the lack of adequate types in the meta-logic this introduction uses a small set of HOL types for
examples to illustrate concepts on the meta-level, assuming an intuitive understanding of the
associated operations and terms.

New types can be defined  using the outer syntax construct
@{theory_text[display]
\<open>typedecl name\<close>}
which introduces the \<^theory_text>\<open>name\<close> for a new type for which the values are different from the values of 
all existing types and the set of values is not empty. No other information about the values is 
given, that must be done separately. See Chapter~\ref{holtdefs} for ways of defining types with
specifying more information about their values.

Types can be parameterized, then the type arguments are denoted \<^emph>\<open>before\<close> the type name, such as in
\<open>nat set\<close> which is the  HOL  type of sets of natural numbers. A type name with \<open>n\<close> parameters is declared
in the form
@{theory_text[display]
\<open>typedecl ('name\<^sub>1,\<dots>,'name\<^sub>n) name\<close>}
where the parentheses may be omitted if \<open>n = 1\<close>, such as in \<^theory_text>\<open>typedecl 'a set\<close>.
The type parameters are denoted by ``type variables'' which always have the 
form \<open>'name\<close> with a leading single quote character.

A type name with parameters is called a ``type constructor'' because it is not a type on its own.
Every use where the parameters are replaced by actual types, such
as in \<open>nat set\<close>, is called an ``instance'' of the parameterized type. If (some of) the parameters
are replaced by type variables, such as in \<open>'a set\<close> or \<open>('a set) set\<close> or if a type is specified
by a single type variable such as \<open>'a\<close> the type is called ``polymorphic''. A polymorphic type can be
used as a type specification, its meaning is that an arbitrary instance can be used where the type
variables are replaced by actual types.

Alternatively a type name can be introduced as a synonym for an existing type in the form
@{theory_text[display]
\<open>type_synonym name = type\<close>}
such as in  \<^theory_text>\<open>type_synonym natset = "nat set"\<close>. Type synonyms can also be parameterized as in
@{theory_text[display]
\<open>type_synonym ('name\<^sub>1,\<dots>,'name\<^sub>n) name = type\<close>}
where \<open>type\<close> may be a polymorphic type which contains atmost the type variables \<open>'name\<^sub>1,\<dots>,'name\<^sub>n\<close>.
\<close>

subsubsection "Constants and Variables"

text \<open>
Terms are mainly built as syntactical structures based on constants and variables. Constants are usually
denoted by names, using the same namespace as type names. Whether a name denotes a constant or a 
type depends on its position in a term.  In HOL  predefined constant names of type
\<open>bool\<close> are \<open>True\<close> and \<open>False\<close>.

Constants of number types, such as \<open>nat\<close>, may be denoted by number literals, such as \<open>6\<close>
or \<open>42\<close>.

A constant can be defined by specifying its type. The  outer syntax construct
@{theory_text[display]
\<open>consts name\<^sub>1 :: type\<^sub>1 \<dots> name\<^sub>n :: type\<^sub>n\<close>}
introduces \<open>n\<close> constants with their names and types. No information is specified about the 
constant's values, in this respect the constants are ``underspecified''. The information about the
values must be specified separately.

If the constant's type is polymorphic (see the previous subsection) the constant is 
also called polymorphic. Thus the declaration
@{theory_text[display]
\<open>consts myset :: "'a set"\<close>}
declares the polymorphic constant \<open>myset\<close> which may be a set of elements of arbitrary type.
 Note the use of quotes because the type is specified in inner syntax and is not a single
type name.

A (term) variable has the same form as a constant name, but it has not been introduced as a 
constant. Whenever a variable is used in a term it has a specific type which is either derived 
from its context or is explicitly specified in  inner syntax in  the form \<open>varname :: type\<close>.

Nested terms are generally written by using parentheses \<open>(\<dots>)\<close>. There are many priority rules how 
to nest terms automatically, but if in doubt, it is always safe to use parentheses.
\<close>
 
subsubsection "Functions"

text \<open>
A constant name denotes an object, which, according to its type, may also be a function of 
arbitrary order. Functions basically have a single argument. The type of a function is written 
 in inner syntax  as \<open>argtype \<Rightarrow> restype\<close>.  This way of denoting function
types belongs to the meta-level of the inner syntax and is thus available in all object logics.

Functions in Isabelle are always total, i.e., they map every value of type \<open>argtype\<close> to some value
of type \<open>restype\<close>. However, a function may be ``underspecified'' so that no information is (yet)
available about the result value for some or all argument values. A function defined by
@{theory_text[display]
\<open>consts mystery :: "nat \<Rightarrow> nat"\<close>}
is completely underspecified: although it maps every natural number to a unique other natural number
no information about these numbers is available. Functions may also be partially specified by 
describing the result value only for some argument values. This does not mean that the function is
``partial'' and has no value for the remaining arguments. The information about these values may
always be provided later, this does not ``modify'' the function, it only adds information about it.
\<close>

subsubsection "Functions with Multiple Arguments"

text\<open>
The result type
of a function may again be a function type, then it may be applied to another argument. This is used
to represent functions with more than one argument. Function types are right associative, thus a 
type \<open>argtype\<^sub>1 \<Rightarrow> argtype\<^sub>2 \<Rightarrow> \<cdots> \<Rightarrow> argtype\<^sub>n \<Rightarrow> restype\<close> describes functions which can be applied 
to \<open>n\<close> arguments. 

Function application terms for a function \<open>f\<close> and an argument \<open>a\<close> are denoted  in inner
syntax  by
\<open>f a\<close>, no parentheses are required around the argument. Function application terms are left 
associative, thus a function application to \<open>n\<close> arguments is written \<open>f a\<^sub>1 \<dots> a\<^sub>n\<close>. Note that an
application \<open>f a\<^sub>1 \<dots> a\<^sub>m\<close> where \<open>m < n\<close> (a ``partial application'') is a correct term and denotes a
function taking the remaining \<open>n-m\<close> arguments.

For every constant alternative syntax forms may be defined for application terms. This is often used
for binary functions to represent application terms in infix notation with an operator symbol.
As an example, the name for the addition function  in HOL  is \<open>plus\<close>, so an application term is denoted
in the form \<open>plus 3 5\<close>. For \<open>plus\<close> the alternative name \<open>(+)\<close> is defined (the parentheses are part
of the name). For functions with such ``operator names'' an application term \<open>(+) 3 5\<close> can also be
denoted in infix form \<open>3 + 5\<close>. Infix notation is supported for many basic functions and predicates
 in HOL ,
having operator names such as \<open>(-)\<close>, \<open>(**)\<close>, \<open>(=)\<close>, \<open>(\<noteq>)\<close>, \<open>(\<le>)\<close>, or \<open>(\<in>)\<close>. 
\<close>

subsubsection "Lambda-Terms"

text\<open>
Functions can be denoted  in inner syntax  by lambda terms of the form \<open>\<lambda>x. term\<close> where \<open>x\<close> is a variable
which may occur in the \<open>term\<close>. The space between the dot and the \<open>term\<close> is often required to
separate both. A function to be applied to \<open>n\<close> arguments can be denoted by the
lambda term \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. term\<close> where  \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close>  are distinct variables. As usual, types may be
specified for (some of) the variables in the form \<open>\<lambda>(x\<^sub>1::t\<^sub>1) \<dots> (x\<^sub>n::t\<^sub>n). term\<close>. The parentheses
may be omitted if there is only one argument variable.

 If a variable from the \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> occurs in the \<open>term\<close> of \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. term\<close> it is called a
``bound'' occurrence and denotes the corresponding function argument. If an occurrence of a variable
\<open>x\<close> is not a part of a lambda term \<open>\<lambda>\<dots> x \<dots> . term\<close> the occurrence is called ``free''.

A constant function has a value which does not depend on the argument, thus the variable \<open>x\<close>
does not occur in the \<open>term\<close>. Then its name is irrelevant and it may be replaced by the ``wildcard''
\<open>_\<close> (an underscore) as in \<open>\<lambda>_. term\<close>.

 A lambda term is a case of ``binder syntax''. It consists of a ``binder'' (here \<open>\<lambda>\<close>)
followed by one or more variables with optional type specifications, followed by a dot and a term.
Terms of the inner syntax nearly always have either the form of a function application, possibly
in infix notation, or the form of a binder syntax.
\<close>

subsubsection "Searching Constants"

text \<open>
Constants may be searched using the command
@{theory_text[display]
\<open>find_consts criterion\<^sub>1 \<dots> criterion\<^sub>n\<close>}
or using the Query panel (see Section~\ref{system-jedit-query}) in the ``Find Constants'' tab using
the sequence \<open>criterion\<^sub>1 \<dots> criterion\<^sub>n\<close> as search specification in the ``Find:'' input field. The
\<open>criterion\<^sub>i\<close> are combined by conjunction.

The command \<^theory_text>\<open>find_consts\<close> may be entered in the text area between other theory content such as
type or constant declarations. It finds all named constants which have been introduced before the
command position. Searches using the Query panel find all named constants which have been introduced
before the cursor position in the text area.

A \<open>criterion\<^sub>i\<close> may be a type, specified in inner syntax and quoted if not a single type name. Then
the search finds all constants where the type occurs as a part of the constant's type. For example,
it finds all functions which have the specified type as argument or result type.

A \<open>criterion\<^sub>i\<close> may also have the form \<open>strict: "type"\<close>, then the search only finds constants which
have that type. In both cases the specified type may be a function type, then the search finds
corresponding named functions.

If the specified type is polymorphic the search will also find constants which have an instance
of it as their type or as a part of the type, respectively.

A \<open>criterion\<^sub>i\<close> may also have the form \<open>name: strpat\<close> where \<open>strpat\<close> is a string pattern which may
use ``*'' as wildcard (then the pattern must be enclosed in double quotes). Then all constants are
found where the \<open>strpat\<close> matches a substring of their name.
\<close>

subsection "Definitions and Abbreviations"
text_raw\<open>\label{basic-theory-definition}\<close>

text \<open>
A constant name may be introduced together with information about its associated value by specifying 
a term for the value. There are two forms for introducing constant names in this way, definitions
and abbreviations.  Both are constructs of the outer syntax.
\<close>

subsubsection "Definitions"

text\<open>
A definition defines a new constant together with its type and value.
It is denoted in the form
@{theory_text[display]
\<open>definition name where "name \<equiv> term"\<close>}
Note that the ``defining equation'' \<open>name \<equiv> term\<close> is specified in inner syntax and must be
delimited by quotes.  The operator \<open>\<equiv>\<close> is the equality operator of the meta-logic (see
Section~\ref{basic-theory-notation}). The \<open>name\<close> may not occur in the \<open>term\<close>, i.e., this form
of definition
does not support recursion. Also, no free variables may occur in the \<open>term\<close>. In the object logic HOL
(see Chapter~\ref{holbasic}) also the normal equality operator \<open>=\<close> may be used instead of \<open>\<equiv>\<close>.

The type of the defined constant is the same as that of the \<open>term\<close>. If that type is polymorphic
(see Section~\ref{basic-theory-terms}) a more specific type may be specified explicitly in the form
@{theory_text[display]
\<open>definition name :: type where "name \<equiv> term"\<close>}
As usual the type is specified in inner syntax and must be quoted if it is not a single type name.

If the type of the defined constant is a function type, the \<open>term\<close> may be a lambda term.
Alternatively, the definition for a function applicable to \<open>n\<close> arguments can be written in the form
@{theory_text[display]
\<open>definition name where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
with variable names \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> which may occur in the \<open>term\<close>. This form is mainly equivalent to
@{theory_text[display]
\<open>definition name where "name \<equiv> \<lambda>x\<^sub>1 \<dots> x\<^sub>n. term"\<close>}

A short form of a definition is
@{theory_text[display]
\<open>definition "name \<equiv> term"\<close>}

Usually, a constant defined in this way is fully specified, i.e., all information about its value
is available. However, if the term does not provide this information, the constant is still 
underspecified. Consider the definition
@{theory_text[display]
\<open>definition mystery2 where "mystery2 \<equiv> mystery"\<close>}
where \<open>mystery\<close> is defined as above. Then it is only known that \<open>mystery2\<close> has type \<open>nat \<Rightarrow> nat\<close> and
is the same total function as \<open>mystery\<close>, but nothing is known about its values.
\<close>

subsubsection "Abbreviations"

text\<open>
An abbreviation definition does not define a constant, it only introduces the name 
as a synonym for a term. Upon input the name is automatically expanded, and upon output it is used 
whenever a term matches its specification and the term is not too complex. 
An abbreviation definition is denoted in a similar form as a definition:
@{theory_text[display]
\<open>abbreviation name where "name \<equiv> term"\<close>}
As for definitions, recursion is not supported, the \<open>name\<close> may not occur in the \<open>term\<close> and also
no free variables. An explicit type may be specified for \<open>name\<close> and the short form is also available
as for definitions.

The alternative form for functions is also available. The abbreviation definition
@{theory_text[display]
\<open>abbreviation name where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
introduces a ``parameterized'' abbreviation. An application term \<open>name term\<^sub>1 \<dots> term\<^sub>n\<close> is replaced
upon input by \<open>term\<close> where all occurrences of \<open>x\<^sub>i\<close> have been substituted by \<open>term\<^sub>i\<close>. Upon output
terms are matched with the structure of \<open>term\<close> and if successful a corresponding application term
is constructed and displayed.
\<close>

subsection "Overloading"
text_raw\<open>\label{basic-theory-overload}\<close>

subsubsection "True Overloading"

text \<open>
One way of providing information about the value of an underspecified constant is overloading.
It provides the information with the help of another constant together with a definition for it.

Overloading depends on the type. Therefore, if a constant is 
polymorphic, different definitions can be associated for different type instances.

Overloading is only possible for constants which do not yet have a definition, i.e., they must
have been defined by \<^theory_text>\<open>consts\<close> (see Section~\ref{basic-theory-terms}).
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
end\<close>}
where all \<open>type\<^sub>i\<close> must be instances of the type declared for \<open>name\<close>.

The auxiliary constants \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are only introduced locally and cannot be used outside
of the \<^theory_text>\<open>overloading\<close> specification.
\<close>

subsubsection "Adhoc Overloading"

text\<open>
There is also a form of overloading which achieves similar effects although it is implemented
completely differently. It is only performed on the syntactic level, like abbreviations.
To use it, the theory \<^theory>\<open>HOL-Library.Adhoc_Overloading\<close> must be imported by the surrounding
theory:
@{theory_text[display]
\<open>imports "HOL-Library.Adhoc_Overloading"\<close>}
(Here the theory name must be quoted because it contains a minus sign.)

Then a constant name \<open>name\<close> can be defined to be a ``type dependent abbreviation''
for \<open>n\<close> terms of different type instances by
@{theory_text[display]
\<open>adhoc_overloading name term\<^sub>1 \<dots> term\<^sub>n\<close>}
Upon input the type of \<open>name\<close> is determined from the context, then it is replaced by the 
corresponding \<open>term\<^sub>i\<close>. Upon output terms are matched with the corresponding \<open>term\<^sub>i\<close> and if 
successful \<open>name\<close> is displayed instead.

Although \<open>name\<close> must be the name of an existing constant, only its type is used. The constant is
not affected by the adhoc overloading, however, it becomes inaccessible because its name is now
used as term abbreviation. 

Several constant names can be overloaded in a common specification:
@{theory_text[display]
\<open>adhoc_overloading name\<^sub>1 term\<^sub>1\<^sub>1 \<dots> term\<^sub>1\<^sub>n and \<dots> and name\<^sub>k \<dots>\<close>}
\<close>

subsection "Propositions"
text_raw\<open>\label{basic-theory-prop}\<close>

text \<open>
A proposition denotes an assertion, which can be valid or not. Valid proposition are called
``facts'', they are the main content of a theory. Propositions are specific terms and
are hence written in inner syntax and must be enclosed in quotes.
\<close>
subsubsection "Formulas"

text \<open>
 A simple form of  a proposition is a single term of type \<open>bool\<close>, such as
@{text[display]
\<open>6 * 7 = 42\<close>}
 The \<open>*\<close> is the infix operator for multiplication, it may not be omitted in arithmetic
terms.

Terms of type \<open>bool\<close> are also called ``formulas''.  Since \<open>bool\<close> belongs to the object
logic HOL, formulas are also specific for HOL or another object logic, there are no formulas in
the meta-logic. The simplest form of a proposition on meta-level is a single variable.

A proposition may contain free variables as in
@{text[display]
\<open>2 * x = x + x\<close>}

A formula as proposition is valid if it evaluates to \<open>True\<close> for all possible values substituted
for the free variables.
\<close>

subsubsection "Derivation Rules"

text \<open>
More complex propositions  on the meta-level  can express ``derivation rules'' used to derive propositions
from other propositions. Derivation rules are denoted using  the meta-logic operator \<open>\<Longrightarrow>\<close>
and can thus be expressed independent of an object logic.

Derivation rules consist of assumptions and a conclusion. They  are written in the form
@{text[display]
\<open>A\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<close>}
where the \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> are the assumptions and \<open>C\<close> is the conclusion.  Since \<open>\<Longrightarrow>\<close> is right-associative
the conclusion can be assumed to be a single variable or a formula. 
The assumptions may be arbitrary propositions. If an
assumption contains meta-logic operators parentheses can be used to delimit them from the rest of the
derivation rule.

A derivation rule states that if the assumptions are valid, the conclusion can be derived
as also being valid.  So  \<open>\<Longrightarrow>\<close>  can be viewed as a ``meta implication'' with a similar meaning as a
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
be again derivation rules. Then the rule is a ``meta rule'' which derives a proposition from other 
rules.
\<close>

subsubsection "Binding Free Variables"

text \<open>
A proposition may contain universally bound variables, using the meta-logic quantifier \<open>\<And>\<close> in the
form
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>n. P\<close>}
where the \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> may occur free in the proposition \<open>P\<close>.  This is another case of binder
syntax (see Section~\ref{basic-theory-terms}). As usual, types may be
specified for (some of) the variables in the form \<open>\<And> (x\<^sub>1::t\<^sub>1) \<dots> (x\<^sub>n::t\<^sub>n). P\<close>. An example for
a valid derivation rule with bound variables is
@{text[display]
\<open>\<And> (x::nat) c n . x < c \<Longrightarrow> n*x \<le> n*c\<close>}
\<close>

subsubsection "Rules with Multiple Conclusions"

text \<open>
A derivation rule may specify several propositions to be derivable from the same assumptions using
the meta-logic operator \<open>&&&\<close> in the form
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
viewed as a ``meta conjunction'' with a similar meaning as a boolean conjunction, but with a
different use.

An example for a rule with two conclusions is
@{text[display]
\<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c &&& n+x < n+c\<close>}\<close>

subsubsection "Alternative Rule Syntax"

text \<open>
An alternative, Isabelle specific syntax for derivation rules  with possibly multiple conclusions is
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

subsubsection "Structured Rule Syntax"

text\<open>
Isabelle supports another alternative syntax for derivation rules  with possibly multiple
conclusions. It is called ``structured'' form, since the rule is not specified by a single
proposition but by several separate propositions for the parts of the rule:
@{theory_text[display]
\<open>"C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m\<close>}
Here the conclusions,  assumptions and the variables may be grouped or separated for better
readability by the keyword \<^theory_text>\<open>and\<close>. For every group of variables (but not for single variables in a
group) a type may be specified in the form \<open>x\<^sub>1 \<dots> x\<^sub>m :: "type"\<close>, it applies to all variables in the
group.

The keywords \<^theory_text>\<open>if\<close>, \<^theory_text>\<open>and\<close>, \<^theory_text>\<open>for\<close> belong to the outer syntax. Thus, a rule in structured form
cannot occur nested in another proposition, such as an assumption in another rule. Moreover, the
original rule must be quoted as a whole, whereas in the structured form only the sub-propositions
 \<open>C\<^sub>1 \<dots> C\<^sub>h, A\<^sub>1, \<dots>, A\<^sub>n\<close>  must be individually quoted. The \<open>x\<^sub>1, \<dots>, x\<^sub>m\<close> need not be quoted, but if a
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

subsubsection "Conditional Definitions"

text\<open>
A definition, as described in Section~\ref{basic-theory-definition} may be conditional, then its
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
Section~\ref{basic-theory-definition} a conditional form is not available.
\<close>

subsection "Theorems"
text_raw\<open>\label{basic-theory-theorem}\<close>

text \<open>
A theorem specifies a proposition together with a proof, that the proposition is valid. Thus it
adds a fact to the enclosing theory.\<close>

subsubsection "Specifying Theorems"

text\<open>
A simple form of a theorem is
@{theory_text[display]
\<open>theorem "prop" \<proof>\<close>}
where \<open>prop\<close> is a proposition in inner syntax and \<^theory_text>\<open>\<proof>\<close> is a proof as described in 
Section \ref{basic-proof}. The keyword \<^theory_text>\<open>theorem\<close> can be replaced by one of the keywords
\<^theory_text>\<open>lemma\<close>, \<^theory_text>\<open>corollary\<close>, \<^theory_text>\<open>proposition\<close> to give a hint about the use of the  theorem  to
the reader.

 The example rule from the previous sections can be stated as a fact by the theorem
@{theory_text[display]
\<open>theorem "\<And> (x::nat) c n . x < c \<Longrightarrow> n*x \<le> n*c" \<proof>\<close>}

If the proposition in a theorem contains free variables they are implicitly universally
bound. Thus the previous example theorem is equivalent to the theorem
@{theory_text[display]
\<open>theorem "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" \<proof>\<close>}
Explicit binding of variables is only required to avoid name clashes with 
constants of the same name. In the theorem
@{theory_text[display]
\<open>theorem "\<And> (True::nat). True < c \<Longrightarrow> n*True \<le> n*c" \<proof>\<close>}
the name \<open>True\<close> is used locally as a variable of type \<open>nat\<close> instead of the predefined constant
of type \<open>bool\<close>. Of course, using well known constant names as variables is confusing and should
be avoided.

If the proposition in a theorem is a derivation rule  with possibly multiple conclusions  it may also
be specified in structured form (see Section~\ref{basic-theory-prop}):
@{theory_text[display]
\<open>theorem "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
with optional grouping of all components by \<^theory_text>\<open>and\<close>. Remember that the \<open>C\<^sub>i\<close> may be arbitrary
propositions, therefore a theorem in this form may specify several derivation rules with additional
common assumptions and common bound variables.

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

subsubsection "Unknowns"

text \<open>
Whenever a theorem turns a proposition to a fact, the free (or universally bound) variables
are replaced by ``unknowns''. For a variable \<open>name\<close> the corresponding unknown is \<open>?name\<close>.
This is only a technical difference, it signals to Isabelle that the unknowns can be 
consistently substituted by arbitrary terms, as long as the types are preserved.

The result of such a substitution is always a special case of the fact and therefore also
a fact. In this way a fact with unknowns gives rise to a (usually infinite) number of facts
which are constructed by substituting unknowns by terms.

 When turned to a fact, the rule used in the example theorems becomes
@{text[display]
\<open>?x < ?c \<Longrightarrow> ?n*?x \<le> ?n*?c\<close>}
with type \<open>nat\<close> associated to all unknowns.

Propositions specified in a theorem may not contain unknowns, they are only introduced by Isabelle
after proving the proposition.

Isabelle can be configured to suppress the question mark when displaying unknowns, then
this technical difference becomes invisible.
\<close>

subsubsection "Named Facts"

text \<open>
Facts are often used in proofs of other facts. For this purpose they can be named so 
that they can be referenced by name. A named fact is specified by a theorem of the form
@{theory_text[display]
\<open>theorem name: "prop" \<proof>\<close>}
The names used for facts have the same form as names for constants and variables (see
Section~\ref{basic-theory-terms}). The same name can be used for a variable and a fact, they can
always be distinguished by the usage context.

The example rule from the previous sections can be turned into a fact named \<open>example1\<close> by
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" \<proof>\<close>}

It is also possible to introduce named collections of facts. A simple way to introduce
such a named collection is 
@{theory_text[display]
\<open>lemmas name = name\<^sub>1 \<dots> name\<^sub>n\<close>}
where \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are names of existing facts or fact collections.

If there is a second rule stated as a named fact by
@{theory_text[display]
\<open>theorem example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m" \<proof>\<close>}
a named collection can be introduced by
@{theory_text[display]
\<open>lemmas examples = example1 example2\<close>}

 If a theorem with multiple conclusions is named in the form
@{theory_text[display]
\<open>theorem name: "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
it introduces the name for the collection of all resulting facts. Moreover, if the conclusions are
grouped by \<^theory_text>\<open>and\<close>, (some of) the groups may be named separately in the form
@{theory_text[display]
\<open>theorem name\<^sub>1: "C\<^sub>1\<^sub>1" \<dots> "C\<^sub>1\<^sub>g\<^sub>1" and \<dots> and name\<^sub>h: "C\<^sub>h\<^sub>1" \<dots> "C\<^sub>h\<^sub>g\<^sub>h"
  if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
which introduces the names for the corresponding collections of facts according to the groups.

In this way the two example facts may be specified and named by the common theorem
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
    and example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m"
\<proof>\<close>}

As an alternative to introducing fact names in theorems   a ``dynamic fact set'' can be declared by
@{theory_text[display]
\<open>named_theorems name\<close>}
It can be used as a ``bucket'' where facts can be added afterwards by specifying the bucket
name in the theorem:
@{theory_text[display]
\<open>theorem [name]: "prop" \<proof>\<close>}
or together with specifying a fixed fact name \<^theory_text>\<open>name\<^sub>f\<close> by
@{theory_text[display]
\<open>theorem name\<^sub>f[name]: "prop" \<proof>\<close>}

There are also some predefined ``internal fact sets''. For them the name can only be used to add
facts as described above, the set cannot be used or displayed by referring it by name. Examples
are the internal fact sets \<open>intro\<close> (see Section~\ref{basic-methods-rule}) and \<open>simp\<close> (see
Section~\ref{basic-methods-simp}).
\<close>

subsubsection "Alternative Theorem Syntax"

text \<open>
If the proposition of a theorem is a derivation rule  with possibly multiple conclusions  Isabelle
supports an alternative structured form for it:
@{theory_text[display]
\<open>theorem
  fixes x\<^sub>1 \<dots> x\<^sub>m
  assumes "A\<^sub>1" \<dots> "A\<^sub>n"
  shows "C\<^sub>1" \<dots> "C\<^sub>h"
  \<proof>\<close>}
Like for the general structured form (see Section~\ref{basic-theory-prop}) the variables,
 assumptions, and conclusions  may be grouped by \<^theory_text>\<open>and\<close>, a type may be specified for each variable
group, the keywords belong to the outer syntax and the  \<open>C\<^sub>i\<close> and \<open>A\<^sub>i\<close>  must be individually quoted.
Note that this structured form may only be used if a  derivation rule  is specified in a theorem.

Using this syntax the two-assumption example rule from Section~\ref{basic-theory-prop} can be
written as
@{theory_text[display]
\<open>theorem 
  fixes x::nat and c n
  assumes "x < c" and "n > 0"
  shows "n*x < n*c"
  \<proof>\<close>}

 Like for the general structured form of a theorem (some of) the conclusion groups may be named
individually which introduces the names for the corresponding fact collections. A possibly
additional name specified after the \<^theory_text>\<open>theorem\<close> keyword names the collection of the resulting facts
from all groups together:
@{theory_text[display]
\<open>theorem name:
  fixes x\<^sub>1 \<dots> x\<^sub>m
  assumes "A\<^sub>1" \<dots> "A\<^sub>n"
  shows name\<^sub>1: "C\<^sub>1\<^sub>1" \<dots> "C\<^sub>1\<^sub>g\<^sub>1" and \<dots> and name\<^sub>h: "C\<^sub>h\<^sub>1" \<dots> "C\<^sub>h\<^sub>g\<^sub>h"
  \<proof>\<close>}\<close>

subsubsection "Definitions as Facts"

text \<open>
The definitions described in Section~\ref{basic-theory-definition} also introduce facts in
the enclosing theory. Every definition introduces a new constant and specifies a defining
equation of the form \<open>name \<equiv> term\<close> for it. This equation is a proposition. It is the initial information given for
the new constant, thus it is valid ``by definition'' and is a fact in the theory.

These facts are automatically named. If \<open>name\<close> is the name of the defined constant, the 
defining equation is named \<open>name_def\<close>. Alternatively an explicit name can be specified in 
the form
@{theory_text[display]
\<open>definition name :: type
where fact_name: "name \<equiv> term"\<close>}

Although the auxiliary constants used in an \<^theory_text>\<open>overloading\<close> specification (see 
Section~\ref{basic-theory-overload}) are not accessible outside the specification, their 
definitions are. So they can be referred by their names and used as information about the 
overloaded constant.
\<close>

subsubsection "Displaying and Searching Named Facts"

text \<open>
A named fact or fact set (but not a dynamic fact set) can be displayed in its standard form
as proposition using the command
@{theory_text[display]
\<open>thm name\<close>}
and it can be displayed in its structured form with \<^theory_text>\<open>fixes\<close>, \<^theory_text>\<open>assumes\<close>, and \<^theory_text>\<open>shows\<close> using the
command
@{theory_text[display]
\<open>print_statement name\<close>}

Named facts may be searched using the command
@{theory_text[display]
\<open>find_theorems criterion\<^sub>1 \<dots> criterion\<^sub>n\<close>}
or using the Query panel (see Section~\ref{system-jedit-query}) in the ``Find Theorems'' tab using
the sequence \<open>criterion\<^sub>1 \<dots> criterion\<^sub>n\<close> as search specification in the ``Find:'' input field. The
\<open>criterion\<^sub>i\<close> are combined by conjunction.

A \<open>criterion\<^sub>i\<close> may be a term containing unknowns as subterms (called a ``term pattern''). Then 
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
positions in a proof. The found facts are displayed with their names in the Output panel (see
Section~\ref{system-jedit-output}).
\<close>

section "Isabelle Proofs"
text_raw\<open>\label{basic-proof}\<close>

text \<open>
Every proposition stated as a fact in an Isabelle theory must be proved
immediately by specifying a proof for it. A proof may have a complex structure of several steps 
and nested subproofs, its structure is part of the outer syntax.
\<close>

subsection "Maintaining Proof State"
text_raw\<open>\label{basic-proof-state}\<close>

text \<open>
Usually it is necessary during a proof to collect information for later use in the proof. For every
proof such state is maintained in two structures: the ``proof context'' and the ``goal state''.
At the end of a proof all proof state is disposed, only the proved fact remains in the enclosing
environment.
\<close>

subsubsection "Proof Context"

text \<open>
The proof context is similar to a temporary theory which collects facts and other proof elements.
It may contain
 \<^item> Facts: as usual, facts are valid propositions. However, they need not be globally valid, 
  they can be assumed to be only valid locally during the proof. Like in a theory facts and fact
  sets may be named in a proof context.
 \<^item> Fixed variables: fixed variables are used to denote the ``arbitrary but fixed'' objects 
  often used in a proof. They can be used in all facts in the same proof context. They
  can be roughly compared to the constants in a theory.
 \<^item> Term abbreviations: these are names introduced locally for terms. They can be roughly compared
  to abbreviations defined in a theory. Using such names for terms
  occurring in propositions it is often possible to denote propositions in a more concise form.

Like in a theory the names for facts and fixed variables have the same form, they can always be
distinguished by their usage context. The names for term abbreviations have the form of unknowns (see
Section~\ref{basic-theory-theorem}) and are thus always different from variable names.

Since the proof context is usually populated by explicitly specifying its elements it is visible
in the proof text and also in the session document. In the interactive editor a list of all elements
of the proof context at the cursor position can be obtained in the Query panel
(see Section~\ref{system-jedit-query}) in tab ``Print Context'' by checking ``terms'' (for term
abbreviations) and/or ``theorems'' (for facts).
\<close>

subsubsection "Goal State"

text \<open>
The goal state is used to collect propositions which have not yet been proved. It is used in the
form of a ``to-do list''. It is the duty of a proof to prove all goals in its goal state.
During the proof goals may be removed from the goal state or may be added. A proof may be terminated
when its goal state is empty.

The content of the goal state is not maintained by explicit specifications of the proof writer, it
is updated implicitly by the Isabelle proof mechanism. As a consequence it is usually not visible
in the session document. In the interactive editor it is displayed in the State panel (see
Section~\ref{system-jedit-state}) or in the Output panel (see Section~\ref{system-jedit-output}).

If a subproof is nested in another proof the goal state of the inner proof hides the goal state of
the outer proof until the inner proof is complete.
\<close>

subsubsection "Initial Proof State"

text \<open>
The initial proof state in a theorem of the form
@{theory_text[display]
\<open>theorem "\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<^sub>1 &&& \<dots> &&& C\<^sub>h" \<proof>\<close>}
has the proposition \<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close>  as the only goal in the goal
state and an empty proof context.

If the proposition of a theorem is specified in structured form
@{theory_text[display]
\<open>theorem "C" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
or
@{theory_text[display]
\<open>theorem 
  fixes x\<^sub>1 \<dots> x\<^sub>m assumes "A\<^sub>1" \<dots> "A\<^sub>n" shows "C" \<proof>\<close>}
the initial goal state only contains the conclusion \<open>C\<close>, whereas the initial proof context contains
the assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> as (assumed) facts and the variables \<open>x\<^sub>1 \<dots> x\<^sub>m\<close> as fixed variables.

 If the theorem has multiple conclusions such as
@{theory_text[display]
\<open>theorem "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
the initial goal state contains the single conclusion \<open>C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close>, i.e., the ``meta
conjunction'' of the separate conclusions. This will be split into separate goals for the individual
conclusions upon the first application of a proof method (see Section~\ref{basic-methods}).

Both structured forms support naming the assumptions in the proof context.
Every assumption group separated by \<^theory_text>\<open>and\<close> may be given a name, i.e., the assumptions
may be specified in the form
@{theory_text[display]
\<open>if name\<^sub>1: "A\<^sub>1\<^sub>1" \<dots> "A\<^sub>1\<^sub>m\<^sub>1" and \<dots> and name\<^sub>n: "A\<^sub>n\<^sub>1" \<dots> "A\<^sub>n\<^sub>m\<^sub>n"\<close>}
or
@{theory_text[display]
\<open>assumes name\<^sub>1: "A\<^sub>1\<^sub>1" \<dots> "A\<^sub>1\<^sub>m\<^sub>1" and \<dots> and name\<^sub>n: "A\<^sub>n\<^sub>1" \<dots> "A\<^sub>n\<^sub>m\<^sub>n"\<close>}
respectively, in the same way as the conclusion groups may be named. However, the assumption names
are only valid in the proof context, whereas the conclusion names are only valid outside of the
proof context after the proof is complete.

Additionally, Isabelle always automatically names the assumptions in all groups together. For the
structured form beginning with \<^theory_text>\<open>if\<close> it uses the name \<open>that\<close>, for the structured form beginning
with \<^theory_text>\<open>assumes\<close> it uses the name \<open>assms\<close>.

Since the assumption names are only defined in the proof context they can only be used locally
in the proof of the theorem. Therefore, if the general structured form of a proposition beginning 
with \<^theory_text>\<open>if\<close> is used in a context where no proof is required, such as in an \<^theory_text>\<open>assume\<close> statement (see
Section~\ref{basic-proof-assume}), it is not possible to specify names for the assumption groups.
\<close>

subsection "Proof Procedure"
text_raw\<open>\label{basic-proof-proc}\<close>

text \<open>
Assume you want to prove a derivation rule \<open>A \<Longrightarrow> C\<close> with a single assumption \<open>A\<close> and  a single
 conclusion \<open>C\<close>. The basic procedure to build a proof for it is to construct a sequence of the form
\<open>F\<^sub>1 \<Longrightarrow> F\<^sub>2, F\<^sub>2 \<Longrightarrow> F\<^sub>3, F\<^sub>3 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<^sub>-\<^sub>1, F\<^sub>n\<^sub>-\<^sub>1 \<Longrightarrow> F\<^sub>n\<close> from rules \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> for \<open>i=1\<dots>n-1\<close> 
which are already known to be valid (i.e., facts) where \<open>F\<^sub>1\<close> matches with \<open>A\<close> and \<open>RA\<^sub>1\<close>, 
\<open>F\<^sub>n\<close> matches with \<open>C\<close> and \<open>RC\<^sub>n\<^sub>-\<^sub>1\<close>, and every other \<open>F\<^sub>i\<close> matches with \<open>RA\<^sub>i\<close> and \<open>RC\<^sub>i\<^sub>-\<^sub>1\<close>.

The sequence can be constructed from left to right (called ``forward reasoning'') or from right 
to left (called ``backward reasoning'') or by a combination of both. 

Consider the rule \<open>(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close>. A proof can be constructed from the two 
example rules \<open>example1\<close> and \<open>example2\<close> from the previous sections as the sequence
\<open>(x::nat) < 5 \<Longrightarrow> 2*x \<le> 2*5, 2*x \<le> 2*5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close> consisting of three facts.

Forward reasoning starts by assuming \<open>A\<close> to be the local fact \<open>F\<^sub>1\<close> and incrementally constructs the
sequence from it. An intermediate result is a part \<open>A, F\<^sub>2, \<dots>, F\<^sub>i\<close> of
the sequence, here \<open>F\<^sub>i\<close> is the ``current fact''. A forward reasoning step consists of
stating a proposition \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and proving it to be a new local fact from the current fact \<open>F\<^sub>i\<close> 
using a valid rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>. The step results in the extended sequence
\<open>A, F\<^sub>2, \<dots>, F\<^sub>i, F\<^sub>i\<^sub>+\<^sub>1\<close> with new current fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. When a step successfully 
proves a current fact \<open>F\<^sub>n\<close> which matches the conclusion \<open>C\<close> the proof is complete.

Backward reasoning starts at the conclusion \<open>C\<close> and incrementally 
constructs the sequence from it backwards. An intermediate result is a part \<open>F\<^sub>i, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close> of the
sequence, here \<open>F\<^sub>i\<close> is the ``current goal''. A backward reasoning step consists of constructing a
new current goal \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> and the extended sequence \<open>F\<^sub>i\<^sub>-\<^sub>1, F\<^sub>i, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close> using a valid
rule \<open>RA\<^sub>i\<^sub>-\<^sub>1 \<Longrightarrow> RC\<^sub>i\<^sub>-\<^sub>1\<close>. When a step produces a new current goal \<open>F\<^sub>1\<close>, which matches the assumption
\<open>A\<close>, the proof is complete.
\<close>

subsubsection "Unification"

text \<open>
The matching at the beginning and end of the sequence and when joining the used rules is done
by ``unification''. Two propositions \<open>P\<close> and \<open>Q\<close> are unified by substituting terms 
for unknowns in \<open>P\<close> and \<open>Q\<close> so that the results become syntactically equal.

Since  usually  only the \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> are facts containing unknowns, only they are modified by the
unification, \<open>A\<close> and \<open>C\<close> remain unchanged. 

Note that when an unknown is substituted by a term in \<open>RA\<^sub>i\<close>, the same unknown must be substituted 
by the same term in \<open>RC\<^sub>i\<close> and vice versa, to preserve the validness of the rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>. In
other words, the sequence is usually constructed from specializations of the facts \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>
where every conclusion is syntactically equal to the assumption of the next rule.

In the example the assumption \<open>?x < ?c\<close> of rule \<open>example1\<close> is unified with \<open>(x::nat) < 5\<close> by 
substituting the term \<open>5\<close> for the unknown \<open>?c\<close>, and the variable \<open>x\<close> for the unknown \<open>?x\<close>
resulting in the specialized rule \<open>(x::nat) < 5 \<Longrightarrow> n*x \<le> n*5\<close>.
The conclusion \<open>?x + ?m \<le> ?c + ?m\<close> of rule \<open>example2\<close> is unified with \<open>2*x+3 \<le> 2*5+3\<close> by 
substituting the term \<open>2*x\<close> for the unknown \<open>?x\<close>, the term \<open>2*5\<close> for the unknown \<open>?c\<close>, and the 
term \<open>3\<close> for the unknown \<open>?m\<close> resulting in the specialized rule 
\<open>2*x \<le> 2*5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close>. Now the two specialized rules can be joined by substituting
the term \<open>2\<close> for the unknown \<open>?n\<close> in the first, resulting in the sequence which constitutes the
proof.
\<close>

subsubsection "Storing Facts During a Proof"

text \<open>
In a proof for a derivation rule \<open>A \<Longrightarrow> C\<close> the assumption \<open>A\<close>, the conclusion \<open>C\<close> and the
intermediate facts \<open>F\<^sub>1, F\<^sub>2, \<dots>, F\<^sub>n\<close> constructed by the proof steps must be stored. There
are mainly two ways how this can be done in an Isabelle proof.

The first way is to store the facts at the beginning of the sequence in the proof context and
the facts at the end of the sequence in the goal state. Initially, \<open>A\<close> is the only fact in the
proof context and \<open>C\<close> is the only goal in the goal state. A forward reasoning step consists of
adding fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> to the proof context and proving its validness using rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>. 
The goal state remains unchanged. A backward reasoning step consists of replacing the current
goal \<open>F\<^sub>i\<close> by the new current goal \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> in the goal state and proving that the new goal implies
the previous one using rule \<open>RA\<^sub>i\<^sub>-\<^sub>1 \<Longrightarrow> RC\<^sub>i\<^sub>-\<^sub>1\<close>. The proof context remains unchanged. The proof is
complete when the current goal matches (unifies with) a fact in the proof context.

Note that the facts in the proof context and in the goal state are treated differently. A backward
step replaces the goal since the old goal needs not be handled again in the proof. Whenever the new
goal has been proved the old goal is known to be valid as well. Since the goal state is used to
determine when the proof is complete, it is crucial to remove all unnecessary goals from it.
A forward step, instead, adds a fact to the proof context. It could remove the previous facts, since
they are not needed in the special case described here, however, there are proofs where facts are
used more than once, therefore it is usually useful to keep them in the proof context, and it is
irrelevant for detecting whether a proof is complete.

The second way is to store all facts in the goal state by using a current goal of the form
\<open>\<lbrakk>F\<^sub>1; \<dots>; F\<^sub>i\<rbrakk> \<Longrightarrow> F\<^sub>i\<^sub>+\<^sub>j\<close>, i.e., a derivation rule. The proof context
is not used at all. Initially, the goal state contains the goal \<open>A \<Longrightarrow> C\<close>. A forward reasoning step
consists of adding fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> as assumption to the current goal and proving its validness as above.
A backward reasoning step consists of replacing the conclusion \<open>F\<^sub>i\<^sub>+\<^sub>j\<close> of the current goal by \<open>F\<^sub>i\<^sub>+\<^sub>j\<^sub>-\<^sub>1\<close>
and proving that it implies \<open>F\<^sub>i\<^sub>+\<^sub>j\<close> as above. The proof is complete when the conclusion of the current
goal unifies with one of its assumptions.

Note that these two ways correspond to the initial proof states prepared by the different forms
of theorems. The basic form \<^theory_text>\<open>theorem "A \<Longrightarrow> C"\<close> puts \<open>A \<Longrightarrow> C\<close> into the goal state and leaves the
proof context empty, as required for the second way. The structured forms, such as 
\<^theory_text>\<open>theorem "C" if "A"\<close> put \<open>A\<close> into the proof context and \<open>C\<close> into the goal state, as required for
the first way.
\<close>

subsubsection "Multiple Assumptions"

text \<open>
If the rule to be proved has more than one assumption \<open>A\<close> the sequence to be constructed becomes
a tree where the branches start at (copies of) the assumptions \<open>A\<^sub>1,\<dots>,A\<^sub>n\<close> and merge to finally 
lead to the conclusion \<open>C\<close>. Two branches which end in facts \<open>F\<^sub>1\<^sub>n\<close> and \<open>F\<^sub>2\<^sub>m\<close> are joined by
a step \<open>\<lbrakk>F\<^sub>1\<^sub>n;F\<^sub>2\<^sub>m\<rbrakk> \<Longrightarrow> F\<^sub>1\<close> to a common branch which continues from fact \<open>F\<^sub>1\<close>.

A proof which constructs this tree may again do this by forward reasoning (beginning at the
branches), by backward reasoning (beginning at the common conclusion) or a mixture of both. It may
use the proof context to store facts or it may use rules in the goal state, as described in the
previous sections.

A forward reasoning step at a position where several branches join uses several current facts to
prove a new current fact. Every forward reasoning step selects a subset of the stored local facts
as the current facts and uses them to prove a new local fact from them.

A backward reasoning step may now produce several new current goals, which belong to different
branches in the tree. A step always produces the goals for all branches which join at the current
position in the tree. In this situation a single goal in the goal state is replaced by several goals.
If rules are used as goals the assumptions from the old goal must be copied to all new goals. Facts
stored in the proof context need not be copied since they are available for all goals. A proof is
complete when it is complete for all goals in the goal state.
\<close>

subsubsection "Proving from External Facts"

text \<open>
The branches in the fact tree need not always start at an assumption \<open>A\<^sub>i\<close>, they may also start
at an ``external'' fact which is not part of the local proof context. In such cases the used 
external facts are referenced by their names. In that way a proof can use facts from the 
enclosing theory and a subproof can use facts from the enclosing proof(s) and the enclosing 
toplevel theory.

In particular, if the proposition of a theorem has no assumptions, i.e., the proposition is a
formula and consists only of the conclusion \<open>C\<close>, every proof must start at one or more external facts
(if \<open>C\<close> is no tautology which is valid by itself).
\<close>

subsection "Basic Proof Structure"
text_raw\<open>\label{basic-proof-struct}\<close>

text \<open>
A proof is written in outer syntax and mainly describes how the fact tree is constructed which
leads from the assumptions or external facts to the conclusion.
\<close>

subsubsection "Statements and Methods"

text \<open>
There are two possible operations for modifying the proof state: statements and method applications.

A statement adds one or more elements to the proof context. In particular,
a statement may ``state a fact'', i.e., add a fact to the proof context, this is the reason for
its name. A statement normally does not modify the goal state, there is one specific statement
which may remove a goal from the goal state.

A method application modifies the goal state but normally leaves the proof context
unchanged. The goal state is always modified so that, if all goals in the new state can be proved,
then also all goals in the old state can be proved. This kind of goal state modification is also
called a ``refinement step''.

When writing a proof the ``proof mode'' determines the kind of operation which may be written next:
whether a statement (mode: \<open>proof(state)\<close>) or a method application (mode: \<open>proof(prove)\<close>) is
admissible.

At the beginning of a proof the mode is always \<open>proof(prove)\<close>, i.e., a method application is expected.
In the course of the proof it is possible to switch to mode \<open>proof(state)\<close> for entering statements, 
but not back again. After switching to statement mode the proof must be completed without further
modifications to the goal state other than removing goals, only at the end a last method may be
applied.

However, for every statement that states a fact a (sub-)proof must be specified, which
again starts in mode \<open>proof(prove)\<close>. This way it is possible to freely switch between 
both modes in the course of a proof with nested subproofs.

A backward reasoning step always modifies the goal state, therefore it must be expressed by a
method application. A forward reasoning step may be expressed by a statement, if intermediate facts
are stored in the proof context. If intermediate facts are stored as assumptions in rules in the
goal state, forward reasoning steps must also be expressed by method applications. 

This implies that a sequence of statements can only represent a proof by forward reasoning where
intermediate facts are stored in the proof context, whereas a sequence of method applications can
represent an arbitrary proof where all facts are stored using rules in the goal state.

As described in Section~\ref{basic-proof-state} statements have the advantage that the facts added
to the proof context are explicitly specified by the proof writer and are visible in the session
document. That makes it easier to write and read a proof which consists only of statements. Method
applications specify an operation on the goal state by name, the resulting new goal state is
determined by Isabelle. It is visible for the proof writer in the interactive editor, but it is not
visible in the session document for a reader of the proof. Therefore proofs consisting of method
applications are difficult to understand and the proof writer must anticipate the effect of a
method on the goal state when writing a proof step.
\<close>

subsubsection "Proof Syntax"

text \<open>
If \<open>MA\<^sub>i\<close> denote method applications and \<open>ST\<^sub>i\<close> denote statements, the general form of a proof is
@{theory_text[display]
\<open>MA\<^sub>1 \<dots> MA\<^sub>n
proof `MA\<^sub>n\<^sub>+\<^sub>1`
  ST\<^sub>1 \<dots> ST\<^sub>m
qed `MA\<^sub>n\<^sub>+\<^sub>2`\<close>}
The last step \<open>MA\<^sub>n\<^sub>+\<^sub>2\<close> may be omitted if it is not needed.

The part \<^theory_text>\<open>proof `MA\<^sub>n\<^sub>+\<^sub>1`\<close> switches from method application mode \<open>proof(prove)\<close> to statement mode
\<open>proof(state)\<close>.
 
The part \<^theory_text>\<open>proof \<dots> qed\<close> can be omitted and replaced by \<^theory_text>\<open>done\<close>, then the proof only consists of 
method applications and has the form \<^theory_text>\<open>MA\<^sub>1 \<dots> MA\<^sub>n done\<close>. Such proofs are called ``proof scripts''.

Since a proof script does not contain statements it cannot use the proof context to store facts.
Proof scripts are intended to store facts as assumptions in the goal state or to apply only
backward reasoning, where no intermediate facts need to be stored in addition to the goals
(see Section~\ref{basic-proof-proc}).

If the method applications \<open>MA\<^sub>1 \<dots> MA\<^sub>n\<close> are omitted the proof only consists of 
the statements part and has the form
@{theory_text[display]
\<open>proof `MA\<^sub>1`
  ST\<^sub>1 \<dots> ST\<^sub>m
qed `MA\<^sub>2`\<close>}
where \<open>MA\<^sub>2\<close> can also be omitted. Such proofs are called ``structured proofs''  and the syntactic
elements used to write them are denoted as ``Isar sublanguage'' of the Isabelle outer syntax.

Since structured proofs consist nearly completely of statements, they are intended to use forward
reasoning and store all assumptions and intermediate facts in the proof context.

A structured proof can be so simple, that it has no statements. For this case the syntax
@{theory_text[display]
\<open>by `MA\<^sub>1` `MA\<^sub>2`\<close>}
abbreviates the form \<^theory_text>\<open>proof `MA\<^sub>1` qed `MA\<^sub>2`\<close>. Again, \<open>MA\<^sub>2\<close> can be omitted which
leads to the form
@{theory_text[display]
\<open>by `MA\<^sub>1`\<close>}
In this form the proof consists of a single method application which directly leads 
from the assumptions and used external facts to the conclusion \<open>C\<close>.

As described in the previous section, a structured proof is usually easier to read and write
than a proof script, since in the former case the sequence of the facts \<open>F\<^sub>i\<close> is explicitly
specified in the proof text, whereas in the latter case the sequence of the facts \<open>F\<^sub>i\<close> is
implicitly constructed and the proof text specifies only the methods.

However, since every statement for a forward reasoning step again requires a proof as its part (a
``subproof'' for the stated fact), no proof can be written using statements alone. The main idea of
writing ``good'' proofs is to use nested structured proofs until every subproof is simple enough
to be done in a single method application, i.e., the applied method directly goes from the 
assumptions to the conclusion of the subproof.  Such a simple proof can always be written in
the form \<^theory_text>\<open>by `MA`\<close>.
\<close>

subsubsection "Fake Proofs"

text \<open>
A proof can also be specified as
@{theory_text[display]
\<open>sorry\<close>}
This is a ``fake proof'' which turns the proposition to a fact without actually proving it.

A fake proof can be specified at any point in method application mode, so it can be used to
abort a proof script in the form \<^theory_text>\<open>MA\<^sub>1 \<dots> MA\<^sub>n sorry\<close>.

A structured proof in statement mode cannot be aborted in this way, however, subproofs
can be specified as fake proofs. This makes it possible to interactively develop a structured
proof in a top-down way, by first stating all required facts for the sequence from the assumptions
to the goal with fake subproofs and then replacing the fake proofs by actual subproofs.

 Fake proofs are dangerous. Isabelle blindly registers the proposition as valid, so that it can be
used for other proofs. If it is not valid, everything can be proved from it. That sounds nicely but
is not what you really want.

There is a second way to abort a proof script by specifying a proof as
@{theory_text[display]
\<open>oops\<close>}
Other than by using \<open>sorry\<close> Isabelle will \<^emph>\<open>not\<close> turn the proposition to a fact, instead, it
ignores it. This can be used to document in a theory that you have tried to prove a proposition
but you did not succeed.
\<close>

subsubsection "Nested Proof Contexts"

text \<open>
Instead of a single proof context a proof may use a set of nested proof contexts, starting
with an outermost proof context. In a nested context the content of the
enclosing contexts is available together with the local content. When a nested context is ended,
it is removed together with all its local content.

A nested proof context is created syntactically by enclosing statements in braces:
@{theory_text[display]
\<open>`ST\<^sub>1` \<dots> `ST\<^sub>m` { `ST\<^sub>m\<^sub>+\<^sub>1` \<dots> `ST\<^sub>n` } `ST\<^sub>n\<^sub>+\<^sub>1` \<dots> \<close>}
Note that according to the description until now the nested context is useless, because the facts
introduced by its statements are removed at its end and cannot contribute to 
the proof. How the content of a nested context can be ``exported'' and preserved for later use
will be explained further below.

For names (of fixed variables, facts and term abbreviations), nested contexts behave like a usual
block structure: A name can be redefined in a nested context, then the named object in the outer
context becomes inaccessible (``shadowed'') in the inner context, but becomes accessible again when
the inner context ends. 

When two nested contexts follow each other immediately, this has the effect of ``clearing''
the content of the inner contexts: the content of the first context is removed and the second
context starts being empty. This can be denoted by the keyword
@{theory_text[display]
\<open>next\<close>}
which can be thought of being equivalent to a pair \<open>} {\<close> of adjacent braces.

Moreover the syntax \<^theory_text>\<open>proof `method\<^sub>1` ST\<^sub>1 \<dots> ST\<^sub>n qed `method\<^sub>2`\<close> automatically wraps the statements
\<open>ST\<^sub>1 \<dots> ST\<^sub>n\<close> in a nested context. Therefore it is possible to denote a structured proof 
which only consists of a sequence of nested contexts without braces as
@{theory_text[display]
\<open>proof `method\<^sub>1`
  ST\<^sub>1\<^sub>1 \<dots> ST\<^sub>1\<^sub>m\<^sub>1 next ST\<^sub>2\<^sub>1 \<dots> ST\<^sub>2\<^sub>m\<^sub>2 next \<dots> next ST\<^sub>n\<^sub>1 \<dots> ST\<^sub>n\<^sub>m\<^sub>n
qed `method\<^sub>n\<^sub>+\<^sub>2`\<close>}
where each occurrence of \<^theory_text>\<open>next\<close> clears the content of the inner context.

Another consequence of this wrapping is that no statement can add elements directly to the outermost
proof context. The outermost proof context can only be filled by the initializations done by the
structured theorem forms as described in Section~\ref{basic-proof-state}. The resulting content of
the context is not affected by clearing nested contexts and remains present until the end of the
proof.

Also the goal state of a proof is not affected by the begin or end of a nested context. The goal
state can be considered to be in the scope of the outermost context, it may use fixed variables
from it. However, it is outside of all nested contexts and cannot contain elements from them.
\<close>

subsubsection "Subproofs"

text \<open>
A subproof takes a single goal and solves it as part of another proof. It has its own goal state
which hides the goal state of the enclosing proof until the subproof is complete.

The outermost proof context used by the subproof is nested in the context of the
enclosing proof, therefore all content of the enclosing proof context is available there and can be
referenced by name, as long as the name is not shadowed by a redefinition in the subproof.

There are mainly two kinds of subproofs: proving a goal which is already in the goal state of the
enclosing proof or specifying a new goal which becomes a fact in the proof context after proving it.

The first kind of subproof has the form
@{theory_text[display]
\<open>subgoal \<proof>\<close>}
and may be specified in method application mode \<open>proof(prove)\<close> in place of a single method
application. Its initial goal state contains a copy of the first goal from the goal state of the
enclosing proof. If the subproof is successfully terminated it removes that goal from the goal state
of the enclosing proof.

There is also the ``structured form''
@{theory_text[display]
\<open>subgoal premises name \<proof>\<close>}
If the goal processed by the subproof is a derivation rule \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> it takes the
assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close>, and adds them as assumed facts into the outermost proof context of the
subproof, like the structured forms of theorems do for their assumptions (see
Section~\ref{basic-proof-state}). If \<open>name\<close> is specified it is used for naming the set of
assumptions, if it is omitted the default name \<open>prems\<close> is used.

Using this form a subproof can be written as a structured proof which stores its facts
in its proof context, although the enclosing proof is a proof script and stores its facts as rule
assumptions in the goal state.

The second kind of subproof occurs as part of some statements, as described in
Section~\ref{basic-proof-statefact}.
\<close>

subsection "Method Application"
text_raw\<open>\label{basic-proof-method}\<close>

text \<open>
A method application mainly specifies a proof method to be applied.
\<close>

subsubsection "Proof Methods"

text \<open>
Proof methods are basically denoted by method names, such as \<^theory_text>\<open>standard\<close>, \<^theory_text>\<open>simp\<close>, or \<^theory_text>\<open>rule\<close>. A
proof method name can also be a symbol, such as \<open>-\<close>.

A method may have arguments, then it usually must be delimited by parentheses such as in \<open>(rule
example1)\<close> or \<^theory_text>\<open>(simp add: example2)\<close>, where \<open>example1\<close> and \<open>example2\<close> are fact names.

Isabelle supports a large number of proof methods. A selection of proof methods used in
this manual is described in Section~\ref{basic-methods}. 
\<close>

subsubsection "Method Application"

text \<open>
A standalone method application step is denoted as
@{theory_text[display]
\<open>apply method\<close>}
where \<open>method\<close> denotes the proof method to be applied, together with its arguments.

The method applications which follow \<^theory_text>\<open>proof\<close> and \<^theory_text>\<open>qed\<close> in a structured proof
are simply denoted by the applied method. Hence the general form of a proof is 
@{theory_text[display]
\<open>apply `method\<^sub>1` \<dots> apply `method\<^sub>n`
proof `method\<^sub>n\<^sub>+\<^sub>1`
  ST\<^sub>1 \<dots> ST\<^sub>m
qed `method\<^sub>n\<^sub>+\<^sub>2`\<close>}
where \<open>ST\<^sub>1 \<dots> ST\<^sub>m\<close> are statements. The method \<open>method\<^sub>n\<^sub>+\<^sub>1\<close> is called the ``initial method''
of the structured proof part.
\<close>

subsection "Stating Facts"
text_raw\<open>\label{basic-proof-statefact}\<close>

text \<open>
The most basic kind of statements is used to add a fact to the proof context.
\<close>

subsubsection "Adding a Fact to the Proof Context"

text \<open>
A fact is added to the (innermost enclosing) proof context by a statement of the form
@{theory_text[display]
\<open>have "prop" \<proof>\<close>}
where \<open>prop\<close> is a proposition in inner syntax and \<^theory_text>\<open>\<proof>\<close> is a (sub-) proof for it. This form
is similar to the specification of a theorem in a theory and has a similar effect in the local 
proof context.

As for a theorem the fact can be named:
@{theory_text[display]
\<open>have name: "prop" \<proof>\<close>}
The scope of the name is the innermost proof context enclosing the statement. In their scope named
facts can be displayed and searched as described for theorems in Section~\ref{basic-theory-theorem}.

As for a theorem, if the fact is a derivation rule  with possibly multiple conclusions  it may also
be specified in structured form:
@{theory_text[display]
\<open>have "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
where the conclusions,  assumptions and variables may be grouped by \<^theory_text>\<open>and\<close>,  conclusion and  assumption
groups may be named, and a type may be specified for each variable group.
 
Note, however, that the structured form using \<^theory_text>\<open>fixes\<close>, \<^theory_text>\<open>assumes\<close>, and \<^theory_text>\<open>shows\<close> (see 
Section~\ref{basic-theory-theorem}) is not available for stating facts in a proof.

The \<^theory_text>\<open>have\<close> statement is called a ``goal statement'', because it states the
proposition \<open>prop\<close> as a (local) goal which is then proved by the subproof \<^theory_text>\<open>\<proof>\<close>.

Note that  the names given to facts by naming conclusion groups cannot be used to access them in the
subproof, because they  are only assigned after the proof has been finished, whereas names given to
assumption groups can only be used in the subproof because their scope is the proof context of the
subproof.
\<close>

subsubsection "Proving a Goal"

text \<open>
A proof using only forward reasoning ends, if the last stated fact \<open>F\<^sub>n\<close> unifies with the conclusion
\<open>C\<close>. If the facts are stored in the proof context, \<open>F\<^sub>n\<close> will be added by a statement. Therefore
a special form of stating a fact exists, which, after proving the fact, tries to unify it with a
goal in the goal state of the enclosing proof, and, if successful, removes the goal from that goal
state. This is done by the statement
@{theory_text[display]
\<open>show "prop" \<proof>\<close>}
which is the only statement which may affect the goal state of the enclosing proof. Its syntax is
the same as for \<^theory_text>\<open>have\<close>, including naming and structured form. Like \<^theory_text>\<open>have\<close> it is also called a
``goal statement''. 

As described in Section~\ref{basic-proof-struct}, statements are always wrapped by a nested proof
context. When the \<^theory_text>\<open>show\<close> statement tries to unify its fact with a goal from the goal state it
replaces all variables fixed in an enclosing nested proof context by unknowns (which is called
``exporting the fact'' from the proof context) so that they can match arbitrary subterms (of the
correct type) in the goal.

If the unification of the exported fact with some goal is not successful the step is erroneous and
the proof cannot be continued, in the interactive editor an error message is displayed.

If a goal has the form of a derivation rule, the exported fact is only unified with the conclusion
of the goal. If also the exported fact is a derivation rule, additionally each of its assumptions
must unify with an assumption of the goal.

This is a special case of a refinement step in the sense of Section~\ref{basic-proof-struct}.
Whenever the exported fact can be proved, also the matching goal can be proved. Since the exported
fact has just been proved by the subproof, the matching goal has been proved as well and may be
removed from the enclosing goal state. So the condition for a successful \<^theory_text>\<open>show\<close> statement can be
stated as ``the exported fact must refine a goal'' (this term is used in error messages).

Note that in a proof using only forward reasoning the proposition \<open>prop\<close> in a \<^theory_text>\<open>show\<close> statement is
the same proposition which has been specified as conclusion \<open>C\<close> in the proposition \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>
which shall be proved by the proof. To avoid repeating it, Isabelle automatically provides the
term abbreviation \<open>?thesis\<close> for it in the outermost proof context. So in the simplest case the last
step of a structured proof by forward reasoning can be written as
@{theory_text[display]
\<open>show ?thesis \<proof>\<close>}
The abbreviation \<open>?thesis\<close> is a single identifier, therefore it needs not be quoted.  If the
proposition has multiple conclusions the abbreviation \<open>?thesis\<close> is not introduced.

If, however, the application of the initial method \<open>method\<close> in a structured proof \<^theory_text>\<open>proof method \<dots> \<close> 
modifies the original goal, this modification is not reflected in \<open>?thesis\<close>. So a statement \<^theory_text>\<open>show 
?thesis \<proof>\<close> will usually not work, because \<open>?thesis\<close> no more refines the  
modified goal. Instead, the proof writer must know the modified goal and specify it
explicitly as proposition in the \<^theory_text>\<open>show\<close> statement. If the \<open>method\<close> splits the goal into several new 
goals, several \<^theory_text>\<open>show\<close> statements may be needed to remove them.

To test whether a proposition refines a goal in the enclosing goal state, a
\<^theory_text>\<open>show\<close> statement can be specified with a fake proof:
@{theory_text[display]
\<open>show "prop" sorry\<close>}
If that statement is accepted, the proposition refines a goal and removes it.  Do not forget to
replace the fake proof by a genuine proof to make sure that the proposition is actually valid.
\<close>
 
subsection "Facts as Proof Input"
text_raw\<open>\label{basic-proof-this}\<close>

text \<open>
If a linear fact sequence \<open>F\<^sub>1, \<dots>, F\<^sub>n\<close> where every fact implies the next one is constructed in
statement mode in the form
@{theory_text[display]
\<open>have "F\<^sub>1" `\<proof>\<^sub>1`
\<dots>
have "F\<^sub>n" `\<proof>\<^sub>n`\<close>}
every fact \<open>F\<^sub>i\<close> needs to refer to the previous fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> in its proof \<open>\<proof>\<^sub>i\<close>. This can be 
done by naming all facts 
@{theory_text[display]
\<open>have name\<^sub>1: "F\<^sub>1" `\<proof>\<^sub>1`
\<dots>
have name\<^sub>n: "F\<^sub>n" `\<proof>\<^sub>n`\<close>}
and refer to \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> in \<open>proof\<^sub>i\<close> by \<open>name\<^sub>i\<^sub>-\<^sub>1\<close>.

Isabelle supports an alternative way by passing facts as input to a proof.
\<close>

subsubsection "Using Input Facts in a Proof"

text \<open>
The input facts are passed as input to the first method applied in the proof. In a proof script
it is the method applied in the first \<^theory_text>\<open>apply\<close> step, in a structured proof \<^theory_text>\<open>proof method \<dots>\<close> it 
is the initial method \<open>method\<close>. 

Every proof method accepts a set of facts as input. Whether it processes them and how it uses
them depends on the kind of method. Therefore input facts for a proof only work in the desired 
way, if a corresponding method is used at the beginning of the proof. See Section~\ref{basic-methods}
for descriptions how methods process input facts.
\<close>

subsubsection "Inputting Facts into a Proof"

text \<open>
In method application mode \<open>proof(prove)\<close> facts can be input to the remaining proof 
\<^theory_text>\<open>\<proof>\<close> by
@{theory_text[display]
\<open>using name\<^sub>1 \<dots> name\<^sub>n \<proof>\<close>}
where the \<open>name\<^sub>i\<close> are names of facts or fact sets. The sequence of all referred facts is input 
to the proof following the \<^theory_text>\<open>using\<close> specification. In a proof script it is input to the next
\<^theory_text>\<open>apply\<close> step. If a structured proof follows, it is input to its initial method. Since in 
method application mode no local facts are stated by previous steps, the facts can only be initial
facts in the outermost proof context (see Section~\ref{basic-proof-state}), or they may be external
facts from the enclosing theory, or, if in a subproof, they may be facts from contexts of enclosing
proofs.

In statement mode \<open>proof(state)\<close> fact input is supported with the help of the special
fact set name \<open>this\<close>. The statement
@{theory_text[display]
\<open>then\<close>}
inputs the facts named \<open>this\<close> to the proof of the following goal statement. 

The statement \<^theory_text>\<open>then\<close>
must be immediately followed by a goal statement (\<^theory_text>\<open>have\<close> or \<^theory_text>\<open>show\<close>). This is enforced by
a special third proof mode \<open>proof(chain)\<close>. In it only a goal statement is allowed, \<^theory_text>\<open>then\<close> 
switches to this mode, the goal statement switches back to mode \<open>proof(state)\<close> after its proof.

Note that \<^theory_text>\<open>then\<close> is allowed in statement mode, although it does not state a fact. There
are several other such auxiliary statements allowed in mode \<open>proof(state)\<close> in addition to the
goal statements \<^theory_text>\<open>have\<close> and \<^theory_text>\<open>show\<close>.

The fact set \<open>this\<close> can be set by the statement
@{theory_text[display]
\<open>note name\<^sub>1 \<dots> name\<^sub>n\<close>}
Therefore the statement sequence 
@{theory_text[display]
\<open>note name\<^sub>1 \<dots> name\<^sub>n
then have "prop" \<proof>\<close>}
inputs the sequence of all facts referred by \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> to the \<^theory_text>\<open>\<proof>\<close>, in the same way
as \<^theory_text>\<open>using\<close> inputs them to the remaining proof following it.

The statement sequence
@{theory_text[display]
\<open>note name\<^sub>1 \<dots> name\<^sub>n then\<close>}
can be abbreviated by the statement
@{theory_text[display]
\<open>from name\<^sub>1 \<dots> name\<^sub>n\<close>}
Like \<^theory_text>\<open>then\<close> it switches to mode \<open>proof(chain)\<close> and it inputs the sequence of the facts referred by 
\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> to the proof of the following goal statement.
\<close>

subsection "Fact Chaining"
text_raw\<open>\label{basic-proof-chain}\<close>

text \<open>
In both cases described for fact input until now, the facts still have been referred by names.
This can be avoided by automatically using a stated fact as input to the proof of the next
stated fact. That is called ``fact chaining''. 
\<close>

subsubsection "Automatic Update of the Current Facts"

text\<open>
Fact chaining is achieved, because Isabelle automatically updates the fact set \<open>this\<close>.
Whenever a new fact is added to the proof context, the set \<open>this\<close> is redefined to contain (only)
this fact. In particular, after every goal statement \<open>this\<close> names the new proved fact. Therefore
the fact set \<open>this\<close> is also called the ``current facts''.

Thus a linear sequence of facts where each fact implies the next one can be constructed by
@{theory_text[display]
\<open>have "F\<^sub>1" `\<proof>\<^sub>1`
then have "F\<^sub>2" `\<proof>\<^sub>2`
\<dots>
then have "F\<^sub>n" `\<proof>\<^sub>n`\<close>}
Now in every \<open>proof\<^sub>i\<close> the fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> is available as input and can be used to prove \<open>F\<^sub>i\<close>.

In this way a structured proof for a rule \<open>A \<Longrightarrow> C\<close> can be written which uses a fact sequence
\<open>A, F\<^sub>2, \<dots> F\<^sub>n\<^sub>-\<^sub>1, C\<close>. If the theorem is specified in the structured form \<^theory_text>\<open>theorem "C" if "A"\<close>
which adds the assumption to the proof context and names it \<open>that\<close> (see
Section~\ref{basic-proof-state}) the proof consists of the statement sequence
@{theory_text[display]
\<open>from that have "F\<^sub>2" `\<proof>\<^sub>1`
then have "F\<^sub>3" `\<proof>\<^sub>2`
\<dots>
then have "F\<^sub>n\<^sub>-\<^sub>1" `\<proof>\<^sub>2`
then show ?thesis `\<proof>\<^sub>n`\<close>}
For the structured form \<^theory_text>\<open>theorem assumes "A" shows "C"\<close> the assumption name \<open>assms\<close> must be used
instead of \<open>that\<close>.

Chaining can be combined with explicit fact referral by a statement of the form
@{theory_text[display]
\<open>note this name\<^sub>1 \<dots> name\<^sub>n\<close>}
It sets \<open>this\<close> to the sequence of \<open>this\<close> and the \<open>name\<^sub>1 \<dots> name\<^sub>n\<close>, i.e., it adds the \<open>name\<^sub>1 \<dots> name\<^sub>n\<close>
to \<open>this\<close>. In this way the current facts can be extended with other facts and then chained
to the proof of the next stated fact.

The statement sequence
@{theory_text[display]
\<open>note this name\<^sub>1 \<dots> name\<^sub>n then\<close>}
can be abbreviated by the statement
@{theory_text[display]
\<open>with name\<^sub>1 \<dots> name\<^sub>n\<close>}
Like \<^theory_text>\<open>then\<close> it switches to mode \<open>proof(chain)\<close> and it inputs the sequence of the facts referred by 
\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> together with the current facts to the proof of the following goal statement.

If a proof consists of a fact tree with several branches, every branch can be constructed this
way. Before switching to the next branch the last fact must be named, so that it can later be used
to prove the fact where the branches join. A corresponding proof pattern for two branches which
join at fact \<open>F\<close> is
@{theory_text[display]
\<open>have "F\<^sub>1\<^sub>1" `\<proof>\<^sub>1\<^sub>1`
then have "F\<^sub>1\<^sub>2" `\<proof>\<^sub>1\<^sub>2`
\<dots>
then have name\<^sub>1: "F\<^sub>1\<^sub>m" `\<proof>\<^sub>1\<^sub>m`
have "F\<^sub>2\<^sub>1" `\<proof>\<^sub>2\<^sub>1`
then have "F\<^sub>2\<^sub>2" `\<proof>\<^sub>2\<^sub>2`
\<dots>
then have "F\<^sub>2\<^sub>n" `\<proof>\<^sub>2\<^sub>n`
with name\<^sub>1 have "F" \<proof>
\<close>}

If the theorem has been specified in structured form \<^theory_text>\<open>theorem "C" if "A\<^sub>1" \<dots> "A\<^sub>n"\<close> every branch
can be started in the form
@{theory_text[display]
\<open>from that have "F\<^sub>1\<^sub>1"
\<dots>\<close>}
which will input all assumptions to every branch. This works since unneeded assumptions usually do
not harm in a proof, but it is often clearer for the reader to explicitly name the assumptions
@{theory_text[display]
\<open>theorem "C" if a\<^sub>1: "A\<^sub>1" and \<dots> and a\<^sub>n: "A\<^sub>n"\<close>}
and specify only the relevant assumption by name in the proof:
@{theory_text[display]
\<open>from a\<^sub>1 have "F\<^sub>1\<^sub>1"
\<dots>\<close>}\<close>

subsubsection "Naming and Grouping Current Facts"

text \<open>
Since the fact set built by a \<^theory_text>\<open>note\<close> statement is overwritten by the next stated fact,
it is possible to give it an explicit name in addition to the name \<open>this\<close> in the form
@{theory_text[display]
\<open>note name = name\<^sub>1 \<dots> name\<^sub>n\<close>}
The \<open>name\<close> can be used later to refer to the same fact set again, when \<open>this\<close> has already been updated.
Defining such names is only possible in the \<^theory_text>\<open>note\<close> statement, not in the abbreviated forms
\<^theory_text>\<open>from\<close> and \<^theory_text>\<open>with\<close>.

The facts specified in \<^theory_text>\<open>note\<close>, \<^theory_text>\<open>from\<close>, \<^theory_text>\<open>with\<close>, and \<^theory_text>\<open>using\<close> can be grouped by separating 
them by \<^theory_text>\<open>and\<close>. Thus it is possible to write
@{theory_text[display]
\<open>from name\<^sub>1 and \<dots> and name\<^sub>n have "prop" \<proof>\<close>}
In the case of a \<^theory_text>\<open>note\<close> statement every group can be given an additional explicit name as in
@{theory_text[display]
\<open>note name\<^sub>1 = name\<^sub>1\<^sub>1 \<dots> name\<^sub>1\<^sub>m\<^sub>1 and \<dots> and name\<^sub>n = name\<^sub>n\<^sub>1 \<dots> name\<^sub>n\<^sub>m\<^sub>n\<close>}\<close>

subsubsection "Accessing Input Facts in a Proof"

text \<open>
At the beginning of a proof the set name \<open>this\<close> is undefined, the name cannot be used
to refer to the input facts (which are the current facts in the enclosing proof). To access
the input facts other than by the first proof method they must be named before they are chained to
the goal statement, then they can be referenced in the subproof by that name. For example in
@{theory_text[display]
\<open>note input = this
then have "prop" \<proof>\<close>}
the input facts can be referenced by the name \<open>input\<close> in \<^theory_text>\<open>\<proof>\<close>.
\<close>

subsubsection "Exporting the Current Facts of a Nested Context"

text \<open>
At the end of a nested context (see Section~\ref{basic-proof-struct}) the current facts are
automatically exported to the enclosing context, i.e. they become available there as the fact
set named \<open>this\<close>, replacing the current facts existing before the nested context. This is another
way how facts from a nested context can contribute to the overall proof.

Basically, only the last fact is current at the end of a context. Arbitrary facts can be 
exported from the nested context by explicitly making them current at its end, typically using a 
\<^theory_text>\<open>note\<close> statement:
@{theory_text[display]
\<open>\<dots> { 
  have f\<^sub>1: "prop\<^sub>1" `\<proof>\<^sub>1`
  \<dots>
  have f\<^sub>n: "prop\<^sub>n" `\<proof>\<^sub>n` 
  note f\<^sub>1 \<dots> f\<^sub>n 
  } \<dots>\<close>}
Here all facts are named and the \<^theory_text>\<open>note\<close> statement makes them current by referring them by 
their names. Note, that the names are only valid in the nested context and cannot be used
to refer to the exported facts in the outer context.

The exported facts can be used in the outer context like all other current facts by directly 
chaining them to the next stated fact:
@{theory_text[display]
\<open>\<dots> { \<dots> } then have "prop" \<proof>  \<dots>\<close>}
or by naming them for later use, with the help of a \<^theory_text>\<open>note\<close> statement:
@{theory_text[display]
\<open>\<dots> { \<dots> } note name = this \<dots>\<close>}\<close>

subsection "Assuming Facts"
text_raw\<open>\label{basic-proof-assume}\<close>

text \<open>
Facts can be added to the proof context without proving them, then they are only assumed.
\<close>

subsubsection "Introducing Assumed Facts"

text \<open>
A proposition is inserted as assumption in the proof context by a statement of the form
@{theory_text[display]
\<open>assume "prop"\<close>}

Assumed facts may be derivation rules  with possibly multiple conclusions,  then they may be specified
directly as proposition or in structured form
@{theory_text[display]
\<open>assume "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m\<close>}
The conclusions \<open>C\<^sub>1, \<dots>, C\<^sub>h\<close> and the rule assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> may be grouped by \<^theory_text>\<open>and\<close>,
however, names may only be specified for the conclusion groups in the usual way to name the
assumed facts resulting from the statement. The rule assumptions cannot be named 
since there is no subproof where the names could be used. Note that variables occurring in the
propositions  \<open>C\<^sub>1, \<dots> C\<^sub>h, A\<^sub>1, \<dots>, A\<^sub>n\<close>  are only turned to unknowns if they are explicitly bound in
the \<^theory_text>\<open>for\<close> part, otherwise they refer to variables bound in an enclosing proof context or remain
free in the assumed rule (which is usually an error).

 In their scope named facts introduced by an \<^theory_text>\<open>assume\<close> statement can be displayed and searched like
other named facts (see Section~\ref{basic-theory-theorem}).

Like goal statements an \<^theory_text>\<open>assume\<close> statement makes the assumed facts current, i.e. it updates
the set \<open>this\<close> to contain the specified propositions as facts, so that they can be chained
to a following goal statement:
@{theory_text[display]
\<open>assume "C"
then have "prop" \<proof>
\<dots>\<close>}\<close>

subsubsection "Exporting Facts with Assumptions"

text\<open>
Assumed facts may be used to prove other local facts, so that arbitrary local facts may depend on
the validness of the assumed facts. This is taken into account when local facts are exported from
a proof context (see Section~\ref{basic-proof-statefact}). Whenever a local fact \<open>F\<close> is exported
it is combined with copies of all locally assumed facts \<open>AF\<^sub>1,\<dots>,AF\<^sub>n\<close> to the derivation rule
\<open>\<lbrakk>AF\<^sub>1;\<dots>;AF\<^sub>n\<rbrakk> \<Longrightarrow> F\<close>, so that \<open>F\<close> still depends on the assumptions after leaving the context.

If the fact \<open>F\<close> is itself a derivation rule \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> then the locally assumed facts
are prepended, resulting in the exported rule \<open>\<lbrakk>AF\<^sub>1;\<dots>;AF\<^sub>n;A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>.

If the fact \<open>F\<close> has been proved in a \<^theory_text>\<open>show\<close> statement it is also exported in this way, resulting
in a derivation rule with all local assumptions added. Therefore it will only refine a goal if
every local assumption unifies with an assumption present in the goal, (see
Section~\ref{basic-proof-statefact}).

If in a previous part of a proof facts have been stored as rule assumptions in the goal state (see
Section~\ref{basic-proof-proc}), they can be ``copied'' to the proof context with the help of
\<^theory_text>\<open>assume\<close> statements and will be ``matched back'' by the \<^theory_text>\<open>show\<close> statements used to remove the
goals.

In particular, if a theorem specifies a rule \<open>A \<Longrightarrow> C\<close> directly as proposition it will become the
initial goal, as described in Section~\ref{basic-proof-state}. Then a structured proof using the
fact sequence \<open>A, F\<^sub>2, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close> can be written
@{theory_text[display]
\<open>assume "A"
then have "F\<^sub>2" \<proof>
\<dots>
then have "F\<^sub>n\<^sub>-\<^sub>1" \<proof>
then show ?thesis \<proof>
\<close>}
The \<^theory_text>\<open>show\<close> statement will export the rule \<open>A \<Longrightarrow> C\<close> which matches and removes the goal.
\<close>

subsubsection "Presuming Facts"

text \<open>
It is also possible to use a proposition as assumed fact which does not unify with an
assumption in a goal, but can be proved from them. In other words, the proof is started
somewhere in the middle of the fact tree, works by forward reasoning, and when 
it reaches the conclusion the assumed fact remains to be proved. The statement
@{theory_text[display]
\<open>presume "prop"\<close>}
inserts such a presumed fact into the proof context. Like for \<^theory_text>\<open>assume\<close>  the structured form with
\<^theory_text>\<open>if\<close> and \<^theory_text>\<open>for\<close> is supported.

When a fact is exported from a context with presumed facts, they do not become a part of
the exported rule. Instead, at the end of the context for each presumed fact \<open>F\<^sub>p\<close> a new goal
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> F\<^sub>p\<close> is added to the goal state of the enclosing proof where \<open>A\<^sub>1,\<dots>,A\<^sub>n\<close> are the
facts assumed in the ended context. So the proof has to continue after 
proving all original goals and is only finished when all such goals for presumed facts 
have been proved as well.
\<close>

subsection "Fixing Variables"
text_raw\<open>\label{basic-proof-fix}\<close>

text \<open>
Variables which have not been declared or defined as a constant in the enclosing theory are called
``free'' if they occur in the proposition of a theorem. Such variables are automatically added as
fixed variables to the outermost proof context, thus they can be used everywhere in the proof where
they are not shadowed. If, instead, they are explicitly bound in the proposition (see
Section~\ref{basic-theory-prop}), their use is restricted to the proposition itself. Thus in
@{theory_text[display]
\<open>theorem "\<And>x::nat. x < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
the variable \<open>x\<close> is restricted to the proposition and is not accessible in \<^theory_text>\<open>\<proof>\<close>, whereas in 
@{theory_text[display]
\<open>theorem "(x::nat) < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
the variable \<open>x\<close> is accessible in \<^theory_text>\<open>\<proof>\<close>. If the theorem is specified in structured form,
variables may be explicitly specified to be fixed in the outermost proof context using \<^theory_text>\<open>for\<close> or
\<^theory_text>\<open>fixes\<close>, respectively (see Section~\ref{basic-proof-state}). Therefore the forms
@{theory_text[display]
\<open>theorem "x < 3 \<Longrightarrow> x < 5" for x::nat \<proof>\<close>}
and
@{theory_text[display]
\<open>theorem fixes x::nat shows "x < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
are completely equivalent to the previous form. Thus explicitly fixing variables is optional for
theorems, however it usually improves readability and provides a place where types can be specified
for them in a systematic way.
\<close>

subsubsection "Local Variables"

text\<open>
Additional variables can be added as fixed to the innermost enclosing proof context by the statement
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>n\<close>}
As usual the variables can be grouped by \<^theory_text>\<open>and\<close> and types can be specified for (some of) the groups. 

A fixed variable in a proof context denotes a specific value of its type. However, if the variable
has been introduced by \<^theory_text>\<open>fix\<close>, \<^theory_text>\<open>for\<close> or \<^theory_text>\<open>fixes\<close> it is underspecified in the same way as a constant
introduced by \<^theory_text>\<open>consts\<close> in a theory (see Section~\ref{basic-theory-terms}): no information is given
about its value. In this sense it denotes an ``arbitrary but fixed value''.

If a variable name is used in a proof context without explicitly fixing it, it either refers to a
variable in an enclosing context or it is free. If it is explicitly fixed it names a variable which
is different from all variables with the same name in enclosing contexts.

If a variable is free in the proof for a theorem its value cannot be proved to be related in any
way to values used in the theorem. Therefore it is useless for the proof and its occurrence should
be considered to be an error. In the interactive editor Isabelle marks free variables by a light red
background as an alert for the proof writer. 

A fixed local variable is common to the whole local context. If it occurs in several local facts 
it always is the same variable and denotes the same value, it is not automatically restricted to
every fact, as for toplevel theorems. Hence in
@{theory_text[display]
\<open>fix x::nat
assume a: "x < 3"
have "x < 5" \<proof>\<close>}
the \<^theory_text>\<open>\<proof>\<close> may refer to fact \<open>a\<close> because the \<open>x\<close> is the same variable in both  propositions.
\<close>

subsubsection "Exporting Facts with Local Variables"

text \<open>
Explicitly fixing variables in a proof context is not only important for avoiding name clashes.
If a fact is exported from a proof context, all fixed local variables are replaced by unknowns,
other variables remain unchanged. Since unification only works for unknowns, it makes a difference
whether a fact uses a local variable or a variable which origins from an enclosing context or
is free.

The proposition \<open>x < 3 \<Longrightarrow> x < 5\<close> can be proved by the statements 
@{theory_text[display]
\<open>fix y::nat
assume "y < 3"
then show "y < 5" \<proof>\<close>}
because when the fact \<open>y < 5\<close> is exported, the assumption is added (as described in 
Section~\ref{basic-proof-assume}) and then variable \<open>y\<close> is replaced by the unknown \<open>?y\<close>
because \<open>y\<close> has been locally fixed. The result is the rule \<open>?y<3 \<Longrightarrow> ?y<5\<close> which unifies
with the proposition.

If, instead, \<open>y\<close> is not fixed, the sequence
@{theory_text[display]
\<open>assume "(y::nat) < 3"
then have "y < 5" \<proof>\<close>}
still works and the local fact \<open>y < 5\<close> can be proved, but it cannot be used with the \<^theory_text>\<open>show\<close>
statement to prove the proposition \<open>x < 3 \<Longrightarrow> x < 5\<close>, because the exported rule is now 
\<open>y<3 \<Longrightarrow> y<5\<close> which does not unify with the proposition, it contains a different variable
instead of an unknown.

If variables are explicitly bound in the proposition of a theorem they are not accessible in the
proof. Instead, corresponding new local variables (which may have the same names) must be fixed in
the proof context and used for the proof. Upon export by a \<^theory_text>\<open>show\<close> statement these variables will
be replaced by unknowns which then are unified with the variables in the goal. A corresponding
proof for the proposition \<open>\<And>x::nat. x < 3 \<Longrightarrow> x < 5\<close> is
@{theory_text[display]
\<open>fix y::nat
assume "y < 3"
then show "y < 5" \<proof>\<close>}\<close>



subsection "Defining Variables"
text_raw\<open>\label{basic-proof-define}\<close>

text \<open>
Local variables may also be introduced together with specifying a value for them. This is done
using a statement of the form
@{theory_text[display]
\<open>define x\<^sub>1 \<dots> x\<^sub>m where "x\<^sub>1\<equiv>term\<^sub>1" \<dots> "x\<^sub>m\<equiv>term\<^sub>m"\<close>}
which specifies a defining equation for every defined variable.
As usual, the variables and equations may be grouped by \<^theory_text>\<open>and\<close>, equation groups may be named, and
types may be specified for (some of) the variable groups. In the object logic HOL
(see Chapter~\ref{holbasic}) also the normal equality operator \<open>=\<close> may be used instead of \<open>\<equiv>\<close>.

The variable \<open>x\<^sub>i\<close> may not occur free in \<open>term\<^sub>i\<close>, otherwise an error is signaled. However, the other
variables are allowed in \<open>term\<^sub>i\<close>. This may lead to cyclic definitions which is not checked by
Isabelle, but then the definition cannot be used to determine the defined value for the
corresponding variables, it is underspecified.
\<close>

subsubsection "Defining Equations as Local Facts"

text \<open>
If there is already a previous definition for an \<open>x\<^sub>i\<close> in the same proof context the former \<open>x\<^sub>i\<close> is
shadowed and becomes inaccessible and a new local variable \<open>x\<^sub>i\<close> is introduced.

Thus a defining equation can never contradict any existing fact in the proof context and Isabelle
safely adds all defining equations as facts to the proof context enclosing the \<^theory_text>\<open>define\<close> statement.
The collection of all these facts is automatically named \<open>x\<^sub>1_\<dots>_x\<^sub>m_def\<close>, replacing this name if it
already exists in the local proof context. Explicit names specified for equation groups are used
to name the corresponding facts.
\<close>

subsubsection "Exporting Facts after Defining Variables"

text\<open>
Unlike facts assumed by an \<^theory_text>\<open>assume\<close> statement (see Section~\ref{basic-proof-assume}) the 
facts created by a \<^theory_text>\<open>define\<close> statement are \<^emph>\<open>not\<close> added as assumptions when a fact \<open>F\<close> is 
exported from the local context. Instead, if a locally defined variable \<open>x\<^sub>i\<close> occurs in \<open>F\<close> it
is replaced by the \<open>term\<^sub>i\<close> according to its defining equation.

If the definition of \<open>x\<^sub>i\<close> is cyclic the occurrences of \<open>x\<^sub>i\<close> in \<open>F\<close> are not replaced and become
an unknown during export, however, then the fact \<open>F\<close> usually is invalid and cannot be proved.
\<close>


subsection "Obtaining Variables"
text_raw\<open>\label{basic-proof-obtain}\<close>

text \<open>
Local variables may also be introduced together with  an arbitrary proposition which allows to
specify additional information about their values.  This is done using a statement of the form
@{theory_text[display]
\<open>obtain x\<^sub>1 \<dots> x\<^sub>m where "prop" \<proof>\<close>}
where \<open>prop\<close> is a proposition in inner syntax which contains the variables \<open>x\<^sub>1 \<dots> x\<^sub>m\<close>. 
Like for variables introduced by \<^theory_text>\<open>fix\<close>  or \<^theory_text>\<open>define\<close>  the variables may be grouped by \<^theory_text>\<open>and\<close> and
types may be specified for (some of) the groups.

 If the proposition \<open>prop\<close> is a derivation rule with possibly multiple conclusions it may be
specified in structured form (see Section~\ref{basic-theory-prop}) using several separate
 propositions:
@{theory_text[display]
\<open>obtain x\<^sub>1 \<dots> x\<^sub>m where "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for y\<^sub>1 \<dots> y\<^sub>p \<proof>\<close>}
As usual, the conclusions, assumptions, and bound variables may be grouped by \<^theory_text>\<open>and\<close>, the assumption
and conclusion groups may be named and types may be specified for (some of) the groups of bound
variables.

The proposition(s) usually relate the values of the new variables to values of existing variables 
(which may be local or come from enclosing contexts). In the simplest case the proposition(s) directly 
specify terms for the new variables, like a \<^theory_text>\<open>define\<close> statement (see
Section~\ref{basic-proof-define}) such as in
@{theory_text[display]
\<open>fix x::nat
obtain y z where "y = x + 3" and "z = x + 5" \<proof>\<close>}
But it is also possible to specify the values indirectly:
@{theory_text[display]
\<open>fix x::nat
obtain y z where "x = y - 3" and "y + z = 2*x +8" \<proof>\<close>}
Here the propositions may be considered to be additional facts which are added to the
proof context.
\<close>

subsubsection "Proving \<open>obtain\<close> Statements"

text\<open>
 An \<^theory_text>\<open>obtain\<close> statement has a similar meaning as the statements
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>m 
assume "prop"\<close>}
but there is one important difference: the proposition  in an \<^theory_text>\<open>obtain\<close> statement must be redundant
in the local proof context.

That is the reason why an \<^theory_text>\<open>obtain\<close> statement is a goal statement and includes a proof. The proof 
must prove the redundancy of the  proposition, which may be stated in the following way: if any other
proposition can be derived from it  in the local proof context it must be possible to also derive it
without the proposition. This can be stated formally as
@{text[display]
\<open>(\<And>x\<^sub>1 \<dots> x\<^sub>m. prop \<Longrightarrow> P) \<Longrightarrow> P\<close>}
which is exactly the goal to be proved for the \<^theory_text>\<open>obtain\<close> statement.

Consider the statements
@{theory_text[display]
\<open>fix x::nat
obtain y where "x = 2*y" \<proof>\<close>}
This proposition is not redundant, because it implies that \<open>x\<close> must be even. Therefore no proof
exists.

Note that after a successful proof of an \<^theory_text>\<open>obtain\<close> statement the current  fact is the proposition
specified in the statement, not the proved redundancy goal. If the proposition is specified in
structured form with multiple conclusions the current facts are the collection of facts
corresponding to the conclusions and if names are specified for conclusion groups they are used
to name the resulting facts.

Input facts may be passed to
\<^theory_text>\<open>obtain\<close> statements. Like for the other goal statements, they are input to the \<open>\<proof>\<close>.
\<close>

subsubsection "Exporting Facts after Obtaining Variables"

text\<open>
Unlike facts assumed by an \<^theory_text>\<open>assume\<close> statement (see Section~\ref{basic-proof-assume}) the 
propositions in an \<^theory_text>\<open>obtain\<close> statement are \<^emph>\<open>not\<close> added as assumptions when a fact \<open>F\<close> is 
exported from the local context. This is correct, since they have been proved to be redundant,
therefore they can be omitted.  Also, unlike variables introduced by a \<^theory_text>\<open>define\<close> statement (see
Section~\ref{basic-proof-define}) occurrences of obtained variables in \<open>F\<close> are not replaced
by defining terms, since such terms are not available in the general case.

That implies that an exported fact \<open>F\<close> may not refer to variables introduced by an
\<^theory_text>\<open>obtain\<close> statement, because the information provided by the proposition about them gets
lost during the export. Otherwise an error is signaled.
\<close>

subsection "Term Abbreviations"
text_raw\<open>\label{basic-proof-let}\<close>

text \<open>
A term abbreviation is a name for a proposition or a term in it. 
\<close>

subsubsection "Defining Term Abbreviations"

text\<open>A term abbreviation can be defined by a statement of the form
@{theory_text[display]
\<open>let ?name = "term"\<close>}
Afterwards the name is ``bound'' to the term and can be used in place of the term in 
propositions and other terms, as in:
@{theory_text[display]
\<open>let ?lhs = "2*x+3"
let ?rhs = "2*5+3"
assume "x < 5"
have "?lhs \<le> ?rhs" \<proof>\<close>}

The name \<open>?thesis\<close> (see Section~\ref{basic-proof-statefact}) is a term abbreviation of this
kind. It is defined automatically for every proof in the outermost proof context.

A \<^theory_text>\<open>let\<close> statement can define several term abbreviations in the form
@{theory_text[display]
\<open>let ?name\<^sub>1 = "term\<^sub>1" and \<dots> and ?name\<^sub>n = "term\<^sub>n"\<close>}

A \<^theory_text>\<open>let\<close> statement can occur everywhere in mode \<open>proof(state)\<close>. However, it does not preserve
the current facts, the fact set \<open>this\<close> becomes undefined by it. 
\<close>

subsubsection "Pattern Matching"

text \<open>
Note that term abbreviations have the form of ``unknowns'' (see Section~\ref{basic-theory-theorem}),
although they are defined (``bound''). The reason is that they are actually defined by unification.

The more general form of a \<^theory_text>\<open>let\<close> statement is
@{theory_text[display]
\<open>let "pattern" = "term"\<close>}
where \<open>pattern\<close> is a term which may contain unbound unknowns. As usual, if the pattern consists of
a single unknown, the quotes may be omitted. The \<^theory_text>\<open>let\<close> statement unifies \<open>pattern\<close>
and \<open>term\<close>, i.e., it determines terms to substitute for the unknowns, so that the pattern becomes
syntactically equal to \<open>term\<close>. If that is not possible, an error is signaled, otherwise the
unknowns are bound to the substituting terms. Note that the equals sign belongs to the outer syntax,
therefore both the pattern and the term must be quoted separately.

The \<^theory_text>\<open>let\<close> statement
@{theory_text[display]
\<open>let "?lhs \<le> ?rhs" = "2*x+3 \<le> 2*5+3"\<close>}
binds the unknowns to the same terms as the two \<^theory_text>\<open>let\<close> statements above.

Pattern matching can be used to define parameterized abbreviations. If the pattern has the form of
a function application where the unknown is the function, it will be bound to a function which,
after substituting the arguments, will be equal to the \<open>term\<close>. So it can be applied to other
arguments to yield terms where the corresponding parts have been replaced. This kind of pattern
matching is called ``higher order unification'' and only succeeds if the pattern and \<open>term\<close> are
not too complex.

The \<^theory_text>\<open>let\<close> statement
@{theory_text[display]
\<open>let "?lhs x \<le> ?rhs 5" = "2*x+3 \<le> 2*5+3"\<close>}
binds both unknowns to the lambda term \<open>\<lambda>a. 2 * a + 3\<close>. Thus afterwards the use \<open>?lhs 7\<close> results
in the term \<open>2 * 7 + 3\<close>. 

The \<open>term\<close> may contain unknowns which are already bound. They are substituted 
by their bound terms before the pattern matching is performed. Thus the \<open>term\<close>
can be constructed with the help of abbreviation which have been defined previously. A useful
example is matching a pattern with \<open>?thesis\<close>:
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5+3" 
proof `method` 
  let "?lhs \<le> ?rhs" = ?thesis
  \<dots>\<close>}
to reuse parts of the conclusion in the proof without specifying them explicitly.

Note that the unknowns are only bound at the end of the whole \<^theory_text>\<open>let\<close> statement. In the form
@{theory_text[display]
\<open>let "pattern\<^sub>1" = "term\<^sub>1" and \<dots> and "pattern\<^sub>n" = "term\<^sub>n"\<close>}
the unknowns in \<open>pattern\<^sub>i\<close> cannot be used to build \<open>term\<^sub>i\<^sub>+\<^sub>1\<close> because they are not yet bound.
In contrast, in the sequence of \<^theory_text>\<open>let\<close> statements
@{theory_text[display]
\<open>let "pattern\<^sub>1" = "term\<^sub>1" 
 \<dots> 
let "pattern\<^sub>n" = "term\<^sub>n"\<close>}
the unknowns in \<open>pattern\<^sub>i\<close> can be used to build \<open>term\<^sub>i\<^sub>+\<^sub>1\<close> because they are already bound.

If a bound unknown occurs in the pattern its bound term is ignored and the unknown is rebound
according to the pattern matching. In particular, it does not imply that the old and new bound
terms must be equal, they are completely independent.

If a part of the term is irrelevant and need not be bound the dummy unknown ``\_'' (underscore)
can be used to match it in the pattern without binding an unknown to it:
@{theory_text[display]
\<open>let "_ \<le> ?rhs" = "2*x+3 \<le> 2*5+3"\<close>}
will only bind \<open>?rhs\<close> to the term on the righthand side.

If the term internally binds variables which are used in a subterm, the subterm cannot be matched
separately by an unknown because then the variable bindings would be lost. Thus the statement
@{theory_text[display]
\<open>let "\<lambda>x. ?t" = "\<lambda>x. x+1"\<close>} 
will fail to bind \<open>?t\<close> to \<open>x+1\<close> whereas
@{theory_text[display]
\<open>let "\<lambda>x. x+?t" = "\<lambda>x. x+1"\<close>} 
will successfully bind \<open>?t\<close> to \<open>1\<close> since the bound variable \<open>x\<close> does not occur in it.
\<close>

subsubsection "Casual Term Abbreviations"

text \<open>
Term abbreviations may also be defined in a ``casual way'' by appending a pattern to a proposition
which is used for some other purpose in the form
@{theory_text[display]
\<open>"prop" (is "pattern")\<close>}
The pattern is matched with the proposition \<open>prop\<close> and if successful the unknowns in the pattern
are bound as term abbreviations.

This is possible for all propositions used in a theorem  (see Section~\ref{basic-theory-theorem}),
such as in
@{theory_text[display]
\<open>theorem "prop" (is ?p) \<proof>
theorem fixes x::nat and c and n 
  assumes asm1: "x < c" (is ?a1) and "n > 0" (is ?a2)
  shows "n*x < n*c" (is "?lhs < ?rhs")
  \<proof>\<close>}
and also in the structured form using \<^theory_text>\<open>if\<close> (see Section~\ref{basic-theory-prop}). The unknowns
will be bound as term abbreviations in the outermost proof context in the proof of the theorem.

Note the difference between the fact name \<open>asm1\<close> and the term abbreviation name \<open>?a1\<close> in the
example. The fact name refers to the proposition \<open>x < c\<close> as a valid fact, it can only be used to
work with the proposition as a logical entity. The abbreviation name \<open>?a1\<close>, instead, refers to the
proposition as a syntactic term of type \<open>bool\<close>, it can be used to construct larger terms such as
in \<open>?a1 \<and> ?a2\<close> which is equivalent to the term \<open>x < c \<and> n > 0\<close>.

Casual term abbreviations may also be defined for propositions used in goal statements (see
Sections~\ref{basic-proof-statefact} and~\ref{basic-proof-obtain}) and in \<^theory_text>\<open>assume\<close>,  \<^theory_text>\<open>presume\<close>,
and \<^theory_text>\<open>define\<close> statements (see Sections~\ref{basic-proof-assume} and~\ref{basic-proof-define}).  Then
the unknowns will be bound as term abbreviations in the \<^emph>\<open>enclosing\<close> proof context, so that they
are available after the statement (and also in the nested subproof of the goal statements). 
\<close>

subsection "Accumulating Facts"
text_raw\<open>\label{basic-proof-moreover}\<close>

text \<open>
Instead of giving individual names to facts in the proof context, facts can be collected in
named fact sets. Isabelle supports the specific fact set named \<open>calculation\<close> and provides
statements for managing it.

The fact set \<open>calculation\<close> is intended to accumulate current facts for later use. Therefore
it is typically initialized by the statement
@{theory_text[display]
\<open>note calculation = this\<close>}
and afterwards it is extended by several statements
@{theory_text[display]
\<open>note calculation = calculation this\<close>}
After the last extension the facts in the set are chained to the next proof:
@{theory_text[display]
\<open>note calculation = calculation this then have \<dots>\<close>}\<close>

subsubsection "Support for Fact Accumulation"

text\<open>
Isabelle supports this management of \<open>calculation\<close> with two  specific  statements. The statement 
@{theory_text[display]
\<open>moreover\<close>}
is equivalent to \<^theory_text>\<open>note calculation = this\<close> when it occurs the first time in a context, 
afterwards it behaves like \<^theory_text>\<open>note calculation = calculation this\<close> but without making 
\<open>calculation\<close> current, instead, it leaves the current fact(s) unchanged. The statement
@{theory_text[display]
\<open>ultimately\<close>}
is equivalent to \<^theory_text>\<open>note calculation = calculation this then\<close>, i.e., it adds the current 
facts to the set, makes the set current, and chains it to the next goal statement.

Due to the block structure of nested proof contexts, the \<open>calculation\<close> set can be reused in nested
contexts without affecting the set in the enclosing context. The first occurrence of 
\<^theory_text>\<open>moreover\<close> in the nested context initializes a fresh local \<open>calculation\<close> set. Therefore
fact accumulation is always local to the current proof context.
\<close>

subsubsection "Accumulating Facts in a Nested Context"

text\<open>
Fact accumulation can be used for collecting the facts in a nested context for export
(see Section~\ref{basic-proof-chain}) without using explicit names for them:
@{theory_text[display]
\<open>\<dots> { 
  have "prop\<^sub>1" `\<proof>\<^sub>1` 
  moreover have "prop\<^sub>2" `\<proof>\<^sub>2`
  \<dots>
  moreover have "prop\<^sub>n" `\<proof>\<^sub>n` 
  moreover note calculation 
  } \<dots>\<close>}
\<close>

subsubsection "Accumulating Facts for Joining Branches"

text\<open>
Fact accumulation can also be used for collecting the facts at the end of joined fact branches
in a proof and inputting them to the joining step. A corresponding proof pattern for two branches
which join at fact \<open>F\<close> is
@{theory_text[display]
\<open>have "F\<^sub>1\<^sub>1" `\<proof>\<^sub>1\<^sub>1`
then have "F\<^sub>1\<^sub>2" `\<proof>\<^sub>1\<^sub>2`
\<dots>
then have "F\<^sub>1\<^sub>m" `\<proof>\<^sub>1\<^sub>m`
moreover have "F\<^sub>2\<^sub>1" `\<proof>\<^sub>2\<^sub>1`
then have "F\<^sub>2\<^sub>2" `\<proof>\<^sub>2\<^sub>2`
\<dots>
then have "F\<^sub>2\<^sub>n" `\<proof>\<^sub>2\<^sub>n`
ultimately have "F" \<proof>
\<close>}
The \<^theory_text>\<open>moreover\<close> statement starts the second branch and saves the fact \<open>F\<^sub>1\<^sub>m\<close> to \<open>calculation\<close>.
The \<^theory_text>\<open>ultimately\<close> statement adds the fact \<open>F\<^sub>2\<^sub>n\<close> to \<open>calculation\<close> and then inputs the set to
the proof of \<open>F\<close>. 

Note that \<^theory_text>\<open>moreover\<close> does not chain the current facts to the following goal statement.

Using nested contexts sub-branches can be constructed and joined in the same way.
\<close>

subsection "Equational Reasoning"
text_raw\<open>\label{basic-proof-equational}\<close>

text \<open>
Often informal proofs on paper are written in the style
@{text[display]
\<open>2*(x+3) = 2*x+6 \<le> 3*x+6 < 3*x+9 = 3*(x+3)\<close>}
to derive the fact \<open>2*(x+3) < 3*(x+3)\<close>. Note that the formula shown above is not a wellformed 
proposition because of several occurrences of the toplevel relation symbols \<open>=\<close>, \<open>\<le>\<close> and \<open><\<close>. 
Instead, the formula is meant as an abbreviated notation of the fact sequence
@{text[display]
\<open>2*(x+3) = 2*x+6, 2*x+6 \<le> 3*x+6, 3*x+6 < 3*x+9, 3*x+9 = 3*(x+3)\<close>}
which sketches a proof for \<open>2*(x+3) < 3*(x+3)\<close>. This way of constructing a proof is called
``equational reasoning'' which is a specific form of forward reasoning.
\<close>

subsubsection "Transitivity Rules"

text\<open>
The full example proof needs additional facts which must be inserted into the sequence. From the
first two facts the fact \<open>2*(x+3) \<le> 3*x+6\<close> is derived, then with the third fact the fact 
\<open>2*(x+3) < 3*x+9\<close> is derived, and finally with the fourth fact the conclusion \<open>2*(x+3) < 3*(x+3)\<close>
is reached. The general pattern of these additional derivations can be stated as the derivation
rules
\<open>\<lbrakk>a = b; b \<le> c\<rbrakk> \<Longrightarrow> a \<le> c\<close>, \<open>\<lbrakk>a \<le> b; b < c\<rbrakk> \<Longrightarrow> a < c\<close>, and \<open>\<lbrakk>a < b; b = c\<rbrakk> \<Longrightarrow> a < c\<close>.

Rules of this form are called ``transitivity rules''. They are valid for relations such as equality,
equivalence, orderings, and combinations thereof.

This leads to the general form of a proof constructed by equational reasoning: every forward 
reasoning step starts at a fact \<open>F\<^sub>i\<close> of the form \<open>a r b\<close> where \<open>r\<close> is a relation symbol. It
proves an intermediate fact \<open>H\<^sub>i\<close> of the form \<open>b r c\<close> where \<open>r\<close> is the same or another relation
symbol and uses a transitivity rule to prove the fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> which is \<open>a r c\<close>. In this way it
constructs a linear sequence of facts which leads to the conclusion. 

The intermediate facts \<open>H\<^sub>i\<close> are usually proved from assumptions or external facts, or they may have
a more complex proof which forms an own fact branch which ends at \<open>H\<^sub>i\<close> and is joined with the
main branch at \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> with the help of the transitivity rule.
\<close>

subsubsection "Support for Equational Reasoning"

text \<open>
Isabelle supports equational reasoning in the following form. It provides the statement
@{theory_text[display]
\<open>also\<close>}
which expects that the set \<open>calculation\<close> contains the fact \<open>F\<^sub>i\<close> and the current fact
\<open>this\<close> is the fact \<open>H\<^sub>i\<close>. It automatically selects an adequate transitivity rule, uses it to
derive the fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and replaces \<open>F\<^sub>i\<close> in \<open>calculation\<close> by it. Upon its first use in a proof
context \<^theory_text>\<open>also\<close> simply stores the current fact \<open>this\<close> in \<open>calculation\<close>. The statement
@{theory_text[display]
\<open>finally\<close>}
behaves in the same way but additionally makes the resulting fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> current, i.e., puts it
into the set \<open>this\<close>, and chains it into the next goal statement. In other words, \<^theory_text>\<open>finally\<close> is 
equivalent to \<^theory_text>\<open>also from calculation\<close>.

Note that \<^theory_text>\<open>also\<close> behaves like \<^theory_text>\<open>moreover\<close> and \<^theory_text>\<open>finally\<close> behaves like \<^theory_text>\<open>ultimately\<close>, both with 
additional application of the transitivity rule.

Additionally, Isabelle automatically maintains the term abbreviation \<open>\<dots>\<close> (which is the 
three-dot-symbol available for input in the Symbols panel (see ~Section~\ref{system-jedit-symbols})
of the interactive editor in tab 
``Punctuation'') for the term on the right hand side of the current fact. Together, the
example equational reasoning proof from above can be written
@{theory_text[display]
\<open>have "2*(x+3) = 2*x+6" \<proof>
also have "\<dots> \<le> 3*x+6" \<proof>
also have "\<dots> < 3*x+9" \<proof>
also have "\<dots> = 3*(x+3)" \<proof>
finally show ?thesis \<proof>\<close>}
where \<open>?thesis\<close> abbreviates the conclusion \<open>2*(x+3) < 3*(x+3)\<close>. This form is quite close to
the informal paper style of the proof.
\<close>

subsubsection "Determining Transitivity Rules"

text\<open>
To automatically determine the transitivity rule used by \<^theory_text>\<open>also\<close> or \<^theory_text>\<open>finally\<close>, Isabelle
maintains the dynamic fact set (see Section~\ref{basic-theory-theorem}) named \<open>trans\<close>.
It selects a rule from that set according to the relation symbols used in the facts in 
\<open>calculation\<close> and \<open>this\<close>.

A transitivity rule which is not in \<open>trans\<close> can be explicitly specified by name in the
form
@{theory_text[display]
\<open>also (name)
finally (name)\<close>}
\<close>

section "Proof Methods"
text_raw\<open>\label{basic-methods}\<close>

text \<open>
The basic building blocks of Isabelle proofs are the proof methods which modify the goal state.
If there are several goals in the goal state it depends on the specific method which goals 
are affected by it. In most cases only the first goal is affected.
\<close>

subsection "The empty Method"
text_raw\<open>\label{basic-methods-empty}\<close>

text\<open>
The empty method is denoted by a single minus sign
@{theory_text[display]
\<open>-\<close>}
If no input facts are passed to it, it does nothing, it does not alter the goal state.  An exception
is a goal of the form \<open>C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close> which is always split to separate goals \<open>C\<^sub>i\<close> whenever a
method is applied (see section~\ref{basic-proof-state}).

The empty method is useful at the beginning of a structured proof of the form
@{theory_text[display]
\<open>proof method ST\<^sub>1 \<dots> ST\<^sub>n qed\<close>}
If the statements \<open>ST\<^sub>1 \<dots> ST\<^sub>n\<close> shall process the unmodified original goal the 
empty method must be specified for \<open>method\<close>, thus the structured proof becomes
@{theory_text[display]
\<open>proof - ST\<^sub>1 \<dots> ST\<^sub>n qed\<close>}

Note that it is possible to syntactically omit the \<open>method\<close> completely, but then it defaults to the 
method named \<open>standard\<close> which alters the goal state  (see Section~\ref{basic-methods-rule}).

If input facts are passed to the empty method, it affects all goals by inserting the input facts as 
assumptions after the existing assumptions. If the input facts are \<open>F\<^sub>1,\<dots>,F\<^sub>m\<close> a goal of the form 
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> is replaced by the goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n;F\<^sub>1,\<dots>,F\<^sub>m\<rbrakk> \<Longrightarrow> C\<close>.

This makes it possible to transfer facts stored in the proof context to the goal state where they
are stored as rule assumptions (see Section~\ref{basic-proof-proc}). Since this way of storing facts
is not useful for structured proofs it is normally useless to input facts into a structured proof
with the empty method as initial method.

If a goal statement instead uses a proof script as subproof the script can be started by applying
the empty method to transfer input facts into the goal state for use by further method applications:
@{theory_text[display]
\<open> \<dots> then have "C" apply - MA\<^sub>1 \<dots> MA\<^sub>n done\<close>}
If the current facts are \<open>F\<^sub>1,\<dots>,F\<^sub>m\<close> before the \<^theory_text>\<open>then\<close> statement the goal state in the subproof
contains the goal \<open>\<lbrakk>F\<^sub>1,\<dots>,F\<^sub>m\<rbrakk> \<Longrightarrow> C\<close> before method application \<open>MA\<^sub>1\<close>, so the facts are available
for use in the proof script.
\<close>

subsection "Terminating Proof Scripts"
text_raw\<open>\label{basic-methods-assumption}\<close>

text\<open>
As described in Section~\ref{basic-proof-state} a proof is complete when its goal state is empty.
In a structured proof goals are removed from the goal state by successful \<^theory_text>\<open>show\<close> statements.
Therefore a structured proof is usually terminated by a \<^theory_text>\<open>show\<close> statement which removes the last
goal in the goal state.

Proof scripts, instead, are intended to store facts as rule assumptions in the goal state (see
Section~\ref{basic-proof-struct}). Then the proof of a goal is complete when the conclusion of the
current goal unifies with one of its assumptions (see Section~\ref{basic-proof-proc}).
\<close>

subsubsection "The \<open>assumption\<close> Method"

text\<open>
Such goals are removed from the goal state by the method
@{theory_text[display]
\<open>assumption\<close>}
The method only affects the first goal. If that goal has the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and one
assumption \<open>A\<^sub>i\<close> unifies with \<open>C\<close> the method removes the goal, otherwise an error is signaled.

The \<^theory_text>\<open>assumption\<close> method is automatically applied by a proof part of the form
@{theory_text[display]
\<open>qed method\<close>}
after applying the specified \<open>method\<close>. The application of the \<^theory_text>\<open>assumption\<close> method is repeated as
long as it is applicable, thus \<^theory_text>\<open>qed\<close> removes all goals from the goal state where the conclusion
matches an assumption. The same holds for the abbreviated forms \<^theory_text>\<open>by method\<close> and \<^theory_text>\<open>by method\<^sub>1
method\<^sub>2\<close> (see Section~\ref{basic-proof-struct}).

Therefore a proof script consisting of method applications \<open>MA\<^sub>1 \<dots> MA\<^sub>n\<close> can be terminated by \<^theory_text>\<open>by -\<close>
if the method applications refine all goals to the form where the conclusion unifies with an
assumption. Note that \<^theory_text>\<open>done\<close> does not remove such goals, when it is used to terminate a proof it
expects that the goal state is already empty.
\<close>

subsection "Basic Rule Application"
text_raw\<open>\label{basic-methods-rule}\<close>

text \<open>
As described in Section~\ref{basic-proof-proc} the basic step in the construction of a proof
is to establish the connection between a fact \<open>F\<^sub>i\<close> and a fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> in the fact sequence. Assume
that there is already a valid derivation rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> named \<open>r\<^sub>i\<close> where \<open>RA\<^sub>i\<close> unifies with 
\<open>F\<^sub>i\<close> and \<open>RC\<^sub>i\<close> unifies with \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. Then the connection can be established by applying that rule.
\<close>

subsubsection "The \<open>rule\<close> Method"

text\<open>
A rule is applied by the method
@{theory_text[display]
\<open>rule name\<close>}
where \<open>name\<close> is the name of a valid rule. The method only affects the first goal. If that goal
has the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and the rule referred by \<open>name\<close> has the form \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m\<rbrakk> \<Longrightarrow> RC\<close> 
the method first unifies \<open>RC\<close> with the goal conclusion \<open>C\<close>. That yields the specialized rule
\<open>\<lbrakk>RA\<^sub>1';\<dots>;RA\<^sub>m'\<rbrakk> \<Longrightarrow> RC'\<close> where \<open>RC'\<close> is syntactically equal to \<open>C\<close> and every \<open>RA\<^sub>j'\<close> results from
\<open>RA\<^sub>j\<close> by substituting unknowns by the same terms as in \<open>RC'\<close>. If the goal does not contain unknowns
(which is the normal case) \<open>C\<close> is not modified by the unification. If the unification fails 
the method cannot be executed on the goal state and an error is signaled. Otherwise the method 
replaces the goal by the \<open>m\<close> new goals \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>j'\<close>.

If the rule has the form \<open>RA \<Longrightarrow> RC\<close> with only one assumption the method replaces the goal by
the single new goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA'\<close>. If the rule is a formula \<open>RC\<close> without any
assumptions the method removes the goal without introducing a new goal.

Note that if facts are stored as rule assumptions in the goal state (see
Section~\ref{basic-proof-proc}) an application of method \<^theory_text>\<open>rule\<close> preserves these facts and copies
them to every new goal.

If an assumption \<open>RA\<^sub>j\<close> is again a rule (i.e., the applied rule is a meta rule) and has the form
\<open>\<lbrakk>B\<^sub>1;\<dots>;B\<^sub>k\<rbrakk> \<Longrightarrow> B\<close> the \<open>j\<close>th new goal becomes \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> (\<lbrakk>B\<^sub>1';\<dots>;B\<^sub>k'\<rbrakk> \<Longrightarrow> B')\<close> which by
definition of the \<open>\<lbrakk>\<dots>;\<dots> \<rbrakk>\<close> syntax (see Section~\ref{basic-theory-prop}) is equivalent to
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n;B\<^sub>1';\<dots>;B\<^sub>k'\<rbrakk> \<Longrightarrow> B')\<close>. In this way the rule can introduce additional assumptions in the
resulting goals, which are inserted after the existing assumptions.
\<close>

subsubsection "Using the \<open>rule\<close> Method for Backward Reasoning Steps"

text\<open>
Assume that during a proof for \<open>A \<Longrightarrow> C\<close> as described in Section~\ref{basic-proof-proc} the
intermediate fact sequence \<open>F\<^sub>i\<^sub>+\<^sub>1, \<dots> F\<^sub>n\<^sub>-\<^sub>1, C\<close> has already been constructed by backward
reasoning, i.e., the current goal is \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. If \<open>r\<^sub>i\<close> names a rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>, the successful
method application
@{theory_text[display]
\<open>apply (rule r\<^sub>i)\<close>}
will replace the current goal by \<open>F\<^sub>i\<close> and thus extend the fact sequence to \<open>F\<^sub>i, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close>.
The fact \<open>F\<^sub>i\<close> is the specialized assumption \<open>RA\<^sub>i'\<close> constructed by the method from
the assumption \<open>RA\<^sub>i\<close> of rule \<open>r\<^sub>i\<close>. Together, this application of the \<^theory_text>\<open>rule\<close> method implements
the backwards reasoning step from \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> to \<open>F\<^sub>i\<close>.

Therefore the fact sequence \<open>F\<^sub>1, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close> of the complete proof can be 
constructed by the proof script consisting of the backward reasoning steps
@{theory_text[display]
\<open>apply (rule `r\<^sub>n\<^sub>-\<^sub>1`)
\<dots>
apply(rule r\<^sub>1)
apply(assumption)
done\<close>} 

Note that we used the \<^theory_text>\<open>assumption\<close> method to remove the goal \<open>A \<Longrightarrow> F\<^sub>1\<close> by unifying \<open>F\<^sub>1\<close> with \<open>A\<close>.
Alternatively we can use the form
@{theory_text[display]
\<open>apply (rule `r\<^sub>n\<^sub>-\<^sub>1`)
\<dots>
apply(rule r\<^sub>1)
by -\<close>} 
where the \<^theory_text>\<open>assumption\<close> method is applied implicitly, as described in
Section~\ref{basic-methods-assumption}, or even shorter
@{theory_text[display]
\<open>apply (rule `r\<^sub>n\<^sub>-\<^sub>1`)
\<dots>
by (rule r\<^sub>1)\<close>}

If the example from Section~\ref{basic-proof-proc} is proved this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" 
  apply (rule example2)
  by (rule example1)\<close>}

Note that the assumption \<open>A\<close> of the initial goal must be reached exactly by the sequence of rule
applications. If it is replaced in the example by the stronger assumption \<open>x < 3\<close> the rule
applications will lead to the goal \<open>x < 3 \<Longrightarrow> x < 5\<close> which is trivial for the human reader
but not applicable to the \<^theory_text>\<open>assumption\<close> method.
\<close>

subsubsection "Automatic Rule Selection"

text\<open>
The \<open>rule\<close> method can be specified in the form
@{theory_text[display]
\<open>rule\<close>}
without naming the rule to be applied. Then it selects a rule automatically. It uses the first
rule from the internal fact set \<open>intro\<close> for which the conclusion unifies with the goal conclusion.
If there is no such rule in the set an error is signaled.

If the rules \<open>example1\<close> and \<open>example2\<close> would be in the \<open>intro\<close> set, the example proof could
be written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
  apply rule
  by rule\<close>}
\<close>

subsubsection "Introduction Rules"

text\<open>
The set \<open>intro\<close> is intended by Isabelle for a specific kind of rules called ``introduction rules''.
In such a rule a specific function \<open>f\<close> (perhaps written using an operator name) occurs only in the
conclusion, but not in any assumption, hence it is ``introduced'' by the rule.

When an introduction rule for \<open>f\<close> is applied to a goal by the \<^theory_text>\<open>rule\<close> method, it works ``backwards''
and removes \<open>f\<close> from the goal. If the set \<open>intro\<close> only contains introduction rules and no rule
adds a function which has been removed by another rule in the set, an iterated application of the
\<^theory_text>\<open>rule\<close> method with automatic rule selection will ``deconstruct'' the goal: every step removes a
function from the goal. The iteration stops when no rule in \<open>intro\<close> is applicable. In some sense
the resulting goals are simpler because the set of functions used in them has been reduced.
Some proofs can be written using this technique, however, they depend on the careful selection of
the introduction rule in \<open>intro\<close>.

This proof technique can also be applied by the method
@{theory_text[display]
\<open>intro name\<^sub>1 \<dots> name\<^sub>n\<close>}
where \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> refer to valid rules. It iterates applying rules from the given set to a goal
in the goal state as long as this is possible. It is intended to be used with introduction rules.
Then it automatically deconstructs the goals as much as possible with the given rules. Note that
the method does not use the \<open>intro\<close> set.

A rule is also called an introduction rule for a function \<open>f\<close> if \<open>f\<close> occurs in some assumption(s)
but in a different form (usually applied to other arguments). Then an application by the \<^theory_text>\<open>rule\<close>
method will replace a term containing \<open>f\<close> by a different term containing \<open>f\<close>. The idea is to replace
terms in several steps using one or more introduction rules until finally removing \<open>f\<close> completely.

The rule \<open>example1\<close> from Section~\ref{basic-theory-theorem} is an introduction rule for both
functions \<open>(\<le>)\<close> and \<open>(*)\<close>, but it is only applicable to special uses of them and it replaces them
by the function \<open>(<)\<close> which also is only useful for some specific proofs. In the rule \<open>example2\<close>
the function \<open>(\<le>)\<close> also occurs in the assumption, however applied to other arguments, therefore it
can also be considered as an introduction rule for \<open>(\<le>)\<close>. 

Using the \<^theory_text>\<open>intro\<close> method the example proof can be written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
  by (intro example1 example2)\<close>}

The rules usually present in \<open>intro\<close> in Isabelle are carefully selected to be as generally
applicable and useful for a large number of proofs as possible. Besides by the \<^theory_text>\<open>rule\<close> method the
\<open>intro\<close> set is also used internally by some of the automatic methods described in
Section~\ref{basic-methods-auto}.

If the cursor in the text area is positioned in a proof, introduction rules applicable to the first
goal in the goal state of the enclosing proof can be searched using the keyword \<open>intro\<close> as criterion
for a search by \<^theory_text>\<open>find_theorems\<close> or in the Query panel, as described in
Section~\ref{basic-theory-theorem}. It finds all named facts which can be applied by the \<open>rule\<close>
method to the first goal, i.e., the conclusions can be unified.
\<close>

subsubsection "The \<open>standard\<close> Method"

text\<open>
The method
@{theory_text[display]
\<open>standard\<close>}
is a method alias which can be varied for different Isabelle applications. Usually it is mainly
an alias for the \<open>rule\<close> method.

The \<open>standard\<close> method is the default, if no method is specified as the initial step in a 
structured proof. Thus 
@{theory_text[display]
\<open>proof ST\<^sub>1 \<dots> ST\<^sub>n qed\<close>}
is an abbreviation for
@{theory_text[display]
\<open>proof standard ST\<^sub>1 \<dots> ST\<^sub>n qed\<close>}

Note that the \<^theory_text>\<open>standard\<close> method as initial method in a structured proof will usually affect the
goal by applying a rule from the set \<open>intro\<close> to it. That may be useful in some cases, but it has to
be taken into account when writing the statements of the proof. If the rules \<open>example1\<close>
and \<open>example2\<close> are again considered to be in the set \<open>intro\<close>, the example proof could be written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" 
proof
  show "x < 5 \<Longrightarrow> 2*x \<le> 2*5" by (rule example1)
qed\<close>}
because \<open>proof\<close> (without the empty method \<open>\<hyphen>\<close>) already applies the rule \<open>example2\<close> by applying
the \<^theory_text>\<open>standard\<close> method. It replaces the original goal by \<open>x < 5 \<Longrightarrow> 2*x \<le> 2*5\<close>, so only this goal
remains to be proved. However, this goal replacement is often not apparent to the reader of the
proof. Therefore this form of structured proof should be used with care, it is only intended for
some standard cases where the goal replacement is clearly expected by the proof reader and writer.
Also note that \<open>?thesis\<close> still abbreviates the original goal conclusion and thus cannot be used in
the proof anymore.

In the abbreviated form \<^theory_text>\<open>by method\<close> of a structured proof the method cannot be omitted, but
the proof \<^theory_text>\<open>by standard\<close> can be abbreviated to
@{theory_text[display]
\<open>..\<close>}
(two dots). It can be used as complete proof for a proposition which can be proved by a single
automatic rule application. Since in the example proof also rule \<open>example1\<close> could be automatically
selected by the \<^theory_text>\<open>standard\<close> method, it could be further abbreviated as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof
  show "x < 5 \<Longrightarrow> 2*x \<le> 2*5" ..
qed\<close>}\<close>

subsection "Rule Application in Forward Reasoning"
text_raw\<open>\label{basic-methods-forward}\<close>

text\<open>
Assume that during a proof for \<open>A \<Longrightarrow> C\<close> as described in Section~\ref{basic-proof-proc} the
intermediate fact sequence \<open>A, F\<^sub>2, \<dots>, F\<^sub>i\<close> has already been constructed by forward reasoning and has
been stored in the proof context. Then the next step is to state fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and prove it using a
rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> named \<open>r\<^sub>i\<close>. \<close>

subsubsection "Using the \<open>rule\<close> Method for Forward Reasoning Steps"

text\<open>
Using method \<^theory_text>\<open>rule\<close> the step can be started by the statement
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" proof (rule r\<^sub>i)\<close>}
The goal of this subproof is simply \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>, so applying the \<^theory_text>\<open>rule\<close> method with \<open>r\<^sub>i\<close> will result
in the new goal \<open>RA\<^sub>i'\<close> which unifies with \<open>F\<^sub>i\<close>. The subproof is not finished, since its goal state 
is not empty. But the goal unifies with an already known fact. The proof method
@{theory_text[display]
\<open>fact name\<close>}
can be used to remove that goal. The method only affects the first goal. If the fact referred by
\<open>name\<close> unifies with it, the goal is removed, otherwise an error is signaled.

Using this method the forward reasoning step can be completed as
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" proof (rule r\<^sub>i) qed (fact f\<^sub>i)\<close>}
if \<open>F\<^sub>i\<close> has been named \<open>f\<^sub>i\<close>. This can be abbreviated (see Section~\ref{basic-proof-struct}) to
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" by (rule r\<^sub>i) (fact f\<^sub>i)\<close>}

Therefore the fact sequence \<open>A, F\<^sub>2, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close> of the complete proof for the goal \<open>A \<Longrightarrow> C\<close> can be
constructed by the structured proof of the form
@{theory_text[display]
\<open>proof -
assume a: "A"
have f\<^sub>2: "F\<^sub>2" by (rule r\<^sub>1) (fact a)
\<dots>
have `f\<^sub>n\<^sub>-\<^sub>1`: "F\<^sub>n\<^sub>-\<^sub>1" by (rule `r\<^sub>n\<^sub>-\<^sub>2`) (fact `f\<^sub>n\<^sub>-\<^sub>2`)
show "?thesis" by (rule `r\<^sub>n\<^sub>-\<^sub>1`) (fact `f\<^sub>n\<^sub>-\<^sub>1`)
qed\<close>}
where \<open>?thesis\<close> abbreviates the conclusion \<open>C\<close>, as usual.

If the example from Section~\ref{basic-proof-proc} is proved this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume a: "x < 5"
  have f\<^sub>2: "2*x \<le> 2*5" by (rule example1) (fact a)
  show ?thesis by (rule example2) (fact f\<^sub>2)
qed\<close>}

The \<open>fact\<close> method can be specified in the form
@{theory_text[display]
\<open>fact\<close>}
without naming the fact to be used. Then it selects a fact automatically. It uses the first
fact from the proof context which unifies with the goal. If there is no such fact in the 
proof context an error is signaled.

Thus the example can be written without naming the facts as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume "x < 5"
  have "2*x \<le> 2*5" by (rule example1) fact
  show ?thesis by (rule example2) fact
qed\<close>}\<close>

subsubsection "Input Facts for the \<open>rule\<close> Method"

text\<open>
If input facts \<open>F\<^sub>1, \<dots>, F\<^sub>n\<close> are passed to the \<open>rule\<close> method, they are used to remove assumptions 
from the rule applied by the method. If the rule has the form \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>n\<^sub>+\<^sub>m\<rbrakk> \<Longrightarrow> RC\<close> and
every fact \<open>F\<^sub>i\<close> unifies with assumption \<open>RA\<^sub>i\<close> the first \<open>n\<close> assumptions are removed and the
rule becomes \<open>\<lbrakk>RA\<^sub>n\<^sub>+\<^sub>1';\<dots>;RA\<^sub>n\<^sub>+\<^sub>m'\<rbrakk> \<Longrightarrow> RC'\<close>, specialized according to the term substitutions performed
by the unifications. Then it is applied to the first goal in the usual way.
If there are more input facts than assumptions or if a fact does not unify, an error is signaled.

This behavior of the \<^theory_text>\<open>rule\<close> method can be explained as follows: as described above, for every
assumption in the applied rule the method creates a goal which has the assumption as conclusion. As
usual, the goal is considered solved, if the conclusion unifies with a fact in the proof context.
By unifying the input facts with the rule assumptions the method determines the goals which would
immediately be solved and thus can be omitted, then it removes the assumptions from the rule so
that the corresponding goals are never created.

This allows to establish the connection from a fact \<open>F\<^sub>i\<close> to \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> in a fact chain by a
forward reasoning step of the form
@{theory_text[display]
\<open>from f\<^sub>i have "F\<^sub>i\<^sub>+\<^sub>1" by (rule r\<^sub>i)\<close>}
where \<open>f\<^sub>i\<close> names the fact \<open>F\<^sub>i\<close>. When it is input to the goal statement it is passed to
the \<^theory_text>\<open>rule\<close> method and removes the assumption from the applied rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>, resulting
in the assumption-less ``rule'' \<open>RC\<^sub>i\<close>. When it is applied to the goal \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> it unifies and
removes the goal, thus the subproof is complete.

For the fact sequence chaining can be used to write a structured proof without naming the facts:
@{theory_text[display]
\<open>proof -
assume "F\<^sub>1"
then have "F\<^sub>2" by (rule r\<^sub>1)
\<dots>
then have "F\<^sub>n\<^sub>-\<^sub>1" by (rule `r\<^sub>n\<^sub>-\<^sub>2`)
then show "F\<^sub>n" by (rule `r\<^sub>n\<^sub>-\<^sub>1`)
qed\<close>}
As described in Section~\ref{basic-methods-rule} the subproof \<open>by (rule r\<^sub>i)\<close> can be abbreviated as
\<open>..\<close> if the rule \<open>r\<^sub>i\<close> is in the \<open>intro\<close> rule set.

If the example from Section~\ref{basic-proof-proc} is proved this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume "x < 5"
  then have "2*x \<le> 2*5" by (rule example1)
  then show ?thesis by (rule example2)
qed\<close>}
\<close>

subsubsection "The Method \<open>this\<close>"

text\<open>
Rule application can also be done by the method
@{theory_text[display]
\<open>this\<close>}
Instead of applying a named method, it applies the input fact as rule to the first goal.

If several input facts are given, the method applies them exactly in the given order. Therefore
the fact sequence can also be constructed by a structured proof of the form:
@{theory_text[display]
\<open>proof -
assume "F\<^sub>1"
with r\<^sub>1 have "F\<^sub>2" by this
\<dots>
with `r\<^sub>n\<^sub>-\<^sub>2` have "F\<^sub>n\<^sub>-\<^sub>1" by this
with `r\<^sub>n\<^sub>-\<^sub>1` show "F\<^sub>n" by this
qed\<close>}
The \<^theory_text>\<open>with\<close> statement inserts the explicitly specified facts \<^emph>\<open>before\<close> the current facts. 
Therefore every goal statement for \<open>F\<^sub>i\<close> gets as input the rule \<open>r\<^sub>i\<^sub>-\<^sub>1\<close> followed by the 
chained fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close>. The method \<open>this\<close> first applies the rule which replaces the goal
by \<open>F\<^sub>i\<^sub>-\<^sub>1\<close>. Then it applies the fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> as rule to this goal which removes it and finishes
the subproof.

The proof
@{theory_text[display]
\<open>by this\<close>}
can be abbreviated by \<open>.\<close> (a single dot).

Therefore the example from Section~\ref{basic-proof-proc} can also be proved in the form
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume "x < 5"
  with example1 have "2*x \<le> 2*5" .
  with example2 show ?thesis .
qed\<close>}\<close>

subsubsection "The Methods \<open>frule\<close> and \<open>drule\<close>"

text\<open>
Instead of storing facts in the proof context and using a structured proof for a forward reasoning
proof the facts may be stored as rule assumptions in the goal state and the forward reasoning proof
may be written as a proof script (see Section~\ref{basic-proof-struct}). 

To construct a proof for the goal \<open>A \<Longrightarrow> C\<close> as fact sequence \<open>A, F\<^sub>2 \<dots> F\<^sub>n\<close> by forward reasoning as
described in Section~\ref{basic-proof-proc} in this way, the intermediate fact sequence
\<open>A, F\<^sub>2, \<dots>, F\<^sub>i\<close> is stored in the extended goal \<open>\<lbrakk>A; F\<^sub>2; \<dots>; F\<^sub>i\<rbrakk> \<Longrightarrow> C\<close> where the last assumption is
the current fact \<open>F\<^sub>i\<close>. Then the next forward reasoning step consists of adding the fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> as
new assumption to the goal and prove it using a rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> named \<open>r\<^sub>i\<close>. When the fact
sequence is complete the goal is \<open>\<lbrakk>A; F\<^sub>2; \<dots>; F\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and \<open>F\<^sub>n\<close> unifies with \<open>C\<close>, thus an
application of method \<^theory_text>\<open>assumption\<close> will remove the goal and terminate the proof
(see Section~\ref{basic-methods-assumption}).

A rule is applied for forward reasoning by the method
@{theory_text[display]
\<open>frule name\<close>}
where \<open>name\<close> is the name of a valid rule. The method only affects the first goal. If that goal
has the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and the rule referred by \<open>name\<close> has the form \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m\<rbrakk> \<Longrightarrow> RC\<close> 
the method first unifies the first assumption \<open>RA\<^sub>1\<close> in the rule with the first assumption \<open>A\<^sub>k\<close> of
the \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> which can be unified with \<open>RA\<^sub>1\<close>. That yields the specialized rule
\<open>\<lbrakk>RA\<^sub>1';\<dots>;RA\<^sub>m'\<rbrakk> \<Longrightarrow> RC'\<close> where \<open>RA\<^sub>1'\<close> is syntactically equal to \<open>A\<^sub>k\<close> and every \<open>RA\<^sub>j'\<close> with \<open>j > 1\<close>
and \<open>RC'\<close> results from \<open>RA\<^sub>j\<close> or \<open>RC\<close>, respectively, by substituting unknowns by the same terms as
in \<open>RA\<^sub>1'\<close>. If the goal does not contain unknowns (which is the normal case) \<open>A\<^sub>k\<close> is not
modified by the unification. If no \<open>A\<^sub>i\<close> unifies with \<open>RA\<^sub>1\<close> the method cannot be executed on the goal
state and an error is signaled. Otherwise the method replaces the goal by the \<open>m-1\<close> new goals
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>j'\<close> for  \<open>j > 1\<close> and the goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n;RC'\<rbrakk> \<Longrightarrow> C\<close>.

If the rule has the form \<open>RA \<Longrightarrow> RC\<close> with only one assumption the method replaces the goal by
the single new goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n;RC'\<rbrakk> \<Longrightarrow> C\<close>, i.e., it adds the conclusion of the rule as assumption
in the goal. If the rule is a formula \<open>RC\<close> without any assumptions the method is not applicable and
signals an error.

Since the first assumption \<open>RA\<^sub>1\<close> in the rule plays a special role in this context, it is also
called the ``major premise'' of the rule.

Together, a forward reasoning step as described above can be implemented by the method application
@{theory_text[display]
\<open>apply (frule r\<^sub>i)\<close>}
and the full proof script for a forward reasoning proof has the form
@{theory_text[display]
\<open>apply(frule r\<^sub>1)
\<dots>
apply (frule `r\<^sub>n\<^sub>-\<^sub>1`)
apply(assumption)
done\<close>} 
or shorter
@{theory_text[display]
\<open>apply (frule r\<^sub>1)
\<dots>
by (frule `r\<^sub>n\<^sub>-\<^sub>1`)\<close>} 

If the example from Section~\ref{basic-proof-proc} is proved this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
  apply (frule example1)
  by (frule example2)\<close>}

However, this form of forward reasoning proof has several drawbacks. First, as always in proof
scripts, the facts \<open>F\<^sub>i\<close> are not specified explicitly, they are constructed implicitly by the
\<^theory_text>\<open>frule\<close> method and can only be seen by interactively inspecting the goal state. Next, since the
current fact is the last assumption in the goal, it is not guaranteed that the rule \<open>r\<^sub>i\<close> is
applied to it. If a previous assumption also unifies with the major premise of \<open>r\<^sub>i\<close> the rule is
not applied in the intended way. Finally, it is not possible to generalize this approach to proofs
with several branches. The branches cannot be joined, because \<^theory_text>\<open>frule\<close> always takes only one
assumption into account.

The second drawback can be compensated for by using another method for applying the rule. This is
done by the method
@{theory_text[display]
\<open>drule name\<close>}
where \<open>name\<close> is the name of a valid rule. The method works like \<^theory_text>\<open>frule\<close>, but instead of adding 
\<open>RC'\<close> to the assumptions it replaces \<open>A\<^sub>k\<close> by it. Thus the method replaces the goal by the \<open>m-1\<close> new
goals \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>k\<^sub>-\<^sub>1; A\<^sub>k\<^sub>+\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>j'\<close> for  \<open>j > 1\<close> and the goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>k\<^sub>-\<^sub>1;A\<^sub>k\<^sub>+\<^sub>1;\<dots>;A\<^sub>n;RC'\<rbrakk> \<Longrightarrow> C\<close>.

When using \<^theory_text>\<open>drule\<close> for constructing a proof in the way described above, it always replaces the
current fact by the next one in the fact sequence. The intermediate fact sequence is represented by
the goal \<open>F\<^sub>i \<Longrightarrow> C\<close>. Since the current fact is the only assumption present in the goal, the step
\<^theory_text>\<open>apply (drule r\<^sub>i)\<close> is always applied to it and replaces the goal by \<open>F\<^sub>i\<^sub>+\<^sub>1 \<Longrightarrow> C\<close>, as intended.

The methods \<^theory_text>\<open>frule\<close> and \<^theory_text>\<open>drule\<close> do not support input facts.
\<close>

subsubsection "Destruction Rules"

text\<open>
Not all rules can always usefully be applied by \<^theory_text>\<open>frule\<close> and \<^theory_text>\<open>drule\<close>. Since both methods only
unify their first assumption (the major premise) of the rule with a term in the goal and then replace
it by the conclusion, the first assumption should have some effect on the conclusion. In particular,
the conclusion should not be a single unknown which does not occur in the first assumption.

If additionally a specific function \<open>f\<close> (perhaps written using an operator name) occurs only in the
first assumption and neither in the conclusion, nor in other assumptions, the rule is called a
``destruction rule'' for \<open>f\<close>. If it is applied in forward direction, such as with  \<^theory_text>\<open>frule\<close>
and \<^theory_text>\<open>drule\<close>, \<open>f\<close> will be removed from the goal, it will be ``destructed''.

Similar to introduction rules (see Section~\ref{basic-methods-rule}) \<open>f\<close> may occur in the
conclusion if it has a different form, so that it may be removed by several steps through
intermediate forms.

Analogous to the \<open>intro\<close> set for introduction rules there is an internal fact set \<open>dest\<close> for
destruction rules. It is used by some automatic methods, however, it is not used for automatically
selecting rules for \<^theory_text>\<open>frule\<close> and \<^theory_text>\<open>drule\<close>.

If the cursor in the text area is positioned in a proof, destruction rules applicable to the first
goal in the goal state of the enclosing proof can be searched using the keyword \<open>dest\<close> as criterion
for a search by \<^theory_text>\<open>find_theorems\<close> or in the Query panel, as described in
Section~\ref{basic-theory-theorem}. It finds all named facts which can be applied by the \<open>frule\<close>
or \<open>drule\<close> method to the first goal, i.e., the major premise unifies with a goal assumption.

The rule \<open>example1\<close> from Section~\ref{basic-theory-theorem} is a
destruction rule for function \<open>(<)\<close>, but it is also only applicable to special uses of it and it
replaces it by the functions \<open>(\<le>)\<close>, \<open>(*)\<close>, and \<open>(+)\<close> which does not help for most proofs.
In the rule \<open>example2\<close> the operator \<open>(\<le>)\<close> also occurs in the conclusion, but in different form.
Therefore it can be considered as destruction rule for \<open>(\<le>)\<close>, although the form in the conclusion
is more complex which also does not help for most proofs.
\<close>

subsection "Composed Proof Methods"
text_raw\<open>\label{basic-methods-composed}\<close>

text \<open>
Proof methods can be composed from simpler methods with the help of ``method expressions''.
A method expression has one of the following forms:
 \<^item> \<open>m\<^sub>1, \<dots>, m\<^sub>n\<close> : a sequence of methods which are applied in their order,
 \<^item> \<open>m\<^sub>1; \<dots>; m\<^sub>n\<close> : a sequence of methods where each is applied to the goals created by the previous method,
 \<^item> \<open>m\<^sub>1| \<dots>| m\<^sub>n\<close> : a sequence of methods where only the first applicable method is applied,
 \<^item> \<open>m[n]\<close> : the method \<open>m\<close> is applied to the first \<open>n\<close> goals,
 \<^item> \<open>m?\<close> : the method \<open>m\<close> is applied if it is applicable,
 \<^item> \<open>m+\<close> : the method \<open>m\<close> is applied once and then repeated as long as it is applicable.

Parentheses are used to structure and nest composed methods.

Composed methods can be used to combine method applications to a single step. Using composed 
methods the example backward reasoning proof script from Section~\ref{basic-methods-rule} can be
written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
  apply(rule example2,rule example1,assumption)
  done\<close>}

In particular, it is also possible to apply an arbitrarily complex composed method as initial 
method in a structured proof. Using composed methods the first example forward reasoning proof in
Section~\ref{basic-methods-forward} can be written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume a: "x < 5"
  have f\<^sub>2: "2*x \<le> 2*5" by (rule example1,fact a)
  show ?thesis by (rule example2,fact f\<^sub>2)
qed\<close>}
\<close>

subsection "The Simplifier"
text_raw\<open>\label{basic-methods-simp}\<close>

text \<open>
A common proof technique is ``rewriting''. If it is known that a term \<open>a\<close> is equal to a term
\<open>b\<close>, some occurrences of \<open>a\<close> in a proposition can be replaced by \<open>b\<close> without changing the 
validity of the proposition.

Equality of two terms \<open>a\<close> and \<open>b\<close> can be expressed by the proposition \<open>a = b\<close>. If that 
proposition has been proved to be valid, i.e., is a fact, \<open>a\<close> can be substituted by \<open>b\<close>
and vice versa in goals during a proof.
\<close>

subsubsection "The \<open>subst\<close> Method" 

text \<open>
Rewriting is performed by the method
@{theory_text[display]
\<open>subst name\<close>}
where \<open>name\<close> references an equality fact. The method only affects the first goal. If the
referenced fact has the form \<open>a = b\<close> the method replaces the first occurrence of \<open>a\<close> in
the goal conclusion by \<open>b\<close>. The order of the terms in the equality fact matters, the 
method always substitutes the term on the left by that on the right. 

If the equality contains unknowns unification is used: \<open>a\<close> is
unified with every sub-term of the goal conclusion, the first match is replaced by \<open>b'\<close>
which is \<open>b\<close> after substituting unknowns in the same way as in \<open>a\<close>. If there is no match
of \<open>a\<close> in the goal conclusion an error is signaled.

For a goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> the method only rewrites in the conclusion \<open>C\<close>. The first
match in the assumptions \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> can be substituted by the form
@{theory_text[display]
\<open>subst (asm) name\<close>}
If not only the first match shall be substituted, a number of the match or a range of numbers
may be specified in both forms as in
@{theory_text[display]
\<open>subst (asm) (i..j) name\<close>}

The equality fact can also be a meta equality of the form \<open>a \<equiv> b\<close>. Therefore the method can
be used to expand constant definitions. After the definition
@{theory_text[display]
\<open>definition "inc x \<equiv> x + 1"\<close>}
the method \<^theory_text>\<open>subst inc_def\<close> will rewrite the first occurrence of a function application 
\<open>(inc t)\<close> in the goal conclusion to \<open>(t + 1)\<close>. Remember from Section~\ref{basic-theory-definition}
that the defining equation is automatically named \<open>inc_def\<close>. Note the use of unification to
handle the actual argument term \<open>t\<close>.

The equality fact may be conditional, i.e., it may be a derivation rule with assumptions of the
form \<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>m\<rbrakk> \<Longrightarrow> a = b\<close>. When the \<open>subst\<close> method applies a conditional equation of this
form to a goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>, it adds the goals \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>i'\<close> to the goal state
after rewriting, where \<open>RA\<^sub>i'\<close> result from \<open>RA\<^sub>i\<close> by the unification of \<open>a\<close> in \<open>C\<close>. These
goals are inserted before the original goal, so the next method application will usually process
the goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>1'\<close>.

As an example if there are theorems
@{theory_text[display]
\<open>theorem eq1: "n = 10 \<Longrightarrow> n+3 = 13" for n::nat \<proof>
theorem eq2: "n = 5 \<Longrightarrow> 2*n = 10" for n::nat \<proof>\<close>}
the method \<^theory_text>\<open>subst (2) eq2\<close> replaces the goal \<open>(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3\<close> by the
goals 
@{text[display]
\<open>x < 5 \<Longrightarrow> 5 = 5
x < 5 \<Longrightarrow> 2 * x + 3 \<le> 10 + 3\<close>}
where the first is trivial (but still must be removed by applying a rule). The second 
goal is replaced by the method \<^theory_text>\<open>subst (2) eq1\<close> by
@{text[display]
\<open>x < 5 \<Longrightarrow> 10 = 10
x < 5 \<Longrightarrow> 2 * x + 3 \<le> 13\<close>}

Note that the method \<^theory_text>\<open>subst eq2\<close> would unify \<open>2*n\<close> with the first match \<open>2*x\<close> in the original 
goal and replace it by
@{text[display]
\<open>x < 5 \<Longrightarrow> x = 5
x < 5 \<Longrightarrow> 10 + 3 \<le> 2 * 5 + 3\<close>}
where the first goal cannot be proved because it is invalid.
\<close>

subsubsection "Simplification" 

text\<open>
If the term \<open>b\<close> in an equation \<open>a = b\<close> is in some sense ``simpler'' than \<open>a\<close>, the goal will
also become simpler by successful rewriting with the equation. If there are several
such equations a goal can be replaced by successively simpler goals by rewriting with these
equations. This technique can contribute to the goal's proof and is called ``simplification''.

Basically, simplification uses a set of equations and searches an equation in the set where 
the left hand side unifies with a sub-term in the goal, then substitutes it. This step is 
repeated until no sub-term in the goal unifies with a left hand side in an equation in the set.

It is apparent that great care must be taken when populating the set of equations, otherwise 
simplification may not terminate. If two equations \<open>a = b\<close> and \<open>b = a\<close> are in the set simplification
will exchange matching terms forever. If an equation \<open>a = a+0\<close> is in the set, a term matching
\<open>a\<close> will be replaced by an ever growing sum with zeroes.

Simplification with a set of definitional equations from constant definitions (see 
Section~\ref{basic-theory-definition}) always terminates. Since constant definitions cannot 
be recursive, every substitution removes one occurrence of a defined constant from the goal. 
Simplification terminates if no defined constant from the set remains in the goal.
Although the resulting goal usually is larger than the original goal, it is simpler in the 
sense that it uses fewer defined constants.

If the set contains conditional equations, simplification may produce additional goals. Then 
simplification is applied to these goals as well. Together, simplification may turn a single
complex goal into a large number of simple goals, but it cannot reduce the number of goals.
Therefore simplification is usually complemented by methods which remove trivial goals 
like \<open>x = x\<close>, \<open>A \<Longrightarrow> A\<close>, and \<open>True\<close>. Such an extended simplification may completely solve and remove 
the goal to which it is applied.
\<close>

subsubsection "The \<open>simp\<close> Method"

text\<open>
Isabelle supports simplification by the method
@{theory_text[display]
\<open>simp\<close>}
which is also called ``the simplifier''. It uses the dynamic fact set \<open>simp\<close> as the set of 
equations, which is also called ``the simpset''. The method only affects the first goal. 
If no equation in the simpset is applicable to it or it is not modified by the applicable equations 
an error is signaled.

The \<open>simp\<close> method simplifies the whole goal, i.e., it applies rewriting to the conclusion and 
to all assumptions.

The simpset may contain facts which are not directly equations, but can be converted to an
equation. In particular, an arbitrary derivation rule \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> can always be converted
to the conditional equation \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C = True\<close>. The simplifier (and also the \<open>subst\<close> method)
performs this conversion if no other conversion technique applies, therefore the simpset may
actually contain arbitrary facts.

The \<open>simp\<close> method also detects several forms of trivial goals and removes them. Thus a complete
proof may be performed by a single application of the simplifier in the form
@{theory_text[display]
\<open>by simp\<close>}

In Isabelle HOL (see Section~\ref{holbasic}) the simpset is populated with a large number of facts
which make the simplifier a very useful proof tool. Actually all examples of facts used
in the previous sections can be proved by the simplifier:
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" by simp
theorem example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m" by simp
theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" by simp
theorem eq1: "n = 10 \<Longrightarrow> n+3 = 13" for n::nat by simp
theorem eq2: "n = 5 \<Longrightarrow> 2*n = 10" for n::nat by simp\<close>}\<close>

subsubsection "Configuring the Simplifier"

text \<open>
The simplifier can be configured by modifying the equations it uses. The form
@{theory_text[display]
\<open>simp add: name\<^sub>1 \<dots> name\<^sub>n\<close>}
uses the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close> in addition to the facts in the simpset for its rewriting
steps. The form 
@{theory_text[display]
\<open>simp del: name\<^sub>1 \<dots> name\<^sub>n\<close>}
uses only the facts from the simpset without the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close>, and the form
@{theory_text[display]
\<open>simp only: name\<^sub>1 \<dots> name\<^sub>n\<close>}
uses only the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close>. The three forms can be arbitrarily combined.

As usual, a theorem may be added permanently to the simpset as described in 
Section~\ref{basic-theory-theorem} by specifying it as
@{theory_text[display]
\<open>theorem [simp]: "prop" \<proof>\<close>}
and the defining equation of a definition can be added by
@{theory_text[display]
\<open>definition name::type where [simp]: "name \<equiv> term"\<close>}

Adding own constant definitions to the simplifier is a common technique to expand the definition
during simplification. However, this may also have a negative effect: If an equation has been 
specified using the defined constant, it is no more applicable for rewriting after expanding
the definition. Note that the facts in the simpset and the facts provided by \<open>add:\<close>, \<open>del:\<close>, and
\<open>only:\<close> are not simplified themselves, the defined constant will not be expanded there.

Therefore it is usually not recommended to add defining equations to the simpset permanently.
Instead, they can be specified by \<open>add:\<close> when they really shall be expanded during simplification.
\<close>

subsubsection "Splitting Terms"

text \<open>
There are certain terms in which the simplifier will not apply its simpset rules. A typical
example are terms with an internal case distinction (see Section~\ref{holtdefs-data-destr}). To 
process such terms in a goal conclusion the terms must be split. Splitting a term usually results
in several new goals with simpler terms which are then further processed by the simplifier.

Term splitting is done by applying specific rules to the goal. These rules are called ``split
rules''. Usually split rules are not automatically determined and applied by the simplifier, this 
must be configured explicitly in the form
@{theory_text[display]
\<open>simp split: name\<^sub>1 \<dots> name\<^sub>n\<close>}
where the \<open>name\<^sub>i\<close> are the names of the split rules to use. This configuration can be arbitrarily 
combined with the other simplifier configuration options.

The usual form of a split rule is a proposition
@{theory_text[display]
\<open>"?P(term) = ((Q\<^sub>1 \<longrightarrow> ?P(term\<^sub>1)) \<and> \<dots> \<and> (Q\<^sub>n \<longrightarrow> ?P(term\<^sub>n)))"\<close>}
where the \<open>term\<^sub>i\<close> are subterms of \<open>term\<close> and every \<open>Q\<^sub>i\<close> represents a condition for which \<open>term\<close>
can be reduced to \<open>term\<^sub>i\<close>. The simplifier applies such a split rule to a goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>m\<rbrakk> \<Longrightarrow> C\<close>
by first unifying the left hand side with the conclusion \<open>C\<close> (which succeeds if \<open>term\<close> occurs in
\<open>C\<close>), then replacing it by the conjunction on the right, then splitting the goal into a separate
goal for every conjunct, and finally moving every \<open>Q\<^sub>i\<close> to the assumptions of their goal. Thus the
resulting goals have the form
@{text[display]
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>m;Q\<^sub>1\<rbrakk> \<Longrightarrow> C\<^sub>1
\<dots>
\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>m;Q\<^sub>n\<rbrakk> \<Longrightarrow> C\<^sub>n\<close>}
where \<open>C\<^sub>i\<close> is constructed from \<open>C\<close> by mainly replacing \<open>term\<close> by \<open>term\<^sub>i\<close>.

Note that this form of a split rule can only be applied for splitting terms in the conclusion of a
goal. See the Isabelle documentation for other forms which split terms in assumptions of a goal.
\<close>

subsubsection "Searching Simplifier Equations"

text \<open>
Named facts applicable for simplification may be searched using the command \<^theory_text>\<open>find_theorems\<close> or in
the Query panel, as described in Section~\ref{basic-theory-theorem}, using a \<open>criterion\<^sub>i\<close> of the
form \<open>simp: termpat\<close> where \<open>termpat\<close> is a term pattern (a term which may contain unknowns) specified
in inner syntax. 

Such a search finds named facts where the conclusion is an equation (using either the operator \<open>=\<close>
or the meta equality \<open>\<equiv>\<close>) and the left side unifies with the specified term pattern. It also finds
facts where the conclusion unifies with the term pattern, if the term pattern has type \<open>bool\<close>,
because such facts are equivalent to an equation with \<open>True\<close> (see above). Facts are found
independent of whether they are in the simpset or not.

A found fact may be used by specifying it for the \<open>subst\<close> method or, if not yet in the simpset, by
configuring the \<open>simp\<close> method to use it with the help of \<open>add:\<close> or \<open>only:\<close>.
\<close>

subsubsection "Input Facts for the \<open>simp\<close> Method"

text \<open>
As usual, facts may be input to the \<open>simp\<close> method. Like the empty method (see 
Section~\ref{basic-methods-empty}) it inserts these facts as assumptions into the goal,
before it starts simplification. Since simplification is also applied to the assumptions,
the input facts will be simplified as well.

As a possible effect of this behavior, after simplifying an input fact and the goal conclusion
the results may unify, leading to the situation where the goal is removed by the \<open>assumption\<close>
method (see Section~\ref{basic-methods-assumption}). This is also done by the simplifier, hence in
this way the input fact may contribute to prove the goal.
\<close>

subsubsection "The \<open>simp_all\<close> Method"

text \<open>
The method
@{theory_text[display]
\<open>simp_all\<close>}
behaves like the \<open>simp\<close> method but processes all goals. It inserts input facts to all goals
in the goal state and simplifies them. If it fails for all goals an error is signaled. Otherwise
it simplifies only the goals for which it does not fail. If it achieves to remove all goals 
the proof is finished.

The \<open>simp_all\<close> method can be configured by \<open>add:\<close>, \<open>del:\<close>, \<open>only:\<close>, and \<open>split:\<close> in the same way as 
the \<open>simp\<close> method.

The \<open>simp_all\<close> method is useful, if first a method \<open>m\<close> is applied to the goal which splits 
it into several subgoals which all can be solved by simplification. Then the complete
proof can be written as
@{theory_text[display]
\<open>by m simp_all\<close>}
\<close>

subsubsection "Debugging the Simplifier"

text \<open>
If the simplifier fails, it may be difficult to find out the reason. There are several debugging
techniques which may help.

The content of the simpset can be displayed by the command
@{theory_text[display]
\<open>print_simpset\<close>}
which may be specified in the proof text in modes \<open>proof(prove)\<close> and \<open>proof(state)\<close> and outside 
of proofs. In the interactive editor the result is displayed in the Output panel (see 
Section~\ref{system-jedit-output}).

There is also a simplifier trace which displays the successful rewrite steps. It is activated
by the command
@{theory_text[display]
\<open>declare [[simp_trace_new depth=n]]\<close>}
outside a theorem or definition. The number \<open>n\<close> should be atleast \<open>2\<close>. When the cursor is
positioned on an application of the \<open>simp\<close> method the button ``Show trace'' can be used
in the Simplifier Trace panel to display the trace in a separate window. See the documentation
for more information about how to use the trace.

Another technique is to replace the \<open>simp\<close> method by a sequence of \<open>subst\<close> method applications
and explicitly specify the equations which should have been used. To do this for a structured
proof, replace it by a proof script for the \<open>subst\<close> method applications.
\<close>

subsection "Other Automatic Proof Methods"
text_raw\<open>\label{basic-methods-auto}\<close>

text\<open>
Isabelle provides several other proof methods which internally perform several steps,
like the simplifier.
\<close>

subsubsection "Automatic Methods"

text\<open>
The following list contains automatic methods other than \<open>simp\<close>:
\<^item> \<open>blast\<close> mainly applies logical rules and can be used to solve complex logical formulas.
\<^item> \<open>clarify\<close> is similar but does not split goals and does not follow unsafe paths. It can
be used to show the problem if \<open>blast\<close> fails.
\<^item> \<open>auto\<close> combines logical rule application with simplification. It processes all goals and
leaves those it cannot solve.
\<^item> \<open>clarsimp\<close> combines \<open>clarify\<close> with simplification. It processes only the first goal and
usually does not split goals.
\<^item> \<open>fastforce\<close> uses more techniques than \<open>auto\<close>, but processes only the first goal.
\<^item> \<open>force\<close> uses even more techniques and tries to solve the first goal.
\<^item> \<open>linarith\<close> solves linear arithmetic problems (on integer and real numbers) for the first goal.
It is automatically included by the simplifier.
\<^item> \<open>arith\<close> uses more techniques than \<open>linarith\<close> but may be slower.
\<close>

text\<open>
The methods which do simplification can be configured like the simplifier by adding 
specifications \<open>simp add:\<close>, \<open>simp del:\<close>, \<open>simp only:\<close>, and \<open>split:\<close>. For example, additional
simplification rules can be specified for the \<open>auto\<close> method in the form
@{theory_text[display]
\<open>auto simp add: name\<^sub>1 \<dots> name\<^sub>n\<close>}

For more information about these methods see the Isabelle documentation.
\<close>

subsubsection "Trying Methods"

text\<open>
Instead of manually trying several automatic methods it is possible to specify the command
@{theory_text[display]
\<open>try\<close>}
anywhere in mode \<open>proof(prove)\<close>, i.e. at the beginning of a proof or in a proof script.
It will try many automatic proof methods and describe the result in the Output window.
It may take some time until results are displayed, in particular, if the goal is invalid and
cannot be proved.

If \<^theory_text>\<open>try\<close> finds a proof for one or more goals it displays it as a single (composed) proof method, 
which, by clicking on it can be copied to the cursor position in the text area. The \<^theory_text>\<open>try\<close> command
must be removed manually.

If \<^theory_text>\<open>try\<close> tells you that the goal can be ``directly solved'' by some fact, you can usually prove it
by the \<open>fact\<close> method, but that also means that there is already a fact of the same form and
your theorem is redundant.

It may also be the case that \<^theory_text>\<open>try\<close> finds a counterexample, meaning that the goal is invalid 
and cannot be proved.
\<close>

section "Case Based Proofs"
text_raw\<open>\label{basic-case}\<close>

text \<open>
If during a proof the goal state contains several goals they are often proved sequentially. Although
there are proof methods which process several goals at once (see examples in
Section~\ref{basic-methods-auto}) most methods only process the first goal. In a proof script, when
a method has solved and removed the first goal, the next goal will become the first and will be
processed by the next method application steps. In a structured proof (see
Section~\ref{basic-proof-struct}) it is not so simple. To prove a goal which is in the goal state
its bound variables and assumptions have to be inserted into the local proof context (by \<^theory_text>\<open>fix\<close> and
\<^theory_text>\<open>assume\<close> statements) and its conclusion must be stated by a \<^theory_text>\<open>show\<close> statement and must be proved.
Isabelle provides some support for simplifying these tasks for working on a sequence of goals.
\<close>

subsection "Named Proof Contexts"
text_raw\<open>\label{basic-case-context}\<close>

text \<open>
Isabelle supports some methods which are able to create ``cases'' for goals. A case contains bound
variables and assumptions from a goal and it may contain other context elements, such as names for
assumptions or assumption groups and an abbreviation for the conclusion of a goal. The cases are
named. Using these names a proof context can be populated with all content of a case in a single
step.

Since a case contains context elements it can be seen as a named
context which has been prepared by a method for later use, but has not been ``activated'' yet.
Usually a named context is used to initialize a new nested proof context immediately after its
beginning by inserting the content of the named context into the new context.
\<close>

subsubsection "The \<^theory_text>\<open>case\<close> Statement"

text \<open>
The content of a case may be inserted into the current proof context by the statement
@{theory_text[display]
\<open>case name\<close>}
where \<open>name\<close> is the case name. It mainly has the effect of the sequence
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>k
let ?a\<^sub>1 = t\<^sub>1 and \<dots> ?a\<^sub>m = t\<^sub>m
assume name: "A\<^sub>1" \<dots> "A\<^sub>n"\<close>}
where \<open>x\<^sub>1 \<dots> x\<^sub>k\<close> are the local variables, \<open>?a\<^sub>1, \<dots>, ?a\<^sub>m\<close> are the term abbreviations, and
\<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> are the facts in the named context of the case. The facts are inserted as assumptions
and the set of these assumptions is named using the case name. Moreover, like the \<^theory_text>\<open>assume\<close>
statement, the \<^theory_text>\<open>case\<close> statement makes the assumed facts current.

Instead of using the case name for naming the assumptions an explicit assumption name \<open>aname\<close> may be 
specified:
@{theory_text[display]
\<open>case aname: name\<close>}
If defined in the case, other names for single assumptions or assumption groups may be automatically
introduced.

The local variables \<open>x\<^sub>1 \<dots> x\<^sub>k\<close> are fixed by the \<^theory_text>\<open>case\<close> statement but are hidden, they cannot be
used in the subsequent proof text. If they should be used, explicit names must be specified for
them in the form
@{theory_text[display]
\<open>case (name y\<^sub>1 \<dots> y\<^sub>j)\<close>}
Then the names \<open>y\<^sub>1 \<dots> y\<^sub>j\<close> can be used to reference the fixed variables in the current proof 
context. If fewer names are specified only the first variables are named, if more names are
specified than there are local variables in the case an error is signaled.

When methods create a named context for a goal they usually only define the term abbreviation
\<open>?case\<close> for the conclusion of the goal.
\<close>

subsubsection "Proof Structure with Cases"

text \<open>
The usual proof structure using cases consists of an initial method which creates cases and of a
sequence of nested contexts (see Section~\ref{basic-proof-struct}). At its beginning each context
is initialized by a \<^theory_text>\<open>case\<close> statement naming one of the created cases, at its end it uses a \<^theory_text>\<open>show\<close>
statement to remove the corresponding goal:
@{theory_text[display]
\<open>proof `method`
case name\<^sub>1
\<dots>
show ?case \<proof>
next
case name\<^sub>2
\<dots>
show ?case \<proof>
next
\<dots>
next
case name\<^sub>n
\<dots>
show ?case \<proof>
qed\<close>}
Every \<^theory_text>\<open>show\<close> statement uses the local term abbreviation \<open>?case\<close> to refer to the conclusion of
the corresponding goal.

To find out which cases have been introduced by a method application, the command
@{theory_text[display]
\<open>print_cases\<close>}
can be used at arbitrary places in the following proof to display the cases in the Output panel.

In the interactive editor also the Query panel (see Section~\ref{system-jedit-query}) can be used
to display the cases available at the cursor position by selecting the tab ``Print Context'' and
checking ``cases''.

Also in the interactive editor, when the cursor is positioned on \<^theory_text>\<open>proof `method`\<close> where the method
supports cases, a skeleton of a proof using the specific cases provided by the method is 
displayed in the Output panel. By clicking on it it may be copied into the text area immediately
after the method specification.
\<close>

subsection \<open>The {\sl goal$\_$cases} Method\<close>
text_raw\<open>\label{basic-case-goalcases}\<close>

text\<open>
The simplest method with support for cases is
@{theory_text[display]
\<open>goal_cases\<close>}
Without modifying the goal state it creates a named case for every existing goal. Input facts
are ignored.

For a goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> the created named context contains the local variables
\<open>x\<^sub>1 \<dots> x\<^sub>m\<close>, the facts \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close>, and the term abbreviation \<open>?case\<close> bound to \<open>C\<close>. If the goal
contains variables which are not explicitly bound by \<open>\<And>\<close> these variables are not added to the
context.

The effect is that if no other variables are fixed and no other facts are assumed a statement
\<^theory_text>\<open>show ?case\<close> after the corresponding \<^theory_text>\<open>case\<close> statement will refine the goal and remove it from the
goal state.

The cases are named by numbers starting with \<open>1\<close>. If other names should be used they may be
specified as arguments to the method:
@{theory_text[display]
\<open>goal_cases name\<^sub>1 \<dots> name\<^sub>n\<close>}
If fewer names are specified than goals are present, only for the first \<open>n\<close> goals cases are created.
If more names are specified an error is signaled.

When \<^theory_text>\<open>goal_cases\<close> is used in a composed proof method it can provide cases for the goals produced
by arbitrary other methods:
@{theory_text[display]
\<open>proof (method, goal_cases)\<close>}
provides cases for all goals existing after \<^theory_text>\<open>method\<close> has been applied. If \<^theory_text>\<open>method\<close> does not split
the goal there will be only one case. This can be useful to work with a goal produced by 
\<^theory_text>\<open>method\<close>. In particular, the conclusion of that goal is available as \<open>?case\<close>.

Note that the proof state(s) resulting from \<^theory_text>\<open>goal_cases\<close> are not visible for the reader of the proof.
Therefore it should only be applied if the goals produced by \<^theory_text>\<open>method\<close> are apparent. In a case the
goal conclusion can be shown partially or fully by defining a possibly abbreviated form of it by
@{theory_text[display]
\<open>let "pattern" = ?case\<close>}
where the \<open>pattern\<close> may contain unknowns which abbreviate sub terms of the conclusion.

A better way to use cases is together with a method which combines both: creating new goals in a
simple and expected way, and immediately creating cases only for these goals.
\<close>

subsection "Case Based Reasoning"
text_raw\<open>\label{basic-case-reasoning}\<close>

text\<open>
Case based proofs are especially convenient for implementing case based reasoning.
The technique of ``case based reasoning'' uses a specific kind of forward reasoning steps
(see Section~\ref{basic-proof-proc}). It adds a new fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> to the proof context ``out of the
blue'' without proving it from the existing facts. For the proof to stay correct, this must be done
for ``all possible cases'' of \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>, and the proof must be completed separately for each of them.

In its simplest form this can be done by adding an arbitrary fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and its negation \<open>\<not> F\<^sub>i\<^sub>+\<^sub>1\<close>,
this covers all possibilities, since \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> may be either \<open>True\<close> or \<open>False\<close>.

Consider the derivation rule \<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> named \<open>example1\<close> in
Section~\ref{basic-theory-prop}. To prove it using case based reasoning the
additional assumption that \<open>n\<close> is zero can be used. Then there are the two cases 
\<open>n = 0\<close> and \<open>n \<noteq> 0\<close> and clearly these cover all possibilities. Using the first case as assumption 
implies that \<open>n*x\<close> and \<open>n*c\<close> are both zero and thus \<open>n*x = n*c\<close>. Using the second case as assumption
together with the original assumption implies that \<open>n*x < n*c\<close>. Together the conclusion \<open>n*x \<le> n*c\<close>
follows.

Since the proof must be completed separately for every such case, a separate goal is required for
each of them. This cannot be achieved by statements, the old goal must be replaced by several new
goals which is only possible by applying a proof method.

More specific, if \<open>Q\<^sub>1 \<dots> Q\<^sub>k\<close> are propositions for the different cases which together cover all
possibilities, a goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> must be replaced by the \<open>k\<close> goals
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; Q\<^sub>1\<rbrakk> \<Longrightarrow> C
\<dots>
\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; Q\<^sub>k\<rbrakk> \<Longrightarrow> C\<close>}
where every goal has one of the propositions \<open>Q\<^sub>i\<close> as additional assumption.

Note that this technique extends the proof procedure described in Section~\ref{basic-proof-proc}.
There a proof consisted of a single tree of facts which started at the assumptions and all branches
joined to finally reach the conclusion. With case based reasoning at any position the remaining
tree may be split into several ``copies'' with additional assumptions which then must all be
completed separately.
\<close>

subsubsection "Case Rules"

text\<open>
This splitting of a goal into goals for different cases can be done by applying a single meta rule
of the specific form
@{text[display]
\<open>\<lbrakk>Q\<^sub>1 \<Longrightarrow> ?P; \<dots>; Q\<^sub>k \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
where \<open>Q\<^sub>1 \<dots> Q\<^sub>k\<close> are all cases of the additional assumption. Such rules are called ``case rules''.

When this case rule is applied to the goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> as described in 
Section~\ref{basic-methods-rule}, it unifies \<open>?P\<close> with the conclusion \<open>C\<close> and replaces the goal
in the way described above.

A case rule is only valid, if the \<open>Q\<^sub>i\<close> together cover all possibilities, i.e., if 
\<open>Q\<^sub>1 \<or> \<dots> \<or> Q\<^sub>k\<close> holds. If this has been proved the case rule is available as a fact which can be
applied. Since the whole conclusion is the single unknown \<open>?P\<close> it unifies with every proposition
used as conclusion in a goal, hence a case rule can always be applied to arbitrary goals. It 
depends on the \<open>Q\<^sub>i\<close> whether splitting a specific goal with the case rule is useful for proving
the goal.

A case rule for testing a natural number for being zero would be
@{text[display]
\<open>\<lbrakk>?n = 0 \<Longrightarrow> ?P; ?n \<noteq> 0 \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
It contains the number to be tested as the unknown \<open>?n\<close>, so that an arbitrary term can be substituted
for it. This is not automatically done by unifying \<open>?P\<close> with the goal's conclusion, thus the rule 
must be ``prepared'' for 
application to a specific goal. To apply it to the goal \<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> in the intended
way the unknown \<open>?n\<close> must be substituted by the variable \<open>n\<close> from the goal conclusion. If the 
prepared rule is then applied to the goal it splits it into the goals
@{text[display]
\<open>\<lbrakk>(x::nat) < c; n = 0\<rbrakk> \<Longrightarrow> n*x \<le> n*c
\<lbrakk>(x::nat) < c; n \<noteq> 0\<rbrakk> \<Longrightarrow> n*x \<le> n*c\<close>}
which can now be proved separately.

Actually, the much more general case rule 
@{text[display]
\<open>\<lbrakk>?Q \<Longrightarrow> ?P; \<not> ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
is used for this purpose. Here the unknown \<open>?Q\<close> represents the complete proposition to be used as
additional assumption, therefore the rule can be used for arbitrary propositions. By substituting 
the term \<open>n = 0\<close> for \<open>?Q\<close> the rule is prepared to be applied in the same way as above.

Case rules may even be more general than shown above. Instead of a single proposition \<open>Q\<^sub>i\<close> every 
case may have locally bound variables and an arbitrary number of assumptions, resulting in a
meta rule of the form
@{text[display]
\<open>\<lbrakk>P\<^sub>1; \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> ?P\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>1\<dots>x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1;\<dots>;Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> ?P\<close>}
That means, the \<open>P\<^sub>i\<close> may be arbitrary rules but they must all have as conclusion the unknown \<open>?P\<close>
which is also the conclusion of the overall case rule. When such a case rule is applied to a goal
it splits the goal into \<open>k\<close> cases and adds the variables \<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i\<close> and the assumptions
\<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>q\<^sub>i\<close> to the \<open>i\<close>th case.

 Note that the goal which must be proved for an \<^theory_text>\<open>obtain\<close> statement (see
Section~\ref{basic-proof-obtain}) has the form of a case rule with only one case of the form
\<open>\<And>x\<^sub>1 \<dots> x\<^sub>m. prop \<Longrightarrow> P\<close>. Thus a proof for this goal shows that \<open>prop\<close> covers all cases, i.e., it
is redundant.

Remember that to write your own case rule you have to specify a theorem which uses variables in
place of the unknowns, such as
@{theory_text[display]
\<open>theorem mycaserule: "\<lbrakk>n = 0 \<Longrightarrow> P; n \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" \<proof>\<close>}
which will be converted to unknowns upon turning the proposition to a fact after the proof.
\<close>

subsubsection "The \<^theory_text>\<open>cases\<close> Method"

text\<open>
Case based reasoning can be performed in a structured proof using the method \<^theory_text>\<open>cases\<close> in the form
@{theory_text[display]
\<open>cases "term" rule: name\<close>}
where \<open>name\<close> is the name of a valid case rule. The method prepares the rule by substituting the
specified \<open>term\<close> for the first unknown in the assumptions, and applies the rule to the first goal
in the goal state.

Additionally, the method creates a named context for every goal resulting from the rule
application. The context contains (only) the variables and assumptions specified in the corresponding
case in the case rule. For the most general form depicted above the context for the \<open>i\<close>th case 
contains the variables \<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i\<close> and the assumptions \<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>q\<^sub>i\<close>. No term abbreviation
\<open>?case\<close> is defined, because the conclusion of every new goal is the same as that of the original 
goal, thus the existing abbreviation \<open>?thesis\<close> can be used instead.

The names used for the contexts created by the \<^theory_text>\<open>cases\<close> method can be specified by attributing
the case rule. Therefore, predefined case rules often create cases with names which are easy to
understand by a proof writer.

In Isabelle HOL (see Section~\ref{holtypes}) the rule \<open>\<lbrakk>?Q \<Longrightarrow> ?P; \<not> ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close> is available
under the name \<open>case_split\<close>. It is attributed to use the case names \<open>True\<close> and \<open>False\<close>. Note that
these are names, not the constants for the values of type \<open>bool\<close>. 

Together, a structured proof for the goal
\<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> with case splitting may have the form
@{theory_text[display]
\<open>proof (cases "n = 0" rule: case_split)
case True
\<dots>
show ?thesis \<proof>
next
case False
\<dots>
show ?thesis \<proof>
qed\<close>}
The \<^theory_text>\<open>cases\<close> method adds the assumptions \<open>n=0\<close> and \<open>n\<noteq>0\<close> respectively to the goals of the cases, 
the \<^theory_text>\<open>case\<close> statements add them as assumed facts to the local context, so that they are part of the 
rule exported by the \<^theory_text>\<open>show\<close> statement and match the assumption in the corresponding goal.

Note that the \<^theory_text>\<open>case\<close> statement adds only the assumptions originating from the case rule. The other
assumptions in the original goal (here \<open>x < c\<close>) must be added to the context in the usual ways (see 
Section~\ref{basic-proof-assume}) if needed for the proof.

Often a case rule has only one unknown in the case assumptions. If there are more, several terms
may be specified in the \<^theory_text>\<open>cases\<close> method for preparing the rule. If less terms are specified than
there are unknowns in the case assumptions the resulting goals will contain unbound unknowns which
must be instantiated in the rest of the proof (e.g., by method \<^theory_text>\<open>drule\<close>). If more terms are
specified an error is signaled.

The \<^theory_text>\<open>cases\<close> method treats input facts like the empty method (see Section~\ref{basic-methods-empty})
by inserting them as assumptions into the original goal before splitting it. Therefore it can be
used both in proof scripts, where facts are stored as rule assumptions in the goal state, and in
structured proofs where facts are stored in the proof context and are input to the initial methods
of subproofs.

However, if the \<^theory_text>\<open>cases\<close> method is specified in the form
@{theory_text[display]
\<open>cases "term"\<close>}
without explicitly naming a case rule and the first input fact has the form of a case rule, it is
used as case rule to split the goal and create the named cases. Therefore in a proof the example
goal can be proved as local fact by inputting (see Section~\ref{basic-proof-this}) the case rule in
the form
@{theory_text[display]
\<open>from case_split
have "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
proof (cases "n = 0")
\<dots>\<close>}

Like the \<^theory_text>\<open>rule\<close> method (see Section~\ref{basic-methods-rule}) the \<^theory_text>\<open>cases\<close> method supports
automatic rule selection for the case rule, if no case rule is specified or input to the method.
Normally the rule is selected according to the type of the specified \<open>term\<close>. In Isabelle HOL (see 
Section~\ref{holbasic}) most types have an associated case rule. Only case rules with a single 
unknown in the case assumptions can be automatically selected in this way.

The rule \<open>case_split\<close> is associated with type \<open>bool\<close>. Therefore the example sub proof shown above
also works without inputting the method to the \<^theory_text>\<open>have\<close> statement, because then it is selected
automatically because the term \<open>n = 0\<close> has type \<open>bool\<close>.

The proof writer may not know the case names specified by an automatically selected case rule.
However, they can be determined using the command \<^theory_text>\<open>print_cases\<close> or from the proof skeleton which
is displayed in the interactive editor when the cursor is positioned on the \<^theory_text>\<open>cases\<close> method (see
Section~\ref{basic-case-context}).
\<close>

subsubsection "Alternative Syntax for Case Rules"

text\<open>
A case rule as described above always uses an unknown \<open>?P\<close> (or with any other name) as conclusion
and as conclusion in all assumptions. It is used technically to preserve the original conclusion
when a goal is split by applying the rule. Therefore Isabelle supports an alternative syntax for
specifying case rules as theorems which omits the variable for this unknown and specifies only the
information which becomes the content of the named cases.

In a theorem in specified in structured form using \<^theory_text>\<open>shows\<close> (see Section~\ref{basic-theory-theorem})
the part of the form \<^theory_text>\<open>shows "C"\<close> may alternatively be specified in the form
@{theory_text[display]
\<open>obtains C\<^sub>1 | \<dots> | C\<^sub>k\<close>}
where every case \<open>C\<^sub>i\<close> has the form
@{theory_text[display]
\<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i where "Q\<^sub>i\<^sub>1" \<dots> "Q\<^sub>i\<^sub>q\<^sub>i"\<close>}
As usual, the variables \<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i\<close> and the propositions \<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>q\<^sub>i\<close> may be grouped by \<open>and\<close>, for
every variable group a type may be specified and the proposition groups may be named. The keywords
and the \<open>|\<close> separators belong to the outer syntax, the propositions must be individually quoted.

This form is mainly equivalent to
@{theory_text[display]
\<open>shows "\<lbrakk>P\<^sub>1;  \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> thesis"\<close>}
where every \<open>P\<^sub>i\<close> is a rule
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>1\<dots>x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1;\<dots>;Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> thesis\<close>}
which is exactly the general form of a case rule stated by the \<^theory_text>\<open>shows\<close> clause, using, after proof,
the unknown \<open>?thesis\<close> for all conclusions.

For its own proof the \<^theory_text>\<open>obtains\<close> form creates the same goal as the \<^theory_text>\<open>shows\<close> form, but additionally
it adds all \<open>P\<^sub>i\<close> as assumed facts to the outermost proof context and names this set \<open>that\<close>.

When the theorem is applied as case rule by the \<^theory_text>\<open>cases\<close> method the named context created for case
\<open>C\<^sub>i\<close> is simply named \<open>i\<close>. An explicit name may be specified for it by using the extended form
@{theory_text[display]
\<open>(name\<^sub>i) x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i where "Q\<^sub>i\<^sub>1" \<dots> "Q\<^sub>i\<^sub>q\<^sub>i"\<close>}
For its own proof the \<^theory_text>\<open>obtains\<close> form uses \<open>name\<^sub>i\<close>, if present, as additional name for \<open>P\<^sub>i\<close> in its
proof context.

If a case \<open>C\<^sub>i\<close> has no bound variables it has simply the form
@{theory_text[display]
\<open>"Q\<^sub>i\<^sub>1" \<dots> "Q\<^sub>i\<^sub>q\<^sub>i"\<close>}
which omits the keyword \<^theory_text>\<open>where\<close>, also if an explicit name is specified.

As an example, the rule \<open>case_split\<close> may be defined and proved as
@{theory_text[display]
\<open>theorem case_split:
  obtains (True) "Q" | (False) "\<not> Q"
  by blast\<close>}
using the case names \<open>True\<close> and \<open>False\<close>, as described above, and using the \<^theory_text>\<open>blast\<close> method (see
Section~\ref{basic-methods-auto}) for the proof.

There is also a statement for stating a case rule on the fly in a structured proof. It has the form
@{theory_text[display]
\<open>consider C\<^sub>1 | \<dots> | C\<^sub>k \<proof>\<close>}
where the cases \<open>C\<^sub>i\<close> are as above. It is mainly equivalent to the statement
@{theory_text[display]
\<open>have "\<lbrakk>P\<^sub>1;  \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> thesis" \<proof>\<close>}
with \<open>P\<^sub>i\<close> as above and is thus also a goal statement.

However, it is not possible to introduce additional unknowns in the \<open>P\<^sub>i\<close> in a \<^theory_text>\<open>consider\<close> statement.
All variables occurring free in the \<open>P\<^sub>i\<close> are assumed to be bound in the context and are not
converted to unknowns at the end of the statement. Therefore the statement cannot be used to
define general case rules like \<open>case_split\<close> which contains the additional unknown \<open>?Q\<close>. It can only
be used to state that specific propositions cover all (remaining) possibilities in the local proof
context. They need not cover all globally possible cases, if some cases have already been excluded
using locally assumed or proved facts, only the remaining possibilities need to be covered.

Since case rules can be input as fact to a proof by case based reasoning, fact chaining can be used
to immediately apply a locally defined case rule in a subsequent subproof. This yields the pattern
@{theory_text[display]
\<open>consider C\<^sub>1 | \<dots> | C\<^sub>k \<proof>
then have "prop" 
proof cases
  case 1 \<dots> show ?thesis \<proof>
next
\<dots>
  case k \<dots> show ?thesis \<proof>
qed\<close>}
using the default case names. The first \<open>\<proof>\<close> proves that the cases cover all local possibilities,
the other \<open>\<proof>\<close>s prove the stated proposition, each using one of the cases \<open>C\<^sub>i\<close> as additional
assumption. The \<^theory_text>\<open>cases\<close> method is always applied without arguments, since there are no additional
unknowns in the \<open>C\<^sub>i\<close> which can be instantiated.

If the example goal \<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> should be stated for locally fixed variables,
the cases \<open>n=0\<close> and \<open>n\<noteq>0\<close> can be proved to cover all possibilities and then used as cases by the
statements
@{theory_text[display]
\<open>fix x c n::nat
consider (Zero) "n = 0" | (Notzero) "n \<noteq> 0" by blast
then have "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
proof cases
  case Zero \<dots> show ?thesis \<proof>
next
  case Notzero \<dots> show ?thesis \<proof>
qed\<close>}
\<close>

subsection "Elimination"
text_raw\<open>\label{basic-case-elim}\<close>

text\<open>
The proof technique of ``(generalized) elimination'' can be seen as a combination of applying a
destruction rule (see Section~\ref{basic-methods-forward}) and an optional case split. It removes an
assumption with a function application from a goal and splits the rest into cases with additional
assumptions.
\<close>

subsubsection "The Method \<open>erule\<close>"

text\<open>
Like destruction rule application and case splitting such a step can be implemented by applying a
rule in a specific way to a goal. This is done by the method
@{theory_text[display]
\<open>erule name\<close>}
where \<open>name\<close> is the name of a valid rule. The method only affects the first goal. If that goal
has the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and the rule referred by \<open>name\<close> has the form \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m\<rbrakk> \<Longrightarrow> RC\<close> 
the method first unifies the first assumption \<open>RA\<^sub>1\<close> in the rule with the first assumption \<open>A\<^sub>k\<close> of
the \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> which can be unified with \<open>RA\<^sub>1\<close> \<^emph>\<open>and\<close> it unifies the rule conclusion \<open>RC\<close> with the
goal conclusion \<open>C\<close>. That yields the specialized rule \<open>\<lbrakk>RA\<^sub>1';\<dots>;RA\<^sub>m'\<rbrakk> \<Longrightarrow> RC'\<close> where \<open>RA\<^sub>1'\<close> is
syntactically equal to \<open>A\<^sub>k\<close>, \<open>RC'\<close> is syntactically equal to \<open>C\<close> and every \<open>RA\<^sub>j'\<close> with \<open>j > 1\<close>
results from \<open>RA\<^sub>j\<close> by substituting unknowns by the same terms as in \<open>RA\<^sub>1'\<close> and \<open>RC'\<close>. If the goal
does not contain unknowns (which is the normal case), \<open>A\<^sub>k\<close> and \<open>C\<close> are not modified by the
unifications. If no \<open>A\<^sub>i\<close> unifies with \<open>RA\<^sub>1\<close> or \<open>C\<close> does not unify with \<open>RC\<close> the method cannot be
executed on the goal state and an error is signaled. Otherwise the method replaces the goal by the
\<open>m-1\<close> new goals \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>j'\<close> for  \<open>j > 1\<close>.

If the rule has the form \<open>RA \<Longrightarrow> RC\<close> with only one assumption a successful application with \<^theory_text>\<open>erule\<close>
removes the goal from the goal state. If the rule is a formula \<open>RC\<close> without any
assumptions the method cannot be applied to the goal state and an error is signaled. If an
assumption \<open>RA\<^sub>j\<close> is a rule with own assumptions, these assumptions are appended to the assumptions
in the resulting goal, as described for the \<^theory_text>\<open>rule\<close> method in Section~\ref{basic-methods-rule}.

As for  rules applied by \<^theory_text>\<open>frule\<close> or \<^theory_text>\<open>drule\<close> (see Section~\ref{basic-methods-forward}) the first
assumption \<open>RA\<^sub>1\<close> in the rule is called the ``major premise'' in this context.

The method \<^theory_text>\<open>erule\<close> does not support input facts.
\<close>

subsubsection "Elimination Rules"

text\<open>
An elimination rule is a generalized combination of a destruction rule and a case rule. It has the
specific form
@{text[display]
\<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P\<close>}
where the first assumption contains the application of a specific function \<open>f\<close> (perhaps written
using an operator name) which may only occur in different form in the other assumptions. The
conclusion is a single unknown which must not occur in the first assumption and may only occur as
conclusion in other assumption (like in an assumption in a case rule).

When an elimination rule is applied to a goal by the \<^theory_text>\<open>erule\<close> method, it removes (``eliminates'')
the function application from an assumption in the goal or it replaces it by a different form, so
that it may be removed in several steps. Depending on the form of the other
assumptions the resulting goals have either the same conclusion as the original goal or are
unrelated to it. Therefore such an application of an elimination rule can be seen as a forward
reasoning step, possibly with case splitting.

 Since the order of the assumptions after the major premise is irrelevant for the rule application
the general form of an elimination rule can be considered to be
@{theory_text[display]
\<open>theorem "\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m; P\<^sub>1; \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> P" \<proof>\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>1\<dots>x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1;\<dots>;Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> P\<close>}
and the variable \<open>P\<close> does not occur in the \<open>RA\<^sub>1 \<dots> RA\<^sub>m\<close>.

As an example consider the elimination rule specified as
@{theory_text[display]
\<open>theorem elimexmp: "\<lbrakk>(x::nat) \<le> c; x < c \<Longrightarrow> P; x = c \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"\<close>}
It replaces an assumption \<open>x \<le> c\<close> by two cases with assumptions \<open>x < c\<close> and \<open>x = c\<close>. If applied to
the goal \<open>(x::nat) \<le> 5 \<Longrightarrow> C\<close> by
@{theory_text[display]
\<open>apply (erule elimexmp)\<close>}
it replaces the goal by the two goals
@{text[display]
\<open>x < 5 \<Longrightarrow> C
x = 5 \<Longrightarrow> C\<close>}

Analogous to the \<open>intro\<close> set for introduction rules there is an internal fact set \<open>elim\<close> for
elimination rules. It is used by some automatic methods, however, it is not used for automatically
selecting rules for \<open>erule\<close>.

If the cursor in the text area is positioned in a proof, elimination rules applicable to the first
goal in the goal state of the enclosing proof can be searched using the keyword \<open>elim\<close> as criterion
for a search by \<^theory_text>\<open>find_theorems\<close> or in the Query panel, as described in
Section~\ref{basic-theory-theorem}. It finds all named facts which can be applied by the \<open>erule\<close>
method to the first goal, i.e., the major premise unifies with a goal assumption and the conclusions
unify as well.

Elimination rule application can be iterated by the method
@{theory_text[display]
\<open>elim name\<^sub>1 \<dots> name\<^sub>n\<close>}
where \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> refer to valid rules. It iterates applying rules by \<^theory_text>\<open>erule\<close> from the given
set to a goal in the goal state as long as this is possible. It is intended to be used with
elimination rules. Then it automatically eliminates functions from assumptions in the goals as much
as possible with the given rules. Note that the method does not use the \<open>elim\<close> set.

Every destruction rule \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> can be re-stated as the elimination rule
\<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>n;C\<Longrightarrow>?P\<rbrakk> \<Longrightarrow> ?P\<close>. If that is applied by \<^theory_text>\<open>erule\<close> it has the same effect as if the
original rule is applied by method \<^theory_text>\<open>drule\<close>.
\<close>

subsubsection "Alternative Syntax for Elimination Rules"

text\<open>
The alternative syntax available for case rules described in Section~\ref{basic-case-reasoning} can
be extended for elimination rules.  An elimination rule
@{theory_text[display]
\<open>theorem "\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m; P\<^sub>1; \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> P" \<proof>\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>1\<dots>x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1;\<dots>;Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> P\<close>}
 can be specified using the alternative syntax
@{theory_text[display]
\<open>theorem
assumes "RA\<^sub>1" \<dots> "RA\<^sub>m"
obtains C\<^sub>1 | \<dots> | C\<^sub>k
\<proof>\<close>}
where every \<open>C\<^sub>i\<close> is
@{theory_text[display]
\<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i where "Q\<^sub>i\<^sub>1" \<dots> "Q\<^sub>i\<^sub>q\<^sub>i"\<close>}
The major premise and possibly other additional assumptions are specified using \<^theory_text>\<open>assumes\<close>, then
the assumptions for the cases are specified using \<^theory_text>\<open>obtains\<close>. As usual, the set \<open>RA\<^sub>1, \<dots>, RA\<^sub>m\<close> is
automatically named \<open>assms\<close> and the set of the \<open>P\<^sub>i\<close> is automatically named \<open>that\<close> in the outermost
proof context of the theorem, additional names may be specified explicitly.

The example rule \<open>elimexmp\<close> from the previous section can alternatively be specified as
@{theory_text[display]
\<open>theorem 
assumes "(x::nat) \<le> c"
obtains "x < c" | "x = c"
\<proof>\<close>}\<close>

subsubsection "Elimination in Structured Proofs"

text\<open>
The method \<open>erule\<close> is intended to be used in proof scripts, therefore it does not process input
facts and does not create named cases. In structured proofs elimination can be done using the
\<open>cases\<close> method.

The \<open>cases\<close> method applies a rule by elimination, if the rule is attributed by \<open>[consumes 1]\<close>. This
means the rule will ``consume'' one assumption by unifying it with its major premise and removing
it. A rule may be attributed upon definition in the form
@{theory_text[display]
\<open>theorem [consumes 1]: "prop" \<proof>\<close>}
or it may be attributed on the fly when it is applied by the \<open>cases\<close> method:
@{theory_text[display]
\<open>cases "term" rule: name[consumes 1]\<close>}

Since the \<open>cases\<close> method is intended to be used in structured proofs where facts are stored in the
proof context it does not unify the rule's major premise with an assumption in the goal, it
unifies it with the first input fact (possibly after the rule itself if not specified as method
argument).

Now the rule \<open>elimexmp\<close> from the previous sections can be defined in the form
@{theory_text[display]
\<open>theorem elimexmp[consumes 1]:
  assumes "(x::nat) \<le> c"
  obtains (lower) "x < c" | (equal) "x = c"
  \<proof>\<close>}
naming the cases by \<open>lower\<close> and \<open>equal\<close>. Then an example for an application in a structured proof
with cases is
@{theory_text[display]
\<open>theorem "C" if "(x::nat) \<le> 5"
  using that 
proof (cases rule: elimexmp)
  case lower \<dots> show ?thesis \<proof>
next
  case equal \<dots> show ?thesis \<proof>
qed
\<close>}
Note the use of the structured theorem form which puts the assumption \<open>(x::nat) \<le> 5\<close> into the proof
context and names it \<open>that\<close> so that it can be input by \<^theory_text>\<open>using that\<close> into the structured proof
and into its initial method \<open>cases\<close> which consumes it.
\<close>

subsection "Induction"
text_raw\<open>\label{basic-case-induction}\<close>

text\<open>
With induction a goal is proved by processing ``all possible cases'' for certain values which
occur in it. If the goal can be proved for all these cases and the cases cover all
possibilities, the goal holds generally. A specific
technique is to assume the goal for some values and then prove it for other values. In this
way it is possible to cover infinite value sets by proofs for only a finite number of values and 
steps from values to other values.

Perhaps the best known example of induction is a proposition which is proved for the natural number
\<open>0\<close> and the step from a number \<open>n\<close> to its successor \<open>n+1\<close>, which together covers the whole infinite
set of natural numbers. 

As a (trivial) example consider the proposition \<open>0\<le>n\<close>. To prove that it is valid for all natural numbers
\<open>n\<close> we prove the ``base case'' where \<open>n\<close> is \<open>0\<close>, which is true because \<open>0\<le>0\<close>. Then we prove the
``induction step'', by assuming that \<open>0\<le>n\<close> (the ``induction hypothesis'') and proving that \<open>0\<le>n+1\<close> 
follows, which is true because addition increases the value.
\<close>

subsubsection "Induction Rules"

text\<open>
Like for case based reasoning (see Section~\ref{basic-case-reasoning}) a goal is split into these
cases by applying a meta rule. For induction the splitting can be done by a meta rule of the form
@{text[display]
\<open>\<lbrakk>P\<^sub>1 ; ...; P\<^sub>n \<rbrakk> \<Longrightarrow> ?P ?a\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form
@{text[display]
\<open>\<And>y\<^sub>i\<^sub>1 \<dots> y\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> ?P term\<^sub>i\<close>}
where the assumptions \<open>Q\<^sub>i\<^sub>j\<close> may contain the unknown \<open>?P\<close> but no other unknowns, in particular not
\<open>?a\<close>. A rule for a base case usually has no bound variables \<open>y\<^sub>i\<^sub>j\<close> and no assumptions
\<open>Q\<^sub>i\<^sub>j\<close>, at least the \<open>Q\<^sub>i\<^sub>j\<close> do not contain \<open>?P\<close>. The remaining rules mostly have only a single
assumption \<open>Q\<^sub>i\<^sub>j\<close> which contains \<open>?P\<close>.

Note that the unknown \<open>?a\<close> only occurs once in the conclusion of the meta rule and nowhere else. Like
the case rules induction rules must be ``prepared'' for use, this is done by replacing \<open>?a\<close>
by a specific term \<open>term\<close>. This is the term for which all possible cases shall be processed
in the goal. It must have the same type as all \<open>term\<^sub>i\<close> in the \<open>P\<^sub>i\<close>.

Usually, ``all possible cases'' means all values of the type of \<open>term\<close>, then \<open>term\<close> consists of a 
single variable which may adopt any values of its type. There are also other forms of induction where
more complex terms are used, but they are not presented in this introduction, refer to other 
Isabelle documentations for them. In the following the unknown \<open>?a\<close> will always be replaced by a
variable \<open>x\<close>.

When a prepared induction rule is applied to a goal \<open>C\<close> without bound variables and assumptions as 
described in Section~\ref{basic-methods-rule}, it unifies \<open>?P x\<close> with the conclusion \<open>C\<close>. This has
the effect of abstracting \<open>C\<close> to a (boolean) function \<open>PC\<close> by identifying all places where \<open>x\<close>
occurs in \<open>C\<close> and replacing it by the function argument. The function \<open>PC\<close> is then bound to the 
unknown \<open>?P\<close>, so that applying \<open>?P\<close> to the argument \<open>x\<close> again yields \<open>C\<close>. The function
\<open>PC\<close> is the property to be proved for all possible argument values. Therefore the cases of the proof
can be described by applying \<open>?P\<close> to the terms \<open>term\<^sub>i\<close> for the specific values in the rules \<open>P\<^sub>i\<close> for 
the cases. 

The application of the prepared rule results in the \<open>n\<close> goals
@{text[display]
\<open>\<And> y\<^sub>1\<^sub>1 \<dots> y\<^sub>1\<^sub>p\<^sub>1. \<lbrakk>Q\<^sub>1\<^sub>1; \<dots>; Q\<^sub>1\<^sub>q\<^sub>1\<rbrakk> \<Longrightarrow> PC term\<^sub>1
\<dots>
\<And> y\<^sub>n\<^sub>1 \<dots> y\<^sub>n\<^sub>p\<^sub>n. \<lbrakk>Q\<^sub>n\<^sub>1; \<dots>; Q\<^sub>n\<^sub>q\<^sub>n\<rbrakk> \<Longrightarrow> PC term\<^sub>n\<close>}

The induction rule is only valid if the terms \<open>term\<^sub>i\<close> cover all possible values of their associated
type. If this has been proved the induction rule is available as a fact which can be applied.
After preparing the induction rule for application, its conclusion \<open>?P x\<close> 
matches all propositions which contain the variable \<open>x\<close> in one or more copies. It depends 
on the \<open>P\<^sub>i\<close> in the rule whether splitting a specific goal with the induction rule is useful for 
proving the goal.

The real power of induction rules emerges, when a \<open>Q\<^sub>i\<^sub>j\<close> contains the unknown \<open>?P\<close>. Due to the
type associated with \<open>?P\<close> it must be applied to an argument \<open>term\<^sub>i\<^sub>j\<close> of the same type as \<open>x\<close> and
the \<open>term\<^sub>i\<close>. Then the goal resulting from \<open>P\<^sub>i\<close> states the property that if \<open>Q\<^sub>i\<^sub>j\<close> holds when
specialized to \<open>PC term\<^sub>i\<^sub>j\<close>, \<open>PC\<close> holds for \<open>term\<^sub>i\<close> (an ``induction step''). Thus, for covering the
possible values of \<open>x\<close>, the step from \<open>term\<^sub>i\<^sub>j\<close> to \<open>term\<^sub>i\<close> can be repeated arbitrarily often which
allows to cover some types with infinite value sets.

An induction rule for the natural numbers is
@{text[display]
\<open>\<lbrakk>?P 0; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}
\<open>P\<^sub>1\<close> is the base case, it has no variables and assumptions and only consists of the conclusion
\<open>?P 0\<close>. \<open>P\<^sub>2\<close> binds the variable \<open>y\<close>, has one assumption \<open>?P y\<close> and the conclusion \<open>?P (y+1)\<close>.
\<open>P\<^sub>1\<close> covers the value \<open>0\<close>, \<open>P\<^sub>2\<close> covers the step from a value \<open>y\<close> to its successor \<open>y+1\<close>, together
they cover all possible values of type \<open>nat\<close>.

To apply the rule to the goal \<open>0\<le>n\<close>, it must be prepared by substituting the variable \<open>n\<close> for the 
unknown \<open>?a\<close>. Then the rule conclusion \<open>?P n\<close> is unified with the goal which abstracts the
goal to the boolean function \<open>PC = (\<lambda>i. 0\<le>i)\<close> and substitutes it for all occurrences of \<open>?P\<close>. 
This results in the rule instance 
\<open>\<lbrakk>(\<lambda>i. 0\<le>i) 0; \<And>y. (\<lambda>i. 0\<le>i) y \<Longrightarrow> (\<lambda>i. 0\<le>i) (y+1)\<rbrakk> \<Longrightarrow> (\<lambda>i. 0\<le>i) n\<close>.
By substituting the arguments in the function applications its assumption part yields the two goals
@{text[display]
\<open>0\<le>0
\<And>y. 0\<le>y \<Longrightarrow> 0\<le>(y+1)\<close>}
which correspond to the base case and induction step as described above.

Induction rules may even be more general than shown above. Instead of applying \<open>?P\<close> to a single 
argument it may have several arguments and the conclusion becomes \<open>?P ?a\<^sub>1 \<dots> ?a\<^sub>r\<close>. Also in the
\<open>P\<^sub>i\<close> every occurrence of \<open>?P\<close> then has \<open>r\<close> terms as arguments. Such an induction rule is valid if it
covers all possible cases for all combinations of the \<open>r\<close> argument values. Finally, in addition
to the assumptions \<open>P\<^sub>i\<close> an induction rule may have assumptions about the argument \<open>?a\<close>
or the arguments \<open>?a\<^sub>1 \<dots> ?a\<^sub>r\<close>.

Note, however, that there is no alternative syntax for induction rules, such as the \<^theory_text>\<open>obtains\<close> form
for case rules.
\<close>

subsubsection "The \<^theory_text>\<open>induction\<close> Method"

text\<open>
Induction can be performed in a structured proof using the method \<^theory_text>\<open>induction\<close> in the form
@{theory_text[display]
\<open>induction x rule: name\<close>}
where \<open>name\<close> is the name of a valid induction rule. The method prepares the rule by substituting the
specified variable \<open>x\<close> for the unknown \<open>?a\<close> and applies the rule to the first goal in the
goal state. 

Additionally, the method creates a named context for every goal resulting from the rule
application. The context contains the variables and assumptions specified in the corresponding
case in the induction rule. For the general form depicted above the context for the \<open>i\<close>th case 
contains the variables \<open>y\<^sub>i\<^sub>1 \<dots> y\<^sub>i\<^sub>p\<^sub>i\<close> and the assumptions \<open>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<close>. 
The term abbreviation \<open>?case\<close> is defined for the case conclusion \<open>PC term\<^sub>i\<close> which is to
be proved for the case.

The \<^theory_text>\<open>induction\<close> method treats input facts like the empty method (see Section~\ref{basic-methods-empty})
and the \<^theory_text>\<open>cases\<close> method (see Section~\ref{basic-case-reasoning}) by inserting them as assumptions 
into the original goal before splitting it.

Also like the \<^theory_text>\<open>cases\<close> method the \<^theory_text>\<open>induction\<close> method supports
automatic rule selection for the induction rule. This is only possible if \<open>?P\<close> is applied to a single
argument, which means that only one variable is specified in the method:
@{theory_text[display]
\<open>induction x\<close>}
Then the rule is selected according to the type of \<open>x\<close>. In Isabelle HOL (see 
Section~\ref{holbasic}) most types have an associated induction rule. 

The rule \<open>\<lbrakk>?P True; ?P False\<rbrakk> \<Longrightarrow> ?P ?a\<close> is associated with type \<open>bool\<close>. Therefore induction can be 
applied to every proposition which contains a variable of type \<open>bool\<close>, such as the goal \<open>b \<and> False = False\<close>.
Applying the method
@{theory_text[display]
\<open>induction b\<close>}
will split the goal into the goals
@{text[display]
\<open>False \<and> False = False
True \<and> False = False\<close>}
which cover all possible cases for \<open>b\<close>. Here, the type has only two values, therefore induction is 
not really needed.

Like for the \<^theory_text>\<open>cases\<close> method (see Section~\ref{basic-case-reasoning}) the names used for the contexts 
created by the \<^theory_text>\<open>induction\<close> method can be specified by attributing the induction rule. They can be 
determined from the proof skeleton which is displayed in the interactive editor
when the cursor is positioned on the \<^theory_text>\<open>induction\<close> method (see Section~\ref{basic-case-context}).

If the induction rule \<open>\<lbrakk>?P 0; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P ?a\<close> for the natural numbers has been
proved and named \<open>induct_nat\<close> with case names \<open>Start\<close> and \<open>Step\<close>, a structured proof for the goal 
\<open>0\<le>n\<close> may have the form
@{theory_text[display]
\<open>proof (induction n rule: induct_nat)
case Start
\<dots>
show ?case \<proof>
next
case Step
\<dots>
show ?case \<proof>
qed\<close>}
The \<^theory_text>\<open>induction\<close> method creates the named contexts \<open>Start\<close> and \<open>Step\<close>. The former has no local 
variables and assumptions and binds \<open>?case\<close> to the proposition \<open>0\<le>0\<close>, the latter has the local
variable \<open>y\<close>, the assumption \<open>0\<le>y\<close> named \<open>Step\<close> and binds \<open>?case\<close> to the proposition \<open>0 \<le> y + 1\<close>.

If the rule \<open>induct_nat\<close> has been associated with type \<open>nat\<close> the rule specification
may be omitted in the method:
@{theory_text[display]
\<open>proof (induction n)
\<dots>\<close>}\<close>

subsubsection "Case Assumption Naming and the \<^theory_text>\<open>induct\<close> Method"

text\<open>
As usual, the \<^theory_text>\<open>case\<close> statement uses the case name as name for the assumptions \<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>q\<^sub>i\<close> in the
\<open>i\<close>th case or an explicit name may be specified for them (see Section~\ref{basic-case-context}).
Additionally, the \<open>induction\<close> method arranges the named context for a case so that the set of
assumptions is split into those which in the rule contain the unknown \<open>?P\<close> and those which do not.
These sets are separately named, so that they can be referenced individually.

The set of assumptions which originally contained \<open>?P\<close> now contain an application of \<open>PC\<close> to
a value \<open>term\<^sub>i\<^sub>j\<close> and allow the step from this value to value \<open>term\<^sub>i\<close> by induction. These assumptions
are called ``induction hypotheses'' and are named \<open>"cname.IH"\<close> where \<open>cname\<close> is the case name or the
explicit name for the case assumptions. The other assumptions are independent from \<open>PC\<close>, they are 
additional hypotheses and are named \<open>"cname.hyps"\<close>. Both forms of names
must be enclosed in quotes because the dot is not a normal name constituent.

For an example consider the induction rule \<open>\<lbrakk>?P 0; ?P 1; \<And>y. \<lbrakk>y\<ge>1; ?P y\<rbrakk> \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P ?a\<close> 
with an additional base case for the value \<open>1\<close> and a step which always starts at value \<open>1\<close> or 
greater. If applied to the goal \<open>0\<le>n\<close> the \<open>induction\<close> method produces the three goals
@{text[display]
\<open>0\<le>0
0\<le>1
\<And>y. \<lbrakk>y\<ge>1; 0\<le>y\<rbrakk> \<Longrightarrow> 0\<le>(y+1)\<close>}
If the default case name \<open>3\<close> is used for the third case, the induction hypothesis \<open>0\<le>y\<close> is named
\<open>"3.IH"\<close> and the additional hypothesis \<open>y\<ge>1\<close> is named \<open>"3.hyps"\<close>.

There is a method \<^theory_text>\<open>induct\<close> which behaves like \<^theory_text>\<open>induction\<close> with the only difference that it does 
not introduce the name \<open>"cname.IH"\<close>, it uses \<open>"cname.hyps"\<close> for all assumptions \<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>q\<^sub>i\<close>, whether
they contain \<open>?P\<close> or not.
\<close>

subsubsection "Goals with Assumptions"

text\<open>
If the \<open>induction\<close> method would apply the prepared induction rule in the same way as the \<open>rule\<close>
method to a goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>m\<rbrakk> \<Longrightarrow> C\<close> with assumptions it would 
unify \<open>?P x\<close> only with the conclusion \<open>C\<close> and copy the assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>m\<close>
to all resulting goals unchanged. However, if \<open>x\<close> also occurs in one or more of the \<open>A\<^sub>l\<close> this 
connection with \<open>C\<close> is lost after applying the prepared induction rule. 

Consider the goal
@{text[display]
\<open>4 < n \<Longrightarrow> 5 \<le> n\<close>}
which is of the form 
@{text[display]
\<open>A \<Longrightarrow> C\<close>}
When applying the prepared induction rule for the natural numbers
\<open>\<lbrakk>?P 0; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P n\<close> in the way of the \<open>rule\<close> method the conclusion will be 
matched which leads to the abstracted function \<open>PC \<equiv> (\<lambda>i. 5\<le>i)\<close> and the resulting goals are
@{text[display]
\<open>4 < n \<Longrightarrow> 5 \<le> 0
\<And>y. \<lbrakk>4 < n; 5 \<le> y\<rbrakk> \<Longrightarrow> 5 \<le> (y+1)\<close>}
where the first goal is invalid. Although the second goal is valid, it shows that the relation
between the variable \<open>n\<close> in the assumption and the variable \<open>y\<close> used in the induction rule has been
lost. 

For a goal with assumptions every occurrence of \<open>?P\<close> in the rule, applied to a specific term must
be replaced by \<open>PC\<close> applied to the term together with all assumptions which must also be adapted to
the same term. Therefore the \<open>induction\<close> and \<open>induct\<close> methods work in a different way. They unify
\<open>?P x\<close> with the conclusion \<open>C\<close> and separately with every assumption \<open>A\<^sub>l\<close> and thus additionally
determine an abstracted function \<open>PA\<^sub>l\<close> for every \<open>A\<^sub>l\<close>. Then they replace every \<open>?P term\<close> in a \<open>P\<^sub>i\<close>
or in a \<open>Q\<^sub>i\<^sub>j\<close> in the rule by an application \<open>PC term\<close> together with assumptions \<open>PA\<^sub>1 term; \<dots>;
PA\<^sub>m term\<close>.

The assumptions for a direct occurrence of \<open>?P term\<^sub>i\<close> as conclusion in a \<open>P\<^sub>i\<close> are added after all
\<open>Q\<^sub>i\<^sub>j\<close>, so that the \<open>i\<close>th goal created by the \<open>induction\<close> method now has the form
@{text[display]
\<open>\<And> y\<^sub>i\<^sub>1 \<dots> y\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i; PA\<^sub>1 term\<^sub>i; \<dots>; PA\<^sub>m term\<^sub>i\<rbrakk> \<Longrightarrow> PC term\<^sub>i\<close>}
Additionally, the assumptions for occurrences of a \<open>?P term\<close> in a \<open>Q\<^sub>i\<^sub>j\<close> must be added which usually
can be done by replacing \<open>Q\<^sub>i\<^sub>j\<close> by the rule \<open>Q\<^sub>i\<^sub>j'\<close> of the form \<open>\<lbrakk>PA\<^sub>1 term; \<dots>; PA\<^sub>m term\<rbrakk> \<Longrightarrow> Q\<^sub>i\<^sub>j''\<close>
where \<open>Q\<^sub>i\<^sub>j''\<close> results by substituting \<open>?P term\<close> in \<open>Q\<^sub>i\<^sub>j\<close> by \<open>PC term\<close>. If \<open>?P\<close> is applied to several
different terms in \<open>Q\<^sub>i\<^sub>j\<close>, several sets of corresponding assumptions are added in \<open>Q\<^sub>i\<^sub>j'\<close>.

Moreover, the \<open>induction\<close> method (and also the \<open>induct\<close> method) arranges the named contexts in a
way that the assumptions \<open>PA\<^sub>1 term\<^sub>i; \<dots>; PA\<^sub>m term\<^sub>i\<close> which originate from the goal are named by
\<open>"cname.prems"\<close> and can thus be referenced separate from the \<open>Q\<^sub>i\<^sub>j'\<close> which are named \<open>"cname.hyps"\<close>
and possibly \<open>"cname.IH"\<close> as described above.

In the example above the \<open>induction\<close> method additionally unifies \<open>?P n\<close> with the assumption \<open>4 < n\<close>
which yields the abstracted function \<open>PA \<equiv> (\<lambda>i. 4<i)\<close> and produces the goals
@{text[display]
\<open>4 < 0 \<Longrightarrow> 5 \<le> 0
\<And>y. \<lbrakk>4 < y \<Longrightarrow> 5 \<le> y; 4 < (y+1)\<rbrakk> \<Longrightarrow> 5 \<le> (y+1)\<close>}
Here \<open>4 < (y+1)\<close> results from applying \<open>PA\<close> to \<open>(y+1)\<close> and \<open>4 < y\<close> results from adding \<open>PA\<close> applied
to \<open>y\<close> as assumption to the assumption \<open>?P y\<close> from the rule. If the default case name \<open>2\<close> is used
for the second case, the case assumption \<open>4 < y \<Longrightarrow> 5 \<le> y\<close> will be named \<open>"2.IH"\<close> and the case 
assumption \<open>4 < (y+1)\<close> will be named \<open>"2.prems"\<close> by the \<^theory_text>\<open>case\<close> statement.

Like the \<open>cases\<close> method the methods \<open>induction\<close> and \<open>induct\<close> insert input facts as assumptions into
the goal before they process the goal assumptions in the described way. Therefore both methods can
be used  both in proof scripts, where facts are stored as rule assumptions in the goal state, and in
structured proofs where facts are stored in the proof context and are input to the initial methods
of subproofs.

Other than for the \<open>cases\<close> method it is not possible to pass the induction rule as input fact to
the methods \<open>induction\<close> and \<open>induct\<close>.
\<close>

subsubsection "Induction with Elimination"

text\<open>
Like case rules, induction rules can be extended to include elimination (see
Section~\ref{basic-case-elim}). Such induction rules have an additional first assumption which is
used as major premise to unify with a goal assumption and eliminate it, before processing the
remaining goal assumptions and splitting the goal into cases.

Like case rules such extended induction rules must be attributed by \<open>[consumes 1]\<close>, then the methods
\<open>induction\<close> and \<open>induct\<close> apply elimination before doing the rest of processing.

As example consider the rule \<open>\<lbrakk>?a \<ge> 42; ?P 42; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P ?a\<close>. It uses \<open>42\<close> as
its base case and can thus only prove a property for numbers equal to or greater than \<open>42\<close>. The
major premise restricts \<open>?a\<close> to these cases. If this rule has been proved and named \<open>induct_nat42\<close>
it may be applied with elimination as initial method of a structured proof for the goal \<open>4 < n \<Longrightarrow>
5 \<le> n\<close> by
@{theory_text[display]
\<open>proof (induction n rule: induct_nat42[consumes 1])\<close>}
If the fact \<open>n \<ge> 42\<close> is available as first input fact the application will be successful, consume
that fact, and split the goal into the goals
@{text[display]
\<open>4 < 42 \<Longrightarrow> 5 \<le> 42
\<And>y. \<lbrakk>4 < y \<Longrightarrow> 5 \<le> y; 4 < (y+1)\<rbrakk> \<Longrightarrow> 5 \<le> (y+1)\<close>}

In contrast to the  \<open>cases\<close> method the methods \<open>induction\<close> and \<open>induct\<close> will also consume the
first assumption present in the goal, if it unifies with the major premise of the induction rule
and no input facts are present.
\<close>

subsubsection "Arbitrary Variables"

text\<open>
If the goal contains bound variables, i.e., is of the form \<open>\<And> x\<^sub>1 \<dots> x\<^sub>k. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>m\<rbrakk> \<Longrightarrow> C\<close> these
variables may occur in the assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>m\<close> and the conclusion \<open>C\<close>. When these are
instantiated for the occurrences of \<open>?P\<close> in the rule as described above, every such instance needs
its own separate copy of bound variables \<open>x\<^sub>1 \<dots> x\<^sub>k\<close>.

Consider the goal
@{text[display]
\<open>\<And>c. n<c \<Longrightarrow> 2*n < 2*c\<close>}
When applying the prepared induction rule for the natural numbers
\<open>\<lbrakk>?P 0; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P n\<close> in the way described above, the variable \<open>c\<close> must be bound
separately for the occurrences \<open>?P y\<close> and \<open>?P (y+1)\<close> because it need not denote the same value in
both positions. This can be accomplished by creating the goals
@{text[display]
\<open>\<And>c. 0<c \<Longrightarrow> 2*0 < 2*c
\<And>y c. \<lbrakk>\<And>c. y<c \<Longrightarrow> 2*y < 2*c; y+1 < c\<rbrakk> \<Longrightarrow> 2*(y + 1) < 2*c\<close>}
with two nested bindings of \<open>c\<close>.

The methods \<open>induction\<close> and \<open>induct\<close> treat explicit bindings of variables in the goal in this way.
However, if variables are not bound explicitly in the goal (i.e., they are free in the goal), there
are two possible meanings: in a theorem all variables are implicitly bound and therefore need a
separate binding for every occurrence of \<open>?P\<close>, whereas in a local goal statement variables may have
been fixed in the enclosing context, then they must denote the same value for every occurrence of
\<open>?P\<close> and must not be bound separately. Since it is difficult for Isabelle to determine the correct
treatment of free variables automatically, it may be specified explicitly by the proof writer.
The free variables which do not denote a fixed value from the context but an ``arbitrary'' value
used only locally in the goal can be specified to the \<open>induction\<close> method in the form
@{theory_text[display]
\<open>induction x arbitrary: x\<^sub>1 \<dots> x\<^sub>k rule: name\<close>}
and in the same form for the \<open>induct\<close> method.

In particular, if a theorem or goal statement is specified in structured form the free variables
are not bound in the goal but in the outermost proof context (see Section~\ref{basic-proof-state})
and the goal only consists of the conclusion \<open>C\<close>. To apply induction as initial proof method the
assumptions must be input to it and the variables must be specified as arbitrary:
@{theory_text[display]
\<open>theorem 
  fixes x\<^sub>1 \<dots> x\<^sub>k
  assumes "A\<^sub>1" \<dots> "A\<^sub>m"
  shows "C"
using assms
proof (induction \<dots> arbitrary: x\<^sub>1 \<dots> x\<^sub>k \<dots>) \<dots> qed\<close>}\<close>

(*
notepad begin

  fix x c n::nat
  let "?U1 x" = "5 + x"
  let "?lhs x \<le> ?rhs 5" = "2*x+3 \<le> 2*5+3"
  let "?eq 2" = "2*x+3 \<le> 2*5+3"
  have xyzzy: "?lhs 7 \<le> 17" (is ?xx) sorry
  assume xyzzy2: "2*x+3 \<le> 2*5+3" (is "?lhs2 x \<le> ?rhs2 5")

consider (Zero) "(n::nat) = 0" | (Notzero) "n \<noteq> 0" by blast
then have "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
proof cases
  case Zero then show ?thesis by simp
next
  case Notzero assume "x < c" with Notzero show ?thesis by simp
qed

  obtain m::nat where "m \<noteq> 0" by auto
  {
  consider p::nat where "p \<noteq> 0" by auto
  fix p::nat
  assume "x \<noteq> 0" "y > 0" if "p>5" for x y :: nat
  have "p>7 \<Longrightarrow> p > 3" sorry
}
end
consts c1::nat

thm case_split
theorem my_case_split:
  assumes "x > 5"
  obtains (True) "Q" | (False) "\<not> Q" by blast
theorem my_case_split2:
  shows "\<lbrakk>Q \<Longrightarrow> thesis; \<not> Q \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis" by blast
theorem my_case_split3:
  "thesis" if "Q \<Longrightarrow> thesis" and "\<not> Q \<Longrightarrow> thesis" for thesis using that by blast

theorem elimx: "\<lbrakk>(x::nat) \<le> c; x < c \<Longrightarrow> P; x = c \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by linarith
theorem elimy[consumes 1]: assumes "(x::nat) \<le> c" obtains (lower) "x<c" | (equal) "x=c" using assms by linarith

theorem "(x::nat) \<le> c \<Longrightarrow> n*x \<le> n*c"
  apply(erule elimx)
  oops

theorem "n*x \<le> n*c" if "(x::nat) \<le> c"
  using that
  apply(cases rule:elimx[consumes 1])
  oops

theorem "n*x \<le> n*c" if "(x::nat) \<le> c"
  using that
  apply(cases rule:elimy)
  oops

theorem "n*x \<le> n*c" if "(x::nat) \<le> c"
  using that 
proof (cases rule:elimy)
  case lower
  then show ?thesis sorry
next
  case equal
  then show ?thesis sorry
qed

theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
proof (cases "n=0")
  case True
  then show ?thesis by simp
next
  case False
  assume "x < c"
  then show ?thesis by simp
qed

theorem example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m" by simp
theorem e3: "Q \<Longrightarrow> Q" sorry
theorem e4: "\<lbrakk>Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by blast
theorem  "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
  apply (drule example1)
  apply (drule example2)
  by -


definition pred::"nat\<Rightarrow>bool" where "pred x \<equiv> x > 5"

lemma ss: "pred 10" using pred_def by simp


lemma r: "\<lbrakk>pred 2; pred 3\<rbrakk> \<Longrightarrow> pred (5)" if "pred 1"
  sorry

lemma "\<lbrakk>pred 10; pred 1; pred 2\<rbrakk> \<Longrightarrow> pred 42"
  apply(drule r)
  apply(subst (asm) ss)
  sorry
lemma imp_uncurry: "P \<longrightarrow> (Q \<longrightarrow> R) \<Longrightarrow> P \<and> Q \<longrightarrow> R"
apply (rule impI)
apply (erule conjE)
apply (drule mp)
apply assumption
apply (drule mp)
apply assumption
  apply assumption
  done

print_statement exE
thm exE

lemma u_c[consumes 1,case_names A]: "\<lbrakk>pred n; pred 10 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" sorry

lemma u_d: "\<lbrakk>pred n; pred 7; pred (n+1)\<rbrakk> \<Longrightarrow> pred 10" sorry

lemma u_d2: "\<lbrakk>pred n; pred 7; pred (n+1)\<rbrakk> \<Longrightarrow> pred 11" sorry

lemma "pred 11 \<and> pred 10"
  apply(rule conjI)
  oops

lemma u_c3: "\<lbrakk>pred 1 \<Longrightarrow> P; pred 7 \<Longrightarrow> P; pred 10 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" sorry

lemma u_e: "\<lbrakk>Q; Q\<Longrightarrow>pred 1 \<Longrightarrow> P; Q\<Longrightarrow>pred 7 \<Longrightarrow> P; Q\<Longrightarrow>pred 10 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" sorry



lemma u_o: obtains "pred 1" | (c2) "pred 2" | "pred 3" sorry

lemma u_s: assumes "pred 1 \<Longrightarrow> P" "pred 2 \<Longrightarrow> P" "pred 3 \<Longrightarrow> P" shows "P" sorry

lemma u_s2: shows "\<lbrakk>pred 1 \<Longrightarrow> thesis; pred 2 \<Longrightarrow> thesis; pred 3 \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis" sorry

lemma elim1[consumes 1]: "\<lbrakk>Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by blast
lemma "X \<Longrightarrow> Y"
  subgoal premises p using p
proof (cases rule: elim1) oops

lemma  "\<lbrakk>\<lbrakk>pred x; pred z\<rbrakk> \<Longrightarrow> P; pred y \<Longrightarrow> P; pred 10 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" sorry
lemma "Z" proof (cases "5::nat" rule: u_c4) oops

lemma "X \<Longrightarrow> Z" if "Y" using that proof (induction rule: u_c3) oops
lemma "X \<Longrightarrow> Y" proof (induct rule: elim1) oops
lemma assumes "X" shows "Y" using assms proof (cases rule: elim1) oops
lemma "Y" if "X" using that  proof (cases rule: elim1) oops

thm conjE disjE
lemma elim2[consumes 1]: "\<lbrakk>P \<and> Q; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" by (rule conjE)
lemma elim3[consumes 1]: "\<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" by (rule disjE)

lemma xxh: "\<lbrakk>pred 1; A; B\<rbrakk> \<Longrightarrow> C" sorry

lemma "\<lbrakk>A\<and>B; pred 1\<rbrakk> \<Longrightarrow> C" apply(erule elim2) oops
lemma "\<lbrakk>A\<and>B; pred 1\<rbrakk> \<Longrightarrow> C\<and>D" apply(rule conjI) apply(erule elim2; goal_cases) oops
lemma "\<lbrakk>A\<and>B; pred 1\<rbrakk> \<Longrightarrow> C" proof (induct rule: elim2) oops
lemma "\<lbrakk>A\<and>B; pred 1\<rbrakk> \<Longrightarrow> C\<and>D" apply(rule conjI) subgoal premises p using elim2 p proof (cases) assume a1: "pred 1" case 1 with a1 show ?thesis apply(rule xxh) done qed oops
lemma "\<lbrakk>A\<and>B; pred 1\<rbrakk> \<Longrightarrow> C\<and>D" apply(rule conjI) subgoal premises p using p apply(cases rule: elim2) apply(rule xxh) apply(assumption+) done oops
lemma assumes "A\<and>B" and "pred 1" shows "C" using assms proof (cases rule: elim2) oops

lemma "\<lbrakk>A\<or>B; pred 1\<rbrakk> \<Longrightarrow> C" apply(erule elim3) oops
lemma "\<lbrakk>A\<or>B; pred 1\<rbrakk> \<Longrightarrow> C\<and>D" apply(rule conjI) apply(erule elim3; goal_cases) oops
lemma "\<lbrakk>A\<or>B; pred 1\<rbrakk> \<Longrightarrow> C" proof (induct rule: elim3) oops
lemma "\<lbrakk>A\<or>B; pred 1\<rbrakk> \<Longrightarrow> C" subgoal premises p using p proof (cases rule: elim3) oops
lemma assumes "A\<or>B" and "pred 1" shows "C" using assms proof (cases rule: elim3) oops
lemma "C" if "A\<or>B" and "pred x" for x using that proof (cases rule: elim3) oops

lemma elim4[consumes 1]: "\<lbrakk>a \<ge> 42; P 42; \<And>y. P y \<Longrightarrow> P (y+1)\<rbrakk> \<Longrightarrow> P a" sorry

lemma "\<lbrakk>n \<ge> 42; n > 4\<rbrakk> \<Longrightarrow> n \<ge> 5"  
proof (induction n rule: elim4) oops
  find_theorems "?t1 \<le> ?t2" name: example

*)


(*
lemma myInduct: "\<lbrakk>P 0; \<And>y. P y \<Longrightarrow> P (y+1)\<rbrakk> \<Longrightarrow> P a" for a::nat
  by (metis add.commute add_cancel_left_left discrete infinite_descent0 le_iff_add less_add_same_cancel2 less_numeral_extra(1))

lemma myInduct': "\<lbrakk>P 0; \<And>y. \<lbrakk>P y; y < 5\<rbrakk> \<Longrightarrow> P (y+1)\<rbrakk> \<Longrightarrow> P a" for a::nat
  sorry

lemma "\<And>c. n < c \<Longrightarrow> 2*n < 2*c" for n::nat
  apply(induction "n" rule: myInduct')
  apply(rule myInduct[where a=n]) 
  oops


lemma myInduct: "\<lbrakk>P 0; \<And>y. P y \<Longrightarrow> P (y+1)\<rbrakk> \<Longrightarrow> P a" for a::nat
  by (metis add.commute add_cancel_left_left discrete infinite_descent0 le_iff_add less_add_same_cancel2 less_numeral_extra(1))

lemma "4 < n \<Longrightarrow> 5 \<le> n" for n::nat
  apply(induction "n" rule: myInduct)
  apply(rule myInduct[where a=n]) 
  oops

lemma myInduct2: "\<lbrakk>P 0; P 1; \<And>y. \<lbrakk>P y; y \<ge> 1\<rbrakk> \<Longrightarrow> P (y+1)\<rbrakk> \<Longrightarrow> P a" for a::nat
  by (metis One_nat_def Suc_eq_plus1 le_simps(3) myInduct neq0_conv)

lemma "0\<le>n" for n::nat
proof (induction n rule:myInduct2)
  case 1
  then show ?case sorry
next
  case (3 y)
  then show ?case sorry
qed


lemma "4 < n \<Longrightarrow> 5 \<le> n" for n::nat
proof (induction "n" rule: myInduct2)
  case start: 1
  then show ?case sorry
next
  case step: (2 y)
  then show ?case sorry
qed


inductive ev :: "nat \<Rightarrow> bool" where
ev0:
 "ev 0" |
evSS : "ev n \<Longrightarrow> ev (n + 2)"
thm ev.induct

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"
thm evn.induct
thm nat.induct int_of_nat_induct
lemma "ev m \<Longrightarrow> evn m"
apply(induction m rule: ev.induct )
  by(simp_all)

lemma 
  assumes "ev m"
  shows "evn m"
  using assms
proof (induction m rule: ev.induct )
qed simp_all

lemma "evn n \<Longrightarrow> ev n"
  apply(rule evn.induct ) sorry

lemma "w = of_nat n + of_nat m" for n::nat and w::int
  apply(induction n m rule: nat.induct) sorry

*)

(*
section "Locales and Classes"

subsection "Locales"
text_raw\<open>\label{basic-theory-locale}\<close>

text \<open>
There are cases where theory content such as definitions and theorems occur which has similar 
structure but differs in some types or terms. Then it is useful to define a ``template'' and 
instantiate it several times. This can be done in Isabelle using a ``locale''.
\<close>

subsubsection "Simple Locales"

text \<open>
A locale can be seen as a parameterized theory fragment, where the parameters are terms. A locale
with \<open>n\<close> parameters is defined by
@{theory_text[display]
\<open>locale name = 
  fixes x\<^sub>1 \<dots> x\<^sub>n
begin
  \<dots>
end\<close>}
where the variables \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are the parameters. Like the bound variables in a theorem they can
be grouped by \<^theory_text>\<open>and\<close> and types can be specified for some or all groups. The content between
\<^theory_text>\<open>begin\<close> and \<^theory_text>\<open>end\<close> may consist of definitions and theorems which may use the parameter names 
like constant names. Content may also be added to an existing locale in the form 
@{theory_text[display]
\<open>context name
begin
  \<dots>
end\<close>}
Therefore the \<^theory_text>\<open>begin \<dots> end\<close> block can also be omitted in the locale definition and the locale can be
filled later.

An instance of the parameterized theory fragment is created by ``interpreting'' the locale in the form
@{theory_text[display]
\<open>interpretation name term\<^sub>1 \<dots> term\<^sub>n .\<close>}
where \<open>term\<^sub>1 \<dots> term\<^sub>n\<close> are the terms to be substituted for the locale parameters, their types must
match the parameter types, i.e., must be instances of them. The final dot in the interpretation
is a rudimentary proof. An actual proof is needed, if the locale definition specifies additional
assumptions for the parameters.
\<close>

subsubsection "Locales with Assumptions"

text \<open>
Additional assumptions for locale parameters can be specified as propositions in the form
@{theory_text[display]
\<open>locale name = 
  fixes x\<^sub>1 \<dots> x\<^sub>n
  assumes A\<^sub>1 \<dots> A\<^sub>m
begin
  \<dots>
end\<close>}
where the \<open>A\<^sub>1, \<dots>, A\<^sub>m\<close> are propositions. Like in a theorem, they can be grouped by \<^theory_text>\<open>and\<close> and 
named. The names can be used to reference the assumptions as facts in proofs in the locale content. 
When the locale is interpreted, all the assumptions must be proved with the actual terms substituted 
for the parameters. Therefore the more general form of an interpretation is
@{theory_text[display]
\<open>interpretation name term\<^sub>1 \<dots> term\<^sub>n \<proof>\<close>}
\<close>

subsubsection "Extending Locales"

text \<open>
A locale may extend one or more other locales using the form
@{theory_text[display]
\<open>locale name = name\<^sub>1 + \<cdots> + name\<^sub>n +
  fixes \<dots>
  assumes \<dots>
begin
  \<dots>
end\<close>}
where \<^theory_text>\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are the names of the extended locales. Their parameters become parameters
of the defined locale, inserted before the parameters declared by the \<^theory_text>\<open>fixes \<dots>\<close> clause.
\<close>

*)
end
