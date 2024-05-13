theory Chapter_holbasic
  imports Chapter_basic
begin

chapter "Isabelle HOL Basics"
text_raw\<open>\label{holbasic}\<close>

text \<open>
The basic mechanisms described in Chapter~\ref{basic} can be used for working with different 
``object logics''. An object logic defines the types of objects available, constants of these types,
and facts about them. An object logic may also extend the syntax, both inner and outer syntax.

The standard object logic for Isabelle is the ``Higher Order Logic'' HOL, it covers a large part
of standards mathematics and is flexibly extensible. This chapter introduces some basic
mechanisms which are available in HOL for arbitrary types.

The abbreviation ``HOL'' is used in the logics community to denote the general concept of higher
order logics. In this document we use it specifically to denote the implementation as object logic
in Isabelle which is also named HOL. 
\<close>

section "Predicates and Relations"
text_raw\<open>\label{holbasic-pred}\<close>

text\<open>
Basically HOL uses the type \<open>'a \<Rightarrow> 'b\<close> of functions provided by Isabelle (see
Section~\ref{basic-theory-terms}) to represent predicates and relations in the usual way.
\<close>

subsection "Predicates"
text_raw\<open>\label{holbasic-pred-pred}\<close>

text\<open>
A predicate on values of arbitrary types \<open>t\<^sub>1, \<dots>, t\<^sub>n\<close> is a function of type \<open>t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>n \<Rightarrow>
bool\<close>. It may be denoted by a lambda term \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. bterm\<close> where \<open>bterm\<close> is a term of type \<open>bool\<close>
which may contain free occurrences of the variables \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close>. Note that also a predicate defined
as a named constant \<open>P\<close> can always be specified by the lambda term \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. P x\<^sub>1 \<dots> x\<^sub>n\<close>.

Note that the concept of predicates actually depends on the specific HOL type \<open>bool\<close>, which is
introduced in Section~\ref{holtypes-bool}. 
\<close>

subsection "Unary Predicates and Sets"
text_raw\<open>\label{holbasic-pred-set}\<close>

text\<open>
Unary predicates of type \<open>t \<Rightarrow> bool\<close> are equivalent to sets of type \<open>t set\<close>. There is a 1-1
correspondence between a predicate and the set of values for which the predicate value is \<open>True\<close>.
Actually, the HOL type constructor \<open>set\<close> described in Section~\ref{holtypes-set} is defined based on
this correspondence. See that section for more information about denoting and using sets.

As a convention HOL often provides a predicate and rules about it in both forms as a set named
\<open>name\<close> and as a predicate named \<open>namep\<close> or \<open>nameP\<close>. Then usually every fact \<open>F\<close> containing
such predicates in set form can be converted to the corresponding fact containing them in predicate
form by applying the attribute \<open>to_pred\<close> as in \<open>F[to_pred]\<close> and vice versa by applying the attribute
\<open>to_set\<close>.
\<close>

subsection "Relations"
text_raw\<open>\label{holbasic-pred-rel}\<close>

text\<open>
A binary relation between values of arbitrary types \<open>t\<^sub>1\<close> and \<open>t\<^sub>2\<close> is a binary predicate of type
\<open>t\<^sub>1 \<Rightarrow> t\<^sub>2 \<Rightarrow> bool\<close>. As binary functions the relations in HOL often have an alternative operator name
of the form \<open>(op)\<close> which supports specifying applications in infix form \<open>x op y\<close> (see
Section~\ref{basic-theory-terms})..

By partial application (see Section~\ref{basic-theory-terms}) the first argument of a relation \<open>R\<close>
can be fixed to yield the unary predicate \<open>(R x)\<close> on the second argument. For operators this must be
done using the operator name in the form \<open>((op) x)\<close>, partial application cannot be written by
omitting an argument on one side of the infix operator.

Since the unary predicate \<open>(R x)\<close> is equivalent to a set, every binary relation of type
\<open>t\<^sub>1 \<Rightarrow> t\<^sub>2 \<Rightarrow> bool\<close> is equivalent to a set-valued function of type \<open>t\<^sub>1 \<Rightarrow> (t\<^sub>2 set)\<close>. It maps every
value of type \<open>t\<^sub>1\<close> to the set of related values of type \<open>t\<^sub>2\<close>. HOL extends the convention described
above and often provides relations named \<open>namep\<close> or \<open>nameP\<close> also as set-valued functions named
\<open>name\<close>.

Note that HOL introduces the specific type constructor \<open>rel\<close> (see Section~\ref{holtypes-rel}), where
the values are equivalent to binary relations.

More generally, \<open>n\<close>-ary relations for \<open>n > 2\<close> are directly represented by \<open>n\<close>-ary predicates. Every
\<open>n\<close>-ary relation is equivalent to an \<open>(n-1)\<close>-ary set-valued function.
\<close>

section "Equality, Orderings, and Lattices"
text_raw\<open>\label{holbasic-equal}\<close>

subsection "The Equality Relation"
text_raw\<open>\label{holbasic-equal-eq}\<close>

text\<open>
HOL introduces the equality relation as a function
@{text[display]
\<open>HOL.eq :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}
with the alternative operator name \<open>(=)\<close> for infix notation.

Inequality can be denoted by
@{text[display]
\<open>not_equal :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}
with the alternative operator name \<open>(\<noteq>)\<close> for infix notation.

Both functions are polymorphic and can be applied to terms of arbitrary type, however, 
they can only be used to compare two terms which have the same type. Therefore the
proposition
@{text[display]
\<open>True \<noteq> 1\<close>}
is syntactically wrong and Isabelle will signal an error for it.

Moreover, in a term such as \<open>term\<^sub>1 = term\<^sub>2\<close> or \<open>term\<^sub>1 \<noteq> term\<^sub>2\<close> no type information can be derived
for \<open>term\<^sub>1\<close> and \<open>term\<^sub>2\<close> other than that they must have the same type. There may be relations with
the same semantics but for operands of a specific type, then it is possible to derive the operand
types. An example is the relation \<open>iff\<close> with operator name \<open>(\<longleftrightarrow>)\<close> which is equal to \<open>(=)\<close> but only
defined for operands of type \<open>bool\<close>. Therefore for the term \<open>term\<^sub>1 \<longleftrightarrow> term\<^sub>2\<close> HOL automatically
derives that \<open>term\<^sub>1\<close> and \<open>term\<^sub>2\<close> have type \<open>bool\<close>.
\<close>

subsection "The Ordering Relations"
text_raw\<open>\label{holbasic-equal-order}\<close>

text\<open>
HOL also introduces two ordering relations as functions
@{text[display]
\<open>less :: 'a \<Rightarrow> 'a \<Rightarrow> bool
less_eq :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}
with the alternative operator names \<open>(<)\<close> and \<open>(\<le>)\<close> for infix notation and the
abbreviations \<open>greater\<close> and \<open>greater_eq\<close> for reversed arguments with operator names
\<open>(>)\<close> and \<open>(\<ge>)\<close>.

Based on these relations HOL also introduces the functions
@{text[display]
\<open>min :: 'a \<Rightarrow> 'a \<Rightarrow> 'a
max :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>}
in the usual way, i.e. if \<open>a\<le>b\<close> then \<open>min a b\<close> is \<open>a\<close>, otherwise \<open>b\<close>. HOL also introduces the
functions
@{text[display]
\<open>Min :: 'a set \<Rightarrow> 'a
Max :: 'a set \<Rightarrow> 'a\<close>}
for the minimum or maximum of all values in a set.

All these functions are polymorphic and can be applied to terms of arbitrary type. Even if the
values of a type are not ordered, an application of an ordering relation or minimum/maximum
function to them is a correct term. However, in that case the resulting value is underspecified, no
information is available about it. Also, the value of \<open>Min\<close> and \<open>Max\<close> is underspecified if applied
to an empty or infinite set.

Moreover, these are only syntactic definitions, no rules about orderings are implied by them. For
some of its predefined types, such as type \<open>nat\<close>, HOL provides more specific specifications by
overloading.

Like for \<open>(=)\<close> the type of \<open>term\<^sub>1\<close> and \<open>term\<^sub>2\<close> cannot be derived in a term such as \<open>term\<^sub>1 < term\<^sub>2\<close>.
There are relations with the same semantics but specific operand types such as \<open>(\<subseteq>)\<close> for the
relation \<open>(\<le>)\<close> on sets (see Section~\ref{holtypes-set}).
\<close>

subsection "Lattice Operations"
text_raw\<open>\label{holbasic-equal-lattice}\<close>

text\<open>
HOL introduces the two lattice operations
@{text[display]
\<open>inf :: 'a \<Rightarrow> 'a \<Rightarrow> 'a
sup :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>}
with the alternative operator names \<open>(\<sqinter>)\<close> and \<open>(\<squnion>)\<close> for infix notation together with the lattice
constants
@{text[display]
\<open>top :: 'a
bot :: 'a\<close>}
with the alternative names \<open>(\<top>)\<close> and \<open>(\<bottom>)\<close> (in the interactive editor available in the Symbols
panel in the Logic tab).

Additionally there are the lattice operations for all values in a set (see
Section~\ref{holtypes-set})
@{text[display]
\<open>Inf :: 'a set \<Rightarrow> 'a
Sup :: 'a set \<Rightarrow> 'a\<close>}
with the alternative operator names \<open>(\<Sqinter>)\<close> and \<open>(\<Squnion>)\<close> for prefix notation.

HOL does not provide the six alternative names automatically. To make them available, the command
@{theory_text[display]
\<open>unbundle lattice_syntax\<close>}
must be used on theory level. It is available after importing the theory \<^theory>\<open>Main\<close> (see
Section~\ref{system-invoke-theory}).

The lattice operations and constants are polymorphic but are not available for arbitrary types.
They are overloaded only for those types which have a corresponding structure. For example, type
\<open>nat\<close> has the \<open>bot\<close> value (which is equal to \<open>0\<close>), but no \<open>top\<close> value. If a lattice operation or
constant is used for a type for which it is not available an error message of the form
``No type arity ...'' is signaled.

Like for equality and ordering relations, because the lattice operations and constants are
overloaded it is not possible to derive the type for valid operands. Again, there are operations and
constants with more specific operand types, such as \<open>(\<inter>)\<close> for \<open>(\<sqinter>)\<close> on sets where HOL automatically
derives the operand types.
\<close>

section "Description Operators"
text_raw\<open>\label{holbasic-descr}\<close>

text\<open>
A description operator selects a value from all values which satisfy a given unary predicate.

Description operators use the binder syntax of the form \<open>OP x. term\<close> (see
Section~\ref{basic-theory-terms}). Like a lambda term it locally binds a variable \<open>x\<close> which may occur in \<open>term\<close>.
\<close>

subsection "The Choice Operator"
text_raw\<open>\label{holbasic-descr-choice}\<close>

text\<open>
An arbitrary value satisfying the given predicate \<open>\<lambda>x. bterm\<close> can be denoted by
@{text[display]
\<open>SOME x. bterm\<close>}
Only a single variable may be specified after \<open>SOME\<close>, however, like in a lambda term a type may be
specified for it.

The value denoted by the term is underspecified in the sense of Section~\ref{basic-theory-terms}.
The only information which can be derived for it is that it satisfies the predicate \<open>\<lambda>x. bterm\<close>.
If there is no value which satisfies the predicate not even this property may be derived.

The operator \<open>SOME\<close> is equivalent to the famous Hilbert choice operator. HOL includes the axiom of
choice and provides the operator on this basis.
\<close>

subsection "The Definite Description Operator"
text_raw\<open>\label{holbasic-descr-definite}\<close>

text\<open>
If only one value satisfies the given predicate \<open>\<lambda>x. bterm\<close> this value can be denoted by
@{text[display]
\<open>THE x. bterm\<close>}
Like for \<open>SOME\<close> only a single variable may be specified with an optional type specification.

The value denoted by the term is also underspecified. However,
after proving that there exists a value \<open>v\<close> which satisfies the predicate \<open>\<lambda>x. bterm\<close> and that
all values satisfying the predicate are equal it is possible to prove that \<open>THE x.bterm = v\<close>.
\<close>

subsection "The Least and Greatest Value Operators"
text_raw\<open>\label{holbasic-descr-least}\<close>

text\<open>
If the values satisfying a predicate \<open>\<lambda>x. bterm\<close> are ordered, the least or greatest of these
values can be denoted by the terms
@{text[display]
\<open>LEAST x. bterm
GREATEST x. bterm\<close>}
Only a single variable with an optional type specification is useful to be specified.

If the values satisfying the predicate are not ordered the value denoted by such a term is
underspecified. The operators use the ordering relations \<open>(\<le>)\<close> and \<open>(\<ge>)\<close> (see
Section~\ref{holbasic-equal-order}) which are applicable to values of arbitrary type. The operators 
are defined using \<open>THE\<close> to return the value \<open>x\<close> which satisfies the predicate and \<open>x \<le> y\<close> or
\<open>x \<ge> y\<close> holds, respectively, for all values \<open>y\<close> which also satisfy the predicate.

Also, if the values are ordered but there is no single least or greatest value among them the
resulting value is underspecified. For example, the term \<open>GREATEST n::nat. n > 0\<close> is correct and
denotes a value of type \<open>nat\<close>, although no information is available about it.
\<close>

section "Undefined Value"
text_raw\<open>\label{holbasic-undefined}\<close>

text\<open>
HOL introduces the undefined value
@{text[display]
\<open>undefined :: 'a\<close>}
which is overloaded for arbitrary types. It is completely underspecified as described in
Section~\ref{basic-theory-terms}, i.e., no further information is given about it.

Despite its name it is a well defined value for every type \<open>'a\<close>. It is typically used for 
values which are irrelevant, such as in the definition
@{theory_text[display]
\<open>definition f :: "nat \<Rightarrow> nat" where "f x \<equiv> undefined"\<close>}
Although the function \<open>f\<close> looks like a completely undefined function, it is not possible to define
true partial functions this way. Functions in Isabelle are always total. Function \<open>f\<close> maps every
natural number to the (same) value \<open>undefined\<close>, which is of type \<open>nat\<close>, but it cannot be proved to
be equal to a specific natural number such as \<open>1\<close> or \<open>5\<close>. However, since it is a single value the
equality \<open>f x = f y\<close> holds for arbitrary \<open>x\<close> and \<open>y\<close> of type \<open>nat\<close>.
\<close>

section "Let Terms"
text_raw\<open>\label{holbasic-let}\<close>

text\<open>
HOL extends the inner syntax for terms described in Section~\ref{basic-theory-terms} by terms of
the following form
@{text[display]
\<open>let x\<^sub>1 = term\<^sub>1; \<dots>; x\<^sub>n = term\<^sub>n in term\<close>}
where \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are variables. The variable bindings are sequential, i.e., if \<open>i<j\<close> variable
\<open>x\<^sub>i\<close> may occur in \<open>term\<^sub>j\<close> and denotes \<open>term\<^sub>i\<close> there. In other words, the scope of \<open>x\<^sub>i\<close> are the 
terms \<open>term\<^sub>j\<close> with \<open>i<j\<close> and the \<open>term\<close>. If \<open>x\<^sub>i\<close> and \<open>x\<^sub>j\<close> are the same variable, the binding of 
its second occurrence shadows the binding of the first and ends the scope of the first occurrence.

Let terms are useful to introduce local variables as abbreviations for sub-terms.
 
 Don't confuse the \<open>let\<close> term with the \<^theory_text>\<open>let\<close> statement described in
Section~\ref{basic-proof-let}. Although they are used for a similar purpose there are several
differences: A \<open>let\<close> term belongs to the inner syntax of the object logic HOL, the \<^theory_text>\<open>let\<close>
statement belongs to the meta-level of the outer syntax. Moreover, the \<^theory_text>\<open>let\<close> statement uses
unification to bind sub-terms to unknowns in a term pattern, a \<open>let\<close> term only binds explicitly
specified terms to single variables.

The let term specified above is an alternative syntax for the nested let terms
@{text[display]
\<open>let x\<^sub>1 = term\<^sub>1 in (\<dots> (let x\<^sub>n = term\<^sub>n in term) \<dots>)\<close>}
and a single let term
@{text[display]
\<open>let x = term' in term\<close>}
is an alternative syntax for the function application term
@{text[display]
\<open>Let term' (\<lambda>x. term)\<close>}
Here \<open>Let\<close> is the polymorphic function
@{text[display]
\<open>Let :: 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<equiv> \<lambda>x f. f x\<close>}
which simply applies its second argument to its first argument.

Occurrences of let terms are usually not automatically resolved by substituting the bound term for
the variable. Therefore a proposition like \<open>(let x = a+b in (x*x)) = ((a+b)*(a+b))\<close> cannot be proved
by the simplifier (or other methods including simplification like \<open>auto\<close>, see
Sections~\ref{basic-methods-simp} and~\ref{basic-methods-auto}). To resolve it, the
simplifier must be configured by adding the definitional equation of \<open>Let\<close> as \<open>simp add: Let_def\<close>.
\<close>

section "Tuples"
text_raw\<open>\label{holbasic-tuples}\<close>

text\<open>
HOL supports type expressions of the form \<open>t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n\<close> for arbitrary types \<open>t\<^sub>1, \<dots>, t\<^sub>n\<close>. They
denote the type of \<open>n\<close>-tuples where the \<open>i\<close>th component has type \<open>t\<^sub>i\<close>. Here the \<open>\<times>\<close> is the ``times
operator'' available in the interactive editor in the Symbols panel in the Operator tab. An
alternative syntax is \<open>t\<^sub>1 * \<dots> * t\<^sub>n\<close> using the ASCII star character. As an example the type
\<open>nat \<times> bool\<close> is the type of pairs of natural numbers and boolean values. The type \<open>nat \<times> 'a \<times> bool\<close>
is the polymorphic type of triples of a natural number, a value of the arbitrary type denoted by the
type parameter \<open>'a\<close>, and a boolean value. As usual, all these type expressions are part of the inner
syntax.

Values for \<open>n\<close>-tuples of type \<open>t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n\<close> are denoted in inner syntax as terms of the form
\<open>(term\<^sub>1, \<dots>, term\<^sub>n)\<close> where \<open>term\<^sub>i\<close> is a term of type \<open>t\<^sub>i\<close> and the parentheses and the comma belong
to the syntax.
\<close>

subsection "Function Argument Tuples"
text_raw\<open>\label{holbasic-tuples-funarg}\<close>

text\<open>
Every \<open>n\<close>-ary function of type \<open>t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>n \<Rightarrow> t\<close> (see Section~\ref{basic-theory-terms}) is
equivalent to a function of type \<open>(t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n) \<Rightarrow> t\<close> with \<open>n\<close>-tuples as argument values, which is
the common way in mathematics to represent a function with \<open>n\<close> arguments. There is a 1-1
correspondence between functions of these two forms. The first form is called the ``curried'' form
and the second form with tuples as arguments is called the ``uncurried'' form (named after Haskell
Curry who introduced the first form for \<open>n\<close>-ary functions). Note that for unary functions both forms
are the same.

Section~\ref{holtypes-func} describes means to convert between both forms and other ways how to
work with them.
\<close>

subsection "Relations as Tuple Sets"
text_raw\<open>\label{holbasic-tuples-rel}\<close>

text\<open>
For an \<open>n\<close>-ary relation of type \<open>t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>n \<Rightarrow> bool\<close> (see Section\ref{holbasic-pred-rel}) the
uncurried form is a predicate of type \<open>(t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n) \<Rightarrow> bool\<close>. Since all arguments together are
represented by a single tuple, this predicate is equivalent to a set of type \<open>(t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n) set\<close>
(see Section\ref{holbasic-pred-set}) where the elements in the set are tuples. This is the
usual form of representing relations in mathematics.

HOL extends the convention described in Section~\ref{holbasic-pred-set} of providing relations
named \<open>namep\<close> or \<open>nameP\<close> also as set-valued functions named \<open>name\<close> by alternatively using a tuple
set named \<open>name\<close>.
\<close>

section "Inductive Definitions"
text_raw\<open>\label{holbasic-inductive}\<close>

text\<open>
HOL supports inductive definitions of predicates as content in theories. An inductive definition
defines a predicate by derivation rules which allow to derive the predicate values for some
arguments from the values for other arguments. An inductive definition for a k-ary predicate has the
form
@{theory_text[display]
\<open>inductive name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
where P\<^sub>1 | \<dots> | P\<^sub>n\<close>}
with derivation rules \<open>P\<^sub>i\<close>. The type specification for the predicate may be omitted if it can be
derived from the use of the defined predicate in the rules \<open>P\<^sub>i\<close>.
\<close>

subsection "The Defining Rules"
text_raw\<open>\label{holbasic-inductive-defrules}\<close>

text\<open>
The \<open>P\<^sub>i\<close> are derivation rules which may be specified in inner syntax of the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> name term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k\<close>}
where the conclusion is always an application of the defined predicate to \<open>k\<close> argument terms. The
defined predicate \<open>name\<close> may occur in arbitrary ways in the rule assumptions \<open>Q\<^sub>i\<^sub>j\<close>, but not in the
argument terms \<open>term\<^sub>i\<^sub>j\<close>. The rule separators \<open>|\<close> belong to the outer syntax, thus every rule must
be separately quoted.

An example is the following inductive definition for an evenness predicate:
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  "evn(0)" | "\<And>n. evn(n) \<Longrightarrow> evn(n+2)"\<close>}\<close>

subsubsection "Alternative Rule Forms"

text\<open>
As for other derivation rules on theory level (see Section~\ref{basic-theory-prop}) the explicit
bindings of the variables \<open>x\<^sub>i\<^sub>1, \<dots>, x\<^sub>i\<^sub>p\<^sub>i\<close> are optional, variables occurring free in the assumptions
or the conclusion are always automatically bound. As usual, types may be specified for (some of)
the variables, so explicit bindings can be used as a central place for specifying types for the
variables, if necessary. The equivalent example with omitted binding is
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  "evn(0)" | "evn(n) \<Longrightarrow> evn(n+2)"\<close>}

Alternatively a rule \<open>P\<^sub>i\<close> may be specified in the structured form described in
Section~\ref{basic-theory-prop}:
@{theory_text[display]
\<open>"name term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k" if "Q\<^sub>i\<^sub>1" \<dots> "Q\<^sub>i\<^sub>q\<^sub>i" for x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i\<close>}
where the assumptions and variables may be grouped by \<^theory_text>\<open>and\<close> and types may be specified for (some
of) the variable groups, however, no names may be specified for assumption groups, because no proof
is specified for the rules. In this form the example is written
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  "evn(0)" | "evn(n+2)" if "evn(n)"\<close>}

The rules \<open>P\<^sub>i\<close> are introduction rules (see Section~\ref{basic-methods-rule}) for the defined
predicate \<open>name\<close> in the sense that they introduce a specific application of \<open>name\<close>, possibly
depending on other applications of \<open>name\<close>. An inductive definition turns the rules \<open>P\<^sub>i\<close> to valid
facts ``by definition'' under the fact set name \<open>name.intros\<close>. Explicit names for (some of) the
rules may be specified in the form
@{theory_text[display]
\<open>inductive name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
where rname\<^sub>1: P\<^sub>1 | \<dots> | rname\<^sub>n: P\<^sub>n\<close>}
Using this form the example can be written as
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  zero: "evn(0)" | step: "evn(n) \<Longrightarrow> evn(n+2)"\<close>}

Note that the syntax of the defining rules only allows to specify when the defined predicate is
\<open>True\<close>, not when it is \<open>False\<close>. In particular, a rule conclusion may not have the form of a negated
application \<open>\<not> name term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k\<close>.
\<close>

subsubsection "Semantics of an Inductive Definition"

text\<open>
To determine whether an application of the predicate to argument values yields the value \<open>True\<close>
the defining rules \<open>P\<^sub>i\<close> can be applied as introduction rules in backward reasoning steps (see
Section~\ref{basic-methods-rule}) until the predicate is not present anymore. However, depending
on the rules, this may not succeed. If the defining rules \<open>P\<^sub>i\<close> would be the only information
available about the defined predicate, it would be underspecified for such cases. The specific
property of an \<^emph>\<open>inductive\<close> definition is the additional regulation that in all such cases the
predicate value is \<open>False\<close>. In other words, if it is not possible to prove that the predicate value
is \<open>True\<close> by using the defining rules it is defined to be \<open>False\<close>. This can happen in two ways.

In the first case there is no rule for which the conclusion unifies with the predicate application
term. Consider the trivial inductive definition
@{theory_text[display]
\<open>inductive uspec\<^sub>1 :: "nat \<Rightarrow> bool" where "uspec\<^sub>1 3" | "uspec\<^sub>1 4"\<close>}
The rules only unify with applications of \<open>uspec\<^sub>1\<close> to the argument values \<open>3\<close> and \<open>4\<close>, for them it
can be derived that the predicate value is \<open>True\<close>. For all other arguments the value is \<open>False\<close>.

In the example the value of \<open>(evn 3)\<close> is \<open>False\<close> because an application of the defining rule \<open>step\<close>
as backwards reasoning step leads to \<open>(evn 1)\<close> which does not unify with the conclusion of either
rule.

In the second case there are rule conclusions which unify with the predicate application term, but
there is no finite sequence of backward rule application steps which removes all occurrences of the
predicate. Consider the inductive definition
@{theory_text[display]
\<open>inductive uspec\<^sub>2 :: "nat \<Rightarrow> bool" where "uspec\<^sub>2 i \<Longrightarrow> uspec\<^sub>2 i"\<close>}
Although the rule is trivially valid it cannot be used to prove that \<open>uspec\<^sub>2\<close> is \<open>True\<close> for any
argument value. Therefore its value is \<open>False\<close> for all arguments.
\<close>

subsubsection "Monotonicity Properties"

text\<open>
Actually, this way of implicit specification when the predicate value is \<open>False\<close> is only possible
if all assumptions \<open>Q\<^sub>i\<^sub>j\<close> used in the rules satisfy a ``monotonicity'' property for the defined
predicate. HOL is able to prove these properties for most forms of the assumptions \<open>Q\<^sub>i\<^sub>j\<close>
automatically and then prove the rules themselves and additional rules to be facts. In the
interactive editor these proof activities are displayed in the Output panel.

A common case where a rule assumption \<open>Q\<^sub>i\<^sub>j\<close> does not satisfy the monotonicity property is if it
contains an application of the defined predicate \<open>name\<close> in negated form. Consider the inductive
definition
@{theory_text[display]
\<open>inductive uspec\<^sub>3 :: "nat \<Rightarrow> bool" where "\<not> uspec\<^sub>3 i \<Longrightarrow> uspec\<^sub>3 i"\<close>}
Although if \<open>uspec\<^sub>3\<close> is defined as \<open>\<lambda>i. True\<close> it would satisfy the defining rule, the rule cannot
be used to prove that \<open>uspec\<^sub>3\<close> is \<open>True\<close> for any argument by applying the rule in backward reasoning
steps. Isabelle will signal an error for the inductive definition, stating that the monotonicity
proof failed for the assumption \<open>\<not> uspec\<^sub>3 i\<close>. Note that negation may also occur in other syntactic
forms like \<open>uspec\<^sub>3 i = False\<close> or \<open>uspec\<^sub>3 i \<Longrightarrow> i > 0\<close>.
\<close>

subsection "Fixed Arguments"
text_raw\<open>\label{holbasic-inductive-fixargs}\<close>

text\<open>
It may be the case that one or more arguments of the defined predicate are ``fixed'', i.e. in all
defining rules the values of these arguments in the conclusion are the same as in all assumptions.
If this is the case for the first \<open>m\<close> arguments the inductive definition can be specified in the
form
@{theory_text[display]
\<open>inductive name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
for y\<^sub>1 \<dots> y\<^sub>m
where P\<^sub>1 | \<dots> | P\<^sub>n\<close>}
The variables \<open>y\<^sub>i\<close> may be grouped by \<open>and\<close> and types may be specified for (some of) the groups.

Then the defining rules \<open>P\<^sub>i\<close> must have the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> name y\<^sub>1 \<dots> y\<^sub>m term\<^sub>i\<^sub>(\<^sub>m\<^sub>+\<^sub>1\<^sub>) \<dots> term\<^sub>i\<^sub>k\<close>}
and every occurrence of \<open>name\<close> in the \<open>Q\<^sub>i\<^sub>j\<close> must also have \<open>y\<^sub>1 \<dots> y\<^sub>m\<close> as its first \<open>m\<close> arguments.

Specifying fixed arguments is optional, it does not have any effect on the defined predicate,
however it makes the rules provided by HOL about the predicate simpler (see below).

As an example consider the inductive definition of a divides predicate
@{theory_text[display]
\<open>inductive divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
for m
where "divides m 0" | "divides m n \<Longrightarrow> divides m (n+m)"\<close>}\<close>

subsection \<open>The {\sl cases} Rule\<close>
text_raw\<open>\label{holbasic-inductive-cases}\<close>

text\<open>
The general form of inductive definition constructs and automatically proves the additional rule
@{text[display]
\<open>\<lbrakk>name ?a\<^sub>1 \<dots> ?a\<^sub>k; RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>?a\<^sub>1=term\<^sub>i\<^sub>1; \<dots>; ?a\<^sub>k=term\<^sub>i\<^sub>k; Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> ?P\<close>}
and names it \<open>name.cases\<close>.

This rule has the form of an elimination rule for the predicate as described in
Section~\ref{basic-case-elim}. The major premise is the application \<open>name ?a\<^sub>1 \<dots> ?a\<^sub>k\<close> of the
defined predicate to arbitrary arguments. When the rule is applied by the methods \<^theory_text>\<open>erule\<close> or
\<^theory_text>\<open>cases\<close> to a goal it removes a predicate application from the goal assumptions or the input facts,
respectively, and splits the goal into cases according to the defining rules of the predicate.
The named cases created by the \<^theory_text>\<open>cases\<close> method are named by numbers starting with 1.

The \<open>cases\<close> rule for the evenness example is \<open>evn.cases\<close>:
@{text[display]
\<open>\<lbrakk>evn ?a; ?a = 0 \<Longrightarrow> ?P; \<And>n. \<lbrakk>?a = n + 2; evn n\<rbrakk> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}

Since it is a case rule it can be displayed by \<^theory_text>\<open>print_statement\<close> in the alternative form (see
Section~\ref{basic-case-reasoning}):
@{theory_text[display]
\<open>fixes a\<^sub>1 \<dots> a\<^sub>k
assumes "name a\<^sub>1 \<dots> a\<^sub>k"
obtains C\<^sub>1 | \<dots> | C\<^sub>n\<close>}
where every case \<open>C\<^sub>i\<close> has the form
@{theory_text[display]
\<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i where "a\<^sub>1=term\<^sub>i\<^sub>1" \<dots> "a\<^sub>k=term\<^sub>i\<^sub>k" "Q\<^sub>i\<^sub>1" \<dots> "Q\<^sub>i\<^sub>q\<^sub>i"\<close>}

Together with \<open>name.cases\<close> the similar rule \<open>name.simps\<close> is provided. It is an equation which
substitutes an arbitrary application of \<open>name\<close> by a disjunction of the cases according to the
defining \<open>P\<^sub>i\<close> and may be used by the simplifier (see Section~\ref{basic-methods-simp}). It is not
added to the simpset automatically, because its application may not terminate (e.g., for \<open>uspec\<^sub>2\<close>
as below).
\<close>

subsubsection "Effect of Fixed Arguments"

text\<open>
If the first \<open>m\<close> predicate arguments are fixed by \<open>for y\<^sub>1 \<dots> y\<^sub>m\<close> as above, \<open>name.cases\<close> has the
simpler form
@{text[display]
\<open>\<lbrakk>name ?y\<^sub>1 \<dots> ?y\<^sub>m ?a\<^sub>1 \<dots> ?a\<^sub>(\<^sub>k\<^sub>-\<^sub>m\<^sub>); RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. 
\<lbrakk>?a\<^sub>1=term\<^sub>i\<^sub>(\<^sub>m\<^sub>+\<^sub>1\<^sub>); \<dots>; ?a\<^sub>(\<^sub>k\<^sub>-\<^sub>m\<^sub>)=term\<^sub>i\<^sub>k; Q\<^sub>i\<^sub>1'; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i'\<rbrakk> \<Longrightarrow> ?P\<close>}
and in the \<open>Q\<^sub>i\<^sub>j'\<close> all applications of \<open>name\<close> have the unknowns \<open>?y\<^sub>1 \<dots> ?y\<^sub>m\<close> as their first arguments.
In other words, the unknowns from the major premise are directly used in place of the first \<open>m\<close>
arguments in all predicate applications without the need of corresponding equations. Therefore
the rule \<open>divides.cases\<close> for the divides predicate above is
@{text[display]
\<open>\<lbrakk>dvds ?m ?a; ?a = 0 \<Longrightarrow> ?P; \<And>n. \<lbrakk>?a = n + ?m; dvds ?m n\<rbrakk> \<Longrightarrow> ?P\<rbrakk>
\<Longrightarrow> ?P\<close>}
\<close>

subsubsection "Using the \<open>cases\<close> Rule"

text\<open>
Due to its form the rule \<open>name.cases\<close> includes information about the implicit definition of \<open>False\<close>
predicate values. If a predicate application does not unify with the conclusion of any \<open>P\<^sub>i\<close> there
will be atleast one assumption \<open>?a\<^sub>j=term\<^sub>i\<^sub>j\<close> in every \<open>RA\<^sub>i\<close> which is false and thus makes \<open>RA\<^sub>i\<close>
solved as a goal. Together that proves that the predicate application implies arbitrary propositions
which means that it is \<open>False\<close>.

Consider the predicate \<open>uspec\<^sub>1\<close> defined as above. The rule \<open>uspec\<^sub>1.cases\<close> is
@{text[display]
\<open>\<lbrakk>uspec\<^sub>1 ?a; ?a=3 \<Longrightarrow> ?P; ?a=4 \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
The proposition \<open>uspec\<^sub>1 0 = False\<close> is equivalent to \<open>uspec\<^sub>1 0 \<Longrightarrow> False\<close> (because the other
direction is trivially valid) which can be proved as follows:
@{theory_text[display]
\<open>theorem "uspec\<^sub>1 0 \<Longrightarrow> False"
  apply (erule uspec\<^sub>1.cases)
  by simp_all\<close>}
The application of \<open>uspec\<^sub>1.cases\<close> creates the goals \<open>0=3 \<Longrightarrow> False\<close> and \<open>0=4 \<Longrightarrow> False\<close> which are
solved by the simplifier.

Note that this does not work for the predicate \<open>uspec\<^sub>2\<close>. For it \<open>uspec\<^sub>2.cases\<close> is
@{text[display]
\<open>\<lbrakk>uspec\<^sub>2 ?a; \<And>i. \<lbrakk>?a = i; uspec\<^sub>2 i\<rbrakk> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
and the application by \<^theory_text>\<open>erule\<close> to \<open>uspec\<^sub>2 0 \<Longrightarrow> False\<close> yields the goal \<open>\<And>i. \<lbrakk>0 = i; uspec\<^sub>2 i\<rbrakk> \<Longrightarrow>
False\<close> which is equivalent to the original goal. Therefore even an iterated application by \<^theory_text>\<open>erule\<close>
will not solve the goal in a finite number of steps.
\<close>

subsubsection "The \<open>cases\<close> Rule in Structured Proofs"

text\<open>
The rule \<open>name.cases\<close> is attributed by \<open>[consumes 1]\<close>, so that it can be applied by the \<^theory_text>\<open>cases\<close>
method in structured proofs (see Section~\ref{basic-case-elim}). The example above can be written
@{theory_text[display]
\<open>theorem "False" if "uspec\<^sub>1 0"
  using that
proof (cases rule: uspec\<^sub>1.cases) qed simp_all\<close>}
Note the use of the structured theorem form to put \<open>uspec\<^sub>1 0\<close> into the proof context with name
\<open>that\<close> so that it is input by \<^theory_text>\<open>using that\<close> into the structured proof and its initial method
\<^theory_text>\<open>cases\<close> which consumes it.

Moreover, the rule \<open>name.cases\<close> is associated to the defined predicate \<open>name\<close> in the following way:
if the first input fact to the \<^theory_text>\<open>cases\<close> method has an inductively defined predicate \<open>name\<close> as its
outermost function, the rule \<open>name.cases\<close> is the default rule applied by the method if no rule is
explicitly specified. So the proof for \<open>"False" if "uspec\<^sub>1 0"\<close> above can be abbreviated to
@{theory_text[display]
\<open>proof cases qed simp_all\<close>}
or even shorter (see Section~\ref{basic-proof-struct}):
@{theory_text[display]
\<open>by cases simp_all\<close>}
Note that this only works if the consumed predicate application is taken as input fact, not if it
is a goal assumption as in the proof script above.
\<close>

subsection "The Induction Rule"
text_raw\<open>\label{holbasic-inductive-induct}\<close>

text\<open>
The general form of inductive definition also constructs and automatically proves the additional
rule
@{text[display]
\<open>\<lbrakk>name ?a\<^sub>1 \<dots> ?a\<^sub>k; RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P ?a\<^sub>1 \<dots> ?a\<^sub>k\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1'; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i'\<rbrakk> \<Longrightarrow> ?P term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k\<close>}
and in the \<open>Q\<^sub>i\<^sub>j'\<close> every application \<open>name t\<^sub>1 \<dots> t\<^sub>k\<close> of the predicate to argument terms is replaced
by the conjunction \<open>name t\<^sub>1 \<dots> t\<^sub>k \<and> ?P t\<^sub>1 \<dots> t\<^sub>k\<close>. The rule is named \<open>name.induct\<close>.

This rule has the form of an induction rule extended by elimination for the predicate as described
in Section~\ref{basic-case-induction}. The major premise is the application \<open>name ?a\<^sub>1 \<dots> ?a\<^sub>k\<close> of the
defined predicate to arbitrary arguments. The rule is attributed by \<open>[consumes 1]\<close>. When it is
applied by the methods \<^theory_text>\<open>induct\<close> or \<^theory_text>\<open>induction\<close> to a goal it consumes a predicate application from
the input facts or the goal assumptions and splits the goal into cases according to the defining
rules of the predicate. The named cases created by the induction methods are named by numbers
starting with 1.

The induction rule for the evenness example is \<open>evn.induct\<close>:
@{text[display]
\<open>\<lbrakk>evn ?a; ?P 0; \<And>n. \<lbrakk>evn n; ?P n\<rbrakk> \<Longrightarrow> ?P (n + 2)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}
\<close>

subsubsection "Using the Induction Rule"

text\<open>
The induction rule can be used to prove properties about the defined predicate \<open>name\<close> which may
involve an iterated application of the defining rules. It abstracts the goal conclusion to a
function with the same arguments as \<open>name\<close> and then splits it together with the predicate according
to the predicate's defining rules. See the Isabelle documentation for corresponding proof
techniques.

Like \<open>name.cases\<close> the rule \<open>name.induct\<close> includes information about the implicit definition of
\<open>False\<close> predicate values. It covers the cases where a predicate application unifies with the
conclusion of a \<open>P\<^sub>i\<close> but cannot be reduced in a finite number of backwards reasoning steps.

Consider the predicate \<open>uspec\<^sub>2\<close> defined as above. The rule \<open>uspec\<^sub>2.induct\<close> is
@{text[display]
\<open>\<lbrakk>uspec\<^sub>2 ?x; \<And>i. \<lbrakk>uspec\<^sub>2 i; ?P i\<rbrakk> \<Longrightarrow> ?P i\<rbrakk> \<Longrightarrow> ?P ?x\<close>}
The proposition \<open>uspec\<^sub>2 0 \<Longrightarrow> False\<close> can be proved as follows:
@{theory_text[display]
\<open>theorem "uspec\<^sub>2 0 \<Longrightarrow> False"
  apply (induction rule: uspec\<^sub>2.induct)
  by simp\<close>}
The application of \<open>uspec\<^sub>2.induct\<close> creates the goal \<open>\<And>i. \<lbrakk>uspec\<^sub>2 i; False\<rbrakk> \<Longrightarrow> False\<close> which is
solved by the simplifier. Actually, this works also for the proposition \<open>uspec\<^sub>2 i \<Longrightarrow> False\<close>
because the conclusion does not depend on the argument of \<open>uspec\<^sub>2\<close>

Note that this does not work for the predicate \<open>uspec\<^sub>1\<close>. For it \<open>uspec\<^sub>1.induct\<close> is
@{text[display]
\<open>\<lbrakk>uspec\<^sub>1 ?x; ?P 3; ?P 4\<rbrakk> \<Longrightarrow> ?P ?x\<close>}
and the application by \<^theory_text>\<open>induction\<close> to \<open>uspec\<^sub>1 0 \<Longrightarrow> False\<close> yields two goals \<open>False\<close> which cannot be
proved.
\<close>

subsubsection "The Induction Rule in Structured Proofs"

text\<open>
Like \<open>name.cases\<close> the rule \<open>name.induct\<close> can also be applied in structured proofs (see
Section~\ref{basic-case-induction}). The example above can be written
@{theory_text[display]
\<open>theorem "False" if "uspec\<^sub>2 0"
  using that
proof (induct rule: uspec\<^sub>2.induct) qed simp\<close>}

Moreover, the rule \<open>name.induct\<close> is associated to the defined predicate \<open>name\<close> in the following way:
if the first input fact to the \<^theory_text>\<open>induction\<close> or \<^theory_text>\<open>induct\<close> method has an inductively defined predicate
\<open>name\<close> as its outermost function, the rule \<open>name.induct\<close> is the default rule applied by the methods
if no rule is explicitly specified. So the proof for \<open>"False" if "uspec\<^sub>2 0"\<close> above can be
abbreviated to
@{theory_text[display]
\<open>proof induction qed simp\<close>}
or even shorter:
@{theory_text[display]
\<open>by induction simp\<close>}\<close>

subsection "Single-Step Inductive Definitions"
text_raw\<open>\label{holbasic-inductive-singlestep}\<close>

text\<open>
A simple case is an inductive definition where no rule assumption \<open>Q\<^sub>i\<^sub>j\<close> contains an application
of the defined predicate \<open>name\<close>. Then for every defining rule a single backward reasoning step
will remove the predicate and determine its value. The rule \<open>name.cases\<close> contains the complete
information about the defined predicate and is sufficient for proving arbitrary properties about
it.

Every predicate defined by an Isabelle definition (see Section~\ref{basic-theory-definition})
@{theory_text[display]
\<open>definition name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
  where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
is equivalent to the predicate defined by the inductive definition
@{theory_text[display]
\<open>inductive name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
  where "term \<Longrightarrow> name x\<^sub>1 \<dots> x\<^sub>n"\<close>}
Thus inductive definitions are a generalization of the basic Isabelle definitions for predicates.

Here \<open>name\<close> cannot occur in \<open>term\<close> because Isabelle definitions do not support recursion, therefore
it is a single-step inductive definition with only one rule. Vice versa, everey single-step
inductive definition can be converted to an Isabelle definition, where the \<open>term\<close> is mainly a
disjunction of the left sides of all defining rules. Actually, for this case the rule \<open>name.simps\<close>
(see above) is equivalent to the defining equation of the corresponding Isabelle definition.

For such predicates it is often simpler to use an Isabelle definition. However, if there are
a lot of alternative cases in \<open>term\<close> it may be easier to use the form of an inductive definition.
Note also, that there are predicates which cannot be defined by an Isabelle definition but can be
defined by a (non-single-step) inductive definition.
\<close>

subsection "Mutually Inductive Definitions"
text_raw\<open>\label{holbasic-inductive-mutual}\<close>

text\<open>
Inductively defined predicates may depend on each other. Then they must be defined by a common
inductive definition of the extended form
@{theory_text[display]
\<open>inductive name\<^sub>1 \<dots> name\<^sub>m
where P\<^sub>1 | \<dots> | P\<^sub>n\<close>}
The \<open>name\<^sub>i\<close> may be grouped by \<open>and\<close> and types may be specified for (some of) the groups.

The defining rules \<open>P\<^sub>i\<close> have the same form as described above, however, every conclusion may be an
application of one of the defined predicates \<open>name\<^sub>i\<close> (with arbitrary ordering of the rules) and
every rule assumption \<open>Q\<^sub>i\<^sub>j\<close> may contain applications of all defined predicates.

The following example defines predicates for even and odd numbers in a mutually inductive way:
@{theory_text[display]
\<open>inductive evn odd :: "nat \<Rightarrow> bool" where
  "evn(0)" | "odd(n) \<Longrightarrow> evn(n+1)" | "evn(n) \<Longrightarrow> odd(n+1)"\<close>}

The set of defining rules is named \<open>name\<^sub>1_\<dots>_name\<^sub>m.intros\<close>. For every \<open>name\<^sub>i\<close> separate rules
\<open>name\<^sub>i.cases\<close> and \<open>name\<^sub>i.simps\<close> are created which cover only the defining rules with \<open>name\<^sub>i\<close> in
the conclusion. As induction rules the set \<open>name\<^sub>1_\<dots>_name\<^sub>m.inducts\<close> is created containing for every
\<open>name\<^sub>i\<close> an induction rule with an application of \<open>name\<^sub>i\<close> as major premise. Additionally, a rule
\<open>name\<^sub>1_\<dots>_name\<^sub>m.induct\<close> is generated without elimination where the conclusion is an explicit case
distinction for all defined predicates.

For the example the rule \<open>evn_odd.induct\<close> is
@{text[display]
\<open>\<lbrakk>?P1 0; \<And>n. \<lbrakk>odd n; ?P2 n\<rbrakk> \<Longrightarrow> ?P1 (n + 1);
  \<And>n. \<lbrakk>evn n; ?P1 n\<rbrakk> \<Longrightarrow> ?P2 (n + 1)\<rbrakk>
\<Longrightarrow> (evn ?x1 \<longrightarrow> ?P1 ?x1) \<and> (odd ?x2 \<longrightarrow> ?P2 ?x2)\<close>}\<close>

section "Well-Founded Relations"
text_raw\<open>\label{holbasic-wellfounded}\<close>

text\<open>
A binary relation \<open>r\<close> of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> (i.e., the related values are of the same type) is
called ``well-founded'' if every non-empty set of values of type \<open>t\<close> has a ``leftmost'' element \<open>x\<close>
for \<open>r\<close> which means that there is no \<open>y\<close> so that \<open>r y x\<close>. If the relation \<open>(<)\<close> (see
Section~\ref{holbasic-equal-order}) is well-founded for a type \<open>t\<close> this is usually described by
``every non-empty set has a minimal element''. 

HOL provides the predicate
@{text[display]
\<open>wfP :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>}
which tests an arbitrary binary relation for being well-founded. The predicate
@{text[display]
\<open>wf :: ('a \<times> 'a) set \<Rightarrow> bool\<close>}
does the same for a binary relation in tuple set form (see Section~\ref{holbasic-tuples-rel}).

For a well-founded relation of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> also the universal set \<open>UNIV :: t set\<close>
(see Section~\ref{holtypes-set-values}) has a leftmost element, which is the leftmost value of type
\<open>t\<close>. Moreover, from that value all other values of type \<open>t\<close> can be reached in a finite number of
steps to a related value, or, if the relation is transitive, even by a single step.

The best-known well-founded relation is the strict less-order \<open>(<)\<close> on the natural numbers. Note
that \<open>(\<le>)\<close> is not well-founded because for every number \<open>n\<close> there is \<open>n\<close> itself so that \<open>n \<le> n\<close>.
\<close>

subsection "Induction"
text_raw\<open>\label{holbasic-wellfounded-induction}\<close>

text\<open>
For every well-founded relation \<open>r\<close> the following principle of (transfinite) induction is valid:
If a property holds for a value whenever it holds for all values ``left'' to it, the property holds
for all values.

HOL provides the induction rules with elimination (see Section~\ref{basic-case-induction})

@{text\<open>wfP_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=2] wfP_induct_rule}
@{text\<open>wf_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=2] wf_induct_rule}

Their major premise is well-foundedness of the relation \<open>?r\<close>. The single case corresponds to the
induction principle.
\<close>

subsection "The Accessible Part of a Relation"
text_raw\<open>\label{holbasic-wellfounded-accp}\<close>

text\<open>
For an arbitrary binary relation \<open>r\<close> of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> generally not all values of \<open>t\<close> can be
reached in a finite number of relation steps from a leftmost element. HOL defines the predicate
\<open>Wellfounded.accp\<close> by the inductive definition (see Section~\ref{holbasic-inductive})
@{theory_text[display]
\<open>inductive accp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where "(\<And>y. r y x \<Longrightarrow> accp r y) \<Longrightarrow> accp r x"\<close>}
Its partial application \<open>accp r\<close> to a binary relation \<open>r\<close> is the predicate which is \<open>True\<close> for all
values of \<open>t\<close> which can be reached in a finite number of relation steps from a leftmost element.
These values are called the ``accessible part'' of relation \<open>r\<close>.

HOL also defines the equivalent set-valued function (see Section~\ref{holbasic-pred-set}) for
relations represented as tuple sets (see Section~\ref{holbasic-tuples-rel})
@{text[display]
\<open>acc :: "('a \<times> 'a) set \<Rightarrow> 'a set"\<close>}
which returns the accessible part of a relation as a set.

A binary relation \<open>r\<close> of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> is well-founded if and only if its accessible part
\<open>accp r\<close> covers all values of \<open>t\<close>. If \<open>r\<close> is not well-founded there may be several leftmost values
in \<open>t\<close> or no such value (in the latter case the accessible part is empty).

For arbitrary binary relations the induction principle can be used on the accessible part. The
corresponding induction rules provided by HOL are

@{text\<open>accp_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=1] accp_induct_rule}

@{text\<open>acc_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=1] acc_induct_rule}

Here the major premise is that the value \<open>?a\<close> for which the property shall be proved belongs to the
accessible part of the relation. Also the induction step is only done for values in the accessible
part (if a value is in the accessible part then also all values ``left'' to it).
\<close>

subsection "Measure Functions"
text_raw\<open>\label{holbasic-wellfounded-measure}\<close>

text\<open>
A binary relation \<open>r\<close> of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> is well-founded if it is mapped by a function
\<open>f :: t \<Rightarrow> u\<close> into a well-founded relation \<open>s\<close> on type \<open>u\<close>. This is the case if
\<open>r x y \<Longrightarrow> s (f x) (f y)\<close> for all values \<open>x\<close> and \<open>y\<close> of type \<open>t\<close>.

This property is often used to prove well-foundedness for a binary relation \<open>r\<close> by specifically
mapping it into the well-founded order \<open>(<)\<close> on type \<open>nat\<close>. In this context the mapping function
\<open>f :: t \<Rightarrow> nat\<close> is called a ``measure function''.

HOL provides the polymorphic function
@{text[display]
\<open>measure :: ('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set\<close>}
which turns a measure function for values of an arbitrary type \<open>'a\<close> to a relation on \<open>'a\<close> in tuple
set form. The relation \<open>measure f\<close> relates values \<open>x\<close> and \<open>y\<close> if \<open>(f x) < (f y)\<close>.

The usual way to prove that a relation \<open>r\<close> of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> is well-founded is to design
a measure function \<open>f :: t \<Rightarrow> nat\<close> and prove that \<open>r x y \<Longrightarrow> (measure f) x y\<close>.
\<close>

subsection \<open>The {\sl size} Function\<close>
text_raw\<open>\label{holbasic-wellfounded-size}\<close>

text\<open>
HOL introduces the polymorphic function
@{text[display]
\<open>size :: 'a \<Rightarrow> nat\<close>}
which is overloaded for many HOL types. If it is not supported for a type an application to a value
of that type will result in an error message ``No type arity ...''.

The \<open>size\<close> function is intended as a standard measure function for proving well-foundedness of
relations on type \<open>'a\<close> with the help of the function \<open>measure\<close>. However, there may be relations
where this does not work and a different measure function is required.

Note that the concept of \<open>size\<close> and \<open>measure\<close> actually depends on the specific HOL type \<open>nat\<close>, which
is introduced in Section~\ref{holtypes-nat}.
\<close>

section \<open>The Proof Method {\sl atomize\_elim}\<close>
text_raw\<open>\label{holbasic-atomize}\<close>

text\<open>
As a useful method for proving elimination rules (see Section~\ref{basic-case-elim}) including the
more specific case rules (see Section~\ref{basic-case-reasoning}) and the goals of \<^theory_text>\<open>obtain\<close>
statements (see Section~\ref{basic-proof-obtain}) HOL introduces the proof method
@{theory_text[display]
\<open>atomize_elim\<close>}
It only affects the first goal. Assume that this goal has the form of an elimination rule
@{theory_text[display]
\<open>theorem "\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m; P\<^sub>1; \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> P" \<proof>\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>1\<dots>x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1;\<dots>;Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> P\<close>}
(see Section~\ref{basic-case-elim}). The method converts the goal to the form
@{theory_text[display]
\<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>m\<rbrakk> \<Longrightarrow> D\<^sub>1 \<or> \<dots> \<or> D\<^sub>p\<close>}
where every \<open>D\<^sub>i\<close> has the form \<open>\<exists>x\<^sub>i\<^sub>1\<dots>x\<^sub>i\<^sub>p\<^sub>i. Q\<^sub>i\<^sub>1 \<and> \<dots> \<and> Q\<^sub>i\<^sub>q\<^sub>i\<close>. For the quantifier \<open>\<exists>\<close> and the boolean
operators \<open>\<or>\<close> and \<open>\<and>\<close> see Section~\ref{holtypes-bool-funcs}. Because the converted goal does not
contain the technical variable \<open>P\<close> any more and uses the boolean operators it is sometimes easier
to prove it.

If the method is applied to the initial goal of the example elimination rule theorem
@{theory_text[display]
\<open>theorem elimexmp: "\<lbrakk>(x::nat) \<le> c; x < c \<Longrightarrow> P; x = c \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"\<close>}
in Section~\ref{basic-case-elim} it converts the goal to
@{text[display]
\<open>x \<le> c \<Longrightarrow> x < c \<or> x = c\<close>}
which can be solved by method \<open>auto\<close>.

If \<open>atomize_elim\<close> is applied to the initial goal of the example case rule theorem
@{theory_text[display]
\<open>theorem mycaserule: "\<lbrakk>n = 0 \<Longrightarrow> P; n \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"\<close>}
in Section~\ref{basic-case-reasoning} it converts the goal to
@{text[display]
\<open>n = 0 \<or> n \<noteq> 0\<close>}
which can be solved by method \<open>simp\<close>.

If \<open>atomize_elim\<close> is applied to the initial goal of the example \<^theory_text>\<open>obtain\<close> statement
@{theory_text[display]
\<open>obtain y z where "x = y - 3" and "y + z = 2*x +8"\<close>}
in Section~\ref{basic-proof-obtain} it converts the goal to
@{text[display]
\<open>\<exists>y z. x = y - 3 \<and> y + z = 2 * x + 8\<close>}
which can be solved by method \<open>arith\<close> (see Section~\ref{basic-methods-auto}).
\<close>

section "Recursive Functions"
text_raw\<open>\label{holbasic-recursive}\<close>

text\<open>
HOL supports the definition of recursive functions in the form
@{theory_text[display]
\<open>function name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n \<proof>\<close>}
The type specification for the function may be omitted if it can be derived from the use of the
function in the \<open>eq\<^sub>i\<close>.

The definition resembles an Isabelle definition as described in
Section~\ref{basic-theory-definition}, but instead of a single defining equation there may be
arbitrary many defining equations \<open>eq\<^sub>i\<close> followed by a proof. Also other than for an Isabelle
definition the part \<^theory_text>\<open>name \<dots> where\<close> cannot be omitted, because the \<open>name\<close> must be known to check
whether the equations have the correct form.

Compared with the inductive definitions in Section~\ref{holbasic-inductive} recursive
functions can not only be predicates but may have an arbitrary result type and equations are used
instead of defining rules.
\<close>

subsection "The Defining Equations"
text_raw\<open>\label{holbasic-recursive-defeqs}\<close>

text\<open>
Each of the defining equations \<open>eq\<^sub>i\<close> has the general form of a derivation rule (see
Section~\ref{basic-theory-prop}) with an equation as its conclusion:
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> name term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k = term\<^sub>i\<close>}
It is specified in inner syntax. The separating bars \<open>|\<close> belong to the outer syntax, therefore each
equation must be separately quoted. Note that the conclusion must be an equation using the symbol
\<open>=\<close> instead of \<open>\<equiv>\<close>. The left side of the equation is restricted to the form of a (non-partial)
application of the defined function to argument terms, i.e., if the defined function has \<open>k\<close>
arguments according to its type, in every equation it must be applied to \<open>k\<close> terms. If the
conclusion is no equation or if the left side has a different form an error is signaled.

Other than in an Isabelle definition the equations may be recursive, i.e. the defined function
\<open>name\<close> may be used in \<open>term\<^sub>i\<close> on the right side of the equation (but not in the \<open>Q\<^sub>i\<^sub>j\<close> or \<open>term\<^sub>i\<^sub>j\<close>).
It may be used in arbitrary ways, also by partial application or by passing it as argument to other
functions.

The familiar example of the faculty function can be defined using two defining equations in the form
@{theory_text[display]
\<open>function fac :: "nat \<Rightarrow> nat" where
  "fac 0 = 1"
| "\<And>n. n > 0 \<Longrightarrow> fac n = n * fac (n-1)"
\<proof>\<close>}

The bound variables \<open>x\<^sub>1, \<dots>, x\<^sub>i\<^sub>p\<^sub>i\<close> may occur in the assumptions and in the conclusion. However, if
a bound variable occurs in \<open>term\<^sub>i\<close> on the right side it must also occur in one or more of the
\<open>term\<^sub>i\<^sub>j\<close> on the left side, otherwise an error is signaled.

After termination has been proved (see the subsection on termination below) for the recursive
function definition the defining equations are available as the fact set
\<open>name.simps\<close>. Note that no defining equation \<open>name_def\<close> (see Section~\ref{basic-theory-theorem})
exists for recursively defined functions, instead the set \<open>name.simps\<close> plays the corresponding role.
\<close>

subsubsection "Alternative Rule Forms"

text\<open>
As for other derivation rules on theory
level (see Section~\ref{basic-theory-prop}) the explicit bindings are optional, variables occurring
free in the assumptions or the conclusion are always automatically bound. As usual, types may be
specified for (some of) the variables, so explicit bindings can be used as a central place for
specifying types for the variables, if necessary. An equivalent definition for the faculty is
@{theory_text[display]
\<open>function fac :: "nat \<Rightarrow> nat" where
  "fac 0 = 1"
| "n > 0 \<Longrightarrow> fac n = n * fac (n-1)"
\<proof>\<close>}
where the binding of \<open>n\<close> is omitted.

Alternatively an equation \<open>eq\<^sub>i\<close> may be specified in the structured form described for derivation
rules in Section~\ref{basic-theory-prop}:
@{theory_text[display]
\<open>"name term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k = term\<^sub>i" if "Q\<^sub>i\<^sub>1" \<dots> "Q\<^sub>i\<^sub>q\<^sub>i" for x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i\<close>}
where the assumptions and variables may be grouped by \<open>and\<close> and types may be specified for (some of)
the variable groups, however, no names may be specified for assumption groups.

In this form the faculty definition becomes
@{theory_text[display]
\<open>function fac :: "nat \<Rightarrow> nat" where
  "fac 0 = 1"
| "fac n = n * fac (n-1)" if "n > 0"
\<proof>\<close>}

Note that on the left side of the equations the arguments may be specified by arbitrary terms, not
only by variables. Therefore the faculty function can also be defined in the form
@{theory_text[display]
\<open>function fac2 :: "nat \<Rightarrow> nat" where
  "fac2 0 = 1"
| "fac2 (n+1) = (n+1) * fac2 n"
\<proof>\<close>}
where the assumption is not required anymore for the second equation.

It is also possible to explicitly name (some of) the single equations by specifying the recursive
definition in the form
@{theory_text[display]
\<open>function name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type" where 
  eqname\<^sub>1: eq\<^sub>1 | \<dots> | eqname\<^sub>n: eq\<^sub>n \<proof>\<close>}

Every function \<open>name\<close> defined by the Isabelle definition (see Section~\ref{basic-theory-definition})
@{theory_text[display]
\<open>definition name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
  where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
is equivalent to the function defined by the recursive definition
@{theory_text[display]
\<open>function name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
  where name_def: "name x\<^sub>1 \<dots> x\<^sub>n = term" \<proof>\<close>}
which actually does not use recursion.
\<close>

subsection "Covering All Arguments"
text_raw\<open>\label{holbasic-recursive-cover}\<close>

text\<open>
As described in Section~\ref{basic-theory-terms} functions in Isabelle must be total, they must be
defined for all possible arguments. It is easy to fail doing so when specifying the defining
equations for a recursive function definition. Consider
@{theory_text[display]
\<open>function nototal :: "nat \<Rightarrow> nat" where
  "nototal 5 = 6" \<proof>\<close>}
The function is only defined for the value \<open>5\<close>, no definition is given for the other natural
numbers.

Therefore HOL expects a proof that the equations are complete in the sense that they cover all
possible cases for the function arguments. In the general case it creates a goal of the form
@{text[display]
\<open>\<And>P x.
  \<lbrakk>\<And>x\<^sub>1\<^sub>1 \<dots> x\<^sub>1\<^sub>p\<^sub>1. \<lbrakk>Q\<^sub>1\<^sub>1; \<dots>; Q\<^sub>1\<^sub>q\<^sub>1; x = (term\<^sub>1\<^sub>1, \<dots>, term\<^sub>1\<^sub>k)\<rbrakk> \<Longrightarrow> P;
     \<dots>
   \<And>x\<^sub>n\<^sub>1 \<dots> x\<^sub>n\<^sub>p\<^sub>n. \<lbrakk>Q\<^sub>n\<^sub>1; \<dots>; Q\<^sub>n\<^sub>q\<^sub>n; x = (term\<^sub>n\<^sub>1, \<dots>, term\<^sub>n\<^sub>k)\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P\<close>}
which must be proved in the recursive function definition's \<open>\<proof>\<close>. This goal has the form of a
case rule (see Section~\ref{basic-case-reasoning}) before replacing the variable \<open>P\<close> by an unknown
upon turning it to a fact. It specifies that \<open>x\<close> covers all possible cases. The variable \<open>x\<close> is set
to the tuples of all the argument terms used on the left side of all equations.

Using tuples here depends on the specific HOL type constructor \<open>prod\<close>, which is introduced in
Section~\ref{holtypes-tup}. The goal could also be constructed without using tuples, however, it is
more compact like that.

Note that the goal does not mention the defined function \<open>name\<close> at all. It is only about the
groups of the argument terms in the equations.

For the faculty function defined as above the goal is
@{text[display]
\<open>\<And>P (x::nat). \<lbrakk>x = 0 \<Longrightarrow> P; \<And>n. \<lbrakk>0 < n; x = n\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>}
It can be proved by method \<open>auto\<close> (see Section~\ref{basic-methods-auto}).

 After the proof of the recursive function definition the goal is available as a case rule
named \<open>name.cases\<close>. If applied by the proof method \<open>cases\<close> (see Section~\ref{basic-case-reasoning})
it splits a goal and introduces named cases (named by numbers starting at 1) according to the
argument regions in the defining equations of function \<open>name\<close>.

If the function \<open>name\<close> has only one argument \<open>name.cases\<close> is a usual case rule for the argument
type, otherwise it is a case rule for the type of the argument tuples.
\<close>

subsubsection "Using Proof Method \<open>atomize_elim\<close>"


text\<open>
 Since the goal has the form of a case rule the method \<open>atomize_elim\<close> (see
Section~\ref{holbasic-atomize}) can be applied to it. It converts the general form of the goal
to the form
@{text[display]
\<open>\<And>x.
    (\<exists> x\<^sub>1\<^sub>1 \<dots> x\<^sub>1\<^sub>p\<^sub>1. Q\<^sub>1\<^sub>1 \<and> \<dots> \<and> Q\<^sub>1\<^sub>q\<^sub>1 \<and> x = (term\<^sub>1\<^sub>1, \<dots>, term\<^sub>1\<^sub>k)
  \<or> \<dots> 
  \<or> (\<exists> x\<^sub>n\<^sub>1 \<dots> x\<^sub>n\<^sub>p\<^sub>n. Q\<^sub>n\<^sub>1 \<and> \<dots> \<and> Q\<^sub>n\<^sub>q\<^sub>n \<and> x = (term\<^sub>n\<^sub>1, \<dots>, term\<^sub>n\<^sub>k)\<close>}
which directly expresses that the cases together cover all possibilities and may be easier to prove. 
In many simple cases of recursive function definitions, however, the method is not necessary and
the goal can be proved by an automatic method like \<open>auto\<close> or \<open>blast\<close> (see
Section~\ref{basic-methods-auto}).

 For the faculty function defined as above the converted goal is
@{text[display]
\<open>\<And>x::nat. x = 0 \<or> (\<exists>n. n > 0 \<and> x = n)\<close>}
which can also be proved by method \<open>auto\<close>, so the method \<open>atomize_elim\<close> is not necessary here.
\<close>

subsubsection "Recursive Definitions vs. Inductive Definitions"

text\<open>
In principle an inductively defined predicate \<open>name\<close> (see Section~\ref{holbasic-inductive}) could
be defined recursively by adding the cases where it has the value \<open>False\<close>, so that all arguments
are covered. The evenness predicate from Section~\ref{holbasic-inductive-defrules} can be defined by
@{theory_text[display]
\<open>function evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True" | "evn 1 = False" | "evn (n+2) = evn n"
\<proof>\<close>}
because the cases \<open>0\<close>, \<open>1\<close>, and \<open>n+2\<close> cover all natural numbers.

However, this is not always possible. It may not be possible to give an explicit specification for
the arguments where the predicate value is \<open>False\<close> or the termination proof (see
Section~\ref{holbasic-recursive-term}) may fail.

Generally, an inductive definition is simpler because it only specifies the positive cases and only
these must be proved in proofs of properties of the defined predicate. On the other hand, if the
negative cases are of interest they are directly provided by a recursive definition and the
defining equations of a recursive definition can be used for rewriting (see
Section~\ref{basic-methods-simp}).
\<close>

subsection "Uniqueness"
text_raw\<open>\label{holbasic-recursive-unique}\<close>

text\<open>
As usual, a function must be unique, mapping every argument to only one value. It is easy to fail
doing so, consider 
@{theory_text[display]
\<open>function nounique :: "nat \<Rightarrow> nat" where
  "nounique 5 = 6"
| "nounique 5 = 7"
\<proof>\<close>}
The function maps the value \<open>5\<close> to two different values \<open>6\<close> and \<open>7\<close> (and thus is no function
anymore).

Therefore HOL expects a proof that the equations are compatible in the sense that they cover
disjoint arguments spaces or, if the spaces of two equations overlap, the equations specify the same
function values on the overlapping regions. In the general case HOL creates (after the goal for
equation completeness) for every pair of equations \<open>eq\<^sub>i\<close> and \<open>eq\<^sub>j\<close> where \<open>i \<le> j\<close> a goal of the form
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i x\<^sub>j\<^sub>1' \<dots> x\<^sub>j\<^sub>p\<^sub>j'.
  (term\<^sub>i\<^sub>1, \<dots>, term\<^sub>i\<^sub>k) = (term\<^sub>j\<^sub>1, \<dots>, term\<^sub>j\<^sub>k) \<Longrightarrow> term\<^sub>i = term\<^sub>j\<close>}
Here \<open>x\<^sub>j\<^sub>b'\<close> is a renamed \<open>x\<^sub>j\<^sub>b\<close> to avoid a name clash with an \<open>x\<^sub>i\<^sub>a\<close> if necessary. The renamed
variables are consistently replaced in all terms. Moreover, all occurrences of the defined function
\<open>name\<close> in \<open>term\<^sub>i\<close> and \<open>term\<^sub>j\<close> are replaced by \<open>name_sumC\<close> which is the uncurried (see
Section~\ref{holtypes-tup-funcs}) form of \<open>name\<close> where the arguments are specified as a tuple.

Together these are $\sum_{i=1}^n i = (n+1)*n/2$ goals where \<open>n\<close> is the number of equations.
The proof of these goals depends on the types and functions used in the equations, for many simple
cases it can be done by method \<open>auto\<close> which solves all goals together.

For the faculty function defined as above these are the three goals
@{text[display]
\<open>0 = 0 \<Longrightarrow> 1 = 1
\<And>n. \<lbrakk>0 < n; 0 = n\<rbrakk> \<Longrightarrow> 1 = n * fac_sumC (n - 1)
\<And>n na. \<lbrakk>0 < n; 0 < na; n = na\<rbrakk>
   \<Longrightarrow> n * fac_sumC (n - 1) = na * fac_sumC (na - 1)\<close>}
where the first and third are trivial and the second is valid because the two assumptions are a
contradiction (because the argument spaces are disjoint). All three goals are solved together by
a single application of method \<open>auto\<close> (see Section~\ref{basic-methods-auto}).
\<close>

subsection "The Domain Predicate"
text_raw\<open>\label{holbasic-recursive-domain}\<close>

text\<open>
Even if the defining equations cover all possible arguments and define the function values in a
unique way the function value may still be underspecified for some arguments. Consider the recursive
definition
@{theory_text[display]
\<open>function uspec :: "nat \<Rightarrow> nat" where
  "uspec i = uspec i"
  by auto\<close>}
The proof of equation completeness and compatibility is successfully done by the \<open>auto\<close> method and
the definition introduces the total function \<open>uspec\<close>, however, no information is available about its
result values.

Information about result values must either be specified directly on the right side of a
non-recursive equation \<open>eq\<^sub>i\<close> or it must be derivable by a finite number of substitutions using the
equations. Such a substitution mainly replaces the function arguments specified on the left side
of the equation by the arguments used in the recursive calls on the right side.

Therefore HOL creates for every recursive definition of a function \<open>name\<close> the relation \<open>name_rel\<close>
which relates for all defining equations the arguments of every recursive call on the right side to
the arguments on the left side. Actually, \<open>name_rel\<close> relates argument tuples, like the arguments of
\<open>name_sumC\<close> as described above. It is defined inductively (see
Section~\ref{holbasic-inductive}) using defining rules of the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> 
  name_rel (term\<^sub>i\<^sub>j\<^sub>1, \<dots>, term\<^sub>i\<^sub>j\<^sub>k) (term\<^sub>i\<^sub>1, \<dots>, term\<^sub>i\<^sub>k)\<close>}
where \<open>term\<^sub>i\<^sub>j\<^sub>l\<close> is the \<open>l\<close>-th argument in the \<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>. There is
one such rule for every recursive call occurring in the defining equations \<open>eq\<^sub>i\<close>. The defined
relation \<open>name_rel\<close> never occurs in the \<open>Q\<^sub>i\<^sub>j\<close>, therefore it is a single-step inductive definition
(see Section~\ref{holbasic-inductive-singlestep}) which could also have been specified as an
Isabelle definition.

For the faculty function defined as above the corresponding definition of the relation \<open>fac_rel\<close> is
@{theory_text[display]
\<open>inductive fac_rel :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where "0 < n \<Longrightarrow> fac_rel (n - 1) n"\<close>}
with only one rule because there is only one recursive call in the definition. This relation relates
every natural number with its immediate successor.

Now it is possible to characterize the arguments for which the function value is fully specified 
by the accessible part \<open>Wellfounded.accp name_rel\<close> of \<open>name_rel\<close> (see
Section\ref{holbasic-wellfounded-accp}). Every substitution by an equation \<open>eq\<^sub>i\<close> corresponds to an
application of \<open>name_rel\<close> from right to left, every chain of such applications is finite on its
accessible part.

For every recursive definition of a function \<open>name :: t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type\<close> HOL defines the
abbreviation
@{theory_text[display]
\<open>abbreviation name_dom :: "(t\<^sub>1 \<times> \<dots> \<times> t\<^sub>k) \<Rightarrow> bool" where
  "name_dom \<equiv> Wellfounded.accp name_rel"\<close>}
called the ``domain predicate'' for the argument tuples for which \<open>name\<close> is fully specified.

For the faculty function the domain predicate is defined by
@{theory_text[display]
\<open>abbreviation fac_dom :: "nat \<Rightarrow> bool" where
  "fac_dom \<equiv> Wellfounded.accp fac_rel"\<close>}
Since every natural number can be reached by a finite number of steps starting at \<open>0\<close> this predicate
is \<open>True\<close> for all natural numbers.
\<close>

subsection "Rules Provided by Recursive Definitions"
text_raw\<open>\label{holbasic-recursive-rules}\<close>

text\<open>
HOL automatically creates and proves some additional rules from a recursive definition and its
proof. The domain predicate is used in these rules to exclude underspecified cases.
\<close>

subsubsection "Simplification Rules"

text\<open>
HOL automatically creates and proves simplification rules which directly correspond to the defining
equations \<open>eq\<^sub>i\<close>. Every such rule is guarded by the domain predicate for the arguments of the
substituted function application. For the equation \<open>eq\<^sub>i\<close> in the general form as given above the
rule is
@{text[display]
\<open>\<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i; name_dom (term\<^sub>i\<^sub>1, \<dots>, term\<^sub>i\<^sub>k)\<rbrakk> \<Longrightarrow>
  name term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k = term\<^sub>i\<close>}
where all occurrences of the bound variables \<open>x\<^sub>i\<^sub>1, \<dots>, x\<^sub>i\<^sub>p\<^sub>i\<close> have been replaced by corresponding
unknowns. The set of all these simplification rules is named \<open>name.psimps\<close>. The rules are not added
to the simpset automatically, they can be explicitly used for ``unfolding'' the recursive definition
in one or more steps. If individual names have been specified for (some of) the \<open>eq\<^sub>i\<close> these names
denote the corresponding facts in \<open>name.psimps\<close>.
\<close>

subsubsection "Elimination Rule"

text\<open>
HOL also creates an elimination rule (see Section~\ref{basic-case-elim}) \<open>name.pelims\<close> where the
major premise has the form \<open>name ?x\<^sub>1 \<dots> ?x\<^sub>k = ?y\<close> and the rule replaces it mainly by case
assumptions according to the defining equations.
\<close>

subsubsection "Induction Rule"

text\<open>
HOL also creates and proves a single induction rule \<open>name.pinduct\<close> of the form
@{text[display]
\<open>\<lbrakk>name_dom (?a\<^sub>1, \<dots>, ?a\<^sub>k); RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P ?a\<^sub>1 \<dots> ?a\<^sub>k\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. 
  \<lbrakk>name_dom (term\<^sub>i\<^sub>1, \<dots>, term\<^sub>i\<^sub>k); Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i; R\<^sub>i\<^sub>1; \<dots>; R\<^sub>i\<^sub>r\<^sub>i\<rbrakk>
  \<Longrightarrow> ?P term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k\<close>}
and every \<open>R\<^sub>i\<^sub>j\<close> has the form \<open>?P term\<^sub>i\<^sub>j\<^sub>1 \<dots> term\<^sub>i\<^sub>j\<^sub>k\<close> where \<open>term\<^sub>i\<^sub>j\<^sub>l\<close> is the \<open>l\<close>-th argument in the
\<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>.

It can be used for induction with elimination (see Section~\ref{basic-case-induction}) where the
major premise is the domain predicate for the arguments of the proved property \<open>?P\<close> which is usually
a property of the defined function \<open>name\<close> applied to these arguments. The cases correspond to the
defining equations and are named by numbers starting with 1. The induction step in every case goes
from the arguments of the recursive calls in \<open>term\<^sub>i\<close> to the arguments on the left side of \<open>eq\<^sub>i\<close>.
This form of induction is also called ``computation induction''.

For the faculty function defined as above the induction rule \<open>fac.pinduct\<close> is
@{text[display]
\<open>\<lbrakk>fac_dom ?a; fac_dom 0 \<Longrightarrow> ?P 0;
  \<And>n. \<lbrakk>fac_dom n; 0 < n; ?P (n - 1)\<rbrakk> \<Longrightarrow> ?P n\<rbrakk> \<Longrightarrow> ?P ?a\<close>}\<close>

subsection "Termination"
text_raw\<open>\label{holbasic-recursive-term}\<close>

text\<open>
In programming languages a recursively defined function \<open>name\<close> is only considered correct if its
value can be determined for every argument by simplification using \<open>name.psimps\<close> in a finite number
of steps (i.e., its computation terminates). This is only the case if the argument (tuple) satisfies
the domain predicate. Therefore it is often of interest to prove that this is the case for all
possible argument (tuple)s. HOL provides specific support for proving this property.

The corresponding theorem for a recursively defined function \<open>name :: t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type\<close> is
@{theory_text[display]
\<open>theorem "\<forall>x :: (t\<^sub>1 \<times> \<dots> \<times> t\<^sub>k). name_dom x" \<proof>\<close>}
 stating that all possible argument tuples satisfy the domain predicate \<open>name_dom\<close> (for the
quantifier \<open>\<forall>\<close> see Section~\ref{holtypes-bool-funcs}). HOL provides the equivalent abbreviated form
@{theory_text[display]
\<open>termination name \<proof>\<close>}
which is called a ``termination proof'' for the recursive function \<open>name\<close>. If \<open>name\<close> is omitted
it refers to the last previously defined recursive function.
\<close>

subsubsection "The Proof Method \<open>relation\<close>"

text\<open>
Note that this theorem is equivalent to the property that the relation \<open>name_rel\<close> is well-founded.
As described in Section~\ref{holbasic-wellfounded-measure} it can be proved by proving that
\<open>name_rel x y \<Longrightarrow> (measure f) x y\<close> holds for a measure function \<open>f :: (t\<^sub>1 \<times> \<dots> \<times> t\<^sub>k) \<Rightarrow> nat\<close>. HOL
provides the proof method
@{theory_text[display]
\<open>relation "M"\<close>}
which replaces the original goal of a termination proof for \<open>name\<close> by the goals
@{text[display]
\<open>wf M
R\<^sub>1
\<dots>
R\<^sub>r\<close>}
where every \<open>R\<^sub>h\<close> corresponds to a defining rule for \<open>name_rel\<close> (see
Section~\ref{holbasic-recursive-domain}) in \<open>name_rel.intros\<close> (see
Section~\ref{holbasic-inductive-defrules}) and has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> 
  ((term\<^sub>i\<^sub>j\<^sub>1, \<dots>, term\<^sub>i\<^sub>j\<^sub>k), (term\<^sub>i\<^sub>1, \<dots>, term\<^sub>i\<^sub>k)) \<in> M\<close>}
where \<open>term\<^sub>i\<^sub>j\<^sub>l\<close> is the \<open>l\<close>-th argument in the \<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>. The goals
\<open>R\<^sub>1, \<dots>, R\<^sub>r\<close> together are equivalent to the goal \<open>name_rel x y \<Longrightarrow> M x y\<close>.

The proof method is usually applied in the form
@{theory_text[display]
\<open>relation "measure f"\<close>}
for an appropriate measure function \<open>f\<close> as above. It must be constructed so that for every tuple
\<open>(term\<^sub>i\<^sub>j\<^sub>1, \<dots>, term\<^sub>i\<^sub>j\<^sub>k)\<close> of arguments for a recursive call the value is strictly lower than for
the argument tuple \<open>(term\<^sub>i\<^sub>1, \<dots>, term\<^sub>i\<^sub>k)\<close> in the defining equations \<open>eq\<^sub>i\<close>. The resulting goals
\<open>wf (measure f)\<close> and \<open>R\<^sub>1, \<dots>, R\<^sub>r\<close> are often solved by method \<open>auto\<close> (see
Section~\ref{basic-methods-auto}). Then the termination proof has the form
@{theory_text[display]
\<open>termination name by (relation "measure f") auto\<close>}

For the faculty function defined as above the goal of the termination proof is
@{text[display]
\<open>\<forall>x :: nat. fac_dom x\<close>}
which is true as argued above. To prove it, the identity function \<open>\<lambda>n. n\<close> is an applicable measure
function because \<open>n > 0 \<Longrightarrow> n-1 < n\<close>. Applying the \<open>relation\<close> method with it yields the two goals
@{text[display]
\<open>wf (measure (\<lambda>n. n))
\<And>n. 0 < n \<Longrightarrow> (n - 1, n) \<in> measure (\<lambda>n. n)\<close>}
They can be solved together by method \<open>auto\<close>, therefore a termination proof for the faculty
definition can be specified as
@{theory_text[display]
\<open>termination fac by (relation "measure (\<lambda>n. n)") auto\<close>}\<close>

subsubsection "The Proof Methods \<open>lexicographic_order\<close> and \<open>size_change\<close>"

text\<open>
HOL also provides the proof method
@{theory_text[display]
\<open>lexicographic_order\<close>}
and the stronger method
@{theory_text[display]
\<open>size_change\<close>}
for termination proofs. They try to automatically construct a measure function from the \<open>size\<close>
function (see Section~\ref{holbasic-wellfounded-size}) combined in a lexicographic way for
argument tuples. They are applied to the original goal and if they are successful they solve it
completely, otherwise an error is signaled. Using the first method a termination proof has the form
@{theory_text[display]
\<open>termination name by lexicographic_order\<close>}

Since for type \<open>nat\<close> the \<open>size\<close> function is the identity the termination proof for the faculty
function may also be specified as
@{theory_text[display]
\<open>termination fac by lexicographic_order\<close>}\<close>

subsection "Rules Provided by Termination Proofs"
text_raw\<open>\label{holbasic-recursive-termrules}\<close>

text\<open>
A termination proof for a function \<open>name\<close> using the command \<^theory_text>\<open>termination\<close> provides the additional
rules \<open>name.simps\<close>, \<open>name.elims\<close>, and \<open>name.induct\<close>. They result from the corresponding rules
provided by the recursive definition by removing all applications of the domain predicate
\<open>name_dom\<close>. This is valid because the termination proof has shown that it is always \<open>True\<close>.

Specifically, the resulting simplification rules exactly correspond to the defining equations and
can be used for unfolding the definition for a function application in one or more steps.

If individual names have been specified for (some of) the \<open>eq\<^sub>i\<close> the termination proof replaces the
associated facts from \<open>name.psimps\<close> by those from \<open>name.simps\<close>.

The resulting induction rule is a plain induction rule without elimination of the form
@{text[display]
\<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P ?a\<^sub>1 \<dots> ?a\<^sub>k\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i; R\<^sub>i\<^sub>1; \<dots>; R\<^sub>i\<^sub>r\<^sub>i\<rbrakk>
  \<Longrightarrow> ?P term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k\<close>}
and every \<open>R\<^sub>i\<^sub>j\<close> has the form \<open>?P term\<^sub>i\<^sub>j\<^sub>1 \<dots> term\<^sub>i\<^sub>j\<^sub>k\<close> where \<open>term\<^sub>i\<^sub>j\<^sub>l\<close> is the \<open>l\<close>-th argument in the
\<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>.

For the faculty function defined as above the induction rule \<open>fac.induct\<close> is
@{text[display]
\<open>\<lbrakk>?P 0; \<And>n. \<lbrakk>0 < n; ?P (n - 1)\<rbrakk> \<Longrightarrow> ?P n\<rbrakk> \<Longrightarrow> ?P ?a\<close>}

To use the rule with the proof methods \<open>induct\<close> and \<open>induction\<close> (see
Section~\ref{basic-case-induction}) it must always be specified explicitly in the form
@{text[display]
\<open>induct \<dots> rule: name.induct\<close>}\<close>

subsection "Mutual Recursion"
text_raw\<open>\label{holbasic-recursive-mutual}\<close>

text\<open>
If several recursive functions are defined depending on each other they must be defined together in
a single recursive definition of the form
@{theory_text[display]
\<open>function name\<^sub>1 \<dots> name\<^sub>m
where eq\<^sub>1 | \<dots> | eq\<^sub>n \<proof>\<close>}
The \<open>name\<^sub>i\<close> may be grouped by \<open>and\<close> and types may be specified for (some of) the groups.

The defining equations \<open>eq\<^sub>i\<close> have the same form as described above, however, every left side may be
an application of one of the defined functions \<open>name\<^sub>i\<close> (with arbitrary ordering of the rules) and
every right side \<open>term\<^sub>i\<close> may contain applications of all defined functions.

A mutual recursive definition of the predicates \<open>evn\<close> and \<open>odd\<close> (see
Section~\ref{holbasic-inductive-mutual}) is
@{theory_text[display]
\<open>function evn odd :: "nat \<Rightarrow> bool"
where "evn 0 = True" | "odd 0 = False"
| "evn (n+1) = odd n" | "odd (n+1) = evn n"
\<proof>\<close>}

The simplification and elimination rules are provided for every defined function as \<open>name\<^sub>i.psimps\<close>,
\<open>name\<^sub>i.pelims\<close>, \<open>name\<^sub>i.simps\<close>, and \<open>name\<^sub>i.elims\<close>. The induction rules are provided for all defined
functions together in the sets named \<open>name\<^sub>1_\<dots>_name\<^sub>m.pinduct\<close> and \<open>name\<^sub>1_\<dots>_name\<^sub>m.induct\<close>. 

The domain predicate and the corresponding relation are common for all defined functions and
are named \<open>name\<^sub>1_\<dots>_name\<^sub>m_dom\<close> and \<open>name\<^sub>1_\<dots>_name\<^sub>m_rel\<close>. They are defined on values of the sum type
(see Section~\ref{holtypes-sum}) of the argument tuples of all defined functions, this is also the
case for the function \<open>name\<^sub>1_\<dots>_name\<^sub>m_sumC\<close> used in the goals for the uniqueness proof. Also a
measure function used in a termination proof must be defined on this sum type.

A termination proof can use the name of either defined function to refer to the mutual recursive
definition.
\<close>

end