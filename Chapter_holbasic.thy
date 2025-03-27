theory Chapter_holbasic
  imports Chapter_case
begin

chapter "Isabelle/HOL Basics"
text_raw\<open>\label{holbasic}\<close>

text \<open>
The basic mechanisms described in the previous Chapters can be used for working with different 
``object logics''. An object logic\index{object logic}\index{logic!object $\sim$} defines the types of objects available, constants of these types,
and facts about them. An object logic may also extend the syntax, both inner and outer syntax.

The standard object logic for Isabelle is the ``Higher Order Logic'' HOL\index{HOL (object logic)}, it covers a large part
of standards mathematics and is flexibly extensible. This chapter introduces some basic
mechanisms which are available in HOL for arbitrary types.

The abbreviation ``HOL'' is used in the logics community to denote the general concept of higher
order logics. In this document we use it specifically to denote the implementation as object logic
in Isabelle which is named Isabelle/HOL. 

Isabelle/HOL consists of the session HOL/HOL\index{HOL (session)}
(see Section~\ref{system-invoke-theory}) and several extensions. Most theories in HOL/HOL
are imported by the theory @{theory Main}\index{Main (theory)}. By importing @{theory Main} the 
content of all these theories becomes available.
The most basic theory in HOL/HOL is also named {\tt\sl HOL}. There are additional theories in
HOL/HOL which are not imported by @{theory Main}, such as for rational and real numbers.

This introduction only covers some of the theories imported by @{theory Main}.
\<close>

section "Predicates and Relations"
text_raw\<open>\label{holbasic-pred}\<close>

text\<open>
Basically HOL uses the type \<open>'a \<Rightarrow> 'b\<close> of functions provided by Isabelle (see
Section~\ref{theory-terms-functions}) to represent predicates and relations in the usual way.
\<close>

subsection "Predicates"
text_raw\<open>\label{holbasic-pred-pred}\<close>

text\<open>
A predicate\index{predicate} on values of arbitrary types \<open>t\<^sub>1, \<dots>, t\<^sub>n\<close> is a function of type \<open>t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>n \<Rightarrow>
bool\<close>. It may be denoted by a lambda term \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. bterm\<close> where \<open>bterm\<close> is a term of type \<open>bool\<close>
which may contain free occurrences of the variables \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close>. Note that also a predicate defined
as a named constant \<open>P\<close> can always be specified by the lambda term \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. P x\<^sub>1 \<dots> x\<^sub>n\<close>.

Note that the concept of predicates actually depends on the specific HOL type \<open>bool\<close>\index{bool (type)}, which is
introduced in Section~\ref{holtypes-bool}. 
\<close>

subsection "Unary Predicates and Sets"
text_raw\<open>\label{holbasic-pred-set}\<close>

text\<open>
Unary predicates\index{predicate!unary $\sim$} of type \<open>t \<Rightarrow> bool\<close> are equivalent to sets of type \<open>t set\<close>. There is a 1-1
correspondence between a predicate and the set of values for which the predicate value is \<open>True\<close>.
Actually, the HOL type constructor \<open>set\<close> described in Section~\ref{holtypes-set} is defined based on
this correspondence. See that section for more information about denoting and using sets.

As a convention HOL often provides a predicate and rules about it in both forms as a set named
\<open>name\<close> and as a predicate named \<open>namep\<close> or \<open>nameP\<close>. Then usually every fact \<open>F\<close> containing
such predicates in set form can be converted to the corresponding fact containing them in predicate
form by applying the attribute \<open>to_pred\<close>\index{to-pred@to$\_$pred (attribute)} as in \<open>F[to_pred]\<close> and vice versa by applying the attribute
\<open>to_set\<close>\index{to-set@to$\_$set (attribute)}.
\<close>

subsection "Relations"
text_raw\<open>\label{holbasic-pred-rel}\<close>

text\<open>
A binary relation\index{relation} between values of arbitrary types \<open>t\<^sub>1\<close> and \<open>t\<^sub>2\<close> is a binary predicate\index{predicate!binary $\sim$} of type
\<open>t\<^sub>1 \<Rightarrow> t\<^sub>2 \<Rightarrow> bool\<close>. As binary functions the relations in HOL often have an alternative operator name
of the form \<open>(op)\<close> which supports specifying applications in infix form \<open>x op y\<close> (see
Section~\ref{theory-terms-multargs}).

By partial application (see Section~\ref{theory-terms-multargs}) the first argument of a relation \<open>R\<close>
can be fixed to yield the unary predicate \<open>(R x)\<close> on the second argument. For operators this must be
done using the operator name in the form \<open>((op) x)\<close>, partial application cannot be written by
omitting an argument on one side of the infix operator.
\<close>

subsubsection "Relation Operations"

text\<open>
HOL provides the composition operation for relations. It is defined as the function
@{text[display]
\<open>relcompp :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('b\<Rightarrow>'c\<Rightarrow>bool) \<Rightarrow> ('a\<Rightarrow>'c\<Rightarrow>bool) \<equiv>
  \<lambda>R\<^sub>1 R\<^sub>2 a c. \<exists>b. R\<^sub>1 a b \<and> R\<^sub>2 b c\<close>}\index{relcompp (constant)}
The quantifier \<open>\<exists>\<close> and the boolean operator \<open>\<and>\<close> have the usual meaning, for more information about
them see Section~\ref{holtypes-bool-funcs}. HOL also provides the operator name \<open>OO\<close> (two capital
letters O) for infix notation, as in \<open>R\<^sub>1 OO R\<^sub>2\<close>.

HOL provides the converse of a relation, defined as the function
@{text[display]
\<open>conversep :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('b\<Rightarrow>'a\<Rightarrow>bool) \<equiv>
  \<lambda>R b a. R a b\<close>}\index{conversep (constant)}
with the alternative notation \<open>R\<^sup>-\<^sup>1\<^sup>-\<^sup>1\<close> for \<open>conversep R\<close>. Note that although the superscript is
applied twice it denotes only a single conversion. The single superscript is used for the conversion
of a different form of relations (see Section~\ref{holbasic-tuples-rel}).

HOL provides functions for the domain and range predicates of a relation:
@{text[display]
\<open>Domainp :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('a\<Rightarrow>bool) \<equiv> \<lambda>R a. \<exists>b. R a b
Rangep :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> ('b\<Rightarrow>bool) \<equiv> \<lambda>R b. \<exists>a. R a b\<close>}
\index{Domainp (constant)}\index{Rangep (constant)}

HOL provides predicates for typical properties of relations:
@{text[display]
\<open>left_total :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> bool \<equiv> \<lambda>R. \<forall>x. \<exists>y. R x y
left_unique :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> bool \<equiv>
  \<lambda>R. \<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y
right_total :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> bool \<equiv> \<lambda>R. \<forall>y. \<exists>x. R x y
right_unique :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> bool \<equiv>
  \<lambda>R. \<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z
bi_total :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> bool \<equiv>
  \<lambda>R. left_total R \<and> right_total R
bi_unique ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> bool \<equiv>
  \<lambda>R. left_unique R \<and> right_unique R\<close>}
\index{left-total@left$\_$total (constant)}\index{left-unique@left$\_$unique (constant)}
\index{right-total@right$\_$total (constant)}\index{right-unique@right$\_$unique (constant)}
\index{bi-total@bi$\_$total (constant)}\index{bi-unique@bi$\_$unique (constant)}
These predicates test whether a relation \<open>R\<close> is a function (\<open>right_unique\<close>), surjective (\<open>right_total\<close>),
injective (\<open>left_unique\<close>), total (\<open>left_total\<close>), an injective function (\<open>bi_unique\<close>), or surjective
and total (\<open>bi_total\<close>). \<open>R\<close> is a bijection if \<open>bi_total R \<and> bi_unique R\<close>. 
\<close>

subsubsection "Relations As Set-Valued Functions"

text\<open>
Since the unary predicate \<open>(R x)\<close> is equivalent to a set, every binary relation of type
\<open>t\<^sub>1 \<Rightarrow> t\<^sub>2 \<Rightarrow> bool\<close> is equivalent to a set-valued function of type \<open>t\<^sub>1 \<Rightarrow> (t\<^sub>2 set)\<close>. It maps every
value of type \<open>t\<^sub>1\<close> to the set of related values of type \<open>t\<^sub>2\<close>. HOL extends the convention described
above and often provides relations named \<open>namep\<close> or \<open>nameP\<close> also as set-valued functions named
\<open>name\<close>.

Note that HOL introduces the specific type constructor \<open>rel\<close> (see Section~\ref{holtypes-rel}), where
the values are equivalent to binary relations on a single type \<open>t\<close>.

More generally, \<open>n\<close>-ary relations for \<open>n > 2\<close> are directly represented by \<open>n\<close>-ary predicates\index{predicate!n-ary $\sim$}. Every
\<open>n\<close>-ary relation is equivalent to an \<open>(n-1)\<close>-ary set-valued function.
\<close>

section "Equality, Orderings, and Lattices"
text_raw\<open>\label{holbasic-equal}\<close>

subsection "The Equality Relation"
text_raw\<open>\label{holbasic-equal-eq}\<close>

text\<open>
HOL introduces the equality\index{equality} relation\index{relation!equality $\sim$} as a function
@{text[display]
\<open>HOL.eq :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}
with the alternative operator name \<open>(=)\<close>\index{=@\<open>=\<close> (operator)} for infix notation.

Inequality can be denoted by
@{text[display]
\<open>not_equal :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}
with the alternative operator name \<open>(\<noteq>)\<close>\index{/=@\<open>\<noteq>\<close> (operator)} for infix notation.

Both functions are polymorphic and can be applied to terms of arbitrary type, however, 
they can only be used to compare two terms which have the same type. Therefore the
proposition
@{text[display]
\<open>True \<noteq> 1\<close>}
is syntactically wrong and Isabelle will signal an error for it.

Moreover, in a term such as \<open>term\<^sub>1 = term\<^sub>2\<close> or \<open>term\<^sub>1 \<noteq> term\<^sub>2\<close> no type information can be derived
for \<open>term\<^sub>1\<close> and \<open>term\<^sub>2\<close> other than that they must have the same type. There may be relations with
the same semantics but for operands of a specific type, then it is possible to derive the operand
types. An example is the relation \<open>iff\<close>\index{iff (constant)} with operator name \<open>(\<longleftrightarrow>)\<close>\index{<-->@\<open>\<longleftrightarrow>\<close> (operator)} which is equal to \<open>(=)\<close> but only
defined for operands of type \<open>bool\<close>. Therefore for the term \<open>term\<^sub>1 \<longleftrightarrow> term\<^sub>2\<close> HOL automatically
derives that \<open>term\<^sub>1\<close> and \<open>term\<^sub>2\<close> have type \<open>bool\<close>.

There is also a restricted form of equality
@{text[display]
\<open>eq_onp :: ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}\index{eq-onp@eq$\_$onp (constant)}
which can only be used to compare values which satisfy a given predicate. Thus \<open>eq_onp P x y\<close> will
only be \<open>True\<close> if \<open>x\<close> and \<open>y\<close> are equal and additionally \<open>P x\<close> holds.
\<close>

subsection "The Ordering Relations"
text_raw\<open>\label{holbasic-equal-order}\<close>

text\<open>
HOL also introduces two ordering relations\index{relation!ordering $\sim$} as functions
@{text[display]
\<open>less :: 'a \<Rightarrow> 'a \<Rightarrow> bool
less_eq :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>}\index{less (constant)}\index{less-eq@less$\_$eq (constant)}
with the alternative operator names \<open>(<)\<close>\index{<@\<open><\<close> (operator)} and \<open>(\<le>)\<close>\index{<=@\<open>\<le>\<close> (operator)} for infix notation and the
abbreviations \<open>greater\<close>\index{greater (constant)} and \<open>greater_eq\<close>\index{greater-eq@greater$\_$eq (constant)} for reversed arguments with operator names
\<open>(>)\<close>\index{>@\<open>>\<close> (operator)} and \<open>(\<ge>)\<close>\index{>=@\<open>\<ge>\<close> (operator)}.

Based on these relations HOL also introduces the functions
@{text[display]
\<open>min :: 'a \<Rightarrow> 'a \<Rightarrow> 'a
max :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>}\index{min (constant)}\index{max (constant)}
in the usual way, i.e. if \<open>a\<le>b\<close> then \<open>min a b\<close> is \<open>a\<close>, otherwise \<open>b\<close>. HOL also introduces the
functions
@{text[display]
\<open>Min :: 'a set \<Rightarrow> 'a
Max :: 'a set \<Rightarrow> 'a\<close>}\index{Min (constant)}\index{Max (constant)}
for the minimum or maximum of all values in a set. The value of \<open>Min\<close> and \<open>Max\<close> is
underspecified if applied to an empty or infinite set.

All these functions are polymorphic but are not available for arbitrary types. They are overloaded
only for those types which have ordered values. However, this is the case for most basic types
introduced by HOL and described in Chapter~\ref{holtypes}. If an ordering function is used for a
type for which it is not available an error message of the form ``No type arity ...'' is signaled.

Basically, these are only syntactic definitions, no rules about orderings are implied by them. For
some of its predefined types, such as type \<open>nat\<close>, HOL provides more specific specifications by
overloading.

As for \<open>(=)\<close> the type of \<open>term\<^sub>1\<close> and \<open>term\<^sub>2\<close> cannot be derived in a term such as \<open>term\<^sub>1 < term\<^sub>2\<close>.
There are relations with the same semantics but specific operand types such as \<open>(\<subseteq>)\<close>\index{/subset-eq@\<open>\<subseteq>\<close> (operator)} for the
relation \<open>(\<le>)\<close> on sets (see Section~\ref{holtypes-set}).
\<close>

subsection "Lattice Operations"
text_raw\<open>\label{holbasic-equal-lattice}\<close>

text\<open>
HOL introduces the two lattice operations
@{text[display]
\<open>inf :: 'a \<Rightarrow> 'a \<Rightarrow> 'a
sup :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>}\index{inf (constant)}\index{sup (constant)}
with the alternative operator names \<open>(\<sqinter>)\<close>\index{/inf@\<open>\<sqinter>\<close> (operator)} and \<open>(\<squnion>)\<close>\index{/sup@\<open>\<squnion>\<close> (operator)} for infix notation together with the lattice
constants
@{text[display]
\<open>top :: 'a
bot :: 'a\<close>}\index{top (constant)}\index{bot (constant)}
with the alternative names \<open>(\<top>)\<close>\index{/top@\<open>\<top>\<close> (operator)} and \<open>(\<bottom>)\<close>\index{/bot@\<open>\<bottom>\<close> (operator)} (in the interactive editor available in the Symbols
panel in the Logic tab).

Additionally there are the lattice operations for all values in a set (see
Section~\ref{holtypes-set})
@{text[display]
\<open>Inf :: 'a set \<Rightarrow> 'a
Sup :: 'a set \<Rightarrow> 'a\<close>}\index{Inf (constant)}\index{Sup (constant)}
with the alternative operator names \<open>(\<Sqinter>)\<close>\index{/Inf@\<open>\<Sqinter>\<close> (operator)} and \<open>(\<Squnion>)\<close>\index{/Sup@\<open>\<Squnion>\<close> (operator)} for prefix notation.

HOL does not provide the six alternative names automatically. To make them available, the command
@{theory_text[display]
\<open>unbundle lattice_syntax\<close>}\index{lattice-syntax@lattice$\_$syntax (bundle)}\index{unbundle (keyword)}
must be used on theory level. It is available after importing the theory \<^theory>\<open>Main\<close> (see
Section~\ref{system-invoke-theory}).

Like the ordering functions (see Section~\ref{holbasic-equal-order}) the lattice operations and constants are polymorphic but are not available for arbitrary types.
They are overloaded only for those types which have a corresponding structure. For example, type
\<open>nat\<close> has the \<open>bot\<close> value (which is equal to \<open>0\<close>), but no \<open>top\<close> value. If a lattice operation or
constant is used for a type for which it is not available an error message of the form
``No type arity ...'' is signaled.

As for equality and ordering relations, because the lattice operations and constants are
overloaded it is not possible to derive the type for valid operands. Again, there are operations and
constants with more specific operand types, such as \<open>(\<inter>)\<close>\index{/inter@\<open>\<inter>\<close> (operator)} for \<open>(\<sqinter>)\<close> on sets where HOL automatically
derives the operand types.
\<close>

section "Description Operators"
text_raw\<open>\label{holbasic-descr}\<close>

text\<open>
A description operator\index{description operator} selects a value from all values which satisfy a given unary predicate.

Description operators use the binder syntax\index{binder syntax} of the form \<open>OP x. term\<close> (see
Section~\ref{theory-terms-lambda}). Like a lambda term it locally binds a variable \<open>x\<close> which may occur in \<open>term\<close>.
\<close>

subsection "The Choice Operator"
text_raw\<open>\label{holbasic-descr-choice}\<close>

text\<open>
An arbitrary value satisfying the given predicate \<open>\<lambda>x. bterm\<close> can be denoted by
@{text[display]
\<open>SOME x. bterm\<close>}\index{SOME (binder)}
Only a single variable may be specified after \<open>SOME\<close>, however, as in a lambda term a type may be
specified for it.

The value denoted by the term is underspecified in the sense of Section~\ref{theory-terms-consts}.
The only information which can be derived for it is that it satisfies the predicate \<open>\<lambda>x. bterm\<close>.
If there is no value which satisfies the predicate not even this property may be derived.

The operator \<open>SOME\<close> is equivalent to the famous Hilbert choice operator\index{choice operator}. HOL includes the axiom of
choice and provides the operator on this basis.
\<close>

subsection "The Definite Description Operator"
text_raw\<open>\label{holbasic-descr-definite}\<close>

text\<open>
If only one value satisfies the given predicate \<open>\<lambda>x. bterm\<close> this value can be denoted by
@{text[display]
\<open>THE x. bterm\<close>}\index{THE (binder)}\index{definite description operator}
As for \<open>SOME\<close> only a single variable may be specified with an optional type specification.

The value denoted by the term is also underspecified. However,
after proving that there exists a value \<open>v\<close> which satisfies the predicate \<open>\<lambda>x. bterm\<close> and that
all values satisfying the predicate are equal it is possible to prove that \<open>THE x.bterm = v\<close>.
\<close>

subsection "The Least and Greatest Value Operators"
text_raw\<open>\label{holbasic-descr-least}\<close>

text\<open>
If the values satisfying a predicate \<open>\<lambda>x. bterm\<close> are ordered, the least or greatest of these
values\index{least value operator}\index{greatest value operator} can be denoted by the terms
@{text[display]
\<open>LEAST x. bterm
GREATEST x. bterm\<close>}\index{LEAST (binder)}\index{GREATEST (binder)}
Only a single variable with an optional type specification is useful to be specified.

The operators 
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
\<open>undefined :: 'a\<close>}\index{undefined (constant)}
which is overloaded for arbitrary types. It is completely underspecified as described in
Section~\ref{theory-terms-consts}, i.e., no further information is given about it.

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
HOL extends the inner syntax for terms described in Section~\ref{theory-terms} by terms of
the following form
@{text[display]
\<open>let x\<^sub>1 = term\<^sub>1; \<dots>; x\<^sub>n = term\<^sub>n in term\<close>}\index{let term}\index{term!let $\sim$}\index{let (inner keyword)}\index{in (inner keyword)}
where \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are variables. The variable bindings are sequential, i.e., if \<open>i<j\<close> variable
\<open>x\<^sub>i\<close> may occur in \<open>term\<^sub>j\<close> and denotes \<open>term\<^sub>i\<close> there. In other words, the scope of \<open>x\<^sub>i\<close> are the 
terms \<open>term\<^sub>j\<close> with \<open>i<j\<close> and the \<open>term\<close>. If \<open>x\<^sub>i\<close> and \<open>x\<^sub>j\<close> are the same variable, the binding of 
its second occurrence shadows the binding of the first and ends the scope of the first occurrence.

Let terms are useful to introduce local variables as abbreviations for sub-terms.
 
Don't confuse the \<open>let\<close> term with the \<^theory_text>\<open>let\<close>\index{let (keyword)} statement described in
Section~\ref{proof-let-define}. Although they are used for a similar purpose there are several
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
Here \<open>Let\<close>\index{Let (constant)} is the polymorphic function
@{text[display]
\<open>Let :: 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<equiv> \<lambda>x f. f x\<close>}
which simply applies its second argument to its first argument.

Occurrences of let terms are usually not automatically resolved by substituting the bound term for
the variable. Therefore a proposition like \<open>(let x = a+b in (x*x)) = ((a+b)*(a+b))\<close> cannot be proved
by the simplifier (or other methods including simplification like \<open>auto\<close>, see
Sections~\ref{methods-simp} and~\ref{methods-auto-methods}). To resolve it, the
simplifier must be configured by adding the definitional equation of \<open>Let\<close> as \<open>simp add: Let_def\<close>.
\<close>

section "Tuples"
text_raw\<open>\label{holbasic-tuples}\<close>

text\<open>
HOL supports type expressions of the form \<open>t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n\<close> for arbitrary types \<open>t\<^sub>1, \<dots>, t\<^sub>n\<close>. They
denote the type of \<open>n\<close>-tuples\index{tuple} where the \<open>i\<close>th component has type \<open>t\<^sub>i\<close>. Here the \<open>\<times>\<close>\index{/x@\<open>\<times>\<close> (operator)} is the ``times
operator'' available in the interactive editor in the Symbols panel in the Operator tab. An
alternative syntax is \<open>t\<^sub>1 * \<dots> * t\<^sub>n\<close> using the ASCII star character. As an example the type
\<open>nat \<times> bool\<close> is the type of pairs\index{pair} of natural numbers and boolean values. The type \<open>nat \<times> 'a \<times> bool\<close>
is the polymorphic type of triples of a natural number, a value of the arbitrary type denoted by the
type parameter \<open>'a\<close>, and a boolean value. As usual, all these type expressions are part of the inner
syntax.

Values for \<open>n\<close>-tuples of type \<open>t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n\<close> are denoted in inner syntax as terms of the form
\<open>(term\<^sub>1, \<dots>, term\<^sub>n)\<close> where \<open>term\<^sub>i\<close> is a term of type \<open>t\<^sub>i\<close> and the parentheses\index{parentheses} and the comma\index{comma} belong
to the syntax.

The selector function \<open>fst\<close> can be used to access the first component of a tuple value, the
selector function \<open>snd\<close> can be used to access the remaining tuple after removing the first component
(which yields the single second component if applied to a pair) (see Section~\ref{holtypes-tup-destrs}).
\<close>

subsection "Function Argument Tuples"
text_raw\<open>\label{holbasic-tuples-funarg}\<close>

text\<open>
Every \<open>n\<close>-ary function\index{function!n-ary $\sim$} of type \<open>t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>n \<Rightarrow> t\<close> (see Section~\ref{theory-terms-multargs}) is
equivalent to a function of type \<open>(t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n) \<Rightarrow> t\<close> with \<open>n\<close>-tuples as argument values, which is
the common way in mathematics to represent a function with \<open>n\<close> arguments. There is a 1-1
correspondence between functions of these two forms. The first form is called the ``curried'' form\index{curried function}\index{function!curried $\sim$}
and the second form with tuples as arguments is called the ``uncurried'' form\index{uncurried function}\index{function!uncurried $\sim$} (named after Haskell
Curry who introduced the first form for \<open>n\<close>-ary functions). Note that for unary functions both forms
are the same.

Section~\ref{holtypes-func} describes means to convert between both forms and other ways how to
work with them.
\<close>

subsection "Relations as Tuple Sets"
text_raw\<open>\label{holbasic-tuples-rel}\<close>

text\<open>
For an \<open>n\<close>-ary relation\index{relation!n-ary $\sim$} of type \<open>t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>n \<Rightarrow> bool\<close> (see Section\ref{holbasic-pred-rel}) the
uncurried form is a predicate of type \<open>(t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n) \<Rightarrow> bool\<close>. Since all arguments together are
represented by a single tuple, this predicate is equivalent to a set of type \<open>(t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n) set\<close>
(see Section\ref{holbasic-pred-set}) where the elements in the set are tuples\index{relation!as tuple set}. This is the
usual form of representing relations in mathematics.

HOL extends the convention described in Section~\ref{holbasic-pred-set} of providing relations
named \<open>namep\<close> or \<open>nameP\<close> also as set-valued functions named \<open>name\<close> by alternatively using a tuple
set named \<open>name\<close>. Moreover it provides the relation operations (see
Section~\ref{holbasic-pred-rel}) for binary relations as tuple sets: composition as function
\<open>relcomp\<close> with operator name \<open>O\<close> (a single capital O), and conversion as function \<open>converse\<close> with
alternative notation \<open>R\<^sup>-\<^sup>1\<close> for \<open>converse R\<close>.
\<close>

section "Inductive Definitions"
text_raw\<open>\label{holbasic-inductive}\<close>

text\<open>
HOL supports inductive definitions\index{definition!inductive $\sim$}\index{inductive definition} of predicates as content in theories. An inductive definition
defines a predicate\index{predicate!inductive definition for $\sim$} by derivation rules which allow to derive the predicate values for some
arguments from the values for other arguments. An inductive definition for a k-ary predicate has the
form
@{theory_text[display]
\<open>inductive name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
where P\<^sub>1 | \<dots> | P\<^sub>n\<close>}\index{inductive (keyword)}\index{where (keyword)}
with derivation rules \<open>P\<^sub>i\<close>. The type specification for the predicate may be omitted if it can be
derived from the use of the defined predicate in the rules \<open>P\<^sub>i\<close>.
\<close>

subsection "The Defining Rules"
text_raw\<open>\label{holbasic-inductive-defrules}\<close>

text\<open>
The \<open>P\<^sub>i\<close> are derivation rules which may be specified in inner syntax of the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> name term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k\<close>}
where the conclusion is always an application of the defined predicate to \<open>k\<close> argument terms. The
defined predicate \<open>name\<close> may occur in arbitrary ways in the rule assumptions \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>, but not in the
argument terms \<open>term\<^sub>i\<^sub>,\<^sub>j\<close>. The rule separators \<open>|\<close> belong to the outer syntax, thus every rule must
be separately quoted.

An example is the following inductive definition for an evenness predicate\index{predicate!evenness $\sim$}:
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  "evn(0)" | "\<And>n. evn(n) \<Longrightarrow> evn(n+2)"\<close>}\index{evn (example constant)}\<close>

subsubsection "Alternative Rule Forms"

text\<open>
As for derivation rules specified in theorems (see Section~\ref{theory-theorem-spec}) the explicit
bindings of the variables \<open>x\<^sub>i\<^sub>,\<^sub>1, \<dots>, x\<^latex>\<open>$_{i,p_i}$\<close>\<close> are optional, variables occurring free in the assumptions
or the conclusion are always automatically bound. As usual, types may be specified for (some of)
the variables, so explicit bindings can be used as a central place for specifying types for the
variables, if necessary. The equivalent example with omitted binding is
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  "evn(0)" | "evn(n) \<Longrightarrow> evn(n+2)"\<close>}\index{evn (example constant)}

Alternatively a rule \<open>P\<^sub>i\<close> may be specified in the structured form described in
Section~\ref{theory-prop-struct}:
@{theory_text[display]
\<open>"name term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k" if "Q\<^sub>i\<^sub>,\<^sub>1" \<dots> "Q\<^latex>\<open>$_{i,q_i}$\<close>" for x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>\<close>}
where the assumptions and variables may be grouped by \<^theory_text>\<open>and\<close> and types may be specified for (some
of) the variable groups, however, no names may be specified for assumption groups, because no proof
is specified for the rules. In this form the example is written
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  "evn(0)" | "evn(n+2)" if "evn(n)"\<close>}\index{evn (example constant)}

The rules \<open>P\<^sub>i\<close> are introduction rules (see Section~\ref{methods-rule-intro}) for the defined
predicate \<open>name\<close> in the sense that they introduce a specific application of \<open>name\<close>, possibly
depending on other applications of \<open>name\<close>. An inductive definition turns the rules \<open>P\<^sub>i\<close> to valid
facts ``by definition'' under the fact set name \<open>name.intros\<close>\index{intros@.intros (fact name suffix)}. Explicit names for (some of) the
rules may be specified in the form
@{theory_text[display]
\<open>inductive name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
where rname\<^sub>1: P\<^sub>1 | \<dots> | rname\<^sub>n: P\<^sub>n\<close>}
Using this form the example can be written as
@{theory_text[display]
\<open>inductive evn :: "nat \<Rightarrow> bool" where
  zero: "evn(0)" | step: "evn(n) \<Longrightarrow> evn(n+2)"\<close>}\index{evn (example constant)}

The fact set \<open>name.intros\<close> together with other facts introduced by an inductive definition can be
displayed using the ``Print Context'' tab in the Query panel\index{panel!query $\sim$} as described in
Section~\ref{theory-theorem-search}.

Note that the syntax of the defining rules only allows to specify when the defined predicate is
\<open>True\<close>, not when it is \<open>False\<close>. In particular, a rule conclusion may not have the form of a negated
application \<open>\<not> name term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k\<close>.
\<close>

subsubsection "Semantics of an Inductive Definition"

text\<open>
To determine whether an application of the predicate to argument values yields the value \<open>True\<close>
the defining rules \<open>P\<^sub>i\<close> can be applied as introduction rules in backward reasoning steps (see
Section~\ref{methods-rule-backwards}) until the predicate is not present anymore. However, depending
on the rules, this may not succeed. If the defining rules \<open>P\<^sub>i\<close> would be the only information
available about the defined predicate, it would be underspecified for such cases. The specific
property of an \<^emph>\<open>inductive\<close> definition is the additional regulation that in all such cases the
predicate value is \<open>False\<close>. In other words, if it is not possible to prove that the predicate value
is \<open>True\<close> by using the defining rules it is defined to be \<open>False\<close>. This can happen in two ways.

In the first case there is no rule for which the conclusion unifies with the predicate application
term. Consider the trivial inductive definition
@{theory_text[display]
\<open>inductive uspec\<^sub>1 :: "nat \<Rightarrow> bool" where "uspec\<^sub>1 3" | "uspec\<^sub>1 4"\<close>}\index{uspec1@\<open>uspec\<^sub>1\<close> (example constant)}
The rules only unify with applications of \<open>uspec\<^sub>1\<close> to the argument values \<open>3\<close> and \<open>4\<close>, for them it
can be derived that the predicate value is \<open>True\<close>. For all other arguments the value is \<open>False\<close>.

In the example the value of \<open>(evn 3)\<close> is \<open>False\<close> because an application of the defining rule \<open>step\<close>
as backwards reasoning step leads to \<open>(evn 1)\<close> which does not unify with the conclusion of either
rule.

In the second case there are rule conclusions which unify with the predicate application term, but
there is no finite sequence of backward rule application steps which removes all occurrences of the
predicate. Consider the inductive definition
@{theory_text[display]
\<open>inductive uspec\<^sub>2 :: "nat \<Rightarrow> bool" where "uspec\<^sub>2 i \<Longrightarrow> uspec\<^sub>2 i"\<close>}\index{uspec2@\<open>uspec\<^sub>2\<close> (example constant)}
Although the rule is trivially valid it cannot be used to prove that \<open>uspec\<^sub>2\<close> is \<open>True\<close> for any
argument value. Therefore its value is \<open>False\<close> for all arguments.
\<close>

subsubsection "Monotonicity Properties"

text\<open>
Actually, this way of implicit specification when the predicate value is \<open>False\<close> is only possible
if all assumptions \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> used in the rules satisfy a ``monotonicity'' property for the defined
predicate. HOL is able to prove these properties for most forms of the assumptions \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>
automatically and then prove the rules themselves and additional rules to be facts. In the
interactive editor these proof activities are displayed in the Output panel.

A common case where a rule assumption \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> does not satisfy the monotonicity property is if it
contains an application of the defined predicate \<open>name\<close> in negated form. Consider the inductive
definition
@{theory_text[display]
\<open>inductive uspec\<^sub>3 :: "nat \<Rightarrow> bool" where "\<not> uspec\<^sub>3 i \<Longrightarrow> uspec\<^sub>3 i"\<close>}\index{uspec3@\<open>uspec\<^sub>3\<close> (example constant)}
Although if \<open>uspec\<^sub>3\<close> is defined as \<open>\<lambda>i. True\<close> it would satisfy the defining rule, the rule cannot
be used to prove that \<open>uspec\<^sub>3\<close> is \<open>True\<close> for any argument by applying the rule in backward reasoning
steps. Isabelle will signal an error for the inductive definition, stating that the monotonicity
proof failed for the assumption \<open>\<not> uspec\<^sub>3 i\<close>. Note that negation may also occur in other syntactic
forms like \<open>uspec\<^sub>3 i = False\<close> or \<open>uspec\<^sub>3 i \<Longrightarrow> i > 0\<close>.
\<close>

subsection "Fixed Arguments"
text_raw\<open>\label{holbasic-inductive-fixargs}\<close>

text\<open>
It may be the case that one or more arguments of the defined predicate are ``fixed''
\index{fixed!argument of inductive definition}\index{inductive definition!fixed argument of $\sim$}, i.e. in all
defining rules the values of these arguments in the conclusion are the same as in all assumptions.
If this is the case for the first \<open>m\<close> arguments the inductive definition can be specified in the
form
@{theory_text[display]
\<open>inductive name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> bool"
for y\<^sub>1 \<dots> y\<^sub>m
where P\<^sub>1 | \<dots> | P\<^sub>n\<close>}\index{for (keyword)}
The variables \<open>y\<^sub>i\<close> may be grouped by \<open>and\<close> and types may be specified for (some of) the groups.

Then the defining rules \<open>P\<^sub>i\<close> must have the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> name y\<^sub>1 \<dots> y\<^sub>m term\<^sub>i\<^sub>,\<^sub>m\<^sub>+\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k\<close>}
and every occurrence of \<open>name\<close> in the \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> must also have \<open>y\<^sub>1 \<dots> y\<^sub>m\<close> as its first \<open>m\<close> arguments.

Specifying fixed arguments is optional, it does not have any effect on the defined predicate,
however it makes the rules provided by HOL about the predicate simpler (see below).

As an example consider the inductive definition of a divides predicate
@{theory_text[display]
\<open>inductive divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
for m
where "divides m 0" | "divides m n \<Longrightarrow> divides m (n+m)"\<close>}\index{divides (example constant)}\<close>

subsection \<open>The {\sl cases} Rule\<close>
text_raw\<open>\label{holbasic-inductive-cases}\<close>

text\<open>
The general form of inductive definition constructs and automatically proves the additional rule\index{cases rule}\index{rule!cases $\sim$}
@{text[display]
\<open>\<lbrakk>name ?a\<^sub>1 \<dots> ?a\<^sub>k; RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>?a\<^sub>1=term\<^sub>i\<^sub>,\<^sub>1; \<dots>; ?a\<^sub>k=term\<^sub>i\<^sub>,\<^sub>k; Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> ?P\<close>}
and names it \<open>name.cases\<close>\index{cases@.cases (fact name suffix)}.

This rule has the form of an elimination rule for the predicate as described in
Section~\ref{case-elim-rules}. The major premise is the application \<open>name ?a\<^sub>1 \<dots> ?a\<^sub>k\<close> of the
defined predicate to arbitrary arguments. When the rule is applied by the methods \<^theory_text>\<open>erule\<close> or
\<^theory_text>\<open>cases\<close> to a goal it removes a predicate application from the goal assumptions or the input facts,
respectively, and splits the goal into cases according to the defining rules of the predicate.
The named cases created by the \<^theory_text>\<open>cases\<close> method are named by numbers starting with 1.

The \<open>cases\<close> rule for the evenness example is \<open>evn.cases\<close>:
@{text[display]
\<open>\<lbrakk>evn ?a; ?a = 0 \<Longrightarrow> ?P; \<And>n. \<lbrakk>?a = n + 2; evn n\<rbrakk> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}

Since it is a case rule it can be displayed by \<^theory_text>\<open>print_statement\<close> in the alternative form (see
Section~\ref{case-reasoning-altsynt}):
@{theory_text[display]
\<open>fixes a\<^sub>1 \<dots> a\<^sub>k
assumes "name a\<^sub>1 \<dots> a\<^sub>k"
obtains C\<^sub>1 | \<dots> | C\<^sub>n\<close>}
where every case \<open>C\<^sub>i\<close> has the form
@{theory_text[display]
\<open>x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close> where "a\<^sub>1=term\<^sub>i\<^sub>,\<^sub>1" \<dots> "a\<^sub>k=term\<^sub>i\<^sub>,\<^sub>k" "Q\<^sub>i\<^sub>,\<^sub>1" \<dots> "Q\<^latex>\<open>$_{i,q_i}$\<close>"\<close>}

Together with \<open>name.cases\<close> the similar rule \<open>name.simps\<close>\index{simps@.simps (fact name suffix)} is provided. It is an equation which
substitutes an arbitrary application of \<open>name\<close> by a disjunction of the cases according to the
defining \<open>P\<^sub>i\<close> and may be used by the simplifier (see Section~\ref{methods-simp-simp}). It is not
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
method in structured proofs (see Section~\ref{case-elim-struct}). The example above can be written
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
or even shorter (see Section~\ref{proof-struct-syntax}):
@{theory_text[display]
\<open>by cases simp_all\<close>}
Note that this only works if the consumed predicate application is taken as input fact, not if it
is a goal assumption as in the proof script above.
\<close>

subsection "The Induction Rule"
text_raw\<open>\label{holbasic-inductive-induct}\<close>

text\<open>
The general form of inductive definition also constructs and automatically proves the additional
rule\index{induction!rule}\index{rule!induction $\sim$}
@{text[display]
\<open>\<lbrakk>name ?a\<^sub>1 \<dots> ?a\<^sub>k; RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P ?a\<^sub>1 \<dots> ?a\<^sub>k\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1'; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>'\<rbrakk> \<Longrightarrow> ?P term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k\<close>}
and in the \<open>Q\<^sub>i\<^sub>,\<^sub>j'\<close> every application \<open>name t\<^sub>1 \<dots> t\<^sub>k\<close> of the predicate to argument terms is replaced
by the conjunction \<open>name t\<^sub>1 \<dots> t\<^sub>k \<and> ?P t\<^sub>1 \<dots> t\<^sub>k\<close>. The rule is named \<open>name.induct\<close>\index{induct@.induct (fact name suffix)}.

This rule has the form of an induction rule extended by elimination for the predicate as described
in Section~\ref{case-induction-elim}. The major premise is the application \<open>name ?a\<^sub>1 \<dots> ?a\<^sub>k\<close> of the
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
to the predicate's defining rules. See \<^cite>\<open>"prog-prove"\<close> for corresponding proof
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
Section~\ref{case-induction-elim}). The example above can be written
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
A simple case is an inductive definition where no rule assumption \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> contains an application
of the defined predicate \<open>name\<close>\index{inductive definition!single-step $\sim$}\index{single-step inductive definition}. Then for every defining rule a single backward reasoning step
will remove the predicate and determine its value. The rule \<open>name.cases\<close> contains the complete
information about the defined predicate and is sufficient for proving arbitrary properties about
it.

Every predicate defined by an Isabelle definition (see Section~\ref{theory-definition-defs})
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
inductive definition of the extended form\index{inductive definition!mutually $\sim$}\index{mutually inductive definition}
@{theory_text[display]
\<open>inductive name\<^sub>1 \<dots> name\<^sub>m
where P\<^sub>1 | \<dots> | P\<^sub>n\<close>}
The \<open>name\<^sub>i\<close> may be grouped by \<open>and\<close> and types may be specified for (some of) the groups.

The defining rules \<open>P\<^sub>i\<close> have the same form as described above, however, every conclusion may be an
application of one of the defined predicates \<open>name\<^sub>i\<close> (with arbitrary ordering of the rules) and
every rule assumption \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> may contain applications of all defined predicates.

The following example defines predicates for even and odd numbers in a mutually inductive way:
@{theory_text[display]
\<open>inductive evn odd :: "nat \<Rightarrow> bool" where
  "evn(0)" | "odd(n) \<Longrightarrow> evn(n+1)" | "evn(n) \<Longrightarrow> odd(n+1)"\<close>}\index{evn (example constant)}\index{odd (example constant)}

The set of defining rules is named \<open>name\<^sub>1_\<dots>_name\<^sub>m.intros\<close>\index{intros@.intros (fact name suffix)}. For every \<open>name\<^sub>i\<close> separate rules
\<open>name\<^sub>i.cases\<close>\index{cases@.cases (fact name suffix)} and \<open>name\<^sub>i.simps\<close>\index{simps@.simps (fact name suffix)} are created which cover only the defining rules with \<open>name\<^sub>i\<close> in
the conclusion. As induction rules the set \<open>name\<^sub>1_\<dots>_name\<^sub>m.inducts\<close>\index{inducts@.inducts (fact name suffix)} is created containing for every
\<open>name\<^sub>i\<close> an induction rule with an application of \<open>name\<^sub>i\<close> as major premise. Additionally, a rule
\<open>name\<^sub>1_\<dots>_name\<^sub>m.induct\<close>\index{induct@.induct (fact name suffix)} is generated without elimination where the conclusion is an explicit case
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
called ``well-founded''\index{relation!well-founded $\sim$}\index{well-founded relation} if every non-empty set of values of type \<open>t\<close> has a ``leftmost'' element \<open>x\<close>
for \<open>r\<close> which means that there is no \<open>y\<close> so that \<open>r y x\<close>. If the relation \<open>(<)\<close> (see
Section~\ref{holbasic-equal-order}) is well-founded for a type \<open>t\<close> this is usually described by
``every non-empty set has a minimal element''. 

HOL provides the predicate
@{text[display]
\<open>wfP :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool\<close>}\index{wfP (constant)}
which tests an arbitrary binary relation for being well-founded. The predicate
@{text[display]
\<open>wf :: ('a \<times> 'a) set \<Rightarrow> bool\<close>}\index{wf (constant)}
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
For every well-founded relation \<open>r\<close> the following principle of (transfinite) induction\index{induction!transfinite $\sim$} is valid:
If a property holds for a value whenever it holds for all values ``left'' to it, the property holds
for all values.

HOL provides the induction rules with elimination (see Section~\ref{case-induction-elim})

@{text\<open>wfp_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=2] wfp_induct_rule}\index{wfp-induct-rule@wfp$\_$induct$\_$rule (fact name)}
@{text\<open>wf_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=2] wf_induct_rule}\index{wf-induct-rule@wf$\_$induct$\_$rule (fact name)}

Their major premise is well-foundedness of the relation \<open>?r\<close>. The single case corresponds to the
induction principle.
\<close>
thm wf_induct_rule
subsection "The Accessible Part of a Relation"
text_raw\<open>\label{holbasic-wellfounded-accp}\<close>

text\<open>
For an arbitrary binary relation \<open>r\<close> of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> generally not all values of \<open>t\<close> can be
reached in a finite number of relation steps from a leftmost element. HOL defines the predicate
\<open>Wellfounded.accp\<close> by the inductive definition (see Section~\ref{holbasic-inductive})
@{theory_text[display]
\<open>inductive accp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where "(\<And>y. r y x \<Longrightarrow> accp r y) \<Longrightarrow> accp r x"\<close>}\index{accp (constant)}
Its partial application \<open>accp r\<close> to a binary relation \<open>r\<close> is the predicate which is \<open>True\<close> for all
values of \<open>t\<close> which can be reached in a finite number of relation steps from a leftmost element.
These values are called the ``accessible part'' of relation \<open>r\<close>\index{relation!accessible part of $\sim$}.

HOL also defines the equivalent set-valued function (see Section~\ref{holbasic-pred-set}) for
relations represented as tuple sets (see Section~\ref{holbasic-tuples-rel})
@{text[display]
\<open>acc :: "('a \<times> 'a) set \<Rightarrow> 'a set"\<close>}\index{acc (constant)}
which returns the accessible part of a relation as a set.

A binary relation \<open>r\<close> of type \<open>t \<Rightarrow> t \<Rightarrow> bool\<close> is well-founded if and only if its accessible part
\<open>accp r\<close> covers all values of \<open>t\<close>. If \<open>r\<close> is not well-founded there may be several leftmost values
in \<open>t\<close> or no such value (in the latter case the accessible part is empty).

For arbitrary binary relations the induction principle can be used on the accessible part. The
corresponding induction rules provided by HOL are

@{text\<open>accp_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=1] accp_induct_rule}
\index{accp-induct-rule@accp$\_$induct$\_$rule (fact name)}

@{text\<open>acc_induct_rule:\<close>}\vspace{-2ex}@{thm[display,indent=1] acc_induct_rule}
\index{acc-induct-rule@acc$\_$induct$\_$rule (fact name)}

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
\<open>f :: t \<Rightarrow> nat\<close> is called a ``measure function''\index{measure function}\index{function!measure $\sim$}.

HOL provides the polymorphic function
@{text[display]
\<open>measure :: ('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set\<close>}\index{measure (constant)}
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
\<open>size :: 'a \<Rightarrow> nat\<close>}\index{size (constant)}
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
As a useful method for proving elimination rules (see Section~\ref{case-elim-rules}) including the
more specific case rules (see Section~\ref{case-reasoning-rules}) and the goals of \<^theory_text>\<open>obtain\<close>
statements (see Section~\ref{proof-obtain}) HOL introduces the proof method
@{theory_text[display]
\<open>atomize_elim\<close>}\index{atomize-elim@atomize$\_$elim (method)}
It only affects the first goal. Assume that this goal has the form of an elimination rule
@{theory_text[display]
\<open>theorem "\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m; P\<^sub>1; \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> P" \<proof>\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>,\<^sub>1\<dots>x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1;\<dots>;Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> P\<close>}
(see Section~\ref{case-elim-rules}). The method converts the goal to the form
@{theory_text[display]
\<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>m\<rbrakk> \<Longrightarrow> D\<^sub>1 \<or> \<dots> \<or> D\<^sub>p\<close>}
where every \<open>D\<^sub>i\<close> has the form \<open>\<exists>x\<^sub>i\<^sub>,\<^sub>1\<dots>x\<^latex>\<open>$_{i,p_i}$\<close>. Q\<^sub>i\<^sub>,\<^sub>1 \<and> \<dots> \<and> Q\<^latex>\<open>$_{i,q_i}$\<close>\<close>. For the quantifier \<open>\<exists>\<close> and the boolean
operators \<open>\<or>\<close> and \<open>\<and>\<close> see Section~\ref{holtypes-bool-funcs}. Because the converted goal does not
contain the technical variable \<open>P\<close> any more and uses the boolean operators it is sometimes easier
to prove it.

If the method is applied to the initial goal of the example elimination rule theorem
@{theory_text[display]
\<open>theorem elimexmp: "\<lbrakk>(x::nat) \<le> c; x < c \<Longrightarrow> P; x = c \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"\<close>}\index{elimexmp (example fact)}
in Section~\ref{case-elim-rules} it converts the goal to
@{text[display]
\<open>x \<le> c \<Longrightarrow> x < c \<or> x = c\<close>}
which can be solved by method \<open>auto\<close>.

If \<open>atomize_elim\<close> is applied to the initial goal of the example case rule theorem
@{theory_text[display]
\<open>theorem mycaserule: "\<lbrakk>n = 0 \<Longrightarrow> P; n \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"\<close>}\index{mycaserule (example fact)}
in Section~\ref{case-reasoning-rules} it converts the goal to
@{text[display]
\<open>n = 0 \<or> n \<noteq> 0\<close>}
which can be solved by method \<open>simp\<close>.

If \<open>atomize_elim\<close> is applied to the initial goal of the example \<^theory_text>\<open>obtain\<close> statement
@{theory_text[display]
\<open>obtain y z where "x = y - 3" and "y + z = 2*x +8"\<close>}
in Section~\ref{proof-obtain-prove} it converts the goal to
@{text[display]
\<open>\<exists>y z. x = y - 3 \<and> y + z = 2 * x + 8\<close>}
which can be solved by method \<open>arith\<close> (see Section~\ref{methods-auto-methods}).
\<close>

section "Recursive Functions"
text_raw\<open>\label{holbasic-recursive}\<close>

text\<open>
HOL supports the definition of recursive\index{recursion} functions\index{function!recursive $\sim$}\index{definition!recursive $\sim$}\index{recursive definition} in the form
@{theory_text[display]
\<open>function name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n \<proof>\<close>}\index{function (keyword)}\index{where (keyword)}\index{/bar@\<open>|\<close> (keyword)}
The type specification for the function may be omitted if it can be derived from the use of the
function in the \<open>eq\<^sub>i\<close>.

The definition resembles an Isabelle definition as described in
Section~\ref{theory-definition-defs}, but instead of a single defining equation there may be
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
Section~\ref{theory-prop-rules}) with an equation as its conclusion:
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> name term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k = term\<^sub>i\<close>}
It is specified in inner syntax. The separating bars \<open>|\<close> belong to the outer syntax, therefore each
equation must be separately quoted. Note that the conclusion must be an equation using the symbol
\<open>=\<close> instead of \<open>\<equiv>\<close>. The left side of the equation is restricted to the form of a (non-partial)
application of the defined function to argument terms, i.e., if the defined function has \<open>k\<close>
arguments according to its type, in every equation it must be applied to \<open>k\<close> terms. If the
conclusion is no equation or if the left side has a different form an error is signaled.

Other than in an Isabelle definition the equations may be recursive, i.e. the defined function
\<open>name\<close> may be used in \<open>term\<^sub>i\<close> on the right side of the equation (but not in the \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> or \<open>term\<^sub>i\<^sub>,\<^sub>j\<close>).
It may be used in arbitrary ways, also by partial application or by passing it as argument to other
functions.

The familiar example of the faculty function can be defined using two defining equations in the form
@{theory_text[display]
\<open>function fac :: "nat \<Rightarrow> nat" where
  "fac 0 = 1"
| "\<And>n. n > 0 \<Longrightarrow> fac n = n * fac (n-1)"
\<proof>\<close>}\index{fac (example constant)}

The bound variables \<open>x\<^sub>i\<^sub>,\<^sub>1, \<dots>, x\<^latex>\<open>$_{i,p_i}$\<close>\<close> may occur in the assumptions and in the conclusion. However, if
a bound variable occurs in \<open>term\<^sub>i\<close> on the right side it must also occur in one or more of the
\<open>term\<^sub>i\<^sub>,\<^sub>j\<close> on the left side, otherwise an error is signaled.

After termination has been proved (see Section~\ref{holbasic-recursive-term}) for the recursive
function definition the defining equations are available as the fact set
\<open>name.simps\<close>.\index{simps@.simps (fact name suffix)} Note that no defining equation \<open>name_def\<close> (see Section~\ref{theory-theorem-defs})
exists for recursively defined functions, instead the set \<open>name.simps\<close> plays the corresponding role.
\<close>

subsubsection "Alternative Rule Forms"

text\<open>
As for derivation rules specified in theorems
(see Section~\ref{theory-theorem-spec}) the explicit bindings are optional, variables occurring
free in the assumptions or the conclusion are always automatically bound. As usual, types may be
specified for (some of) the variables, so explicit bindings can be used as a central place for
specifying types for the variables, if necessary. An equivalent definition for the faculty is
@{theory_text[display]
\<open>function fac :: "nat \<Rightarrow> nat" where
  "fac 0 = 1"
| "n > 0 \<Longrightarrow> fac n = n * fac (n-1)"
\<proof>\<close>}\index{fac (example constant)}
where the binding of \<open>n\<close> is omitted.

Alternatively an equation \<open>eq\<^sub>i\<close> may be specified in the structured form described for derivation
rules in Section~\ref{theory-prop-struct}:
@{theory_text[display]
\<open>"name term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k = term\<^sub>i" if "Q\<^sub>i\<^sub>,\<^sub>1" \<dots> "Q\<^latex>\<open>$_{i,q_i}$\<close>" for x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>\<close>}
where the assumptions and variables may be grouped by \<open>and\<close> and types may be specified for (some of)
the variable groups, however, no names may be specified for assumption groups.

In this form the faculty definition becomes
@{theory_text[display]
\<open>function fac :: "nat \<Rightarrow> nat" where
  "fac 0 = 1"
| "fac n = n * fac (n-1)" if "n > 0"
\<proof>\<close>}\index{fac (example constant)}

Note that on the left side of the equations the arguments may be specified by arbitrary terms, not
only by variables. Therefore the faculty function can also be defined in the form
@{theory_text[display]
\<open>function fac2 :: "nat \<Rightarrow> nat" where
  "fac2 0 = 1"
| "fac2 (n+1) = (n+1) * fac2 n"
\<proof>\<close>}\index{fac2 (example constant)}
where the assumption is not required anymore for the second equation.

It is also possible to explicitly name (some of) the single equations by specifying the recursive
definition in the form
@{theory_text[display]
\<open>function name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type" where 
  eqname\<^sub>1: eq\<^sub>1 | \<dots> | eqname\<^sub>n: eq\<^sub>n \<proof>\<close>}

Every function \<open>name\<close> defined by the Isabelle definition (see Section~\ref{theory-definition-defs})
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
As described in Section~\ref{theory-terms-functions} functions in Isabelle must be total, they must be
defined for all possible arguments. It is easy to fail doing so when specifying the defining
equations for a recursive function definition. Consider
@{theory_text[display]
\<open>function nototal :: "nat \<Rightarrow> nat" where
  "nototal 5 = 6" \<proof>\<close>}\index{nototal (example constant)}
The function is only defined for the value \<open>5\<close>, no definition is given for the other natural
numbers.

Therefore HOL expects a proof that the equations are complete in the sense that they cover all
possible cases for the function arguments. In the general case it creates a goal of the form
@{text[display]
\<open>\<And>P x.
  \<lbrakk>\<And>x\<^sub>1\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{1,p_1}$\<close>. \<lbrakk>Q\<^sub>1\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{1,q_1}$\<close>; x = (term\<^sub>1\<^sub>,\<^sub>1, \<dots>, term\<^sub>1\<^sub>,\<^sub>k)\<rbrakk> \<Longrightarrow> P;
     \<dots>
   \<And>x\<^sub>n\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{n,p_n}$\<close>. \<lbrakk>Q\<^sub>n\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{n,q_n}$\<close>; x = (term\<^sub>n\<^sub>,\<^sub>1, \<dots>, term\<^sub>n\<^sub>,\<^sub>k)\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P\<close>}
which must be proved in the recursive function definition's \<open>\<proof>\<close>. This goal has the form of a
case rule (see Section~\ref{case-reasoning-rules}) before replacing the variable \<open>P\<close> by an unknown
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
It can be proved by method \<open>auto\<close> (see Section~\ref{methods-auto-methods}).

After the proof of the recursive function definition the goal is available as a case rule
named \<open>name.cases\<close>\index{cases@.cases (fact name suffix)}. If applied by the proof method \<open>cases\<close> (see Section~\ref{case-reasoning-cases})
it splits a goal and introduces named cases (named by numbers starting at 1) according to the
argument regions in the defining equations of function \<open>name\<close>.

If the function \<open>name\<close> has only one argument \<open>name.cases\<close> is a usual case rule for the argument
type, otherwise it is a case rule for the type of the argument tuples.
\<close>

subsubsection "Using Proof Method \<open>atomize_elim\<close>"

text\<open>
Since the goal has the form of a case rule the method \<open>atomize_elim\<close>\index{atomize-elim@atomize$\_$elim (method)} (see
Section~\ref{holbasic-atomize}) can be applied to it. It converts the general form of the goal
to the form
@{text[display]
\<open>\<And>x.
    (\<exists> x\<^sub>1\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{1,p_1}$\<close>. Q\<^sub>1\<^sub>,\<^sub>1 \<and> \<dots> \<and> Q\<^latex>\<open>$_{1,q_1}$\<close> \<and> x = (term\<^sub>1\<^sub>,\<^sub>1, \<dots>, term\<^sub>1\<^sub>,\<^sub>k)
  \<or> \<dots> 
  \<or> (\<exists> x\<^sub>n\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{n,p_n}$\<close>. Q\<^sub>n\<^sub>,\<^sub>1 \<and> \<dots> \<and> Q\<^latex>\<open>$_{n,q_n}$\<close> \<and> x = (term\<^sub>n\<^sub>,\<^sub>1, \<dots>, term\<^sub>n\<^sub>,\<^sub>k)\<close>}
which directly expresses that the cases together cover all possibilities and may be easier to prove. 
In many simple cases of recursive function definitions, however, the method is not necessary and
the goal can be proved by an automatic method like \<open>auto\<close> or \<open>blast\<close> (see
Section~\ref{methods-auto-methods}).

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
\<proof>\<close>}\index{evn (example constant)}
because the cases \<open>0\<close>, \<open>1\<close>, and \<open>n+2\<close> cover all natural numbers.

However, this is not always possible. It may not be possible to give an explicit specification for
the arguments where the predicate value is \<open>False\<close> or the termination proof (see
Section~\ref{holbasic-recursive-term}) may fail.

Generally, an inductive definition\index{inductive definition}\index{definition!inductive $\sim$} is simpler because it only specifies the positive cases and only
these must be proved in proofs of properties of the defined predicate. On the other hand, if the
negative cases are of interest they are directly provided by a recursive definition and the
defining equations of a recursive definition can be used for rewriting (see
Section~\ref{methods-simp}).
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
\<proof>\<close>}\index{nounique (example constant)}
The function maps the value \<open>5\<close> to two different values \<open>6\<close> and \<open>7\<close> (and thus is no function
anymore).

Therefore HOL expects a proof that the equations are compatible in the sense that they cover
disjoint arguments spaces or, if the spaces of two equations overlap, the equations specify the same
function values on the overlapping regions. In the general case HOL creates (after the goal for
equation completeness) for every pair of equations \<open>eq\<^sub>i\<close> and \<open>eq\<^sub>j\<close> where \<open>i \<le> j\<close> a goal of the form
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close> x\<^sub>j\<^sub>,\<^sub>1' \<dots> x\<^latex>\<open>$_{j,p_j}$\<close>'.
  (term\<^sub>i\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>k) = (term\<^sub>j\<^sub>,\<^sub>1, \<dots>, term\<^sub>j\<^sub>,\<^sub>k) \<Longrightarrow> term\<^sub>i = term\<^sub>j\<close>}
Here \<open>x\<^sub>j\<^sub>,\<^sub>b'\<close> is a renamed \<open>x\<^sub>j\<^sub>,\<^sub>b\<close> to avoid a name clash with an \<open>x\<^sub>i\<^sub>,\<^sub>a\<close> if necessary. The renamed
variables are consistently replaced in all terms. Moreover, all occurrences of the defined function
\<open>name\<close> in \<open>term\<^sub>i\<close> and \<open>term\<^sub>j\<close> are replaced by \<open>name_sumC\<close>\index{sumC@$\_$sumC (constant name suffix)} which is the uncurried (see
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
a single application of method \<open>auto\<close> (see Section~\ref{methods-auto-methods}).
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
  by auto\<close>}\index{uspec (example constant)}
The proof of equation completeness and compatibility is successfully done by the \<open>auto\<close> method and
the definition introduces the total function \<open>uspec\<close>, however, no information is available about its
result values.

Information about result values must either be specified directly on the right side of a
non-recursive equation \<open>eq\<^sub>i\<close> or it must be derivable by a finite number of substitutions using the
equations. Such a substitution mainly replaces the function arguments specified on the left side
of the equation by the arguments used in the recursive calls on the right side.

Therefore HOL creates for every recursive definition of a function \<open>name\<close> the relation \<open>name_rel\<close>\index{rel@$\_$rel (constant name suffix)}
which relates for all defining equations the arguments of every recursive call on the right side to
the arguments on the left side. Actually, \<open>name_rel\<close> relates argument tuples, like the arguments of
\<open>name_sumC\<close> as described above. It is defined inductively (see
Section~\ref{holbasic-inductive}) using defining rules of the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> 
  name_rel (term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>k) (term\<^sub>i\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>k)\<close>}
where \<open>term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>l\<close> is the \<open>l\<close>-th argument in the \<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>. There is
one such rule for every recursive call occurring in the defining equations \<open>eq\<^sub>i\<close>. The defined
relation \<open>name_rel\<close> never occurs in the \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>, therefore it is a single-step inductive definition
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
  "name_dom \<equiv> Wellfounded.accp name_rel"\<close>}\index{dom@$\_$dom (constant name suffix)}
called the ``domain predicate''\index{domain predicate}\index{predicate!domain $\sim$} for the argument tuples for which \<open>name\<close> is fully specified.

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
proof. The domain predicate is used in these rules to exclude underspecified cases. The rules can be
displayed using the ``Print Context'' tab in the Query panel\index{panel!query $\sim$} as described in
Section~\ref{theory-theorem-search}.
\<close>

subsubsection "Simplification Rules"

text\<open>
HOL automatically creates and proves simplification rules which directly correspond to the defining
equations \<open>eq\<^sub>i\<close>. Every such rule is guarded by the domain predicate for the arguments of the
substituted function application. For the equation \<open>eq\<^sub>i\<close> in the general form as given above the
rule is
@{text[display]
\<open>\<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>; name_dom (term\<^sub>i\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>k)\<rbrakk> \<Longrightarrow>
  name term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k = term\<^sub>i\<close>}
where all occurrences of the bound variables \<open>x\<^sub>i\<^sub>,\<^sub>1, \<dots>, x\<^latex>\<open>$_{i,p_i}$\<close>\<close> have been replaced by corresponding
unknowns. The set of all these simplification rules is named \<open>name.psimps\<close>\index{psimps@.psimps (fact name suffix)}. The rules are not added
to the simpset automatically, they can be explicitly used for ``unfolding'' the recursive definition
in one or more steps. If individual names have been specified for (some of) the \<open>eq\<^sub>i\<close> these names
denote the corresponding facts in \<open>name.psimps\<close>.
\<close>

subsubsection "Elimination Rule"

text\<open>
HOL also creates an elimination rule (see Section~\ref{case-elim-rules}) \<open>name.pelims\<close>\index{pelims@.pelims (fact name suffix)} where the
major premise has the form \<open>name ?x\<^sub>1 \<dots> ?x\<^sub>k = ?y\<close> and the rule replaces it mainly by case
assumptions according to the defining equations.
\<close>

subsubsection "Induction Rule"

text\<open>
HOL also creates and proves a single induction rule \<open>name.pinduct\<close>\index{pinduct@.pinduct (fact name suffix)} of the form
@{text[display]
\<open>\<lbrakk>name_dom (?a\<^sub>1, \<dots>, ?a\<^sub>k); RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P ?a\<^sub>1 \<dots> ?a\<^sub>k\<close>}
where every \<open>RA\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. 
  \<lbrakk>name_dom (term\<^sub>i\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>k); Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>; R\<^sub>i\<^sub>,\<^sub>1; \<dots>; R\<^latex>\<open>$_{i,r_i}$\<close>\<rbrakk>
  \<Longrightarrow> ?P term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k\<close>}
and every \<open>R\<^sub>i\<^sub>,\<^sub>j\<close> has the form \<open>?P term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>k\<close> where \<open>term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>l\<close> is the \<open>l\<close>-th argument in the
\<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>.

It can be used for induction with elimination (see Section~\ref{case-induction-elim}) where the
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
\<open>termination name \<proof>\<close>}\index{termination (keyword)}
which is called a ``termination proof''\index{termination proof}\index{proof!termination $\sim$} for the recursive function \<open>name\<close>. If \<open>name\<close> is omitted
it refers to the last previously defined recursive function.
\<close>

subsubsection "The Proof Method \<open>relation\<close>"

text\<open>
Note that this theorem is equivalent to the property that the relation \<open>name_rel\<close> is well-founded.
As described in Section~\ref{holbasic-wellfounded-measure} it can be proved by proving that
\<open>name_rel x y \<Longrightarrow> (measure f) x y\<close> holds for a measure function \<open>f :: (t\<^sub>1 \<times> \<dots> \<times> t\<^sub>k) \<Rightarrow> nat\<close>. HOL
provides the proof method
@{theory_text[display]
\<open>relation "M"\<close>}\index{relation (method)}
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
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> 
  ((term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>k), (term\<^sub>i\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>k)) \<in> M\<close>}
where \<open>term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>l\<close> is the \<open>l\<close>-th argument in the \<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>. The goals
\<open>R\<^sub>1, \<dots>, R\<^sub>r\<close> together are equivalent to the goal \<open>name_rel x y \<Longrightarrow> M x y\<close>.

The proof method is usually applied in the form
@{theory_text[display]
\<open>relation "measure f"\<close>}
for an appropriate measure function\index{measure function}\index{function!measure $\sim$} \<open>f\<close> as above. It must be constructed so that for every tuple 
\<open>(term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>k)\<close> of arguments for a recursive call the value is strictly lower than for
the argument tuple \<open>(term\<^sub>i\<^sub>,\<^sub>1, \<dots>, term\<^sub>i\<^sub>,\<^sub>k)\<close> in the defining equations \<open>eq\<^sub>i\<close>. The resulting goals
\<open>wf (measure f)\<close> and \<open>R\<^sub>1, \<dots>, R\<^sub>r\<close> are often solved by method \<open>auto\<close> (see
Section~\ref{methods-auto-methods}). Then the termination proof has the form
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
\<open>lexicographic_order\<close>}\index{lexicographic-order@lexicographic$\_$order (method)}
and the stronger method
@{theory_text[display]
\<open>size_change\<close>}\index{size-change@size$\_$change (method)}
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
rules \<open>name.simps\<close>\index{simps@.simps (fact name suffix)}, \<open>name.elims\<close>\index{elims@.elims (fact name suffix)}, and \<open>name.induct\<close>\index{induct@.induct (fact name suffix)}. They result from the corresponding rules
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
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>; R\<^sub>i\<^sub>,\<^sub>1; \<dots>; R\<^latex>\<open>$_{i,r_i}$\<close>\<rbrakk>
  \<Longrightarrow> ?P term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k\<close>}
and every \<open>R\<^sub>i\<^sub>,\<^sub>j\<close> has the form \<open>?P term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>k\<close> where \<open>term\<^sub>i\<^sub>,\<^sub>j\<^sub>,\<^sub>l\<close> is the \<open>l\<close>-th argument in the
\<open>j\<close>-th recursive call of \<open>name\<close> in \<open>term\<^sub>i\<close>.

For the faculty function defined as above the induction rule \<open>fac.induct\<close> is
@{text[display]
\<open>\<lbrakk>?P 0; \<And>n. \<lbrakk>0 < n; ?P (n - 1)\<rbrakk> \<Longrightarrow> ?P n\<rbrakk> \<Longrightarrow> ?P ?a\<close>}

To use the rule with the proof methods \<open>induct\<close> and \<open>induction\<close> (see
Section~\ref{case-induction-naming}) it must always be specified explicitly in the form
@{text[display]
\<open>induct \<dots> rule: name.induct\<close>}

All these rules can be displayed using the ``Print Context'' tab in the Query panel\index{panel!query $\sim$} as described in
Section~\ref{theory-theorem-search}, if the curser is positioned after the termination proof.\<close>

subsection "Mutual Recursion"
text_raw\<open>\label{holbasic-recursive-mutual}\<close>

text\<open>
If several recursive functions are defined depending on each other they must be defined together in
a single recursive definition\index{mutual recursive definition}\index{recursive definition!mutual $\sim$}\index{definition!mutual recursive $\sim$} of the form
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

section "Functors"
text_raw\<open>\label{holbasic-functor}\<close>

text\<open>
The content of this and the following section are not required for understanding most of the
remaining chapters and may be skipped upon first reading. However, some of the concepts in the
remaining chapters are based on functors and these two sections may be useful for fully
understanding these concepts.

A type constructor such as \<open>set\<close> (see Section~\ref{theory-terms-types}) can be seen as a mapping
from types to types, mapping an arbitrary type \<open>T\<close> to the type \<open>T set\<close> having as values sets of
values of type \<open>T\<close>. However, the mapping does not specify any details about the values of \<open>T\<close>. From
category theory the concept of a ``functor''\index{functor} can be used to extend type constructors
in that direction.

A functor for \<open>set\<close> additionally maps functions on the values of \<open>T\<close> to functions on the values of
\<open>T set\<close>.\<close>

subsection "Mappers"
text_raw\<open>\label{holbasic-functor-mapper}\<close>

text\<open>
For a type constructor \<open>C\<close> such a mapping can be specified to lead from functions on a type parameter
\<open>'a\<close> to functions on the polymorphic type \<open>'a C\<close> (see Section~\ref{theory-terms-types}). Such a
mapping is itself a function of the polymorphic type \<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a C \<Rightarrow> 'a C)\<close>. Such functions
are called ``mappers''\index{mapper} or ``mapper functions''\index{mapper function}\index{function!mapper $\sim$}
for the type constructor \<open>C\<close>. A mapper is said to ``lift''\index{lifting} functions on \<open>'a\<close> to functions on \<open>'a C\<close>.

More generally, a mapper may have the type \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a C \<Rightarrow> 'b C)\<close> and lift functions between
two types to functions between the corresponding types constructed by \<open>C\<close>. Since the type constructor
\<open>C\<close> is directly determined by the mapper's type, a functor may be fully specified by the mapper
without explicitly naming the type constructor.

To be a mapper for a functor, \<open>m\<close> must satisfy two additional properties: it must be compatible with
function composition and with the identity function. This may be expressed by the two laws
@{text[display]
\<open>comp: (m f) \<circ> (m g) = m (f \<circ> g)
id: m id = id\<close>}\index{comp (fact name)}\index{id (fact name)}
where \<open>\<circ>\<close>\index{/comp@\<open>\<circ>\<close> (operator)} denotes function composition (see Section~\ref{holtypes-func-funcs})
and \<open>id\<close>\index{id (constant)} denotes the (polymorphic) identity function\index{identity function}
\index{function!identity $\sim$} (see Section~\ref{holtypes-func-values}).

These properties allow to lift an arbitrary term built from function applications by lifting the
individual functions and building the corresponding term from the results. For this reason functors
provide a versatile basic tool for transferring terms between types.

As an example the function \<open>image :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set\<close>\index{image (constant)} (see Section~\ref{holtypes-set-funcs})
maps every function \<open>f\<close> to \<open>image f\<close> which returns for a set \<open>A\<close> of members of type \<open>'a\<close> the set of
\<open>f\<close>-values of these members, i.e., \<open>image f\<close> applies \<open>f\<close> to all members of its argument sets. \<open>image\<close>
is a mapper for the type constructor \<open>set\<close>, because the facts \<open>comp\<close> and \<open>id\<close> are satisfied for it.
Therefore \<open>set\<close> is a functor with \<open>image\<close> as its mapper. \<open>image\<close> lifts every function \<open>f :: 'a \<Rightarrow> 'b\<close>
to a function of type \<open>'a set \<Rightarrow>'b set\<close>.

Not every function with the type of a mapper is a mapper, for example the function \<open>\<lambda>f. (\<lambda>A. {})\<close>
which maps every function \<open>f\<close> to the constant function returning the empty set is not a mapper
because it does not satisfy the law \<open>id\<close>.

Mappers are not unique for type constructors. For example, the function \<open>\<lambda>f. id\<close>
which maps every function to the identity function is a (trivial) mapper for all type constructors.

There is a second kind of mapper type for type constructors \<open>C\<close>. It has the form
\<open>('b \<Rightarrow> 'a) \<Rightarrow> 'a C \<Rightarrow> 'b C\<close> (i.e., the direction of \<open>'a\<close> and \<open>'b\<close> is reversed). Mappers of this
type are called ``contravariant mappers''\index{mapper!contravariant $\sim$}. To distinguish both
the other kind of mappers is also called ``covariant mappers''\index{mapper!covariant $\sim$}. The
law \<open>comp\<close> for a contravariant mapper \<open>m\<close> has the slightly different form
@{text[display]
\<open>comp: (m f) \<circ> (m g) = m (g \<circ> f)\<close>}

As an example, the function \<open>vimage\<close>\index{vimage (constant)} (see Section~\ref{holtypes-set-funcs})
which maps every function to its reverse image on sets is a contravariant mapper
for \<open>set\<close>.

Often the intended mapper which causes a type constructor \<open>C\<close> to be a functor is assumed to be known
implicitly, then \<open>C\<close> is simply said to be a functor without explicitly specifying the mapper.
\<close>

subsection "Multivariate Functors"
text_raw\<open>\label{holbasic-functor-multi}\<close>

text\<open>
The concept of functors can be extended to type constructors with more than one type parameters. For
a type constructor \<open>C\<close> with \<open>n\<close> parameters the mapper type has the form
@{text[display]
\<open>('a\<^sub>1\<Rightarrow>'b\<^sub>1) \<Rightarrow> \<dots> \<Rightarrow> ('a\<^sub>n\<Rightarrow>'b\<^sub>n) \<Rightarrow> ('a\<^sub>1,\<dots>,'a\<^sub>n) C \<Rightarrow> ('b\<^sub>1,\<dots>,'b\<^sub>n) C\<close>}
A corresponding mapper lifts \<open>n\<close> functions to a single function between the types constructed by \<open>C\<close>
from the argument or result types, respectively.

The functor laws are extended accordingly:
@{text[display]
\<open>comp: (m f\<^sub>1 \<dots> f\<^sub>n) \<circ> (m g\<^sub>1 \<dots> g\<^sub>n) = m (f\<^sub>1\<circ>g\<^sub>1) \<dots> (f\<^sub>n\<circ>g\<^sub>n)
id: m id \<dots> id = id\<close>}
In category theory the resulting functors are also called ``multivariate functors''
\index{functor!multivariate $\sim$}\index{multivariate functor}.

As an example consider the type constructor \<open>prod\<close>\index{prod (type)} (see Section~\ref{holtypes-tup}) for the type
of pairs. It has two type parameters and the polymorphic type \<open>('a\<^sub>1, 'a\<^sub>2) prod\<close> may be
abbreviated by \<open>'a\<^sub>1 \<times> 'a\<^sub>2\<close> (see Section~\ref{holbasic-tuples}). Therefore the mapper type for \<open>prod\<close>
has the form \<open>('a\<^sub>1 \<Rightarrow> 'b\<^sub>1) \<Rightarrow> ('a\<^sub>2 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> ('a\<^sub>1,'a\<^sub>2) prod \<Rightarrow> ('b\<^sub>1,'b\<^sub>2) prod\<close>. A possible mapper
is the function \<open>map_prod \<equiv> \<lambda>f\<^sub>1 f\<^sub>2. \<lambda>(x,y). (f\<^sub>1 x, f\<^sub>2 y)\<close>\index{map-prod@map$\_$prod (constant)} (see Section~\ref{holtypes-tup-funcs}).
It applies \<open>f\<^sub>1\<close> to the first component of the pair \<open>(x,y)\<close> and \<open>f\<^sub>2\<close> to the second component. In this
way it lifts \<open>f\<^sub>1\<close> and \<open>f\<^sub>2\<close> to a function on pairs. It can easily be verified that \<open>map_prod\<close> satisfies
the functor laws and causes \<open>prod\<close> to be a functor.

A mapper type for \<open>n\<close> parameters may also be contravariant in some parameters and covariant in the
other parameters. Then the \<open>comp\<close> law must be modified accordingly, by reversing the function
compositions for those parameters.

As an example consider the type constructor \<open>fun\<close>\index{fun (type)} (see Section~\ref{theory-terms-functions}) for
function types. It has two type parameters and the polymorphic type \<open>('a\<^sub>1, 'a\<^sub>2) fun\<close> may be
abbreviated by \<open>'a\<^sub>1 \<Rightarrow> 'a\<^sub>2\<close>. Therefore a mapper type for \<open>fun\<close> may have the form
\<open>('b\<^sub>1 \<Rightarrow> 'a\<^sub>1) \<Rightarrow> ('a\<^sub>2 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> ('a\<^sub>1,'a\<^sub>2) fun \<Rightarrow> ('b\<^sub>1,'b\<^sub>2) fun\<close>
which is contravariant in the first parameter and covariant in the second. A possible mapper of this
type is the function \<open>map_fun \<equiv> \<lambda>f\<^sub>1 f\<^sub>2. \<lambda>f. f\<^sub>2 \<circ> f \<circ> f\<^sub>1\<close>\index{map-fun@map$\_$fun (constant)} (see Section~\ref{holtypes-func-funcs}).
It can easily be verified that it satisfies the functor laws and causes \<open>fun\<close> to be a functor.

Similar to a partial function application (see Section~\ref{theory-terms-multargs}) some of the
parameters of a type constructor with \<open>n\<close> parameters may be filled by specific constant types,
resulting in a type constructor with the remaining type parameters only. If one of \<open>n\<close> parameters of
a type constructor is filled by a constant type the resulting type constructor has \<open>n-1\<close> parameters.
Whenever a type constructor is a functor all type constructors resulting from filling some parameters
by constant types are also functors. The mappers for them are constructed by partially applying the
original mapper to the identity function in the corresponding arguments.

As an example the polymorphic type \<open>(nat, 'a) fun\<close> is equivalent to a type constructor with one
parameter. For every type \<open>'a\<close> its values are the functions from natural numbers to result values of
type \<open>'a\<close>. Since \<open>fun\<close> is a functor this type constructor is also a functor and its mapper is
\<open>map_fun id\<close> which is \<open>\<lambda>f\<^sub>2. \<lambda>f. f\<^sub>2 \<circ> f \<circ> id\<close> and thus is equivalent to the function composition \<open>\<circ>\<close>.

Even more generally an arbitrary polymorphic type expression built from several type constructors may be
considered as a mapping from the type parameters to the resulting type instances and thus may
satisfy the properties of a functor if combined with a corresponding mapper. Whenever all
constructors used for the type are functors, then the resulting type is also a functor and the
mapper can always be constructed from the mappers of the constructors. This property is called
``composability''\index{functor!composability of $\sim$} of functors.

As an example the polymorphic type expression \<open>('a\<^sub>1 set, 'a\<^sub>2) fun\<close> denotes a functor because \<open>set\<close> and \<open>fun\<close> are
functors. The mapper is of type
\<open>('b\<^sub>1 \<Rightarrow> 'a\<^sub>1) \<Rightarrow> ('a\<^sub>2 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> ('a\<^sub>1 set, 'a\<^sub>2) fun \<Rightarrow> ('b\<^sub>1 set, 'b\<^sub>2) fun\<close> and may be defined as
\<open>\<lambda> f\<^sub>1 f\<^sub>2. map_fun (image f\<^sub>1) f\<^sub>2\<close> from the mappers \<open>image\<close> and \<open>map_fun\<close>.
\<close>

subsection "Registering Functors"
text_raw\<open>\label{holbasic-functor-reg}\<close>

text\<open>
Functors are used by HOL for several purposes. Therefore HOL provides an outer syntax construct for
``registering'' a functor, i.e., making known to HOL that a function is a mapper for a functor:
@{theory_text[display]
\<open>functor "term" \<proof>\<close>}\index{functor (keyword)}
where \<open>term\<close> is a term for a function of a mapper type for a type constructor \<open>C\<close>. It is mainly an
abbreviation for
@{theory_text[display]
\<open>theorem "c &&& i" \<proof>\<close>}
where \<open>c\<close> and \<open>i\<close> are the propositions for the \<open>comp\<close> and \<open>id\<close> laws according to the mapper type.
The proof must prove that \<open>term\<close> satisfies these laws and is thus a mapper for \<open>C\<close>.
As proved facts the laws are automatically named \<open>C.comp\<close> and \<open>C.id\<close>. Using these names the facts
may then be used in proofs of other theorems. The facts can be displayed using the ``Print Context''
tab in the Query panel\index{panel!query $\sim$} as described in Section~\ref{theory-theorem-search}.

If more than one mapper shall be registered for the same type constructor the fact name prefix may
be specified explicitly in the form
@{theory_text[display]
\<open>functor pre: "term" \<proof>\<close>}
resulting in the fact names \<open>pre.comp\<close> and \<open>pre.id\<close>.

Both forms of the registration command provide the laws in two additional alternative forms named
\<open>pre.compositionality\<close> and \<open>pre.identity\<close>.

The registration works for arbitrary multivariate functors with arbitrary contravariant parameters. The
corresponding forms of \<open>c\<close> and \<open>i\<close> are automatically determined from the type of the \<open>term\<close>. The
registration does not work for arbitrary polymorphic type expressions built from several constructors because
their functor property always follows from those of the single constructors.
\<close>

section "Bounded Natural Functors"
text_raw\<open>\label{holbasic-bnf}\<close>

text\<open>
The most important use of functors in HOL is their special case of ``bounded natural functors''
\index{bounded natural functor}\index{functor!bounded natural $\sim$} (BNF)\index{BNF}. It is
closely related to the support of type definitions in HOL described in Chapter~\ref{holtdefs}.
\<close>

subsection "Natural Functors"
text_raw\<open>\label{holbasic-bnf-natural}\<close>

text\<open>
HOL calls a single-parameter functor \<open>C\<close> with mapper \<open>m\<close> ``natural''\index{natural functor}
\index{functor!natural $\sim$} if there is a function \<open>s\<close> of
type \<open>'a C \<Rightarrow> 'a set\<close> which satisfies the laws
@{text[display]
\<open>set_map: s \<circ> (m f)  = (image f) \<circ> s
map_cong0: (\<And>z. z \<in> s x \<Longrightarrow> f z = g z) \<Longrightarrow> m f x = m g x\<close>}\index{set-map@set$\_$map (fact name)}\index{map-cong0@map$\_$cong0 (fact name)}

Note that \<open>set\<close> is also a single-parameter functor, thus \<open>s\<close> is a mapping from one functor type to
another. In category theory such mappings are called ``natural transformation'' if they satisfy the
law \<open>set_map\<close>. For this reason the functor \<open>C\<close> is called ``natural'' in HOL. The transformation \<open>s\<close>
is usually called a ``set-function''\index{set-function}\index{function!set-} in HOL.
\<close>

subsubsection "Container Types"

text\<open>
Natural functors model container types\index{container type}\index{type!container $\sim$}
such as lists or trees which are often used as data types in
programming. They consist of a ``shape'' (the container) and a ``content'' (the contained values).
The type of the contained values is specified by the functor's type parameter, the container shape
is determined by the functor. Thus the same shape may be instantiated to have content of arbitrary
type.

In this view the set-function \<open>s\<close> returns the content of a container value as the set of the
content values. The function \<open>m f\<close> replaces content values by applying a function \<open>f\<close> to them. The
law \<open>set_map\<close> states that the content after applying \<open>f\<close> lifted by the mapper is the same as applying
\<open>f\<close> to each value of the original content. The law \<open>map_cong0\<close> states that a function lifted by \<open>m\<close>
has no effect on the shape and only affects the content: if \<open>f\<close> and \<open>g\<close> have the same effect on the
content of \<open>x\<close> the lifted functions \<open>m f\<close> and \<open>m g\<close> already have the same effect on the whole
container \<open>x\<close>.

As an example consider the functor \<open>(nat,'a) fun\<close> with mapper \<open>\<circ>\<close> (see Section~\ref{holbasic-functor-multi}).
Its values are functions from natural numbers to the values of \<open>'a\<close>. They can be viewed to be
infinite containers of numbered values of \<open>'a\<close>. The common shape is the infinite sequence of
slots numbered by natural numbers. Together with the set-function \<open>range :: ('a \<Rightarrow> 'b) \<Rightarrow> 'b set\<close>\index{range (constant)}
(see Section~\ref{holtypes-func-funcs}), which maps every function to the set of all its possible
result values, this is a natural functor. Viewed as a container the content of a function is the set
of its possible result values, which is retrieved by \<open>range\<close>. It is easily verified that the laws
\<open>set_map\<close> and \<open>map_cong0\<close> are satisfied.

Another example is the functor \<open>set\<close> itself. Using the identity \<open>id\<close> as set-function, the laws
are trivially satisfied, therefore \<open>set\<close> is a natural functor. The container shape is the set, the
content consists of the set elements.
\<close>

subsubsection "Natural Multivariate Functors"

text\<open>
As for functors (see Section~\ref{holbasic-functor-multi}) the concept of natural functors can be
extended to type constructors with more than one parameter. Then a separate set-function \<open>s\<^sub>i\<close> is
required for every type parameter \<open>'a\<^sub>i\<close>. A multivariate functor \<open>C\<close> with \<open>n\<close> type parameters \<open>'a\<^sub>1,\<dots>,'a\<^sub>n\<close> is
natural, if there are functions \<open>s\<^sub>i :: ('a\<^sub>1,\<dots>,'a\<^sub>n) C \<Rightarrow> 'a\<^sub>i set\<close> for \<open>i = 1,\<dots>,n\<close> satisfying the
laws
@{text[display]
\<open>set_map: 
  s\<^sub>1 \<circ> (m f\<^sub>1 \<dots> f\<^sub>n)  = (image f\<^sub>1) \<circ> s\<^sub>1
  \<dots>
  s\<^sub>n \<circ> (m f\<^sub>1 \<dots> f\<^sub>n)  = (image f\<^sub>n) \<circ> s\<^sub>n
map_cong0:
  \<lbrakk>\<And>z\<^sub>1. z\<^sub>1 \<in> s\<^sub>1 x \<Longrightarrow> f\<^sub>1 z = g\<^sub>1 z;
   \<dots>;
   \<And>z\<^sub>n. z\<^sub>n \<in> s\<^sub>n x \<Longrightarrow> f\<^sub>n z = g\<^sub>n z\<rbrakk>
  \<Longrightarrow> (m f\<^sub>1 \<dots> f\<^sub>n) x = (m g\<^sub>1 \<dots> g\<^sub>n) x\<close>}
\index{set-map@set$\_$map (fact name)}\index{map-cong0@map$\_$cong0 (fact name)}

Seen as container type, a natural multivariate functor has content of different types corresponding to its
type parameters. Every set-function \<open>s\<^sub>i\<close> retrieves the set of content values of type \<open>'a\<^sub>i\<close>. The
function \<open>(m f\<^sub>1 \<dots> f\<^sub>n)\<close> lifted by the mapper selectively applies its \<open>n\<close> argument functions to the
corresponding content values.

As an example consider the multivariate functor \<open>prod\<close> with mapper \<open>map_prod\<close> (see Section~\ref{holbasic-functor-multi}).
Using the functions \<open>\<lambda>(x,y). {x}\<close> and \<open>\<lambda>(x,y). {y}\<close> as set-functions, which return the singleton
sets of the first or second component, respectively, \<open>prod\<close> is a natural (multivariate) functor. The type
\<open>('a\<^sub>1, 'a\<^sub>2) prod\<close> is a container type, having as content a single value of type \<open>'a\<^sub>1\<close> and a single
value of type \<open>'a\<^sub>2\<close>.

As for functors the concept of natural functors can immediately be extended to arbitrary polymorphic
type expressions. Like functors, natural functors are composable: if all type constructors used in a type
expression are natural functors then the resulting type is also a natural functor and the
set-functions can be constructed from those of the type constructors.
\<close>

subsubsection "Live and Dead Type Parameters"

text\<open>
The multivariate functor \<open>fun\<close> with mapper \<open>map_fun\<close> (see Section~\ref{holbasic-functor-multi}) is no
natural functor because it has a contravariant type parameter. The definition of natural functors
in HOL requires that all its type parameters must be covariant. However, if the first type parameter
is instantiated by an arbitrary type, such as in \<open>(nat,'a) fun\<close> (see above), the resulting type
expression always denotes a natural functor. 

This situation is described by saying that \<open>fun\<close> is a natural functor with one ``dead''
type parameter\index{type!parameter!dead $\sim$} (the first one). The second type parameter is
called ``live''\index{type!parameter!live $\sim$}. In general a natural
functor may have several dead and live type parameters. A set-function only exists for
each live type parameter and the mapper lifts only functions for the live type parameters.

Seen as container type, the dead type parameters contribute to the container shape, the live type
parameters specify the types of content values. In the example \<open>(nat,'a) fun\<close> the type \<open>nat\<close>
determines the shape as being an infinite sequence of numbered slots. If it is replaced by
\<open>bool\<close> the type \<open>(bool,'a) fun\<close> is a container with only two slots for content values of type \<open>'a\<close>.

A dead type parameter may also be covariant, then the corresponding values are also considered to be
parts of the shape instead of being content. Whether a type parameter is live or dead is determined
by the type of the mapper and by the number and types of the set-functions.

If natural functors are composed all type parameters of a constructor used on a dead parameter
position of another constructor become dead for the resulting type. As an example the type
\<open>('a\<^sub>1 set, 'a\<^sub>2) fun\<close> (see Section~\ref{holbasic-functor-multi}) has the dead parameter \<open>'a\<^sub>1\<close> because
\<open>'a\<^sub>1 set\<close> occurs on the position of the dead parameter of \<open>fun\<close>. The parameter \<open>'a\<^sub>2\<close> is live and the 
corresponding set-function is \<open>range\<close>.
\<close>

subsection "Predicators and Relators"
text_raw\<open>\label{holbasic-bnf-predrel}\<close>

text\<open>
There are two other useful functions for every natural functor \<open>C\<close> with mapper \<open>m\<close> and set-function
\<open>s\<close>. These are called ``predicator''\index{predicator function}\index{function!predicator $\sim$}
and ``relator''\index{relator function}\index{function!relator $\sim$}.
\<close>

subsubsection "The Predicator"

text\<open>
A predicator is a function \<open>p :: ('a \<Rightarrow> bool) \<Rightarrow> ('a C \<Rightarrow> bool)\<close>, i.e., it lifts predicates (see
Section~\ref{holbasic-pred-pred}) on type \<open>'a\<close> to predicates on type \<open>'a C\<close>. It must satisfy the law
@{text[display]
\<open>pred_set: p P = (\<lambda>x. \<forall>v\<in>(s x). P v)\<close>}\index{pred-set@pred$\_$set (fact name)}
which directly specifies a definition for \<open>p\<close>: for a container value \<open>x\<close> the lifted predicate \<open>p P\<close>
is valid if the original predicate \<open>P\<close> is valid for all content values retrieved by \<open>s x\<close> (for the
syntax see Section~\ref{holtypes-set-funcs}). Since \<open>p\<close> can be constructed in this way from the
set-function \<open>s\<close>, a predicator is available for every natural functor.

The predicator for \<open>(nat,'a) fun\<close> is the function \<open>\<lambda>P. \<lambda>f. \<forall>v\<in>(range f). P v\<close>. The lifted predicate
tests the possible result values of \<open>f\<close> whether the predicate \<open>P\<close> is valid for all of them.

For a natural multivariate functor the predicator has the type \<open>('a\<^sub>1\<Rightarrow>bool) \<Rightarrow>\<dots>\<Rightarrow> ('a\<^sub>n\<Rightarrow>bool) \<Rightarrow> (('a\<^sub>1,\<dots>,'a\<^sub>n) C \<Rightarrow> bool)\<close>.
It lifts \<open>n\<close> predicates on the type parameters to a combined predicate on the functor type. The law
\<open>pred_set\<close> is accordingly extended to apply to each set of content values the predicate corresponding
to their type.

The predicator for \<open>prod\<close> is the function \<open>pred_prod\<close>\index{pred-prod@pred$\_$prod (constant)} (see Section~\ref{holtypes-tup-funcs}).
It lifts two predicates \<open>P\<^sub>1, P\<^sub>2\<close> on \<open>'a\<^sub>1\<close> and \<open>'a\<^sub>2\<close>, respectively, to the predicate on pairs of type
\<open>('a\<^sub>1, 'a\<^sub>2) prod\<close> which tests the first component by \<open>P\<^sub>1\<close> and the second component by \<open>P\<^sub>2\<close>.

Predicators are composable: if a type expression consists of composed natural functors, the
predicators can be composed in the same way to yield a predicator for the resulting type. As example
the predicator for the type \<open>('a\<^sub>1, ('a\<^sub>2, 'a3) prod) prod\<close> is \<open>\<lambda>P\<^sub>1 P\<^sub>2 P\<^sub>3. pred_prod P\<^sub>1 (pred_prod P\<^sub>2 P\<^sub>3)\<close>.
\<close>

subsubsection "The Relator"

text\<open>
A relator is a function \<open>r :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a C \<Rightarrow> 'b C \<Rightarrow> bool)\<close>, i.e., it lifts relations
(see Section~\ref{holbasic-pred-rel}) between types \<open>'a\<close> and \<open>'b\<close> to relations between types \<open>'a C\<close>
and \<open>'b C\<close>. It must satisfy the law
@{text[display]
\<open>in_rel: r R =
  (\<lambda>x y. \<exists>z::('a\<times>'b) C. \<forall>(a,b)\<in>(s z). R a b
                       \<and> (m fst) z = x \<and> (m snd) z = y)\<close>}\index{in-rel@in$\_$rel (fact name)}
which specifies a definition for \<open>r\<close> using both \<open>s\<close> and \<open>m\<close> (for the inner syntax used here
see Chapter~\ref{holtypes}).
It tests two containers \<open>x :: 'a C\<close> and \<open>y :: 'b C\<close> whether they are related by the relation lifted
from \<open>R :: 'a\<Rightarrow>'b\<Rightarrow>bool\<close>. For this it uses a container \<open>z\<close> of type \<open>('a\<times>'b) C\<close> where all contained
values are pairs (see Section~\ref{holbasic-tuples}). Using the set-function \<open>s\<close> it retrieves these
pairs and tests whether their components are related by \<open>R\<close>. Using the mapper \<open>m\<close> applied to the selector
functions \<open>fst\<close> and \<open>snd\<close> for the components of a pair (see Section~\ref{holbasic-tuples}) it
replaces every contained pair in \<open>z\<close> by its first or second component, respectively, which must
result in the containers \<open>x\<close> and \<open>y\<close> tested for being related. Since \<open>r\<close> can be constructed in this
way from \<open>s\<close> and \<open>m\<close>, a relator is available for every natural functor.

The construction of the container \<open>z\<close> of type \<open>('a\<times>'b) C\<close> for the containers \<open>x\<close> and \<open>y\<close> of type
\<open>'a C\<close> and \<open>'b C\<close> is a generalization of the well-known function ``zip'' in functional programming,
which constructs the list of pairs of corresponding elements from two lists. Therefore this
construction is called ``zip construction''\index{zip construction} in this introduction, \<open>z\<close> is
called a ``zipped container'', and \<open>x\<close> and \<open>y\<close> are called ``unzipped containers''.

Trivially, a relator \<open>r\<close> always lifts equality to equality: \<open>r (=)\<close> has type \<open>'a C \<Rightarrow> 'a C \<Rightarrow> bool)\<close>
and relates two containers if they have the same shape and their content is the same.

The relator for \<open>(nat,'a) fun\<close> is the function \<open>\<lambda>R. \<lambda>f g. \<forall>i::nat. R (f i) (g i)\<close>. The lifted
relation tests for all natural numbers \<open>i\<close> whether the result values \<open>f i\<close> and \<open>g i\<close> are related
by \<open>R\<close>.

For a natural multivariate functor the relator has the type \<open>('a\<^sub>1\<Rightarrow>'b\<^sub>1\<Rightarrow>bool) \<Rightarrow>\<dots>\<Rightarrow> ('a\<^sub>n\<Rightarrow>'b\<^sub>n\<Rightarrow>bool) \<Rightarrow> (('a\<^sub>1,\<dots>,'a\<^sub>n) C \<Rightarrow> ('b\<^sub>1,\<dots>,'b\<^sub>n) C \<Rightarrow> bool)\<close>.
It lifts \<open>n\<close> relations between types \<open>'a\<^sub>i\<close> and \<open>'b\<^sub>i\<close> to a combined relation between the functor types
constructed from the \<open>'a\<^sub>i\<close> and \<open>'b\<^sub>i\<close>, respectively. The law \<open>in_rel\<close> is extended accordingly, using
\<open>(m fst \<dots> fst)\<close> and \<open>(m snd \<dots> snd)\<close> to extract the unzipped containers \<open>x\<close> and \<open>y\<close> from the zipped
container \<open>z\<close>.

The relator for \<open>prod\<close> is the function \<open>rel_prod\<close> (see Section~\ref{holtypes-tup-funcs}).
It lifts two relations \<open>R\<^sub>1, R\<^sub>2\<close> between \<open>'a\<^sub>1, 'b\<^sub>1\<close> and \<open>'a\<^sub>2, 'b\<^sub>2\<close>, respectively, to the relation
between pairs of type \<open>('a\<^sub>1, 'a\<^sub>2) prod\<close> and \<open>('b\<^sub>1, 'b\<^sub>2) prod\<close> which compares the first components
by \<open>R\<^sub>1\<close> and the second components by \<open>R\<^sub>2\<close>.

Like predicators relators are composable: if a type expression consists of composed natural functors,
the relators can be composed in the same way to yield a relator for the resulting type. As example
the relator for the type \<open>('a\<^sub>1, ('a\<^sub>2, 'a3) prod) prod\<close> is \<open>\<lambda>R\<^sub>1 R\<^sub>2 R\<^sub>3. rel_prod R\<^sub>1 (rel_prod R\<^sub>2 R\<^sub>3)\<close>.
\<close>

subsubsection "Predicator and Relator for Functions"

text\<open>
Although \<open>fun\<close> has no set-function for its contravariant first type parameter, a
predicator and relator can be defined for it. HOL provides the functions
@{text[display]
\<open>pred_fun :: ('p\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>1, 'p\<^sub>2) fun \<Rightarrow> bool
  \<equiv> \<lambda>p\<^sub>1 p\<^sub>2 f. \<forall>x. p\<^sub>1 x \<longrightarrow> p\<^sub>2 (f x)\<close>}\index{pred-fun@pred$\_$fun (constant)}
and
@{text[display]
\<open>rel_fun :: ('p\<^sub>1 \<Rightarrow> 'q\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> 'q\<^sub>2 \<Rightarrow> bool)
  \<Rightarrow> ('p\<^sub>1, 'p\<^sub>2) fun \<Rightarrow> ('q\<^sub>1, 'q\<^sub>2) fun \<Rightarrow> bool
  \<equiv> \<lambda>r\<^sub>1 r\<^sub>2 f g. \<forall>x y. r\<^sub>1 x y \<longrightarrow> r\<^sub>2 (f x) (g y)\<close>}\index{rel-fun@rel$\_$fun (constant)}
which lift predicates or relations, respectively, from argument and result type to the function
type.

As an example using the predicate \<open>evn\<close> from Section~\ref{holbasic-inductive-defrules}, the partial
application \<open>pred_fun evn evn\<close> is the predicate of type \<open>(nat \<Rightarrow> nat) \<Rightarrow> bool\<close> which tests whether
a function on natural numbers maps all even numbers to even numbers.

As for the mapper \<open>map_fun\<close> the predicator and relator for an instantiation \<open>(T, 'a) fun\<close> such as
\<open>(nat, 'a) fun\<close> (see Section~\ref{holbasic-functor-multi}) can be obtained by partial application.
The predicator for \<open>(nat,'a) fun\<close> (see above) is equal to \<open>pred_fun (\<lambda>_. True)\<close>, the relator for
\<open>(nat,'a) fun\<close> (see above) is equal to \<open>rel_fun (=)\<close>. Note that these functions are also polymorphic
for the argument type, so they can be used for functions of arbitrary types \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close>.

Since functions with multiple arguments in curried form (see Section~\ref{holbasic-tuples-funarg})
have functions as intermediate result values the lifting can be iterated over multiple arguments.
For example, a relation \<open>r\<close> on the result type \<open>t\<close> can be lifted to binary functions of type
\<open>t\<^sub>1 \<Rightarrow> t\<^sub>2 \<Rightarrow> t\<close> by \<open>rel_fun (=) (rel_fun (=) r)\<close> which is equivalent to the relation on functions
\<open>\<lambda>f g. \<forall>x y. r (f x y) (g x y))\<close>.
\<close>

subsection "Bounded Natural Functors"
text_raw\<open>\label{holbasic-bnf-bounded}\<close>

text\<open>
A natural functor is called ``bounded''\index{bounded natural functor}\index{functor!bounded natural $\sim$},
if the size of its content is restricted. The shape is not
arbitrarily ``elastic'' to admit content value sets of arbitrary large cardinality. For a multivariate
functor to be bounded, the content sets for all live type parameters must be bounded. In this
introduction (and also in other HOL documentation) bounded natural functors are usually abbreviated
as BNF.

The natural functor \<open>set\<close> (see Section~\ref{holbasic-bnf-natural}) is not bounded. Depending on
the type substituted for the type parameter \<open>'a\<close>, a container value of type \<open>'a set\<close> may have
arbitrary large cardinality, because the universal set \<open>UNIV\<close> (see Section~\ref{holtypes-set-values})
always contains all values of type \<open>'a\<close>.

The natural functor \<open>prod\<close> is bounded, because every container value has only two content values,
independent of their types. The natural functor \<open>(nat, 'a) fun\<close> is bounded, because every container
has countably many content values, even if \<open>'a\<close> is instantiated by a type with more values, such as
the type of real numbers.

More generally, the bound may not depend on the live type parameters, but it may depend on the dead
type parameters, because they contribute to the shape instead of the content. Therefore the natural
functor \<open>fun\<close> with one dead and one live type parameter is bounded by the cardinality of the
function argument type which is specified by the dead type parameter.

There is a second requirement for a bounded natural functor, stated as the law
@{text[display]
\<open>(r R\<^sub>1\<dots>R\<^sub>n) OO (r S\<^sub>1\<dots>S\<^sub>n) \<le> r (R\<^sub>1 OO S\<^sub>1) \<dots> (R\<^sub>n OO S\<^sub>n)\<close>}
where \<open>r\<close> is the relator (see Section~\ref{holbasic-bnf-predrel}) of a natural functor
with \<open>n\<close> live type parameters. The operator \<open>OO\<close> is relation composition (see
Section~\ref{holbasic-pred-rel}), the ordering \<open>\<le>\<close> on relations is the usual ``stronger as''
ordering (see Section~\ref{holtypes-func-funcs}). The other direction \<open>\<ge>\<close> of the ordering is
automatically satisfied, together the law states distributivity of the relator \<open>r\<close> with respect to
relation composition. Therefore the law is also called ``subdistributivity of the relator''.

BNFs are composable: Whenever in a type expression all type constructors occurring on live type
parameter positions are bounded, then the type denoted by the expression is bounded as well. The type
\<open>('a\<^sub>1 set, 'a\<^sub>2) fun\<close> (see Section~\ref{holbasic-bnf-natural}) is a BNF because
the constructor \<open>set\<close>, which is not bounded, occurs on the position of the dead parameter of \<open>fun\<close>.
\<close>

subsubsection "Cardinalities"

text\<open>
HOL represents cardinalities\index{cardinality} by specific binary ordering relations of type \<open>('a\<times>'a) set\<close> (see
Section~\ref{holbasic-tuples-rel}). The predicate \<open>card_order :: ('a\<times>'a) set \<Rightarrow> bool\<close>\index{card-order@card$\_$order (constant)}
determines such relations. The predicate \<open>regularCard :: ('a\<times>'a) set \<Rightarrow> bool\<close>\index{regularCard (constant)}
test the specific property of being ``regular'', the predicate \<open>cinfinite :: ('a\<times>'a) set \<Rightarrow> bool\<close>\index{cinfinite (constant)}
tests a cardinality for being infinite.

The cardinality of the natural numbers, usually denoted by \<open>\<aleph>\<^sub>0\<close> in mathematics, corresponds
to the ordering \<open>(\<le>)\<close> (see Section~\ref{holbasic-equal-order}) on type \<open>nat\<close>, HOL defines the
constant name \<open>natLeq\<close>\index{natLeq (constant)} for it. The function \<open>card_suc\<close>\index{card-suc@card$\_$suc (constant)}
maps a cardinality to the next higher cardinality. The cardinality of a set can be determined
by the function \<open>card_of :: 'a set \<Rightarrow> ('a\<times>'a) set\<close>\index{card-of@card$\_$of (constant)} and
cardinalities can be compared by \<open>ordLess2 :: ('a\<times>'a) set \<Rightarrow> ('a\<times>'a) set \<Rightarrow> bool\<close>\index{ordLess2 (constant)}
for being strictly ranked. The syntax \<open>|A|\<close> for \<open>card_of A\<close> and the operator name
\<open>(<o)\<close>\index{/ordless2@\<open><o\<close> (operator)} for \<open>ordLess2\<close> are available after using the command
@{theory_text[display]
\<open>unbundle cardinal_syntax\<close>}\index{cardinal_syntax@cardinal$\_$syntax (bundle)}
on theory level, which is available after importing the theory \<^theory>\<open>Main\<close> (see
Section~\ref{system-invoke-theory}).

The theories \<^theory>\<open>HOL.BNF_Cardinal_Order_Relation\<close> and  \<^theory>\<open>HOL.BNF_Cardinal_Arithmetic\<close>
introduce many rules which can be used to prove goals about cardinalities.
\<close>

subsection "Registering Bounded Natural Functors"
text_raw\<open>\label{holbasic-bnf-register}\<close>

text\<open>
Some type definition mechanisms in HOL, as described in Chapter~\ref{holtdefs}, require the
information whether a type constructor is a BNF. Therefore HOL supports
registering BNFs (i.e., adding them to internal HOL data structures so that they can be retrieved
by HOL mechanisms). In most cases this need not be done explicitly, because
the type definition mechanisms automatically register newly defined types as bounded natural
functor, if applicable.
\<close>

subsubsection "The \<^theory_text>\<open>bnf\<close> Command"

text\<open>
A polymorphic type with \<open>n\<close> type parameters is registered as BNF using the
outer syntax command
@{theory_text[display]
\<open>bnf name: "type" 
  map: "term" sets: "term\<^sub>1" \<dots> "term\<^sub>m" bd: "bterm" \<proof>\<close>}\index{bnf (keyword)}
\index{map: (keyword)}\index{sets: (keyword)}\index{bd: (keyword)}
where \<open>term\<close> is a function of a mapper type for the \<open>type\<close>, the \<open>term\<^sub>i\<close> are set functions for the
\<open>type\<close> and \<open>bterm\<close> is an infinite regular cardinality which is strictly larger than that of all sets
returned by the set functions. As usual, the terms need not be quoted, if they consist of a single
identifier. The \<open>map:\<close>, \<open>sets:\<close>, and \<open>bd:\<close> are keywords and are part of the command syntax.

The type is registered with \<open>m\<close> live type parameters, the remaining parameters are considered dead.
The live type parameters are determined from the types of the set functions, the type of the mapper
function must match exactly, otherwise an error is signaled.

The command generates \<open>7+2*m\<close> goals which must be proved in the \<open>\<proof>\<close>. These are the two functor
laws \<open>comp\<close> and \<open>id\<close> (see Section~\ref{holbasic-functor-mapper}), the law \<open>map_cong0\<close> and \<open>m\<close> laws
\<open>set_map\<close> for a natural functor (see Section~\ref{holbasic-bnf-natural}), \<open>m\<close> laws of the form
\<open>|term\<^sub>i| <o bterm\<close> for the cardinality bound, the goals \<open>card_order bterm\<close>, \<open>regularCard bterm\<close>,
and \<open>cinfinite bterm\<close>, and the law for the subdistributivity of the (automatically constructed)
relator (see Section~\ref{holbasic-bnf-bounded}).

After the proof of these facts is completed HOL uses them to construct and automatically prove
about 40 other named facts. They can be displayed using the ``Print Context'' tab in the Query
panel\index{panel!query $\sim$} as described in Section~\ref{theory-theorem-search}, if the cursor
is positioned after the proof of the \<^theory_text>\<open>bnf\<close> command.

All fact names use the \<open>name\<close> specified in the \<open>bnf\<close> command as prefix. In some cases \<open>name\<close> may be
omitted and is automatically constructed from the \<open>type\<close>. This is possible if the \<open>type\<close> is a
single type constructor \<open>C\<close> applied to type variables, then \<open>C\<close> is used as prefix.

As an example, the natural multivariate functor \<open>prod\<close> (see Section~\ref{holbasic-bnf-natural}) can be
registered as a BNF using the command
@{theory_text[display]
\<open>bnf myprod: "('a, 'b) prod" 
  map: map_prod sets: "\<lambda>(x,y).{x}" "\<lambda>(x,y).{y}" bd: natLeq \<proof>\<close>}
Since both set functions return finite sets (singletons) the cardinality \<open>natLeq\<close> of the natural
numbers can be used as strictly larger infinite bound. A name must be specified because HOL already
registers this type as BNF under its type name \<open>prod\<close>.

The natural functor \<open>(nat,'a) fun\<close> (see Section~\ref{holbasic-bnf-natural}) can be registered as a
BNF by
@{theory_text[display]
\<open>bnf natfun: "((nat, 'a) fun)"
  map: "(\<circ>) :: ('b \<Rightarrow> 'c) \<Rightarrow> ((nat, 'b) fun) \<Rightarrow> ((nat, 'c) fun)"
  sets: "range :: ((nat, 'a) fun) \<Rightarrow> 'a set"
  bd: "card_suc natLeq" \<proof>\<close>}
The types for the mapper and set function must be specified to restrict the general functions
\<open>(\<circ>)\<close> and \<open>range\<close> to the specific functions on natural numbers. The cardinality of the content set
is not larger than that of the natural numbers, therefore its successor \<open>card_suc natLeq\<close> can be
used as strictly larger bound.

For an example that registers \<open>fun\<close> as a BNF with one dead and one live parameter
including the proof see \<^cite>\<open>"Section 6.2, introductory examples" in datatypes\<close>
\<close>

subsubsection "Registering Relator and Predicator"

text\<open>
If required, HOL automatically constructs the relator and predicator
(see Section~\ref{holbasic-bnf-predrel}) for a registered bounded natural functor, using names of the 
form \<open>pred_name\<close> and \<open>rel_name\<close>. However, it is also possible to define these as named functions and add
them to the registration, so that they can be used by HOL. This is done by an extended \<^theory_text>\<open>bnf\<close>
command of the form
@{theory_text[display]
\<open>bnf \<dots> rel: "rterm" pred: "pterm" \<proof>\<close>}\index{rel: (keyword)}\index{pred: (keyword)}
where \<open>rterm\<close> is a term for the relator and \<open>pterm\<close> is a term for the predicator. The predicator
is optional, the relator may only be omitted together with the predicator.

In this extended form the command generates the additional goals \<open>in_rel\<close> and \<open>pred_set\<close> which must
be proved to show that the specified functions actually correspond to the definition of a relator
or predicator, respectively.

As an example \<open>prod\<close> can be registered together with its relator and predicator by
@{theory_text[display]
\<open>bnf myprod: "('a, 'b) prod" 
  map: map_prod sets: "\<lambda>(x,y).{x}" "\<lambda>(x,y).{y}" bd: natLeq
  rel: rel_prod pred: pred_prod \<proof>\<close>}
\<close>

subsubsection "Registering the Mapper Function"

text\<open>
The command \<^theory_text>\<open>bnf name: "type" map: "term" \<dots>\<close> does not register the \<open>term\<close> specified for the mapper
function as a functor (see Section~\ref{holbasic-functor-reg}). This may cause problems when HOL
needs only the functor property of \<open>type\<close> later. An example is the definition of a quotient type
(see Section~\ref{holtdefs-quot}). It signals a warning if a quotient type is defined for a type
that has not been registered as a functor.

To make a registered BNF known as a functor it must explicitly be registered as functor in the form
@{theory_text[display]
\<open>functor "term" \<proof>\<close>}
where \<open>term\<close> denotes the mapper function specified in the \<^theory_text>\<open>bnf\<close> command.

Although the \<^theory_text>\<open>bnf\<close> command does not register the type as functor, it provides the facts \<open>comp\<close> and
\<open>id\<close> which must be proved for the \<open>functor\<close> command, named \<open>map_comp\<close> and \<open>map_id0\<close> prefixed by the
\<open>name\<close> specified in the \<^theory_text>\<open>bnf\<close> command. Therefore it is easiest to register a type as functor after
registering it as BNF, reusing the facts provided by the \<^theory_text>\<open>bnf\<close> command for the proof of the
\<^theory_text>\<open>functor\<close> command. After type \<open>prod\<close> has been registered as BNF as above it can be registered as
functor using
@{theory_text[display]
\<open>functor map_prod
  using myprod.map_comp by fastforce (simp add: myprod.map_id0)\<close>}\<close>

subsubsection "Displaying Registered Bounded Natural Functors"

text\<open>
All registered BNFs can be displayed by the command
@{theory_text[display]
\<open>print_bnfs\<close>}\index{print-bnfs!print$\_$bnfs (keyword)}
It prints a list of short descriptions of all BNFs which have been registered
at the position of the command to the Output panel\index{panel!output $\sim$} (see
Section~\ref{system-jedit-output}).
\<close>

section "Transfer"
text_raw\<open>\label{holbasic-transfer}\<close>

text\<open>
This section describes the transfer mechanism in detail and is only intended for the interested
reader. Usually the transfer mechanism can be used without knowing the details, as described in
Section~\ref{holbasic-quotlift-lift}.

The relator \<open>rel_fun\<close> for the function type (see Section~\ref{holbasic-bnf-predrel}) lifts a relation
\<open>R\<^sub>a\<close> between two argument types and a relation \<open>R\<^sub>r\<close> between two result types to a relation between
the corresponding function types. It is defined in a way that the following law is valid:
@{text[display]
\<open>\<lbrakk>(rel_fun R\<^sub>a R\<^sub>r) f g; R\<^sub>a x y\<rbrakk> \<Longrightarrow> R\<^sub>r (f x) (g y)\<close>}
It states that if two functions
\<open>f\<close> and \<open>g\<close> are related by \<open>rel_fun R\<^sub>a R\<^sub>r\<close> and the arguments \<open>x\<close> and \<open>y\<close> are related by \<open>R\<^sub>a\<close> then
the function results are related by \<open>R\<^sub>r\<close>.

Thus it is possible to replace the function application term \<open>(f x)\<close> by \<open>(g y)\<close> and to repeat this
for enclosing function applications in a complex term while changing the overall result value to a
related one. If that is done for the body of a lambda term  (see Section~\ref{theory-terms-lambda})
the resulting lambda term is also related (as function) to the original one.

In Isabelle terms of the inner syntax are always built from function applications and lambda terms
(all other binder syntax forms are defined as specific combinations of both). Thus the replacement
schema described above can be used for arbitrary terms. By replacing all constants (for values and functions)
occurring in a term by related ones, a new term results which usually has another type, but its
value is related to that of the original term. This is called ``transfer''\index{transfer}: the
term is ``transferred'' from a type to a different target type.

In this context the relations used for the transfer between corresponding types are called
``transfer relations''\index{transfer!relation}\index{relation!transfer $\sim$}.

As an example consider a relation \<open>rnb\<close> between type \<open>bool\<close> and the target type \<open>nat\<close> which relates
\<open>True\<close> with \<open>1\<close> and \<open>False\<close> with \<open>0\<close>. Then \<open>(rel_fun rnb rnb)\<close> is a transfer relation between
operations on \<open>bool\<close> and operations on \<open>nat\<close>. It can easily be verified that it relates the boolean
conjunction \<open>\<and>\<close> with multiplication \<open>*\<close> and the boolean disjunction \<open>\<or>\<close> with the maximum function
\<open>max\<close> (see Section~\ref{holbasic-equal-order}). Then the boolean term \<open>False \<or> (True \<and> False)\<close> can
be transferred to the term \<open>max 0 (1 * 0)\<close>.

Note that this is an artificial example, transfer is not intended to relate types such as \<open>nat\<close> and
\<open>bool\<close>.
\<close>

subsection "Transfer Rules"
text_raw\<open>\label{holbasic-transfer-rules}\<close>

text\<open>
To transfer a term a replacement must be found for every constant occurring in it. This is done
with the help of simple theorems of the form
@{text[display]
\<open>R term term'\<close>}
where \<open>R\<close> is a transfer relation applied to the two terms. It states that \<open>term\<close> and \<open>term'\<close> are 
related by \<open>R\<close>. In this context such theorems are called ``transfer rules''
\index{transfer!rule}\index{rule!transfer $\sim$}.

To find a replacement for a constant it is matched with the \<open>term'\<close> of every known transfer rule.
A match yields both the \<open>term\<close> for the replacement and the transfer relation \<open>R\<close> which is needed for
determining the arguments relation for the next enclosing function application. Backtracking is
used to determine a consistent set of transfer rules for all constants in a term. If for atleast
one constant no transfer rule matches the term cannot be transferred.

Note that HOL always matches constants with the second relation argument term, thus the transfer
rules are applied ``from right to left''. The target type is always the left argument type of the
transfer relation.
\<close>

subsubsection "Transfer Rules for Functions"

text\<open>
In a transfer rule for functions the transfer relation \<open>R\<close> is constructed with the help of \<open>rel_fun\<close>,
so the rule has the form
@{text[display]
\<open>(rel_fun R\<^sub>a R\<^sub>r) term term'\<close>}

As an alternative syntax HOL provides the operator name \<open>(===>)\<close>\index{/rel-fun@\<open>===>\<close> (operator)}
for \<open>rel_fun\<close> so that the rule can be specified as
@{text[display]
\<open>(R\<^sub>a ===> R\<^sub>r) term term'\<close>}
The operator name \<open>(===>)\<close> is only available after using the command
@{theory_text[display]
\<open>unbundle lifting_syntax\<close>}\index{lifting_syntax@lifting$\_$syntax (bundle)}
on theory level.

This syntax is intended to make the term for the relation syntactically resemble the (function) types
of \<open>term :: T\<^sub>a\<Rightarrow>T\<^sub>r\<close> and \<open>term' :: T\<^sub>a'\<Rightarrow>T\<^sub>r'\<close>: \<open>R\<^sub>a\<close> is the transfer relation between the argument
types \<open>T\<^sub>a\<close> and \<open>T\<^sub>a'\<close>, \<open>R\<^sub>r\<close> is the transfer relation between the result types \<open>T\<^sub>r\<close> and \<open>T\<^sub>r'\<close>.

If the functions have types of the form \<open>T\<^sub>a\<^sub>,\<^sub>1\<Rightarrow>\<dots>\<Rightarrow>T\<^sub>a\<^sub>,\<^sub>n\<Rightarrow>T\<^sub>r\<close> with \<open>n\<close> arguments the relator \<open>rel_fun\<close>
can be iterated as described in Section~\ref{holbasic-bnf-predrel}, yielding a transfer rule of the
form
@{text[display]
\<open>(R\<^sub>a\<^sub>,\<^sub>1 ===> \<dots> ===> R\<^sub>a\<^sub>,\<^sub>n ===> R\<^sub>r) term term'\<close>}
\<close>

subsubsection "Example"

text\<open>
For transferring from \<open>bool\<close> to \<open>nat\<close> the transfer relation \<open>rnb\<close> can be defined inductively (see
Section~\ref{holbasic-inductive}) as
@{theory_text[display]
\<open>inductive rnb :: "nat \<Rightarrow> bool \<Rightarrow> bool"
where "rnb 1 True" | "rnb 0 False"\<close>}\index{rnb (example constant)}

Then the defining rules are transfer rules which can be used to replace the value constants \<open>True\<close>
and \<open>False\<close>. The transfer rules for replacing the boolean operations \<open>\<and>\<close> and \<open>\<or>\<close> are
@{text[display]
\<open>(rnb ===> rnb ===> rnb) (*) (\<and>)
(rnb ===> rnb ===> rnb) max (\<or>)\<close>}
With all four rules together the term \<open>False \<or> (True \<and> False)\<close> can be transferred to the term
\<open>max 0 (1 * 0)\<close>.
\<close>

subsubsection "Relating by Equality"

text\<open>
A specific case occurs if the equality relation \<open>(=)\<close> (see Section~\ref{holbasic-equal-eq}) is used
as transfer relation. It is polymorphic, but always relates a type with itself and also every value
with the same value. Thus the transfer rule \<open>(R\<^sub>a ===> (=)) f g\<close> states that if \<open>x\<close> and \<open>y\<close> are
related by \<open>R\<^sub>a\<close> then \<open>(f x) = (g y)\<close>. If \<open>(g y)\<close> is transferred using this rule, the value of this
term remains unchanged. More generally, an arbitrary term can be transferred with preserving its
value if the outermost function or operator is replaced using a transfer relation of the form
\<open>A ===> (=)\<close>.

If transfer is applied in this way to formulas (terms of type \<open>bool\<close>, see
Section~\ref{theory-prop-formulas}), their truth value is preserved by the transfer. This makes
transfer to a very powerful tool for constructing proofs: to prove a formula about values of one or
more types it is transferred to a formula about values of target types related by transfer relations,
then this formula is proved. Often this proof already exists and can thus be reused.

Transfer can be extended to arbitrary propositions involving meta operators using the equivalence
of derivation rules and boolean terms described in Section~\ref{holtypes-bool-rules}.
\<close>

subsubsection "Transferring Equations"

text\<open>
If the term to be transferred is an equation of two terms the outermost operator is the equality as
a binary predicate on the type of both terms. It can be replaced by the equality on a related type
if the transfer rule
@{text[display]
\<open>(R\<^sub>a ===> R\<^sub>a ===> (=)) (=) (=)\<close>}
is valid. The first occurrence of \<open>(=)\<close> states that the related functions preserve their values,
the second and third occurrences denote the related instances of equality on the target type and the
original type.

For the example relation \<open>rnb\<close> the corresponding transfer rule
@{text[display]
\<open>(rnb ===> rnb ===> (=)) (=) (=)\<close>}
together with the four transfer rules above can be used to transfer the equation \<open>(False \<or> (True \<and>
False)) = False\<close> to the equation \<open>max 0 (1 * 0) = 0\<close> while preserving the validity of the equations.
\<close>

subsubsection "Transferring Propositions with Variables"

text\<open>
If a proposition contains universally bound variables it has the form \<open>\<And> x\<^sub>1 \<dots> x\<^sub>n. P\<close> (see
Section~\ref{theory-prop-bind}). This is equivalent to the formula \<open>\<forall> x\<^sub>1 \<dots> x\<^sub>n. P\<close>, as described in
Section~\ref{holtypes-bool-rules}. Here the outermost operator is the quantifier \<open>\<forall>\<close> which also
corresponds to a function (see Section~\ref{holtypes-bool-funcs}) and can be replaced for transfer.

HOL has a predefined transfer rule which replaces \<open>\<forall>\<close> on a type by \<open>\<forall>\<close> on any target type. However,
this is only valid if the transfer relation \<open>R\<close> between both types is bi-total. Therefore the
property \<open>bi_total R\<close> (see Section~\ref{holbasic-pred-rel}) must be provided as a fact, only then
the transfer rule can be used.

If the relation is only total on the original type the quantifier \<open>\<forall>\<close> must be replaced by a bounded
quantifier over the domain of \<open>R\<close>, i.e., only the values of the target type which are related with a
value in the original type. It has the form \<open>\<forall> x. Domainp R x \<longrightarrow> \<dots>\<close> which restricts \<open>x\<close> to the
domain of \<open>R\<close> (see Section~\ref{holbasic-pred-rel}). HOL has a predefined transfer rule for this
replacement, to be used the property \<open>right_total R\<close> must be provided as a fact. If \<open>R\<close> is not
right-total the (unbounded) quantifier \<open>\<forall>\<close> cannot be transferred.

HOL uses facts of the form
@{text[display]
\<open>Domainp R = (\<lambda>x. \<dots>)\<close>}
specifying the domain as an explicit predicate. If available, the explicit predicate is used instead
of \<open>Domainp R\<close> in a transferred term.

Note that the example relation \<open>rnb\<close> is right-total, but not bi-total. Therefore the additional
rules
@{text[display]
\<open>right_total rnb
Domainp rnb = (\<lambda>n. n\<le>1)\<close>}
can be used to transfer the proposition
@{text[display]
\<open>\<And> a b c. (a \<or> (b \<and> c)) = ((a \<or> b) \<and> (a \<or> c))\<close>}
to the proposition
@{text[display]
\<open>\<And> a b c. \<lbrakk>a \<le> 1; b \<le> 1; c \<le> 1\<rbrakk> \<Longrightarrow>
  max a (b * c) = max a b * max a c\<close>}
\<close>

subsection \<open>The {\sl transfer} Method\<close>
text_raw\<open>\label{holbasic-transfer-method}\<close>

text\<open>
HOL supports transfer by the proof method
@{theory_text[display]
\<open>transfer\<close>}\index{transfer (method)}
The method only affects the first goal, by transferring it. The method uses the dynamic fact set
(see Section~\ref{theory-theorem-named}) \<open>transfer_rule\<close> for matching the constants in the goal.
If no consistent set of matches for all constants can be found in \<open>transfer_rule\<close> the goal will be
partially transferred with additional goals for the replacement of the unmatched constants.

Facts in \<open>transfer_rule\<close> may have additional assumptions, i.e., they may be genuine derivation rules
with a transfer relation application as conclusion. However, a constant only matches such a rule
successfully if all goals resulting from the assumptions can be proved by applying other rules in
\<open>transfer_rule\<close> (which need not have transfer relation applications as conclusions).

Typical assumptions in transfer rules are properties such as \<open>right_total\<close> or \<open>bi_unique\<close> (see
Section~\ref{holbasic-pred-rel}) for the transfer relation. Thus facts stating these properties for
specific relations must also be added to the \<open>transfer_rule\<close> set to be used for transfer.

HOL uses another dynamic fact set \<open>transfer_domain_rule\<close> for explicit specifications of the domain
of transfer relations. 

Note that the \<open>transfer\<close> method has no arguments, its effect is fully determined by the facts in the
sets \<open>transfer_rule\<close> and \<open>transfer_domain_rule\<close>. Usually these sets are populated automatically by
HOL (see Section~\ref{holbasic-quotlift}) so that the \<open>transfer\<close> method is applicable for goals
about values of certain types.
\<close>

subsubsection "Example"

text\<open>
The \<open>transfer\<close> method can be applied to the example using the transfer relation \<open>rnb\<close> as follows.

In the definition of \<open>rnb\<close> the defining rules are directly added to the \<open>transfer_rule\<close> set:
@{theory_text[display]
\<open>inductive rnb :: "nat \<Rightarrow> bool \<Rightarrow> bool"
where [transfer_rule]: "rnb 1 True"
    | [transfer_rule]: "rnb 0 False"\<close>}\index{rnb (example constant)}
The transfer rules for the operations and the equality must be added and proved as theorems:
@{theory_text[display]
\<open>unbundle lifting_syntax
theorem [transfer_rule]: "(rnb ===> rnb ===> rnb) (*) (\<and>)"
  using rnb.simps by fastforce
theorem [transfer_rule]: "(rnb ===> rnb ===> rnb) max (\<or>)"
  using rnb.simps by fastforce
theorem [transfer_rule]: "(rnb ===> rnb ===> (=)) (=) (=)"
  using rnb.simps by fastforce\<close>}
Then it is possible to use \<open>transfer\<close> on goals without variables:
@{theory_text[display]
\<open>theorem "(False \<or> (True \<and> False)) = False"
  apply(transfer) by simp\<close>}
Here the \<open>transfer\<close> method replaces the goal by the transferred goal
@{text[display]
\<open>max 0 (1 * 0) = 0\<close>}
which can be proved (like the original goal) by \<open>simp\<close>.

For goals with variables the fact that \<open>rnb\<close> is right-total must be added to the \<open>transfer_rule\<close> set:
@{theory_text[display]
\<open>theorem [transfer_rule]: "right_total rnb"
  using rnb.simps right_total_def by metis\<close>}
This fact allows to replace the quantifier \<open>\<forall>\<close> and makes it possible to use \<open>transfer\<close> on goals
with variables:
@{theory_text[display]
\<open>theorem "(a \<or> (b \<and> c)) = ((a \<or> b) \<and> (a \<or> c))" apply(transfer)
  using rnb.simps by fastforce\<close>}
Here the \<open>transfer\<close> method replaces the goal by the transferred goal
@{text[display]
\<open>\<And>a b c. \<lbrakk>Domainp rnb a; Domainp rnb b; Domainp rnb c\<rbrakk> \<Longrightarrow>
  max a (b * c) = max a b * max a c\<close>}
which can be proved using \<open>fastforce\<close>.

The domain predicate for \<open>rnb\<close> can be made explicit by using the dynamic fact set
\<open>transfer_domain_rule\<close>:
@{theory_text[display]
\<open>theorem [transfer_domain_rule]: "Domainp rnb = (\<lambda>n. n\<le>1)"
  using rnb.simps by force\<close>}
Then the \<open>transfer\<close> method in
@{theory_text[display]
\<open>theorem "(a \<or> (b \<and> c)) = ((a \<or> b) \<and> (a \<or> c))" apply(transfer)
  using le_eq_less_or_eq by fastforce\<close>}
replaces the goal by the transferred goal
@{text[display]
\<open>\<And>a b c. \<lbrakk>a \<le> 1; b \<le> 1; c \<le> 1\<rbrakk> \<Longrightarrow>
  max a (b * c) = max a b * max a c\<close>}
which can be proved by \<open>fastforce\<close> using the additional fact \<open>le_eq_less_or_eq\<close>.
\<close>

subsection "Polymorphic Types"
text_raw\<open>\label{holbasic-transfer-poly}\<close>

text\<open>
Assume we have a target type \<open>T\<close>, related by a transfer relation \<open>R\<close> to a type \<open>T'\<close> for transfer
from \<open>T'\<close> to \<open>T\<close>. It may happen that a term containing subterms of type \<open>T'\<close> also contains subterms
of a type \<open>T' C\<close> where \<open>C\<close> is a type constructor applied to \<open>T'\<close>, such as \<open>T' set\<close>. Then these
subterms must also be transferred, which requires a transfer relation between \<open>T' C\<close> and a
corresponding target type. A natural candidate is the type \<open>T C\<close>. The transfer relation between
\<open>T C\<close> and \<open>T' C\<close> can be constructed from \<open>R\<close> by using a relator \<open>rel_C\<close> (see
Section~\ref{holbasic-bnf-predrel}) for \<open>C\<close> as the lifted relation \<open>rel_C R\<close>.

Whenever \<open>C\<close> is a natural functor (see Section~\ref{holbasic-bnf-natural}) such a relator is
available and transfer can immediately be applied to all instances of the polymorphic type \<open>'a C\<close>,
if \<open>'a\<close> is instantiated by a type related by a transfer relation to a target type.

Using the example transfer relation \<open>rnb\<close>, the relation \<open>rel_set rnb\<close> relates the target type
\<open>nat set\<close> with the type \<open>bool set\<close> and can be used to specify corresponding transfer rules.
\<close>

subsubsection "Multivariate Functors"

text\<open>
As usual, this can be extended to multivariate natural functors \<open>C\<close> with \<open>n\<close> type parameters. An
instance \<open>(T\<^sub>1',\<dots>,T\<^sub>n') C\<close> is related to a corresponding target type by the transfer relation
\<open>(rel_C R\<^sub>1 \<dots> R\<^sub>n)\<close> where \<open>R\<^sub>i\<close> is the transfer relation relating \<open>T\<^sub>i'\<close> to a target type \<open>T\<^sub>i\<close>. If a
parameter \<open>T\<^sub>i'\<close> of \<open>C\<close> is not to be transferred, the equality \<open>(=)\<close> is used as \<open>R\<^sub>i\<close> and \<open>T\<^sub>i\<close> is the
same as \<open>T\<^sub>i'\<close>.

Note that lifting transfer relations \<open>R\<^sub>a\<close> and \<open>R\<^sub>r\<close> between argument and result types to a function
type as \<open>(rel_fun R\<^sub>a R\<^sub>r)\<close> or \<open>(R\<^sub>a ===> R\<^sub>r)\<close>, which is the basis of the transfer mechanism, is a special
application of this.

Since relators can be composed according to the structure of a type expression (see
Section~\ref{holbasic-bnf-predrel}) it is possible to systematically construct relators and thus
transfer relations for arbitrary types which are composed from natural functors.
\<close>

subsubsection "Transferring Polymorphic Functions"

text\<open>
A function with a type instance \<open>T' C\<close> as argument or result type is often itself polymorphic and
defined for the polymorphic type \<open>'a C\<close>, i.e., for arbitrary types as parameters. Then it
is not possible to specify a transfer rule for the function in the way described above, because no
common transfer relation for the type parameter is available (other than trivial polymorphic
relations like \<open>=\<close>).

However, there are polymorphic functions for which the definition does not depend on the type
parameter(s) at all. An example is the function \<open>image\<close> (see Section~\ref{holbasic-functor-mapper}).
For a function \<open>f :: 'a \<Rightarrow> 'b\<close> and a set \<open>A\<close> of argument values \<open>image f A\<close> is the set of result
values of \<open>f\<close> applied to all values in \<open>A\<close>. This definition is completely independent of the actual
types substituted for the type parameters \<open>'a\<close> and \<open>'b\<close>.

Such functions are called ``parametrically polymorphic''\index{parametrically polymorphic function}
\index{function!parametrically polymorphic $\sim$}. Polymorphic functions with a direct, inductive, or
recursive definition are usually parametrically polymorphic, whereas functions defined by overloading
(see Section~\ref{theory-overload-true}) are usually not, because different definitions may be used
for different type parameters.

Since parametrically polymorphic functions work in the same way for all values of its type
parameters it is possible to replace these values in the argument in arbitrary ways and they will be
replaced in the result in related ways. Therefore it is possible to specify a transfer rule for
the function using \<^emph>\<open>all possible relations\<close> on \<^emph>\<open>all possible types\<close> substituted for the type
parameters, i.e., the transfer relations for the type parameters occur as universally bound
variables in the transfer rule.

An example is the transfer rule
@{theory_text[display]
\<open>theorem image_transfer [transfer_rule]:
  "\<And>R\<^sub>1 R\<^sub>2. ((R\<^sub>1 ===> R\<^sub>2) ===> rel_set R\<^sub>1 ===> rel_set R\<^sub>2) image image"
  by (simp add: rel_fun_def rel_set_def) blast\<close>}
which is provided by HOL. It states that for the function \<open>image\<close> an instance for an element type \<open>T\<close>
is always related to an instance of \<open>image\<close> for any other element type. Thus transfer will syntactically
preserve occurrences of \<open>image\<close> although its type instance is transferred. Note how
the relation \<open>((R\<^sub>1 ===> R\<^sub>2) ===> rel_set R\<^sub>1 ===> rel_set R\<^sub>2)\<close> is constructed according to the structure
of the type expression \<open>('a\<^sub>1 \<Rightarrow> 'a\<^sub>2) \<Rightarrow> ('a\<^sub>1 set) \<Rightarrow> ('a\<^sub>2 set)\<close> for the type of \<open>image\<close> from the
corresponding relators. The type parameters \<open>'a\<^sub>1\<close> and \<open>'a\<^sub>2\<close> are replaced by the universally bound
variables \<open>R\<^sub>1\<close> and \<open>R\<^sub>2\<close> for the arbitrary relations.

Such transfer rules for a single polymorphic function are called ``parametricity rules''
\index{parametricity rule}\index{rule!parametricity $\sim$}
because they are equivalent to the proposition that the function is parametrically polymorphic.
HOL provides such parametricity rules for most of the predefined polymorphic functions, such as
most functions for sets described in Section~\ref{holtypes-set-funcs}.

Normal transfer rules between two polymorphic functions may be specified using universally bound
variables in the same way if both functions are parametrically polymorphic.

Some parametrically polymorphic functions are independent of the type parameters but cannot be
related by arbitrary relations. Then their parametricity rule has additional assumptions which
restrict the transfer relation. An example is the equality as a polymorphic function. It can only
be transferred by bi-unique transfer relations, otherwise it would identify values in one type which
are different in the other. The corresponding parametricity rule provided by HOL is
@{theory_text[display]
\<open>theorem eq_transfer [transfer_rule]:
  "bi_unique R \<Longrightarrow> (R ===> R ===> (=)) (=) (=)"
  by (auto simp add: bi_unique_def rel_fun_def)\<close>}\index{eq-transfer@eq$\_$transfer (fact name)}
\<close>

section "Quotients and Lifting"
text_raw\<open>\label{holbasic-quotlift}\<close>

text\<open>
Assume a relation (see Section~\ref{holbasic-pred-rel}) \<open>R :: T \<Rightarrow> T' \<Rightarrow> bool\<close> between types \<open>T\<close> and
\<open>T'\<close> which is right-total and right-unique. This implies the existence of a surjective function
\<open>abs_T' :: T \<Rightarrow> T'\<close>\index{abs-@abs$\_$ (constant name prefix)} mapping every value of \<open>T\<close> to the
single value of \<open>T'\<close> which is related by \<open>R\<close>.

Since \<open>R\<close> need not be left-unique \<open>abs_T'\<close> need not be injective and gives rise to the definition
of the equivalence relation \<open>E :: T \<Rightarrow> T \<Rightarrow> bool\<close> which relates all values mapped by \<open>abs_T'\<close> to a
common value in \<open>T'\<close>. Since \<open>R\<close> need not be left-total \<open>abs_T'\<close> is underspecified (see
Section~\ref{theory-terms-consts}) for all values of \<open>T\<close> which are not related to a value of \<open>T'\<close> by
\<open>R\<close>. This gives rise to the definition of the set \<open>D :: T set\<close> of all values in \<open>T\<close> which are
related to a value of \<open>T'\<close>. The set \<open>D\<close> is the domain of \<open>R\<close>, represented as a set. Also,
\<open>E\<close> is in general a partial equivalence relation and does not relate values outside of \<open>D\<close>, not even
with themselves (which is the case for the values in \<open>D\<close> since as an equivalence relation \<open>E\<close> must
be reflexive).

The predicate \<open>reflp\<close>\index{reflp (constant)} (see Section~\ref{holtypes-rel-funcs}) may be used to specify that \<open>E\<close> is
reflexive on the whole type \<open>T\<close>, thus the proposition \<open>reflp E\<close> is equivalent to the proposition
\<open>left_total R\<close> and also to \<open>D = (UNIV ::T)\<close> where \<open>(UNIV ::T)\<close> is the universal set of type \<open>T\<close> (see
Section~\ref{holtypes-set-values}).
\<close>

subsection "Abstract and Raw Types"
text_raw\<open>\label{holbasic-quotlift-absraw}\<close>

text\<open>
In this situation the values of type \<open>T'\<close> are considered to be ``more abstract'' than those of \<open>T\<close>
because there may be several distinct related values in \<open>T\<close> so that they may represent more details
and there may be values in \<open>T\<close> which have no related values in \<open>T'\<close> at all. Therefore the type \<open>T'\<close>
is called an ``abstract type''\index{abstract type}\index{type!abstract $\sim$} and \<open>T\<close> is called
its associated ``raw type''\index{raw type}\index{type!raw $\sim$}. Usually, in HOL for an abstract type
only one relation \<open>R\<close> is considered and thus only one associated raw type, whereas \<open>T\<close> may be the
raw type for several abstract types.

The function \<open>abs_T'\<close> which maps values of the raw type to values of the abstract type is called
``abstraction function''\index{abstraction!function}\index{function!abstraction $\sim$} in this context.

The interrelation between \<open>R\<close>, \<open>abs_T'\<close> and \<open>E\<close> can be formally described by the laws
@{theory_text[display]
\<open>E v\<^sub>1 v\<^sub>2 = (E v\<^sub>1 v\<^sub>1 \<and> E v\<^sub>2 v\<^sub>2 \<and> abs_T' v\<^sub>1 = abs_T' v\<^sub>2)
R v v' = E v v \<and> abs_T' v = v'))\<close>}
where \<open>E v v\<close> is equivalent to the property that \<open>v\<close> has a related value in \<open>T'\<close>, i.e., \<open>v \<in> D\<close>.

Note that the relation \<open>R\<close> can also be used as transfer relation (see Section~\ref{holbasic-transfer}).
Then terms are transferred from the abstract type to the raw type.
\<close>

subsubsection "Example"

text\<open>
The relation \<open>rnb\<close> used as example in Section~\ref{holbasic-transfer} is right-total and
right-unique. In this case \<open>bool\<close> is the abstract type and \<open>nat\<close> is the raw type. If defined as
above the function \<open>abs_bool\<close> maps \<open>0\<close> to \<open>False\<close> and \<open>1\<close> to \<open>True\<close> and is underspecified for all
other natural numbers. Thus the equivalence classes are trivially \<open>{0}\<close> and \<open>{1}\<close> (because \<open>rnb\<close> is
also left-unique) and the corresponding equivalence relation \<open>E\<close> is the relation \<open>rnbE\<close> which can be
defined inductively (see Section~\ref{holbasic-inductive}) as
@{theory_text[display]
\<open>inductive rnbE :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where "rnbE 1 1" | "rnbE 0 0"\<close>}\index{rnbE (example constant)}
It is partial in the sense that it only relates values in the set defined as
@{theory_text[display]
\<open>definition rnbD :: "nat set"
where "rnbD \<equiv> {0,1}"\<close>}\index{rnbD (example constant)}
which are the only values in \<open>nat\<close> related to values in \<open>bool\<close> by \<open>rnb\<close>. Using the restricted
equality \<open>eq_onp\<close> (see Section~\ref{holbasic-equal-eq}) \<open>rnbE\<close> can also be represented as
\<open>eq_onp (\<lambda>x. x \<in> rnbD)\<close>.

Alternatively consider the relation \<open>rnb2\<close> which relates all natural numbers which are not \<open>0\<close> to
\<open>True\<close>. Then \<open>abs_bool\<close> is fully specified (because \<open>rnb2\<close> is left-total), it maps \<open>0\<close> to \<open>False\<close>
and all other numbers to \<open>True\<close>. The equivalence classes of \<open>rnb2E\<close> are \<open>{0}\<close> and the set of all
numbers greater \<open>0\<close>, the set \<open>rnb2D\<close> contains all natural numbers.
\<close>

subsection "Quotient Theorems"
text_raw\<open>\label{holbasic-quotlift-quot}\<close>

text\<open>
Note that there is a 1-to-1 relation between the equivalence classes of \<open>E\<close> and the values of \<open>T'\<close>. 
Therefore an abstract type is also called a ``quotient''\index{quotient} of its raw type, because
in algebra, the notion of a ``quotient'' is used for sets of equivalence classes.
\<close>

subsubsection "Representation Values"

text\<open>
Since \<open>R\<close> is right-total every abstract value \<open>v'\<close> in \<open>T'\<close> has at least one related value in \<open>T\<close>.
Thus it is possible to select one of these values as ``representation value''\index{representation!value}
for \<open>v'\<close>. A ``representation function''\index{representation!function}\index{function!representation $\sim$}
\<open>rep_T' :: T' \<Rightarrow> T\<close>\index{rep-@rep$\_$ (constant name prefix)}
maps every value of \<open>T'\<close> to a selected representation value.

Due to its definition \<open>abs_T'\<close> maps each representation value back to its abstract value, i.e.,
the law \<open>abs_T' (rep_T' v') = v'\<close> holds for every abstract value \<open>v'\<close>. Moreover, \<open>E (rep_T' v')
(rep_T' v')\<close> holds because \<open>E\<close> is reflexive on the image of \<open>rep_T'\<close>. The functions \<open>abs_T'\<close> and
\<open>rep_T'\<close> are called ``morphisms'' of the quotient \<open>T'\<close>\index{quotient!morphisms of a $\sim$}
\index{morphisms!of a quotient}.

In the \<open>rnb\<close> example the only possible representation function \<open>rep_bool\<close> maps \<open>False\<close> to \<open>0\<close> and
\<open>True\<close> to \<open>1\<close>. In the \<open>rnb2\<close> example \<open>rep_bool\<close> may map \<open>True\<close> to any number greater \<open>0\<close>, so there
are infinitely many possible representation functions.
\<close>

subsubsection "The \<open>Quotient\<close> Predicate"

text\<open>
HOL provides the predicate
@{text[display]
\<open>Quotient :: (T\<Rightarrow>T\<Rightarrow>bool) \<Rightarrow> (T\<Rightarrow>T') \<Rightarrow> (T'\<Rightarrow>T) \<Rightarrow> (T\<Rightarrow>T'\<Rightarrow>bool) \<Rightarrow> bool\<close>}\index{Quotient (constant)}
It is defined as the conjunction of the two laws about \<open>R\<close>, \<open>abs_T'\<close>, and \<open>E\<close> above and the two laws
about \<open>rep_T'\<close>, so that \<open>Quotient E abs_T' rep_T' R\<close> states that \<open>T'\<close> is a quotient of \<open>T\<close> with the
specified relations and morphisms.

Theorems stating that \<open>Quotient\<close> holds for four specific arguments are called ``quotient theorems''
\index{quotient!theorem}\index{theorem!quotient $\sim$}.

The quotient theorem for the \<open>rnb\<close> example is
@{theory_text[display]
\<open>theorem qrnb: "Quotient rnbE abs_bool rep_bool rnb" \<proof>\<close>}\index{qrnb (example fact)}
\<close>

subsubsection "Unique Representation Values"

text\<open>
If \<open>R\<close> is also left-unique, every abstract value \<open>v'\<close> in \<open>T'\<close> has exactly one related value in \<open>T\<close>.
Thus the representation function \<open>rep_T'\<close> is uniquely determined by \<open>R\<close> and has the set \<open>D\<close> as its
image, thus the law \<open>rep_T' v' \<in> D\<close> holds for every abstract value \<open>v'\<close>.

Also, since every abstract value in \<open>T'\<close> has only one single representation value in \<open>T\<close>, \<open>rep_T'\<close>
is the inverse of \<open>abs_T'\<close> on the set \<open>D\<close>, i.e., the law \<open>v \<in> D \<Longrightarrow> rep_T' (abs_T' v) = v\<close> holds for
every value \<open>v\<close> in the raw type.

Note that together with the law \<open>abs_T' (rep_T' v') = v'\<close> (see above) these two laws uniquely
determine the relation \<open>R\<close> and cause it to be right-total and bi-unique, i.e., they cause \<open>T'\<close> to
be a quotient of \<open>T\<close> with the uniquely determined representation function \<open>rep_T'\<close>.

Moreover, in this case the equivalence relation \<open>E\<close> can always be represented by \<open>eq_onp (\<lambda>x. x\<in>D)\<close>
using the restricted equality described in Section~\ref{holbasic-equal-eq}.

In the \<open>rnb\<close> example \<open>rnb\<close> is left-unique and the representation function \<open>rep_bool\<close> is uniquely
determined.
\<close>

subsubsection "The \<open>type_definition\<close> Predicate"

text\<open>
For the case of a left-unique transfer relation \<open>R\<close> HOL provides the predicate
@{text[display]
\<open>type_definition :: (T'\<Rightarrow>T) \<Rightarrow> (T\<Rightarrow>T') \<Rightarrow> (T set) \<Rightarrow> bool\<close>}\index{type-definition@type$\_$definition (constant)}
It is defined as the conjunction of the three laws about \<open>abs_T'\<close>, \<open>rep_T'\<close>, and \<open>D\<close> mentioned in the
previous section, so that \<open>type_definition rep_T' abs_T' D\<close> states that \<open>T'\<close> is a quotient of \<open>T\<close>
with unique representation function \<open>rep_T'\<close>. For an explanation of the predicate name see
Section~\ref{holtdefs-sub-setup}.

Theorems stating that \<open>type_definition\<close> holds for three specific arguments are called ``type-definition
theorems''\index{type-definition theorem}\index{theorem!type-definition $\sim$}.

The type-definition theorem for the \<open>rnb\<close> example is
@{theory_text[display]
\<open>theorem trnb: "type_definition rep_bool abs_bool rnbD" \<proof>\<close>}\index{trnb (example fact)}
\<close>

subsection "Polymorphic Quotients"
text_raw\<open>\label{holbasic-quotlift-poly}\<close>

text\<open>
If the raw and abstract type are polymorphic types \<open>'a C\<close> and \<open>'a C'\<close> the transfer relation \<open>R\<close> is
also polymorphic with type parameter \<open>'a\<close> and so are the equivalence relation \<open>E\<close> and the morphisms
\<open>abs_C'\<close> and \<open>rep_C'\<close>.

As described in Section~\ref{holbasic-transfer-poly}, if a relator \<open>rel_C\<close> is available for the raw
type \<open>'a C\<close>, it is possible to construct a transfer relation between \<open>'a C\<close> and \<open>'b C\<close> from an
arbitrary transfer relation \<open>R\<^sub>a\<close> between the type parameters \<open>'a\<close> and \<open>'b\<close> as \<open>rel_C R\<^sub>a\<close>. Composed
(see Section~\ref{holbasic-pred-rel}) with \<open>R\<close> it yields the parameterized transfer relation
\index{relation!transfer $\sim$!parameterized $\sim$}\index{parameterized!transfer relation}
\index{parameterized!correspondence relation}
\<open>pcr = \<lambda>R\<^sub>a. (rel_C R\<^sub>a) OO R\<close> (where \<open>pcr\<close> stands for ``parameterized correspondence relation'').

The totality and uniqueness properties of the argument relation \<open>R\<^sub>a\<close> are preserved by the relator
\<open>rel_C\<close> and by composition and thus also by \<open>pcr_C'\<close>. Therefore the properties
@{text[display]
\<open>right_total R\<^sub>a \<Longrightarrow> right_total (pcr R\<^sub>a)
right_unique R\<^sub>a \<Longrightarrow> right_unique (pcr R\<^sub>a)\<close>}
are always satisfied which implies that \<open>pcr R\<^sub>a\<close> is actually a transfer relation if \<open>R\<^sub>a\<close> is a
transfer relation.

In other words, if \<open>T'\<close> is a quotient of \<open>T\<close> then \<open>T' C'\<close> is a quotient of \<open>T C\<close>. Using transfer
rules with transfer relation \<open>pcr R\<^sub>a\<close>, transfer works for \<open>T'\<close> when it is used as type parameter
of a polymorphic quotient.

As usual, if \<open>C\<close> and \<open>C'\<close> are multivariate functors with \<open>n\<close> type parameters the relator \<open>rel_C\<close>
takes \<open>n\<close> relations as arguments and the parameterized transfer relation has the form
\<open>pcr = \<lambda>R\<^sub>1\<dots>R\<^sub>n. (rel_C R\<^sub>1\<dots>R\<^sub>n) OO R\<close>.\<close>

subsection "Registering Quotients"
text_raw\<open>\label{holbasic-quotlift-setup}\<close>

text\<open>
HOL supports a mechanism for automatically transferring functions between a quotient and its raw
type. It is called the ``lifting package''.

The first step of using the package consists of registering a type \<open>T'\<close> as quotient, together with
its raw type \<open>T\<close> and the morphisms \<open>abs_T'\<close> and \<open>rep_T'\<close>. Registering means that the fact that \<open>T'\<close>
is a quotient of \<open>T\<close> is stored together with the morphisms in internal HOL data structures so that
they can be retrieved by HOL mechanisms. All the information to be stored is contained in a
quotient or type-definition theorem for \<open>T'\<close>, therefore a quotient is registered by specifying the
name of a fact which is such a theorem. This is done using a command of the form
@{theory_text[display]
\<open>setup_lifting name\<close>}\index{setup-lifting@setup$\_$lifting (keyword)}
where \<open>name\<close> is the name of a quotient theorem or a type-definition theorem.

In the case of a type-definition theorem the command internally defines the relation \<open>R\<close> named
\<open>cr_T'\<close> using the definition
@{text[display]
\<open>cr_T'_def: cr_T' \<equiv> \<lambda>(x::T) y::T'. x = rep_T' y\<close>}
Note that in this case the equivalence relation \<open>E\<close> is always the equality \<open>eq_onp (\<lambda>x. x\<in>D)\<close>
restricted to the domain set \<open>D\<close>.

Moreover, the command always tries to define the parameterized transfer relation \<open>pcr_T'\<close> (see
Section~\ref{holbasic-quotlift-poly}) using a definition of the form
@{text[display]
\<open>pcr_T'_def: pcr_T' \<equiv> \<lambda>R\<^sub>1\<dots>R\<^sub>n. (rel_T R\<^sub>1\<dots>R\<^sub>n) OO R\<close>}
where \<open>n\<close> is the number of type parameters for a polymorphic quotient \<open>T'\<close>. If \<open>T'\<close> is not
polymorphic \<open>pcr_T'\<close> has no arguments and is equal to \<open>R\<close>.

Note that for a polymorphic quotient the definition of \<open>pcr_T'\<close> depends on the existence of the
relator \<open>rel_T\<close>. If the relator is not known to HOL the command signals a warning ``Generation of a
parametrized correspondence relation failed. Reason:  No relator for the type \<open>T\<close> found.'' and omits
the definition of \<open>pcr_T'\<close>, which results in weaker transfer support (see below). If the raw type
\<open>T\<close> has been registered as BNF (see Section~\ref{holbasic-bnf-register}) the relator is always known
to HOL, otherwise usually not. However, if \<open>T\<close> has been registered as BNF with dead type parameters
(see Section~\ref{holbasic-bnf-natural}) the relator has fewer parameters than expected by
\<^theory_text>\<open>setup_lifting\<close> and cannot be used for constructing \<open>pcr_T'\<close>. Then \<^theory_text>\<open>setup_lifting\<close> will still
signal the warning about not finding the relator.\<close>

subsubsection "Basic Support for Transfer"

text\<open>
The \<^theory_text>\<open>setup_lifting\<close> command supports transfer in the following way. First it adds the facts
@{text[display]
\<open>T'.right_total: right_total pcr_T'
T'.right_unique: right_unique pcr_T'\<close>}
to the set \<open>transfer_rule\<close> (see Section~\ref{holbasic-transfer-method}). For a polymorphic \<open>T'\<close>
they have the form
@{text[display]
\<open>T'.right_total: \<lbrakk>right_total R\<^sub>1, \<dots>, right_total R\<^sub>n\<rbrakk>
  \<Longrightarrow> right_total (pcr_T' R\<^sub>1 \<dots> R\<^sub>n)
T'.right_unique: \<lbrakk>right_unique R\<^sub>1, \<dots>, right_unique R\<^sub>n\<rbrakk>
  \<Longrightarrow> right_unique (pcr_T' R\<^sub>1 \<dots> R\<^sub>n)\<close>}
They state that \<open>pcr_T'\<close> is a transfer relation if all \<open>R\<^sub>i\<close> are transfer relations and provide the
base for introducing transfer rules
with \<open>pcr_T'\<close> as transfer relation. Additionally, the rule \<open>T'.right_total\<close> allows the
\<open>transfer\<close> method to replace the universal quantification on \<open>T'\<close> by quantification on \<open>T\<close>
restricted to the domain \<open>D\<close> of \<open>pcr_T'\<close> (see Section~\ref{holbasic-transfer-rules}). For a
polymorphic \<open>T'\<close> it allows to replace the universal quantification on \<open>('a\<^sub>1,\<dots>,'a\<^sub>n) T'\<close> by
quantification on \<open>('b\<^sub>1,\<dots>,'b\<^sub>n) T\<close> restricted to the domain of \<open>(pcr_T' R\<^sub>1\<dots>R\<^sub>n)\<close> for
arbitrary types \<open>'b\<^sub>1,\<dots>,'b\<^sub>n\<close> and \<open>'a\<^sub>1,\<dots>,'a\<^sub>n\<close> related as quotients by arbitrary relations
\<open>R\<^sub>1,\<dots>,R\<^sub>n\<close>.

If \<open>pcr_T'\<close> could not be defined because the relator of \<open>T\<close> is not known, these and all subsequently
described transfer rules are defined using \<open>R\<close> as transfer relation instead of \<open>pcr_T'\<close>. This
results in weaker effects when the \<open>transfer\<close> method is applied to terms involving type \<open>T'\<close>.

The \<^theory_text>\<open>setup_lifting\<close> command also adds a rule \<open>T'.domain\<close> to the set \<open>transfer_domain_rule\<close> which
constructs an explicit representation of the domain of \<open>pcr_T' R\<^sub>1 \<dots> R\<^sub>n\<close> from the domains of the
\<open>R\<^sub>i\<close> (see Section~\ref{holbasic-transfer-method}).

Note that all fact names are qualified by the type name \<open>T'\<close> of the quotient, therefore the names
are specific for the quotient registered by \<^theory_text>\<open>setup_lifting\<close>. If two \<^theory_text>\<open>setup_lifting\<close> commands are
specified for the same quotient \<open>T'\<close> an error is signaled.
\<close>

subsubsection "Support for Equality Transfer"

text\<open>
If the quotient is registered using a quotient theorem the \<^theory_text>\<open>setup_lifting\<close> command also adds the
fact
@{text[display]
\<open>T'.rel_eq_transfer:
  (pcr_T' (=)\<dots>(=) ===> pcr_T' (=)\<dots>(=) ===> (=)) E (=)\<close>}
to the set \<open>transfer_rule\<close>. It allows the \<open>transfer\<close> method to replace the equality on \<open>T'\<close> by the
equivalence \<open>E\<close> on \<open>T\<close>. If the quotient is registered by a type-definition theorem no such rule is
required, the standard HOL transfer rules for transferring equations, such as \<open>eq_transfer\<close> (see
Section~\ref{holbasic-transfer-poly}) are sufficient.

Since the relator lifts equality to equality (see Section~\ref{holbasic-bnf-predrel}), the
application \<open>pcr_T' (=) \<dots> (=)\<close> to \<open>n\<close> equality relations is always equal to the transfer relation
\<open>R\<close>. Thus the rule \<open>T'.rel_eq_transfer\<close> is equivalent to the form
\<open>(R ===> R ===> (=)) E (=)\<close>. In the polymorphic case the rule only supports transferring equality
on \<open>('a\<^sub>1,\<dots>,'a\<^sub>n) T'\<close> to the equivalence \<open>E\<close> on \<open>('a\<^sub>1,\<dots>,'a\<^sub>n) T\<close> where the type parameters are the
same.

However, if \<open>E\<close> is parametrically polymorphic (see Section~\ref{holbasic-transfer-poly}) it can
further be transferred to a different instance \<open>('b\<^sub>1,\<dots>,'b\<^sub>n) T\<close>. Therefore, when using a quotient
theorem, the \<^theory_text>\<open>setup_lifting\<close> command supports the extended form
@{theory_text[display]
\<open>setup_lifting name parametric pname\<close>}\index{parametric (keyword)}
where \<open>pname\<close> is the name of a fact of the form
@{text[display]
\<open>(rel_T R\<^sub>1\<dots>R\<^sub>n ===> rel_T R\<^sub>1\<dots>R\<^sub>n ===> (=)) E E\<close>}
which is a parametricity rule (see Section~\ref{holbasic-transfer-poly}) stating that \<open>E\<close> is
parametrically polymorphic. In this form the \<^theory_text>\<open>setup_lifting\<close> command generates the stronger
transfer rule
@{text[display]
\<open>T'.rel_eq_transfer:
  (pcr_T' R\<^sub>1\<dots>R\<^sub>n ===> pcr_T' R\<^sub>1\<dots>R\<^sub>n ===> (=)) E (=)\<close>}
with arbitrary relations \<open>R\<^sub>1,\<dots>,R\<^sub>n\<close> relating the different instances of the type parameters. It
supports transferring equality on \<open>('a\<^sub>1,\<dots>,'a\<^sub>n) T'\<close> to the equivalence \<open>E\<close> on \<open>('b\<^sub>1,\<dots>,'b\<^sub>n) T\<close>.

When using a type-definition theorem for \<^theory_text>\<open>setup_lifting\<close> no parametricity rule may be specified.
It is not required because then the equivalence \<open>E\<close> is always the (possibly restricted) equality
which is always parametric for a bi-unique transfer relation (see below).

In the \<open>rnb\<close> example after the command
@{theory_text[display]
\<open>setup_lifting qrnb\<close>}
where \<open>qrnb\<close> is the name of the quotient theorem as defined in Section~\ref{holbasic-quotlift-quot},
the \<open>transfer\<close> method will transfer equations of the form \<open>\<And>x::bool. x = \<dots>\<close> to propositions of the
form
@{text[display]
\<open>\<And>x::nat. rnbE x x \<Longrightarrow> rnbE x \<dots>\<close>}
After the command
@{theory_text[display]
\<open>setup_lifting trnb\<close>}
where \<open>trnb\<close> is the name of the type-definition theorem as defined in
Section~\ref{holbasic-quotlift-quot}, the \<open>transfer\<close> method will transfer equations of the form
\<open>\<And>x::bool. x = \<dots>\<close> to propositions of the form
@{text[display]
\<open>\<And>x::nat. x \<in> rnbD \<Longrightarrow> x = \<dots>\<close>}
\<close>

subsubsection "Left-Total Transfer Relations"

text\<open>
If it uses a quotient theorem the \<^theory_text>\<open>setup_lifting\<close> command may be specified in the extended form
@{theory_text[display]
\<open>setup_lifting name rname\<close>}\index{setup-lifting@setup$\_$lifting (keyword)}
where \<open>rname\<close> is the name of a fact of the form \<open>reflp E\<close> and \<open>E\<close> is the equivalence relation
used in the quotient theorem \<open>name\<close>. The fact \<open>rname\<close> is called a ``reflexivity rule''
\index{reflexivity rule}\index{rule!reflexivity $\sim$} for \<open>E\<close>. As described at the beginning of
Section~\ref{holbasic-quotlift} it is equivalent with \<open>left_total R\<close>. This property allows HOL to
introduce stronger transfer rules as follows.

The command in this form adds the additional rule
@{text[display]
\<open>T'.bi_total:
  \<lbrakk>bi_total R\<^sub>1; \<dots> bi_total R\<^sub>n\<rbrakk> \<Longrightarrow> bi_total (pcr_T' R\<^sub>1\<dots>R\<^sub>n)\<close>}
to the set \<open>transfer_rule\<close>. It allows the \<open>transfer\<close> method to replace quantification on
\<open>('a\<^sub>1,\<dots>,'a\<^sub>n) T'\<close> to unrestricted quantification on \<open>('b\<^sub>1,\<dots>,'b\<^sub>n) T\<close> (see
Section~\ref{holbasic-transfer-rules}).

It also adds the rule
@{text[display]
\<open>T'.id_abs_transfer: (rel_T R\<^sub>1\<dots>R\<^sub>n ===> pcr_T' R\<^sub>1\<dots>R\<^sub>n) (\<lambda>x. x) abs_T'\<close>}
It allows to replace the morphism \<open>abs_T'\<close> by the identity function on \<open>('b\<^sub>1,\<dots>,'b\<^sub>n) T\<close>. 

In the \<open>rnb2\<close> example from Section~\ref{holbasic-quotlift-absraw} after the theorems
@{theory_text[display]
\<open>theorem qrnb2: "Quotient rnb2E abs_bool rep_bool rnb2" \<proof>
theorem rrnb2: "reflp rnb2E" \<proof>\<close>}
with a corresponding equivalence relation \<open>rnb2E\<close> and accordingly modified morphisms \<open>abs_bool\<close> and
\<open>rep_bool\<close> the command
@{theory_text[display]
\<open>setup_lifting qrnb2 rrnb2\<close>}
introduces the transfer rules as described. Then the \<open>transfer\<close> method will transfer the (invalid)
equation
\<open>\<And>(x::bool) (n::nat). x = (abs_bool n)\<close> to the proposition
@{text[display]
\<open>\<And>(x::nat) (n::nat). rnb2E x n\<close>}\<close>

subsubsection "Left-Unique Transfer Relations"

text\<open>
HOL provides special support for a quotient with left-unique transfer relation only if the quotient
is specified by a \<^theory_text>\<open>setup_lifting\<close> command using a type-definition theorem.

Then the command always adds the additional rule
@{text[display]
\<open>T'.bi_unique:
  \<lbrakk>bi_unique R\<^sub>1; \<dots> bi_unique R\<^sub>n\<rbrakk> \<Longrightarrow> bi_unique (pcr_T' R\<^sub>1\<dots>R\<^sub>n)\<close>}
to the set \<open>transfer_rule\<close>. Together with the standard HOL transfer rules for transferring equations,
such as \<open>eq_transfer\<close> (see Section~\ref{holbasic-transfer-poly}), it allows the \<open>transfer\<close> method to
transfer equality from \<open>('a\<^sub>1,\<dots>,'a\<^sub>n) T'\<close> to \<open>('b\<^sub>1,\<dots>,'b\<^sub>n) T\<close>.

It also adds the rule
@{text[display]
\<open>T'.rep_transfer: (pcr_T' R\<^sub>1\<dots>R\<^sub>n ===> rel_T R\<^sub>1\<dots>R\<^sub>n) (\<lambda>x. x) rep_T'\<close>}
It allows to replace the function \<open>rep_T'\<close> by the identity function on \<open>('b\<^sub>1,\<dots>,'b\<^sub>n) T\<close>. 

In the \<open>rnb\<close> example the command
@{theory_text[display]
\<open>setup_lifting trnb\<close>}
introduces the transfer rules as described. Then the \<open>transfer\<close> method will transfer the (invalid)
equation
\<open>\<And>(x::bool) (n::nat). (rep_bool x) = n\<close> to the proposition
@{text[display]
\<open>\<And>(x::nat) (n::nat). x = n\<close>}

If the transfer relation is also left-total, \<open>T'\<close> and \<open>T\<close> are isomorphic and \<open>D\<close> is the universal
set (see Section~\ref{holtypes-set-values}) \<open>UNIV\<close>. HOL detects type-definition theorems of the
form \<open>type-definition rep_T' abs_T' UNIV\<close> and also adds the rules \<open>T'.bi_total\<close> and
\<open>T'.id_abs_transfer\<close> as described above for left-total transfer relations.\<close>

subsection "Lifting"
text_raw\<open>\label{holbasic-quotlift-lift}\<close>

text\<open>
Whenever \<open>T'\<close> is a quotient of \<open>T\<close> it is possible to ``lift'' operations from \<open>T\<close> to \<open>T'\<close> by first
mapping the argument of type \<open>T'\<close> to its representation value of type \<open>T\<close> using \<open>rep_T'\<close>, then
applying the original operation, and finally mapping the result back using \<open>abs_T'\<close>. 

Moreover, since the relation \<open>R\<close> can always be used as a transfer relation (see
Section~\ref{holbasic-transfer}) it is possible to transfer terms with occurrences of the lifted
operation to a corresponding term where it is replaced by the original operation. The lifting
package supports this by automatically configuring the required transfer rules for lifted operations.
\<close>

subsubsection "Respectful Functions"

text\<open>
A function \<open>f :: T\<Rightarrow>T\<close> ``respects''\index{respectful!function}\index{function!respects a relation}
the equivalence relation \<open>E\<close> if it preserves \<open>E\<close> for its arguments in the sense that the law
@{text[display]
\<open>\<And>x y. E x y \<Longrightarrow> E (f x) (f y)\<close>}
is satisfied. A theorem stating such a law is called a
``respectfulness theorem''\index{respectfulness theorem}\index{theorem!respectfulness $\sim$}
for \<open>f\<close>. In mathematics in this case \<open>E\<close> is also called a ``congruence relation'' for \<open>f\<close>.

If two functions \<open>f\<close> and \<open>g\<close> are lifted as described above, the composition of the lifted functions
is \<open>abs_T' (f (rep_T' (abs_T' (g (rep_T' x)))))\<close>. Here \<open>rep_T' (abs_T' y)\<close> may map \<open>y\<close> to a different
value in \<open>T\<close>, but that must be equivalent. If \<open>f\<close> respects \<open>E\<close> the result is always the same as the
result \<open>abs_T' (f (g (rep_T' x)))\<close> of applying the lifted composition \<open>f\<circ>g\<close>, i.e., lifting is
compatible with function composition. Therefore HOL supports lifting only for functions which
respect \<open>E\<close>.

If the corresponding transfer relation \<open>R\<close> is left-unique the equivalence relation \<open>E\<close> is the equality
\<open>eq_onp (\<lambda>x. x\<in>D)\<close> restricted to the domain \<open>D\<close> of \<open>R\<close> (see Section~\ref{holbasic-quotlift-setup}).
Then the respectfulness theorem for a function \<open>f\<close> and \<open>E\<close> is equivalent to the proposition
@{text[display]
\<open>\<And>x. x \<in> D \<Longrightarrow> (f x) \<in> D\<close>}
which means that the domain \<open>D\<close> is closed under \<open>f\<close>.\<close>

subsubsection "Defining Functions by Lifting"

text\<open>
After registering a type \<open>T'\<close> as quotient of \<open>T\<close> with relations \<open>R\<close> and \<open>E\<close> and morphisms \<open>abs_T'\<close>
and \<open>rep_T'\<close> it is possible to lift operations on \<open>T\<close> respecting \<open>E\<close> to \<open>T'\<close> using the command
@{theory_text[display]
\<open>lift_definition name :: "T' \<Rightarrow> T'" is "term" \<proof>\<close>}
\index{lift-definition@lift$\_$definition (keyword)}\index{is (keyword)}
where \<open>term\<close> is a term of type \<open>T\<Rightarrow>T\<close>. The command introduces a definition \<open>name_def\<close> for \<open>name\<close> as
\<open>name x \<equiv> abs_T' (term (rep_T' x))\<close>. Note that this is equivalent to \<open>name \<equiv> map_fun rep_T' abs_T'
term\<close> using the mapper \<open>map_fun\<close> (see Section~\ref{holbasic-functor-multi}), which is the form
actually used by HOL.

Every \<^theory_text>\<open>lift_definition\<close> command creates a goal and includes the \<open>\<proof>\<close> for the respectfulness
theorem for the given \<open>term\<close> and the quotient's equivalence relation \<open>E\<close>. If \<open>T'\<close> has been registered
using a type-definition theorem the goal is generated in the form that \<open>D\<close> must be closed under
\<open>term\<close>.

In the \<open>rnb\<close> example after registering type \<open>bool\<close> as quotient of type \<open>nat\<close> a negation operation
can be defined using lifting in the form
@{theory_text[display]
\<open>lift_definition mynot :: "bool \<Rightarrow> bool" is "\<lambda>n. 1-n" \<proof>\<close>}
If the quotient has been registered using the quotient theorem \<open>qrnb\<close>, the command generates the
respectfulness theorem
@{text[display]
\<open>\<And>x y. rnbE x y \<Longrightarrow> rnbE (1-x) (1-y)\<close>}
as goal to be proved. If it has been registered using the type-definition theorem \<open>trnb\<close>, the command
generates the closedness theorem
@{text[display]
\<open>\<And>n. n \<in> rnbD \<Longrightarrow> 1-n \<in> rnbD\<close>}
as goal to be proved.\<close>

subsubsection "Generalized Lifting"

text\<open>
More generally, lifting is supported for respectful functions \<open>f\<close> of a type \<open>T\<^sub>1\<Rightarrow>T\<^sub>2\<close> with different
types for argument and result. If both types are registered quotients the lifted function is defined
using the corresponding morphisms \<open>abs_T\<^sub>2\<close> and \<open>rep_T\<^sub>1\<close>. If only one of both types is a registered
quotient, the other is retained by lifting, then the corresponding application of \<open>abs_T\<^sub>2\<close> or
\<open>rep_T\<^sub>1\<close> is omitted. The respectfulness theorem has the form \<open>E\<^sub>1 x y \<Longrightarrow> E\<^sub>2 (f x) (f y)\<close> where \<open>E\<^sub>i\<close>
is replaced by equality if \<open>T\<^sub>i\<close> is not a registered quotient.

Since functions with multiple arguments are represented by types of the form \<open>T\<^sub>1\<Rightarrow>\<dots>\<Rightarrow>T\<^sub>n\<Rightarrow>T\<close>
lifting is also applicable to them. Finally, a single value is lifted from \<open>T\<close> to \<open>T'\<close> by application of
\<open>abs_T'\<close>. Together, the general form of the command is
@{theory_text[display]
\<open>lift_definition name :: type is "term" \<proof>\<close>}
where \<open>type\<close> is an arbitrary type and the type of \<open>term\<close> must result from \<open>type\<close> by replacing all
occurrences of registered quotients by their corresponding raw types.

The definition of \<open>name\<close> can be systematically constructed from \<open>type\<close> by replacing occurrences of
registered quotients by their corresponding morphism \<open>abs_T\<close> or \<open>rep_T\<close> and replacing all other type
constructors by their mapper function (see Section~\ref{holbasic-functor-mapper}) and all other
types by the identity function \<open>id\<close>. This is similar as constructing predicators and relators
according to the structure of a type expression consisting of composed natural functors (see
Section~\ref{holbasic-bnf-predrel}). HOL defines the operator name \<open>(--->)\<close>
\index{/map-fun@\<open>--->\<close> (operator)} for \<open>map_fun\<close> to make mappers for function types resemble
visually to the corresponding type. Like the operator name \<open>(===>)\<close> for \<open>rel_fun\<close> (see
Section~\ref{holbasic-transfer-rules}) \<open>(--->)\<close> is only available after using the command
@{theory_text[display]
\<open>unbundle lifting_syntax\<close>}\index{lifting_syntax@lifting$\_$syntax (bundle)}
on theory level.

As examples, if \<open>type\<close> is \<open>T\<^sub>1'\<Rightarrow>T\<^sub>2'\<close> the definition generated
for \<open>name\<close> is \<open>name \<equiv> (rep_T\<^sub>1' ---> abs_T\<^sub>2') term\<close> and if \<open>type\<close> is \<open>T\<^sub>1'\<Rightarrow>T\<^sub>2'\<Rightarrow>nat\<close> the definition
generated for \<open>name\<close> is \<open>name \<equiv> (rep_T\<^sub>1' ---> rep_T\<^sub>2' ---> id) term\<close>.

In the \<open>rnb\<close> example after registering type \<open>bool\<close> as quotient of type \<open>nat\<close> boolean connectives
can be defined using lifting in the form
@{theory_text[display]
\<open>lift_definition myand :: "bool \<Rightarrow> bool \<Rightarrow> bool" is "(*)" \<proof>
lift_definition myor :: "bool \<Rightarrow> bool \<Rightarrow> bool" is "max" \<proof>\<close>}
A predicate on natural numbers can be defined using lifting in the form
@{theory_text[display]
\<open>lift_definition is_zero :: "nat \<Rightarrow> bool" is "\<lambda>n. 1-n" \<proof>\<close>}
Note how the type determines how the specified term is lifted. Here only the result type is lifted
to \<open>bool\<close>, in the definition of \<open>mynot\<close> above the argument type is lifted as well.\<close>

subsubsection "Support for Transfer"

text\<open>
To support transfer from the lifted function to the original function a \<^theory_text>\<open>lift_definition\<close> command
for \<open>name\<close>, \<open>type\<close>, and \<open>term\<close> adds the transfer rule
@{text[display]
\<open>name.transfer: REL' term name\<close>}
where \<open>REL'\<close> is the relator constructed according to the structure of \<open>type\<close> as described in
Section~\ref{holbasic-bnf-predrel}. As usual, it allows the \<open>transfer\<close> method to replace occurrences
of \<open>name\<close> by \<open>term\<close>.

If \<open>type\<close> is polymorphic, the type parameters are replaced by \<open>(=)\<close> when constructing \<open>REL'\<close>, thus
the transfer rule only supports transfer when type parameters are instantiated by the same type for
the quotient and the raw type. HOL supports the extended form
@{theory_text[display]
\<open>lift_definition name :: type is "term" parametric pname \<proof>\<close>}
where \<open>pname\<close> is the name of a fact of the form
@{text[display]
\<open>REL term term\<close>}
where \<open>REL\<close> is the relator constructed according to the structure of the type of \<open>term\<close>.
This is a parametricity rule (see Section~\ref{holbasic-transfer-poly}) stating that \<open>term\<close> is
parametrically polymorphic. In this form the \<^theory_text>\<open>lift_definition\<close> command replaces type parameters
by arbitrary relations \<open>R\<^sub>1,\<dots>,R\<^sub>n\<close> when constructing \<open>REL'\<close>. The resulting stronger transfer rule
allows to replace \<open>name\<close> by \<open>term\<close> even if different types are substituted for the type parameters
in the quotient and in the raw type.

In the \<open>rnb\<close> example the transfer rules generated by the definitions above are
@{text[display]
\<open>mynot.transfer: (pcr_bool ===> pcr_bool) (\<lambda>n. 1-n) mynot
myand.transfer: (pcr_bool ===> pcr_bool ===> pcr_bool) (*) myand
myor.transfer: (pcr_bool ===> pcr_bool ===> pcr_bool) max myor
is_zero.transfer: ((=) ===> pcr_bool) (\<lambda>n. 1-n) is_zero\<close>}
If the quotient has been registered using the type-definition theorem \<open>trnb\<close>, these rules cause the
\<open>transfer\<close> method in
@{theory_text[display]
\<open>theorem "mynot (myor a b) = myand (mynot a) (mynot b)"
  apply(transfer)
  by (simp add: mult_eq_if)\<close>}
to replace the goal by the transferred goal
@{text[display]
\<open>\<And>a b. \<lbrakk>a \<in> rnbD; b \<in> rnbD\<rbrakk> \<Longrightarrow> 1 - max a b = (1-a) * (1-b)\<close>}
which can be proved by the simplifier using the additional fact \<open>mult_eq_if\<close>.\<close>

subsection "Quotients as Bounded Natural Functors"
text_raw\<open>\label{holbasic-quotlift-bnf}\<close>

text\<open>
As described in Section~\ref{holbasic-quotlift-setup} a polymorphic quotient  \<open>T'\<close> should have a
registered BNF (see Section~\ref{holbasic-bnf}) without dead type parameters as its raw type \<open>T\<close>,
so that the relator \<open>rel_T\<close> is available for constructing \<open>pcr_T'\<close> and benefitting from full
transfer support. Moreover, in this case the quotient \<open>T'\<close> may again be a BNF.

Since the cardinality of a quotient is never greater than that of the raw type, the quotient
is bounded as soon as the raw type is bounded.

The mapper \<open>m\<close> of \<open>T\<close> can be lifted to \<open>T'\<close> as
@{text[display]
\<open>m' = \<lambda>f\<^sub>1 \<dots> f\<^sub>n. abs_T' \<circ> (m f\<^sub>1 \<dots> f\<^sub>n) \<circ> rep_T'\<close>}
if it respects the equivalence relation \<open>E\<close> of the quotient (see Section~\ref{holbasic-quotlift-lift}),
i.e., if the proposition
@{text[display]
\<open>\<And>x y. E x y \<Longrightarrow> E ((m f\<^sub>1 \<dots> f\<^sub>n) x) ((m f\<^sub>1 \<dots> f\<^sub>n) y)\<close>}
is valid for all possible functions \<open>f\<^sub>1 \<dots> f\<^sub>n\<close> where \<open>n\<close> is the number of type parameters of the BNF \<open>T\<close>.
In this case the lifted mapper \<open>m'\<close> is compatible with function composition (see
Section~\ref{holbasic-quotlift-lift}), thus \<open>T'\<close> is a functor with mapper \<open>m'\<close> (see
Section~\ref{holbasic-functor-mapper}).

The remaining conditions for \<open>T'\<close> to be a BNF are the existence of the set-function(s), the
satisfying of the laws of a natural functor (see Section~\ref{holbasic-bnf-natural}), and the
subdistributivity of the relator (see Section~\ref{holbasic-bnf-bounded}).
\<close>

subsubsection "Quotients as Natural Functors"

text \<open>
If the quotient \<open>T'\<close> has been registered by a type-definition theorem (see
Section~\ref{holbasic-quotlift-setup}) the set-functions \<open>s\<^sub>1, \<dots>, s\<^sub>n\<close> can also be lifted:
@{text[display]
\<open>s\<^sub>i' = s\<^sub>i \<circ> rep_T'\<close>}
because they trivially respect \<open>E\<close> which is the equality restricted to the domain \<open>D\<close> of the
transfer relation. In a similar way the predicator and relator of \<open>T\<close> can be lifted to \<open>T'\<close>.

To satisfy the laws of a natural functor only two properties must be satisfied: the domain \<open>D\<close>
of the transfer relation must be closed under the mapper \<open>m\<close>:
@{text[display]
\<open>x \<in> D \<Longrightarrow> (m f\<^sub>1 \<dots> f\<^sub>n) x \<in> D\<close>}
and under the zip construction (see Section~\ref{holbasic-bnf-predrel}) using the mapper \<open>m\<close> and the
set-functions \<open>s\<^sub>i\<close>:
@{text[display]
\<open>\<lbrakk>(m fst\<dots>fst) z \<in> D, (m snd\<dots>snd) z \<in> D\<rbrakk>
 \<Longrightarrow> \<exists>zz \<in> D.
       s\<^sub>1 zz \<subseteq> s\<^sub>1 z \<and> \<dots> \<and> s\<^sub>n zz \<subseteq> s\<^sub>n z \<and>
       (m fst\<dots>fst) zz = (m fst\<dots>fst) z \<and>
       (m snd\<dots>snd) zz = (m snd\<dots>snd) z\<close>}
Here for every zipped container \<open>z\<close> (see Section~\ref{holbasic-bnf-predrel}) for which the unzipped
containers are in \<open>D\<close> there must be a zipped container \<open>zz\<close> in \<open>D\<close> with no additional content
and the same unzipped containers. The subdistributivity of the relator (see
Section~\ref{holbasic-bnf-bounded}) directly carries over from \<open>T\<close>.

If the quotient \<open>T'\<close> has been registered by a quotient theorem the set-functions could only be
lifted if they respect the equivalence relation \<open>E\<close>, which means that values of the BNF \<open>T\<close> can only
be equivalent if they have the same content, differing only in their shape. To support more general
equivalence relations HOL constructs the set-functions, the relator and the predicator for \<open>T'\<close>
from \<open>E\<close> and \<open>m\<close> in a different way.

For this construction the laws of a natural functor can be satisfied by proving a single goal about
the equivalence relation \<open>E\<close>. A second goal corresponds to the subdistributivity of the relator.
More information about these conditions can be found in \<^cite>\<open>fuerer\<close>.
\<close>

subsubsection "The \<^theory_text>\<open>lift_bnf\<close> Command"

text\<open>
HOL supports registering a quotient of a BNF as BNF using the command
@{text[display]
\<open>lift_bnf ('name\<^sub>1,\<dots>,'name\<^sub>n) name \<proof>\<close>}\index{lift-bnf@lift$\_$bnf (keyword)}
where the parentheses may be omitted if \<open>n = 1\<close>. \<open>name\<close> must be the type constructor name of a 
registered quotient (see Section~\ref{holbasic-quotlift-setup}) and the
\<open>'name\<^sub>1\<close> must be type variables for its type parameters. If \<open>name\<close> has not been registered as a
quotient using \<^theory_text>\<open>setup_lifting\<close> the command signals an error.

The command generates two goals which must be proved in the \<^theory_text>\<open>\<proof>\<close>. The goals are as described
above and differ depending whether the quotient has been registered using a type-definition theorem
or a quotient theorem. 

After the \<^theory_text>\<open>\<proof>\<close> of both goals the \<^theory_text>\<open>lift_bnf\<close> command generates definitions for the mapper \<open>m\<close>,
the set-functions \<open>s\<^sub>i\<close>, the predicator \<open>p\<close>, and the relator \<open>r\<close>, with the usual names \<open>map_name\<close>,
\<open>seti_name\<close>, \<open>pred_name\<close>, and \<open>rel_name\<close>. Alternative names for (some of) these functions may be
specified in the form
@{theory_text[display]
\<open>lift_bnf (sname\<^sub>1: 'name\<^sub>1,\<dots>, sname\<^sub>n: 'name\<^sub>n) name
  for map: mname pred: pname rel: rname\<close>}\index{for (keyword)}

After the definition of the BNF functions the command generates and proves the same named facts
as the \<^theory_text>\<open>bnf\<close> command (see Section~\ref{holbasic-bnf-register}) and registers the quotient \<open>name\<close> as
BNF.

If the quotient \<open>T'\<close> has been registered using a quotient theorem the \<^theory_text>\<open>lift_bnf\<close> command requires that
the quotient's transfer relation \<open>R\<close> is left-total, i.e., a reflexivity theorem \<open>reflp E\<close> must have
been specified in the \<^theory_text>\<open>setup_lifting\<close> command used to register the quotient (see
Section~\ref{holbasic-quotlift-setup}). Otherwise the \<^theory_text>\<open>lift_bnf\<close> command signals an error.

If the quotient \<open>T'\<close> has been registered using a type-definition theorem the \<^theory_text>\<open>lift_bnf\<close> command
may complain that a ``nonemptiness witness of the raw type's BNF was lost''. This means that it must
be proved that the domain \<open>D\<close> of \<open>R\<close> is not empty by specifying an actual element (a ``witness'') in
it. This is done by the extended form
@{text[display]
\<open>lift_bnf ('name\<^sub>1,\<dots>,'name\<^sub>n) name [wits: "term"] \<proof>\<close>}\index{wits (keyword)}
of the \<^theory_text>\<open>lift_bnf\<close> command where \<open>term\<close> is a function with arguments of types \<open>'name\<^sub>1,\<dots>,'name\<^sub>n\<close>.
Remember that the raw type is a BNF, i.e., a type of container values consisting of shape and content.
The function arguments denote content values, the function result is a corresponding container.
In this form the command generates additional goals to be proved: one that the resulting container
is always in \<open>D\<close>, and \<open>n\<close> goals stating that the container value has no other content of type
\<open>'name\<^sub>i\<close> than the argument values of that type.

For examples of using \<^theory_text>\<open>lift_bnf\<close> see Sections~\ref{holtdefs-sub-bnf} and~\ref{holtdefs-quot-bnf}.

Like the \<^theory_text>\<open>bnf\<close> command the \<^theory_text>\<open>lift_bnf\<close> command does not register the generated mapper \<open>m\<close> as
functor. If needed this must be done explicitly using the \<^theory_text>\<open>functor\<close> command (see
Section~\ref{holbasic-bnf-register}).
\<close>

subsubsection "The \<^theory_text>\<open>copy_bnf\<close> Command"

text\<open>
If the transfer relation \<open>R\<close> for a quotient \<open>T'\<close> is left-total and left-unique \<open>T'\<close> is isomorphic
to the raw type \<open>T\<close> and can be registered as quotient using a type-definition theorem with the
universal set \<open>UNIV\<close> as domain \<open>D\<close> of the transfer relation (see Section~\ref{holbasic-quotlift-setup}).

If \<open>T\<close> is a BNF the closedness properties for the mapper and the zip construction required for \<open>T'\<close>
to also be a BNF (see above) are trivially satisfied. HOL supports registering such a quotient
as BNF using the command
@{theory_text[display]
\<open>copy_bnf ('name\<^sub>1,\<dots>,'name\<^sub>n) name\<close>}\index{copy-bnf@copy$\_$bnf (keyword)}
where the parentheses may be omitted if \<open>n = 1\<close>. \<open>name\<close> must be the name of the quotient and the
\<open>'name\<^sub>1\<close> must be type variables for its type parameters. No proof is required, the two goals are
proved automatically by HOL. As for \<^theory_text>\<open>lift_bnf\<close> \<open>name\<close> must have been registered as a quotient
using \<^theory_text>\<open>setup_lifting\<close>, otherwise the command signals an error.

The \<^theory_text>\<open>copy_bnf\<close> command generates definitions for the mapper \<open>m\<close>, the set-functions \<open>s\<^sub>i\<close>, the
predicator \<open>p\<close>, and the relator \<open>r\<close>, with the usual names \<open>map_name\<close>, \<open>seti_name\<close>, \<open>pred_name\<close>, and
\<open>rel_name\<close>. Alternative names for (some of) these functions may be specified similar as for \<^theory_text>\<open>lift_bnf\<close>
in the form
@{theory_text[display]
\<open>copy_bnf (sname\<^sub>1: 'name\<^sub>1,\<dots>, sname\<^sub>n: 'name\<^sub>n) name
  for map: mname pred: pname rel: rname\<close>}\index{for (keyword)}

After the definition of the BNF functions the command generates and proves most of the named facts
provided by the \<^theory_text>\<open>lift_bnf\<close> command and registers the quotient \<open>name\<close> as BNF.

For an example of using \<^theory_text>\<open>copy_bnf\<close> see Section~\ref{holtdefs-sub-bnf}.

Like the \<^theory_text>\<open>bnf\<close> command the \<^theory_text>\<open>copy_bnf\<close> command does not register the generated mapper \<open>m\<close> as
functor. If needed this must be done explicitly using the \<^theory_text>\<open>functor\<close> command (see
Section~\ref{holbasic-bnf-register}).
\<close>

end