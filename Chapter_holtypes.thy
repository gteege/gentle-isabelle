theory Chapter_holtypes
  imports Chapter_holtdefs HOL.BNF_Cardinal_Arithmetic
begin

chapter "Isabelle/HOL Types"
text_raw\<open>\label{holtypes}\<close>

text \<open>
This chapter introduces a small basic part of the types available in HOL\index{HOL (object logic)}.

Most of the types are algebraic types (see Section~\ref{holtdefs-data}). Although some of them are
defined differently for technical reasons, they are configured afterwards to behave as if they 
have been defined as algebraic types. Therefore they are described here using the corresponding
datatype definition.

A type basically provides the type name or type constructor, if the type is parametric.
Together with a type, HOL introduces functions on the values of the type, either implicitly by
using type definition mechanisms described in Section~\ref{holtdefs}, or explicitly by using 
definitions (see Sections~\ref{theory-definition}, \ref{holbasic-inductive},
and~\ref{holbasic-recursive}). In this way HOL populates the object level of the inner syntax with
a rich language for expressing mathematical content. Additionally, HOL provides facts (usually 
derivation rules) about these functions which can be used in proofs. For every type this
introduction describes its mathematical meaning, it gives a short description of (most of) the
defined functions, and it lists some exemplary rules with explanations.

If applicable, the functions described for a type include the specific forms of ordering relations
and lattice operations (see Section~\ref{holbasic-equal}) and functions for binder syntax (see
Section~\ref{holbasic-descr}).

The semantics of the described functions is either given informally for well-known functions or by
a description of the form \<open>name :: type \<equiv> lambda-term\<close>. The latter is often not the actual
definition used by HOL for the function, it is only used here for documentation purpose.

At the beginning of each of the following sections the theories in session HOL are listed
where the type, functions, and rules described in the section are actually defined.
\<close>

section "Boolean Values"
text_raw\<open>\label{holtypes-bool}\<close>

text\<open>\<^bold>\<open>Theories:\<close> {\tt\sl HOL, Orderings, Complete$\_$Lattices}\<close>

text\<open>
The type of boolean values is specified equivalent to an algebraic type of the form
of the enumeration type (see Section~\ref{holtdefs-data-constr})
@{theory_text[display]
\<open>datatype bool = True | False\<close>}\index{bool (type)}\index{True (constant)}\index{False (constant)}

The type \<open>bool\<close> plays a special role in HOL since it is the type of all terms which are used 
as formulas (see Section~\ref{theory-prop-formulas}) in Isabelle. Every object logic\index{object logic}\index{logic!object $\sim$}
used in Isabelle must define a type which plays this role.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-bool-values}\<close>

text\<open>
Values of type \<open>bool\<close> can directly be denoted by the parameterless constructors \<open>True\<close> and \<open>False\<close>.

The lattice constants \<open>top\<close> and \<open>bot\<close> (see Section~\ref{holbasic-equal-lattice}) are available for
type \<open>bool\<close> and denote the values \<open>True\<close> and \<open>False\<close>, respectively.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-bool-destrs}\<close>

text\<open>
Since both constructors are constant no selectors can be defined. Discriminators are not required
since the constants are already boolean values.

A \<open>case\<close> term for type \<open>bool\<close> has the form
@{text[display]
\<open>case term of True \<Rightarrow> term\<^sub>1 | False \<Rightarrow> term\<^sub>2\<close>}
where \<open>term\<close> is a term of type \<open>bool\<close>.

As an alternative syntax HOL provides the usual form\index{if-term}\index{term!if $\sim$}
@{text[display]
\<open>if term then term\<^sub>1 else term\<^sub>2\<close>}\index{if (inner keyword)}\index{then (inner keyword)}\index{else (inner keyword)}
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-bool-funcs}\<close>

text\<open>
The usual logical functions are defined for type \<open>bool\<close>: \<open>conj, disj, implies, iff\<close>
of type \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> with operator names \<open>(\<and>), (\<or>), (\<longrightarrow>), (\<longleftrightarrow>)\<close> and the unary negation
\<open>Not\<close> of type \<open>bool \<Rightarrow> bool\<close> and operator name \cbstart \<open>\<not>\<close> \cbend. The function \<open>(\<longleftrightarrow>)\<close> is the specific
instance of \<open>(=)\<close> for type \<open>bool\<close> (see Section~\ref{holbasic-equal-eq}).
\index{conj (constant)}\index{disj (constant)}\index{implies (constant)}\index{iff (constant)}\index{Not (constant)}
\index{/and@\<open>\<and>\<close> (operator)}\index{/or@\<open>\<or>\<close> (operator)}\index{/imp@\<open>\<longrightarrow>\<close> (operator)}\index{/iff@\<open>\<longleftrightarrow>\<close> (operator)}
\index{/not@\<open>\<not>\<close> (operator)}
\<close>

subsubsection "Functions for Orderings and Lattices"

text\<open>
The ordering relations (see Section~\ref{holbasic-equal-order}) and the lattice operations (see
Section~\ref{holbasic-equal-lattice}) are defined for type \<open>bool\<close> so that \<open>False < True\<close>. This
implies that \<open>(\<le>)\<close> is equivalent to \<open>(\<longrightarrow>)\<close> and \<open>(\<sqinter>), (\<squnion>)\<close> and also \<open>min, max\<close> are equivalent to
\<open>(\<and>), (\<or>)\<close>.

The lattice operators \<open>(\<Sqinter>)\<close> and \<open>(\<Squnion>)\<close> on sets are provided for \<open>bool\<close> by definitions
\<open>\<Sqinter>A \<equiv> (False \<notin> A)\<close> and \<open>\<Squnion>A \<equiv> (True \<in> A)\<close>, so they correspond to conjunction and disjunction
over sets, respectively. Note that the meta-logic quantifier \<open>\<And>\<close> (see
Section~\ref{theory-prop-bind}) does \<^emph>\<open>not\<close> denote a conjunction operation on sets of boolean
values. For nonempty \cbdelete sets of boolean values the functions \<open>Min\<close> and \<open>Max\<close> are equivalent to
\<open>(\<Sqinter>)\<close> and \<open>(\<Squnion>)\<close>.
\<close>

subsubsection "Functions for Binder Syntax"

text\<open>
The quantifiers\index{quantifier}\index{binder} are defined as ``predicates on predicates'':
@{text[display]
\<open>All :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> \<lambda>P. (P = (\<lambda>x. True))
Ex :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> \<lambda>P. (\<not> All (\<lambda>x. \<not> P x))
Uniq :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
  \<lambda>P. (All (\<lambda>x. (All (\<lambda>y. P x \<longrightarrow> P y \<longrightarrow> y = x))))
Ex1 :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
  \<lambda>P. (Ex (\<lambda>x. P x \<and> (All (\<lambda>y. P y \<longrightarrow> y = x))))\<close>}
\index{All (constant)}\index{Ex (constant)}\index{Uniq (constant)}\index{Ex1 (constant)}
with the alternative binder syntax \<open>\<forall>x. bterm\<close> for the application \<open>All (\<lambda>x. bterm)\<close>, \<open>\<exists>x. bterm\<close>
for \<open>Ex (\<lambda>x. bterm)\<close>, \<open>\<exists>\<^sub>\<le>\<^sub>1x. bterm\<close> for \<open>Uniq (\<lambda>x. bterm)\<close>, and \<open>\<exists>!x. bterm\<close> for \<open>Ex1 (\<lambda>x. bterm)\<close>.
\index{/all@\<open>\<forall>\<close> (binder)}\index{/ex@\<open>\<exists>\<close> (binder)}\index{/uniq@\<open>\<exists>\<^sub>\<le>\<^sub>1\<close> (binder)}\index{/ex1@\<open>\<exists>!\<close> (binder)}
The \<open>Uniq\<close> quantifier states that there is atmost one value satisfying the predicate, the \<open>Ex1\<close>
quantifier states that there is exactly one such value.

An iterated application for an n-ary predicate \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. bterm\<close> can be written in the
form \<open>\<forall> x\<^sub>1 \<dots> x\<^sub>n. bterm\<close> for all quantifiers. As for lambda terms (see
Section~\ref{theory-terms-lambda}) types may be specified for (some of) the variables as in
\<open>\<forall> (x\<^sub>1 :: type\<^sub>1) \<dots> (x\<^sub>n :: type\<^sub>n). bterm\<close>.

HOL also provides several functions which support binder syntax where a single bound variable is
restricted (``bounded'') by an ordering (see Section~\ref{holbasic-equal-order}) or inequality
(see Section~\ref{holbasic-equal-eq}) relation to some value.

HOL provides functions similar to \<open>All\<close> and \<open>Ex\<close> to support the syntax of the bounded quantifiers\index{quantifier!bounded $\sim$}
@{text[display]
\<open>\<forall>x<y. bterm \<equiv> \<forall>x. x < y \<longrightarrow> bterm
\<exists>x<y. bterm \<equiv> \<exists>x. x < y \<and> bterm
\<forall>x\<le>y. bterm \<equiv> \<forall>x. x \<le> y \<longrightarrow> bterm
\<exists>x\<le>y. bterm \<equiv> \<exists>x. x \<le> y \<and> bterm
\<forall>x>y. bterm \<equiv> \<forall>x. x > y \<longrightarrow> bterm
\<exists>x>y. bterm \<equiv> \<exists>x. x > y \<and> bterm
\<forall>x\<ge>y. bterm \<equiv> \<forall>x. x \<ge> y \<longrightarrow> bterm
\<exists>x\<ge>y. bterm \<equiv> \<exists>x. x \<ge> y \<and> bterm
\<forall>x\<noteq>y. bterm \<equiv> \<forall>x. x \<noteq> y \<longrightarrow> bterm
\<exists>x\<noteq>y. bterm \<equiv> \<exists>x. x \<noteq> y \<and> bterm\<close>}\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-bool-rules}\<close>

text\<open>
The rules described here are the usual rules for an algebraic type and introduction / elimination
/ destruction rules for the functions, and some specific rules for negation. HOL provides
many additional rules, see the Isabelle documentation \<^cite>\<open>"isar-ref" and "prog-prove" and tutorial\<close>
for how to use them in proofs.

Complex proofs using these rules can often be done automatically by the proof method \<open>blast\<close>\index{blast (method)} (see
Section~\ref{methods-auto-methods}).
\<close>

subsubsection "Algebraic Type Rules"

text\<open>
Since there are no selectors for \<open>bool\<close> and all constructors are constant the main simplifier rules
are the rule sets \<open>bool.distinct\<close> and \<open>bool.case\<close> (see Section~\ref{holtdefs-data-rules}):
@{text[display]
\<open>True \<noteq> False
False \<noteq> True
(case True of True \<Rightarrow> ?t\<^sub>1 | False \<Rightarrow> ?t\<^sub>2) = ?t\<^sub>1
(case False of True \<Rightarrow> ?t\<^sub>1 | False \<Rightarrow> ?t\<^sub>2) = ?t\<^sub>2\<close>}

The case, split, and induction rules are
@{text[display]
\<open>bool.exhaust:
  \<lbrakk>?y = True \<Longrightarrow> ?P; ?y = False \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P
bool.split:
  ?P (case ?t of True \<Rightarrow> ?t\<^sub>1 | False \<Rightarrow> ?t\<^sub>2) =
  ((?t = True \<longrightarrow> ?P ?t\<^sub>1) \<and> (?t = False \<longrightarrow> ?P ?t\<^sub>2))
bool.induct:
  \<lbrakk>?P True; ?P False\<rbrakk> \<Longrightarrow> ?P ?a\<close>}

Actually, as automatic case rule for type \<open>bool\<close> instead of \<open>bool.exhaust\<close> the slightly different
rule
@{text[display]
\<open>case_split:
  \<lbrakk>?Q \<Longrightarrow> ?P; \<not> ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}\index{case-split@case$\_$split (fact name)}
is used, as described in Section~\ref{case-reasoning-rules}.

For the alternate case term form described in Section~\ref{holtypes-bool-destrs} there is also a
split rule:
@{text[display]
\<open>if_split:
  ?P (if ?t then ?t\<^sub>1 else ?t\<^sub>2) = 
  ((?t \<longrightarrow> ?P ?t\<^sub>1) \<and> (\<not> ?t \<longrightarrow> ?P ?t\<^sub>2))\<close>}\index{if-split@if$\_$split (fact name)}
Other than \<open>bool.split\<close> this rule is automatically applied by the simplifier (see
Section~\ref{methods-simp-split}) for splitting \<open>if\<close>-terms\index{if-term}\index{term!if $\sim$}.
\<close>

subsubsection "Rules About Boolean Functions"

text\<open>
For the functions described in Section~\ref{holtypes-bool-funcs} corresponding introduction rules
(see Section~\ref{methods-rule-intro}), destruction rules (see Section~\ref{methods-forward-dest}),
and elimination rules (see Section~\ref{case-elim-rules}) are available. They are present in the
rule sets \<open>intro\<close>, \<open>dest\<close>, or \<open>elim\<close>, respectively.

The introduction rules are:

@{text\<open>conjI:\<close>} @{thm conjI}\index{conjI (fact name)}\\
@{text\<open>disjI1:\<close>} @{thm disjI1}\index{disjI1 (fact name)}\\
@{text\<open>disjI2:\<close>} @{thm disjI2}\index{disjI2 (fact name)}\\
@{text\<open>notI:\<close>} @{thm notI}\index{notI (fact name)}\\
@{text\<open>impI:\<close>} @{thm impI}\index{impI (fact name)}\\
@{text\<open>iffI:\<close>} @{thm iffI}\index{iffI (fact name)}\\
@{text\<open>allI:\<close>} @{thm allI}\index{allI (fact name)}\\
@{text\<open>exI:\<close>} @{thm exI}\index{exI (fact name)}

The destruction rules are:

@{text\<open>conjunct1:\<close>} @{thm conjunct1}\index{conjunct1 (fact name)}\\
@{text\<open>conjunct2:\<close>} @{thm conjunct2}\index{conjunct2 (fact name)}\\
@{text\<open>mp:\<close>} @{thm mp}\index{mp (fact name)}\\
@{text\<open>spec:\<close>} @{thm spec}\index{spec (fact name)}\\
@{text\<open>iffD1:\<close>} @{thm iffD1}\index{iffD1 (fact name)}\\
@{text\<open>iffD2:\<close>} @{thm iffD2}\index{iffD2 (fact name)}

The rule \<open>mp\<close> is the well known logic rule ``modus ponens''\index{modus ponens}.

The elimination rules are:

@{text\<open>conjE:\<close>} @{thm conjE}\index{conjE (fact name)}\\
@{text\<open>disjE:\<close>} @{thm disjE}\index{disjE (fact name)}\\
@{text\<open>notE:\<close>} @{thm notE}\index{notE (fact name)}\\
@{text\<open>impE:\<close>} @{thm impE}\index{impE (fact name)}\\
@{text\<open>iffE:\<close>} @{thm iffE}\index{iffE (fact name)}\\
@{text\<open>allE:\<close>} @{thm allE}\index{allE (fact name)}\\
@{text\<open>exE:\<close>} @{thm exE}\index{exE (fact name)}

Additionally, the following four rules can be used for ``proofs by contradiction''\index{proof!by contradiction}:

@{text\<open>contrapos_pn:\<close>} @{thm contrapos_pn}\index{contrapos-pn@contrapos$\_$pn (fact name)}\\
@{text\<open>contrapos_pp:\<close>} @{thm contrapos_pp}\index{contrapos-pp@contrapos$\_$pp (fact name)}\\
@{text\<open>contrapos_nn:\<close>} @{thm contrapos_nn}\index{contrapos-nn@contrapos$\_$nn (fact name)}\\
@{text\<open>contrapos_np:\<close>} @{thm contrapos_np}\index{contrapos-np@contrapos$\_$np (fact name)}
\<close>

subsubsection "Equivalence of Derivation Rules and Boolean Terms"

text\<open>
Using these rules together with the rules about the meta-logic operators

@{text\<open>atomize_all:\<close>} @{thm atomize_all}\index{atomize-all@atomize$\_$all (fact name)}\\
@{text\<open>atomize_imp:\<close>} @{thm atomize_imp}\index{atomize-imp@atomize$\_$imp (fact name)}\\
@{text\<open>atomize_conjL:\<close>} @{thm atomize_conjL}\index{atomize-conjL@atomize$\_$conjL (fact name)}\\
@{text\<open>atomize_conj:\<close>} @{thm atomize_conj}\index{atomize-conj@atomize$\_$conj (fact name)}

every meta-logic derivation rule with possibly multiple conclusions (see
Section~\ref{theory-prop-multconcl})
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close>}
can be converted to the boolean term
@{text[display]
\<open>\<forall> x\<^sub>1 \<dots> x\<^sub>m. (A\<^sub>1' \<and> \<dots> \<and> A\<^sub>n') \<longrightarrow> C\<^sub>1' \<and> \<dots> \<and> C\<^sub>h'\<close>}
(where each \<open>A\<^sub>i'\<close> and \<open>C\<^sub>i'\<close> is converted in the same way if it is again a derivation rule), and
vice versa.

In principle every theorem may be specified in either of both forms. However, its application by
proof methods in other proofs is usually only possible if it is specified in derivation rule form.
Therefore it is usually preferable to specify theorems in this form.
\<close>

section "The Unit Type"
text_raw\<open>\label{holtypes-unit}\<close>

text\<open>\<^bold>\<open>Theories:\<close> {\tt\sl Product$\_$Type}\<close>

text\<open>
The unit type has only one value. It is specified equivalent to an algebraic type of the form
of the enumeration type (see Section~\ref{holtdefs-data-constr})
@{theory_text[display]
\<open>datatype unit = Unity\<close>}\index{unit (type)}\index{Unity (constant)}

A typical use of the unit type is for instantiating a parameter of a parameterized type when
you actually don't care about it. For example, if you have to use binary predicates of type
\<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> but do not care about the second argument you can use the type
\<open>'a \<Rightarrow> unit \<Rightarrow> bool\<close>. Syntactically its values are still binary predicates, however, since there is
only one possible value for the second argument, it cannot affect the result, so semantically they
are unary predicates. Another use of the unit type is for the more part in unextended record types
(see Section~\ref{holtdefs-record-def}).

So the unit type plays the role of an ``empty type'' (which does not exist for formal reasons).
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-unit-values}\<close>

text\<open>
Values of type \<open>unit\<close> can directly be denoted by the parameterless constructor \<open>Unity\<close>. The
usual way of denoting it is by its alternative form \<open>()\<close>\index{() (constant)}, which has been chosen because the unit
type is also used to represent empty tuples\index{empty tuple}\index{tuple!empty $\sim$} (see Section~\ref{holtypes-tup}).
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-unit-destrs}\<close>

text\<open>
A \<open>case\<close> term for type \<open>unit\<close> has the form
@{text[display]
\<open>case term of () \<Rightarrow> term\<^sub>1\<close>}
where \<open>term\<close> is a term of type \<open>unit\<close>. It is equivalent to \<open>term\<^sub>1\<close>.
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-unit-rules}\<close>

text\<open>
The usual rules for an algebraic type are also defined for \<open>unit\<close>. They are of no much use, but
here they are shown for the interested reader:
@{text[display]
\<open>unit.exhaust: (?y = () \<Longrightarrow> ?P) \<Longrightarrow> ?P
unit.split: ?P (case ?t of () \<Rightarrow> ?t\<^sub>1) = (?t = () \<longrightarrow> ?P ?t\<^sub>1)
unit.induct: ?P () \<Longrightarrow> ?P ?a\<close>}
The split rule is required if during a proof a \<open>case\<close> term for type \<open>unit\<close> (see
Section~\ref{holtypes-unit-destrs}) occurs for some reason. Although it is trivially equivalent to
its subterm \<open>term\<^sub>1\<close>, the simplifier will not use that equivalence since it never splits \<open>case\<close> terms
automatically. It must be configured as \<open>simp split: unit.split\<close> to do so.

Since there are no functions for \<open>unit\<close> there are no introduction / destruction / elimination rules.
\<close>

section "Natural Numbers"
text_raw\<open>\label{holtypes-nat}\<close>

text\<open>\<^bold>\<open>Theories:\<close> {\tt\sl Nat, Groups, Rings}\<close>

text\<open>
The type of natural numbers is specified equivalent to a recursive algebraic type (see 
Section~\ref{holtdefs-data}) of the form
@{theory_text[display]
\<open>datatype nat = 0 | Suc nat\<close>}\index{nat (type)}\index{Suc (constant)}
It is not really defined in this way, because \<open>0\<close> is syntactically not a constructor, but it can
mainly be used in the same way.

The type \<open>nat\<close> denotes the mathematical concept of natural numbers\index{natural numers}, it has infinitely many values,
there is no upper limit.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-nat-values}\<close>

text\<open>
Values of type \<open>nat\<close> can be denoted in the usual way using constructor expressions such as \<open>Suc 0,
Suc (Suc 0), \<dots>\<close>.

Alternatively they can be denoted by decimal number literals\index{number literal} such as \<open>0, 1, 2, \<dots>\<close> of arbitrary size.

However, the decimal number literals are overloaded and may also denote values of other numerical
types, such as type \<open>int\<close> for the integer numbers. Therefore the type of an isolated decimal number
literal is not determined, which may cause unexpected effects. To denote a value of type \<open>nat\<close> its
type may be explicitly specified as described in Section~\ref{theory-terms-consts}, such as \<open>1::nat\<close>.

The lattice constant \<open>bot\<close> (see Section~\ref{holbasic-equal-lattice}) is available for type \<open>nat\<close>
and denotes the value \<open>0\<close>. The constant \<open>top\<close> is not available for type \<open>nat\<close>.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-nat-destrs}\<close>

text\<open>
Since \<open>Suc\<close> plays the role of a constructor, corresponding destructors can be defined.
The selector function which inverts \<open>Suc\<close> is defined as \<open>nat.pred\<close>\index{nat.pred (constant)} where \<open>nat.pred x\<close> is equivalent
to \<open>x - 1\<close> and \<open>nat.pred 0 = 0\<close>. This selector is not intended to be used directly, use the
subtraction function described below instead. There are no discriminators, instead the equality
terms \<open>x = 0\<close> and \<open>x \<noteq> 0\<close> can be used.

A \<open>case\<close> term for type \<open>nat\<close> has the form
@{text[display]
\<open>case term of 0 \<Rightarrow> term\<^sub>1 | Suc n \<Rightarrow> term\<^sub>2\<close>}
where \<open>term\<close> is a term of type \<open>nat\<close>.
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-nat-funcs}\<close>

text\<open>
The usual basic arithmetic functions are defined for type \<open>nat\<close>: \<open>plus, minus, times, divide, modulo\<close>
\index{plus (constant)}\index{minus (constant)}\index{times (constant)}\index{divide (constant)}\index{modulo (constant)}
of type \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> with operator names \<open>(+), (-), (*), (div), (mod)\<close> and alternate
operator name \<open>(/)\<close> for \<open>(div)\<close>. Subtraction is truncated at \<open>0\<close>, e.g. \<open>4 - 7\<close> evaluates to \<open>0\<close>.
Also defined is the binary ``divides'' relation \<open>dvd_class.dvd\<close> with operator name \<open>(dvd)\<close>.
\index{/plus@\<open>+\<close> (operator)}\index{/minus@\<open>-\<close> (operator)}\index{/times@\<open>*\<close> (operator)}\index{/div@\<open>/\<close> (operator)}\index{div (operator)}\index{mod (operator)}

Like decimal number literals all these functions are overloaded and not restricted to natural
numbers. As a consequence, a proposition such as 
@{theory_text[display]
\<open>4 - 7 = 0\<close>}
is not valid and cannot be proved. To become a provable fact it must be specified in a form like
@{theory_text[display]
\<open>(4::nat) - 7 = 0\<close>}
which can be proved by method \<open>simp\<close>. Note that it is sufficient to specify the type for a single
literal, because then the type of the function \<open>(-)\<close> is derived to be \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> (there are
no ``mixed-typed'' arithmetic functions) from which the type of the second literal is derived and
similar for the equality.

For type \<open>nat\<close> HOL defines the \<open>size\<close> function (see Section~\ref{holbasic-wellfounded-size})
to be the identity function.
\<close>

subsubsection "Functions for Orderings and Lattices"

text\<open>
The ordering relation \<open>(<)\<close> (see Section~\ref{holbasic-equal-order}) is defined to be the usual
ordering on natural numbers. This implies that also \<open>min\<close> and \<open>max\<close> have their usual meaning.
The lattice operations (see Section~\ref{holbasic-equal-lattice}) are overloaded for type \<open>nat\<close> so
that \<open>(\<sqinter>), (\<squnion>)\<close> are equivalent to \<open>min, max\<close>.

The functions \<open>Min\<close> and \<open>Max\<close> on sets are also defined as expected on finite nonempty sets of
natural numbers, otherwise their result is underspecified. The lattice operators \<open>(\<Sqinter>)\<close> and \<open>(\<Squnion>)\<close>
are equivalent to \<open>Min\<close> and \<open>Max\<close>, additionally \<open>\<Squnion>{}\<close> is specified to be \<open>0\<close> and \<open>(\<Sqinter>)\<close> is also
specified to return the minimal value for infinite sets of natural numbers.
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-nat-rules}\<close>

text\<open>
HOL provides a large number of rules applicable for proofs about values of type \<open>nat\<close>. Here we only
show rules for an algebraic type and introduction / elimination / destruction rules for the
functions, as for other types. They are usually not sufficient for proofs about natural numbers
and should only give an impression about the type \<open>nat\<close> in comparison with other types.

Proofs for linear arithmetic properties of \<open>nat\<close> values using these and other rules can often be
done automatically by the proof methods \<open>linarith\<close> or \<open>arith\<close> (see Section~\ref{methods-auto-methods}).
\<close>

subsubsection "Algebraic Type Rules"

text\<open>
The simplifier rules for the constructors of type \<open>nat\<close> are the rule sets \<open>nat.inject\<close>, 
\<open>nat.distinct\<close> and \<open>nat.case\<close> (see Section~\ref{holtdefs-data-rules}):
@{text[display]
\<open>(Suc ?x = Suc ?y) = (?x = ?y)
0 \<noteq> Suc ?x
Suc ?x \<noteq> 0
(case 0 of 0 \<Rightarrow> ?t\<^sub>1 | Suc x \<Rightarrow> ?t\<^sub>2 x) = ?t\<^sub>1
(case Suc ?x of 0 \<Rightarrow> ?t\<^sub>1 | Suc x \<Rightarrow> ?t\<^sub>2 x) = ?t\<^sub>2 ?x\<close>}
Note the difference between the unknown \<open>?x\<close> and the locally bound \<open>x\<close> in the last rule.

The case, split, and induction rules are
@{text[display]
\<open>nat.exhaust:
  \<lbrakk>?y = 0 \<Longrightarrow> ?P; \<And>x. ?y = Suc x \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P
nat.split:
  ?P (case ?t of 0 \<Rightarrow> ?t\<^sub>1 | Suc x \<Rightarrow> ?t\<^sub>2 x) =
  ((?t = 0 \<longrightarrow> ?P ?t\<^sub>1) \<and> (\<forall>x. ?t = Suc x \<longrightarrow> ?P (?t\<^sub>2 x)))
nat.induct:
  \<lbrakk>?P 0; \<And>i. ?P i \<Longrightarrow> ?P (Suc i)\<rbrakk> \<Longrightarrow> ?P ?n\<close>}
For the case and induction rule the cases are named \<open>0\<close> and \<open>Suc\<close>.
\<close>

subsubsection "Other Induction Rules"

text\<open>
The rule \<open>nat.induct\<close> is the induction rule associated with type \<open>nat\<close>. Additionally, there are
several other induction rules for values of type \<open>nat\<close> which may be used for other types of
induction by specifying them explicitly to the \<open>induction\<close> or \<open>induct\<close> method:
@{text[display]
\<open>nat_less_induct:
  \<lbrakk>\<And>i. \<forall> j<i. ?P j \<Longrightarrow> ?P i\<rbrakk> \<Longrightarrow> ?P ?n
infinite_descent0:
  \<lbrakk>?P 0; \<And>i. \<lbrakk>0 < i; \<not> ?P i\<rbrakk> \<Longrightarrow> \<exists> j<i. \<not> ?P j\<rbrakk> \<Longrightarrow> ?P ?n
diff_induct:
  \<lbrakk>\<And>i. ?P i 0; \<And>j. ?P 0 (Suc j); \<And>i j. ?P i j \<Longrightarrow> ?P (Suc i) (Suc j)\<rbrakk>
  \<Longrightarrow> ?P ?m ?n
less_Suc_induct [consumes 1]:
  \<lbrakk>?m < ?n; \<And>i. ?P i (Suc i);
   \<And>i j k. \<lbrakk>i < j; j < k; ?P i j; ?P j k\<rbrakk> \<Longrightarrow> ?P i k\<rbrakk>
  \<Longrightarrow> ?P ?m ?n
nat_induct_at_least [consumes 1]:
  \<lbrakk>?m \<le> ?n; ?P ?m; \<And>i. \<lbrakk>?m \<le> i; ?P i\<rbrakk> \<Longrightarrow> ?P (Suc i)\<rbrakk> \<Longrightarrow> ?P ?n
nat_induct_non_zero [consumes 1]:
  \<lbrakk>0 < ?n; ?P 1; \<And>i. \<lbrakk>0 < i; ?P i\<rbrakk> \<Longrightarrow> ?P (Suc i)\<rbrakk> \<Longrightarrow> ?P ?n
inc_induct [consumes 1]:
  \<lbrakk>?n \<le> ?m; ?P ?m; \<And>i. \<lbrakk>?n \<le> i; i < ?m; ?P (Suc i)\<rbrakk> \<Longrightarrow> ?P i\<rbrakk>
  \<Longrightarrow> ?P ?n
strict_inc_induct [consumes 1]:
  \<lbrakk>?n < ?m; \<And>i. ?m = Suc i \<Longrightarrow> ?P i;
   \<And>i. \<lbrakk>i < ?m; ?P (Suc i)\<rbrakk> \<Longrightarrow> ?P i\<rbrakk>
  \<Longrightarrow> ?P ?n
dec_induct [consumes 1]:
  \<lbrakk>?m \<le> ?n; ?P ?m; \<And>i. \<lbrakk>?m \<le> i; i < ?n; ?P i\<rbrakk> \<Longrightarrow> ?P (Suc i)\<rbrakk>
  \<Longrightarrow> ?P ?n\<close>}
\index{nat-less-induct@nat$\_$less$\_$induct (fact name)}\index{infinite-descent0@infinite$\_$descent0 (fact name)}\index{diff-induct@diff$\_$induct (fact name)}
\index{less-Suc-induct@less$\_$Suc$\_$induct (fact name)}\index{nat-induct-at-least@nat$\_$induct$\_$at$\_$least (fact name)}\index{nat-induct-non-zero@nat$\_$induct$\_$non$\_$zero (fact name)}
\index{inc-induct@inc$\_$induct (fact name)}\index{strict-inc-induct@strict$\_$inc$\_$induct (fact name)}\index{dec-induct@dec$\_$induct (fact name)}
Note that the last six rules combine induction with elimination, as described in
Section~\ref{case-induction-elim}, and are therefore attributed by \<open>[consumes 1]\<close>.
\<close>

subsubsection "Rules About Functions"

text\<open>
The constructor function \<open>Suc\<close> has result type \<open>nat\<close> and therefore cannot occur as outermost
operator in a proposition. Therefore introduction, destruction, and elimination rules for \<open>Suc\<close>
must embed the application term in a proposition with the help of a predicate. The ordering
relations are used for this purpose, thus only ordering properties can be proved using these rules.

Introduction rules (see Section~\ref{methods-rule-intro}) for \<open>Suc\<close> are

@{text\<open>le_SucI:\<close>} @{thm le_SucI}\index{le-SucI@le$\_$SucI (fact name)}\\
@{text\<open>less_SucI:\<close>} @{thm less_SucI}\index{less-SucI@less$\_$SucI (fact name)}\\
@{text\<open>Suc_leI:\<close>} @{thm Suc_leI}\index{Suc-leI@Suc$\_$leI (fact name)}\\
@{text\<open>Suc_lessI:\<close>} @{thm Suc_lessI}\index{Suc-lessI@Suc$\_$lessI (fact name)}

Destruction rules (see Section~\ref{methods-forward-dest}) for \<open>Suc\<close> are

@{text\<open>Suc_leD:\<close>} @{thm Suc_leD}\index{Suc-leD@Suc$\_$leD (fact name)}\\
@{text\<open>Suc_lessD:\<close>} @{thm Suc_lessD}\index{Suc-lessD@Suc$\_$lessD (fact name)}\\
@{text\<open>Suc_less_SucD:\<close>} @{thm Suc_less_SucD}\index{Suc-less-SucD@Suc$\_$less$\_$SucD (fact name)}\\
@{text\<open>Suc_le_lessD:\<close>} @{thm Suc_le_lessD}\index{Suc-le-lessD@Suc$\_$le$\_$lessD (fact name)}

An elimination rule (see Section~\ref{case-elim-rules}) for \<open>Suc\<close> is

@{text\<open>less_SucE:\<close>}\\
  @{thm less_SucE}\index{less-SucE@less$\_$SucE (fact name)}

For the arithmetic functions described in Section~\ref{holtypes-nat-funcs} most properties are
specified by equations such as

@{text\<open>add_Suc_right:\<close>} @{thm add_Suc_right}\index{add-Suc-right@add$\_$Suc$\_$right (fact name)}\\
@{text\<open>mult_Suc_right:\<close>} @{thm mult_Suc_right}\index{mult-Suc-right@mult$\_$Suc$\_$right (fact name)}\\
@{text\<open>diff_Suc_1:\<close>} @{thm diff_Suc_1}\index{diff-Suc-1@diff$\_$Suc$\_$1 (fact name)}\\
@{text\<open>min_Suc_Suc:\<close>} @{thm min_Suc_Suc}\index{min-Suc-Suc@min$\_$Suc$\_$Suc (fact name)}\\
@{text\<open>max_Suc_Suc:\<close>} @{thm min_Suc_Suc}\index{max-Suc-Suc@max$\_$Suc$\_$Suc (fact name)}\\
@{text\<open>dvd_diff_nat:\<close>} @{thm dvd_diff_nat}\index{dvd-diff-nat@dvd$\_$diff$\_$nat (fact name)}

Many of these equations are members of the simpset, therefore many simple arithmetic properties can
be proved by the simplifier. More complex properties may need the methods \<open>linarith\<close> or \<open>arith\<close>,
or can be proved by induction or a combination thereof.
\<close>

section "Sets"
text_raw\<open>\label{holtypes-set}\<close>

text\<open>\<^bold>\<open>Theories:\<close> {\tt\sl Set, Boolean$\_$Algebras, \cbstart Relation, BNF$\_$Def\cbend, Finite$\_$Set}\<close>

text\<open>
You may think of the type constructor \<open>set\<close> as being specified equivalent to the parameterized
algebraic type
@{theory_text[display]
\<open>datatype 'a set = Collect (contains: 'a \<Rightarrow> bool)\<close>}\index{set (type)}\index{Collect (constant)}\index{contains (constant)}
Thus a set is simply a wrapper for a unary predicate of type \<open>'a \<Rightarrow> bool\<close> (see
Section~\ref{holbasic-pred-pred}).

The selector \<open>contains\<close> is not intended for general use and can only be specified in qualified
form as \<open>Predicate_Compile.contains\<close>.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-set-values}\<close>

text\<open>
Basically, values of type \<open>'a set\<close> are denoted by constructor application terms of the form
\<open>Collect (\<lambda>x. bterm)\<close> where \<open>(\<lambda>x. bterm)\<close> is a unary predicate (see
Section~\ref{holbasic-pred-pred}).

For such a term HOL provides the alternative ``set comprehension''\index{set comprehension}\index{syntax!set comprehension $\sim$} syntax (which is a special form
of binder syntax)
@{text[display]
\<open>{x. bterm}\<close>}

HOL also provides two standard abbreviations:
 \<^item> \<open>{}\<close>\index{/emp@\<open>{}\<close> (constant)} for the empty set, which is written \<open>{x. False}\<close> in comprehension syntax, and 
 \<^item> \<open>UNIV\<close>\index{UNIV (constant)} for the universal set \<open>{x. True}\<close>.

Both abbreviations are available for arbitrary types \<open>'a set\<close>. The universal set is the set of all
values of the type \<open>'a\<close>. Examples are \<open>UNIV :: bool set\<close> which is the set \<open>{True, False}\<close> and
\<open>UNIV :: nat set\<close> which is the set of all natural numbers.

The lattice constants \<open>top\<close> and \<open>bot\<close> (see Section~\ref{holbasic-equal-lattice}) are available for
sets and denote the universal set \<open>UNIV\<close> and the empty set \<open>{}\<close>, respectively.

For a set comprehension of the form
@{text[display]
\<open>{x. \<exists> x\<^sub>1 \<dots> x\<^sub>n. x = term \<and> bterm}\<close>}
HOL provides the alternative syntax
@{text[display]
\<open>{term | x\<^sub>1 \<dots> x\<^sub>n. bterm}\<close>}\index{/bar@\<open>|\<close> (inner keyword)}
Note that the bindings of the variables \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> follow the \<open>|\<close> although the scope of the
bindings includes the \<open>term\<close> before the \<open>|\<close>.

An example for this syntax is the set
@{text[display]
\<open>{2*x | x::nat. x < 5}\<close>}
which contains the numbers \<open>0, 2, 4, 6, 8\<close>. Note that types may be specified in the bindings in the
same way as for the \<open>\<exists>\<close> quantifier.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-set-destrs}\<close>

text\<open>
For use instead of the selector
@{text[display]
\<open>Predicate_Compile.contains :: 'a set \<Rightarrow> 'a \<Rightarrow> bool\<close>}
HOL provides the function with reversed arguments
@{text[display]
\<open>Set.member :: 'a \<Rightarrow> 'a set \<Rightarrow> bool\<close>}\index{member (constant)}\index{/member@\<open>\<in>\<close> (operator)}
with alternate operator name \<open>(\<in>)\<close>. It combines unwrapping and applying the predicate and
corresponds to the usual member test predicate for sets.

Since there is only one constructor, discriminators and case terms are not available for sets.
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-set-funcs}\<close>

text\<open>
In addition to the basic function \<open>Set.member\<close> and its negation \<open>Set.not_member\<close>\index{not-member@not$\_$member (constant)}\index{/not-member@\<open>\<notin>\<close> (operator)} with operator name
\<open>(\<notin>)\<close> HOL provides the other usual functions on sets: the relations \<open>subset\<close>, \<open>subset_eq\<close>,
\<open>supset\<close>, \<open>supset_eq\<close> with operator names \<open>(\<subset>)\<close>, \<open>(\<subseteq>)\<close>, \<open>(\<supset>)\<close>, \<open>(\<supseteq>)\<close>
\index{subset (constant)}\index{subset-eq@subset$\_$eq (constant)}\index{supset (constant)}\index{supset-eq@supset$\_$eq (constant)}
\index{/subset@\<open>\<subset>\<close> (operator)}\index{/subset-eq@\<open>\<subseteq>\<close> (operator)}\index{/supset@\<open>\<supset>\<close> (operator)}\index{/supset-eq@\<open>\<supseteq>\<close> (operator)}
and the operations \<open>inter\<close>,
\<open>union\<close>, \<open>minus\<close> with operator names \<open>(\<inter>)\<close>, \<open>(\<union>)\<close>, \<open>(-)\<close>.
\index{inter (constant)}\index{union (constant)}\index{minus (constant)}
\index{/inter@\<open>\<inter>\<close> (operator)}\index{/union@\<open>\<union>\<close> (operator)}\index{/minus@\<open>-\<close> (operator)}
The function \<open>minus\<close> is set difference,
there is also the unary set complement (relative to the universal set \<open>UNIV\<close>,
see Section~\ref{holtypes-set-values}) \<open>uminus\<close>\index{uminus (constant)} which also has the operator name \<open>(-)\<close> for prefix
application. The functions \<open>minus\<close> and \<open>uminus\<close> are overloaded for other types as well, therefore
Isabelle will not automatically derive that their arguments are sets.

Intersection and union of a family of sets is supported by the functions
@{text[display]
\<open>Inter :: 'a set set \<Rightarrow> 'a set
Union :: 'a set set \<Rightarrow> 'a set\<close>}\index{Inter (constant)}\index{Union (constant)}
\index{/Inter@\<open>\<Inter>\<close> (operator)}\index{/Union@\<open>\<Union>\<close> (operator)}
with operator names \<open>(\<Inter>)\<close> and \<open>(\<Union>)\<close> for prefix notation.

HOL also provides the function
@{text[display]
\<open>insert :: 'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<equiv> \<lambda>a B. {x. x = a \<or> x \<in> B}\<close>}\index{insert (constant)}
which inserts a value into a set. HOL uses it to introduce the set enumeration syntax\index{set enumeration}\index{syntax!set enumeration $\sim$}
@{text[display]
\<open>{x\<^sub>1, \<dots>, x\<^sub>n}\<close>}
as abbreviation for \<open>insert x\<^sub>1 (\<dots> (insert x\<^sub>n {}) \<dots>)\<close>.

Moreover HOL provides the functions
@{text[display]
\<open>Pow :: 'a set \<Rightarrow> 'a set set \<equiv> \<lambda>A. {B. B\<subseteq>A}\<close>}\index{Pow (constant)}\cbstart
@{text[display]
\<open>Powp :: ('a\<Rightarrow>bool) \<Rightarrow> 'a set \<Rightarrow> bool \<equiv> \<lambda>P B. \<forall>x \<in> B. P x)\<close>}\index{Powp (constant)}\cbend
\cbdelete
@{text[display]
\<open>is_singleton :: 'a set \<Rightarrow> bool \<equiv> \<lambda>A. (\<exists>x. A = {x})
the_elem :: 'a set \<Rightarrow> 'a \<equiv> \<lambda>A. (THE x. A = {x})
pairwise :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool \<equiv>
  \<lambda>f A. (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> f x y)
disjnt :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<equiv> \<lambda>A B. A \<inter> B = {}\<close>}
\index{is-singleton@is$\_$singleton (constant)}\index{the-elem@the$\_$elem (constant)}
\index{pairwise (constant)}\index{disjnt (constant)}
\<open>Pow\<close> is the powerset operator, \cbstart \<open>Powp\<close> is the same for a predicate instead of a set\cbend.
As usual, the result of \<open>the_elem A\<close> is underspecified
(see Section~\ref{holbasic-descr-definite}) if \<open>A\<close> is not known to be a singleton set. The relation
application \<open>pairwise f A\<close> is satisfied if \<open>f\<close> is satisfied for all pairs of different elements of
\<open>A\<close>. The relation \<open>disjnt\<close> tests two sets for being disjoint.

As a convention, variables for sets are usually denoted by uppercase letters.
\<close>

subsubsection "Functions for Orderings and Lattices"

text\<open>
The ordering relations (see Section~\ref{holbasic-equal-order}) are defined for sets so that \<open>(<)\<close>
is equivalent to the subset relation \<open>(\<subset>)\<close> and analogously for \<open>(\<le>), (>), (\<ge>)\<close>. The lattice
operations \<open>(\<sqinter>)\<close>, \<open>(\<squnion>)\<close>, \<open>(\<Sqinter>)\<close>, and \<open>(\<Squnion>)\<close> (see Section~\ref{holbasic-equal-lattice}) are
overloaded to be equivalent to \<open>(\<inter>)\<close>, \<open>(\<union>)\<close>, \<open>(\<Inter>)\<close>, and \<open>(\<Union>)\<close>.

Since \<open>(\<subset>)\<close> is not a total ordering the functions \<open>min\<close> and \<open>max\<close> are \<^emph>\<open>not\<close> equivalent to \<open>(\<inter>)\<close>
and \<open>(\<union>)\<close> and the functions \<open>Min\<close> and \<open>Max\<close> are not available for sets of sets.
\<close>

subsubsection "Functions for Binder Syntax"

text\<open>
HOL provides many functions which support binder syntax where a single bound variable is restricted
(``bounded'') by a member or subset relation to some set.

HOL provides functions similar to \<open>All\<close> and \<open>Ex\<close> (see Section~\ref{holtypes-bool-funcs}) to support
the syntax of bounded quantifiers
@{text[display]
\<open>\<forall>x\<in>sterm. bterm \<equiv> \<forall>x. x \<in> sterm \<longrightarrow> bterm
\<exists>x\<in>sterm. bterm \<equiv> \<exists>x. x \<in> sterm \<and> bterm
\<exists>!x\<in>sterm. bterm \<equiv> \<exists>!x. x \<in> sterm \<and> bterm
\<forall>x\<subset>sterm. bterm \<equiv> \<forall>x. x \<subset> sterm \<longrightarrow> bterm
\<exists>x\<subset>sterm. bterm \<equiv> \<exists>x. x \<subset> sterm \<and> bterm
\<forall>x\<subseteq>sterm. bterm \<equiv> \<forall>x. x \<subseteq> sterm \<longrightarrow> bterm
\<exists>x\<subseteq>sterm. bterm \<equiv> \<exists>x. x \<subseteq> sterm \<and> bterm
\<exists>!x\<subseteq>sterm. bterm \<equiv> \<exists>!x. x \<subseteq> sterm \<and> bterm
\<close>}
and the bounded \cbstart descriptor (see Section~\ref{holbasic-descr-least})
@{text[display]
\<open>LEAST x\<in>sterm. bterm \<equiv> LEAST x. x \<in> sterm \<and> bterm\<close>}\index{LEAST (binder)}
Note that there is no such form for \<open>GREATEST\<close>. Other than for the plain quantifier only one bounded
variable may be specified for this form.\cbend If
there are more, the quantifiers must be nested as in \<open>\<forall>x\<in>sterm\<^sub>1. \<forall>y\<in>sterm\<^sub>2. bterm\<close>.

As set comprehension syntax for the special case of a predicate which includes a member test HOL
provides the syntax
@{text[display]
\<open>{x\<in>sterm. bterm}\<close>}
for a term of the form \<open>{x. x\<in>sterm \<and> bterm}\<close>.

For the operations \cbstart \<open>(\<Inter>), (\<Union>)\<close> \cbend HOL provides the alternative syntax of the form
@{text[display]
\<open>\<Inter>x\<in>term\<^sub>1. term\<^sub>2\<close>}
where both terms must have a \<open>set\<close> type and \<open>x\<close> may occur free in \<open>term\<^sub>2\<close>. This form is equivalent
to \<open>\<Inter>{term\<^sub>2 | x. x\<in>term\<^sub>1}\<close> which is the intersection over all sets returned by \<open>term\<^sub>2\<close> when \<open>x\<close>
adopts all values in the set \<open>term\<^sub>1\<close>.\cbdelete

For both operators HOL also provides the abbreviated syntax of the form
@{text[display]
\<open>\<Inter>x. term\<^sub>2\<close>}
for \<open>\<Inter>x\<in>UNIV. term\<^sub>2\<close> and the further abbreviation
@{text[display]
\<open>\<Inter>x\<^sub>1 \<dots> x\<^sub>n. term\<^sub>2\<close>}
for \<open>\<Inter>x\<^sub>1. \<dots> \<Inter>x\<^sub>n. term\<^sub>2\<close> (which is not available for the form with \<open>\<in>\<close>).

Note that \<open>MIN x::nat. x < 5\<close> is \<^emph>\<open>not\<close> the minimum of the numbers which are less than \<open>5\<close>, instead
it is the minimum of the boolean values which occur as the result of \<open>x < 5\<close> if \<open>x\<close> adopts all
possible values of type \<open>nat\<close>, i.e. it is equal to the value \<open>False\<close>. The minimum of the numbers
which are less than \<open>5\<close> is denoted by \<open>LEAST x::nat. x < 5\<close> which is equal to the value \<open>0\<close>.
\<close>

text_raw\<open>\cbstart\<close>
subsubsection "BNF Functions"

text\<open>
As described in Section~\ref{holbasic-bnf-natural} the type constructor \<open>set\<close> is a natural functor,
although not bounded. The corresponding mapper is provided as the function
@{text[display]
\<open>image :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<equiv> \<lambda>f A. {y. \<exists>x\<in>A. y = f x}\<close>}
\index{image (constant)}
with operator name \<open>(`)\<close>\index{/image@\<open>`\<close> (operator)}.
As set-function the identity \<open>id\<close> is used.

The predicator (see Section~\ref{holbasic-bnf-predrel}) is the function \<open>Powp\<close> (see above),
the relator is defined as
@{text[display]
\<open>rel_set :: ('a\<Rightarrow>'b\<Rightarrow>bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool
  \<equiv> \<lambda>R A B. (\<forall>x\<in>A. \<exists>y\<in>B. R x y) \<and> (\<forall>y\<in>B. \<exists>x\<in>A. R x y)\<close>}\index{rel-set@rel$\_$set (constant)}
Two sets are related if every element in the first set is related with an element in the second set
and vice versa.

HOL also provides the function
@{text[display]
\<open>vimage :: ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set \<equiv> \<lambda>f A. {x. f x \<in> A}\<close>}
\index{vimage (constant)}
with operator name \<open>(-`)\<close>\index{/vimage@\<open>-`\<close> (operator)} for the reverse image of a function.
As described in Section~\ref{holbasic-functor-mapper} it is a contravariant mapper for \<open>set\<close>.
\<close>
text_raw\<open>\cbend\<close>

subsubsection "Functions for Finite Sets"

text\<open>
HOL defines the predicate \<open>finite\<close> by the inductive definition (see
Section~\ref{holbasic-inductive})
@{theory_text[display]
\<open>inductive finite :: "'a set \<Rightarrow> bool" where
  "finite {}"
| "finite A \<Longrightarrow> finite (insert a A)"\<close>}\index{finite (constant)}
So a set is finite if it can be constructed from the empty set by a finite sequence of inserting
single elements.

For iterating through the elements of a finite set HOL introduces the function
@{text[display]
\<open>Finite_Set.fold :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b\<close>}\index{fold (constant)}
where \<open>fold f z {x\<^sub>1, \<dots>, x\<^sub>n} = f x\<^sub>1 (\<dots> (f x\<^sub>n z)\<dots>)\<close> if the resulting value is independent of the
order of the \<open>x\<^sub>i\<close>, i.e., the function \<open>f\<close> must be ``left-commutative'' on the values in the set. If
it is not, its result is underspecified. If the set is not finite the result is always the starting
value \<open>z\<close>.

The function \<open>Finite_Set.fold\<close> is not intended for direct use, it is used by HOL to provide other
functions. The most basic is
@{text[display]
\<open>card :: 'a set \<Rightarrow> nat \<equiv> \<lambda>A. Finite_Set.fold (\<lambda>_ n. Suc n) 0 A\<close>}\index{card (constant)}
for the cardinality\index{cardinality} of sets. For finite sets it is the number of elements, for infinite sets, due
to the way \<open>fold\<close> is defined, it is always \<open>0\<close>. \cbstart Note the difference to the cardinalities described
in Section~\ref{holbasic-bnf-bounded}, which are represented by ordering relations and also
support infinite cardinalities.\cbend
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-set-rules}\<close>

subsubsection "Algebraic Type Rules"

text\<open>
Since HOL does not define the type \<open>'a set\<close> as an algebraic type it does not provide the standard
rules and rule sets. However, the relevant properties are available in slightly different form.

Injectivity of the constructor is not specified as a simplifier equation, instead there is the rule

@{text\<open>Collect_inj:\<close>} @{thm Collect_inj}\index{Collect-inj@Collect$\_$inj (fact name)}

Note that the other direction is always satisfied for arbitrary functions (see
Section~\ref{holtypes-func-rules}). It is provided in the form where the predicates are applied to
arguments:

@{text\<open>Collect_eqI:\<close>} @{thm Collect_eqI}\index{Collect-eqI@Collect$\_$eqI (fact name)}

where its name reflects that it has the form of an introduction rule (see
Section~\ref{methods-rule-intro}) for the equality relation \<open>(=)\<close> (see
Section~\ref{holbasic-equal-eq}) on type \<open>'a set\<close>.

Equivalent to a ``defining equation'' for the selector there is the rule
@{text[display]
\<open>mem_Collect_eq: Set.member ?a (Collect ?P) = ?P ?a\<close>}\index{mem-Collect-eq@mem$\_$Collect$\_$eq (fact name)}
which is
@{text[display]
\<open>(?a \<in> {x. ?P x}) = ?P ?a\<close>}
in alternative syntax. This rule is also provided in the form of two separate rules for both
dirctions:
@{text[display]
\<open>CollectI: ?P ?a \<Longrightarrow> ?a \<in> {x. ?P x}
CollectD: ?a \<in> {x. ?P x} \<Longrightarrow> ?P ?a\<close>}\index{CollectI (fact name)}\index{CollectD (fact name)}
having the form of an introduction and a destruction rule (see Section~\ref{methods-forward-dest}).

Due to the simple wrapper structure of type \<open>'a set\<close> no other algebraic type rules apply.
\<close>

subsubsection "Rules About Functions"

text\<open>
Using the rules described above and the definitions of the functions on sets described in
Section~\ref{holtypes-set-funcs} it is possible to convert every proposition about sets to an
equivalent proposition about predicates and boolean operations (see
Section~\ref{holtypes-bool-funcs}) and prove it in this form. Most automatic proof methods described
in Section~\ref{methods-auto-methods} use this conversion and can thus prove many goals which involve
sets and set operations, in particular the method \<^theory_text>\<open>blast\<close>.

Additionally HOL provides rules which directly work for functions on sets such as the introduction
rules (see Section~\ref{methods-rule-intro})

@{text\<open>subsetI:\<close>} @{thm subsetI}\index{subsetI (fact name)}\\
@{text\<open>IntI:\<close>} @{thm IntI}\index{IntI (fact name)}\\
@{text\<open>UnI1:\<close>} @{thm UnI1}\index{UnI (fact name)}\\
@{text\<open>PowI:\<close>} @{thm PowI}\index{PowI (fact name)}

the destruction (see Section~\ref{methods-forward-dest}) and elimination
(see Section~\ref{case-elim-rules}) rules

@{text\<open>subsetD:\<close>} @{thm subsetD}\index{subsetD (fact name)}\\
@{text\<open>IntD1:\<close>} @{thm IntD1}\index{IntD1 (fact name)}\\
@{text\<open>UnE:\<close>} @{thm UnE}\index{UnE (fact name)}\\
@{text\<open>PowD:\<close>} @{thm PowD}\index{PowD (fact name)}

and the simplifier equations (see Section~\ref{methods-simp-simplif})

@{text\<open>subset_eq:\<close>} @{thm subset_eq}\index{subset-eq@subset$\_$eq (fact name)}\\
@{text\<open>Int_def: ?A \<inter> ?B = {x. x \<in> ?A \<and> x \<in> ?B}\<close>}\index{Int-def@Int$\_$def (fact name)}\\
@{text\<open>Un_def: ?A \<union> ?B = {x. x \<in> ?A \<or> x \<in> ?B}\<close>}\index{Un-def@Un$\_$def (fact name)}\\
@{text\<open>Pow_def: Pow ?A = {B. B \<subseteq> ?A}\<close>}\index{Pow-def@Pow$\_$def (fact name)}

where, despite their names, \<open>(\<inter>)\<close> and \<open>(\<union>)\<close> are not really defined in this way.

There are also many rules about \<open>finite\<close> and \<open>card\<close> such as

@{text\<open>finite_subset:\<close>} @{thm finite_subset}\index{finite-subset@finite$\_$subset (fact name)}\\
@{text\<open>finite_Un:\<close>} @{thm finite_Un}\index{finite-Un@finite$\_$Un (fact name)}\\
@{text\<open>finite_Int:\<close>} @{thm finite_Int}\index{finite-Int@finite$\_$Int (fact name)}\\
@{text\<open>card_mono:\<close>} @{thm card_mono}\index{card-@card$\_$mono (fact name)}\\
@{text\<open>card_Diff_subset_Int:\<close>}\\\hspace*{1em}@{thm card_Diff_subset_Int}\index{card-Diff-subset-Int@card$\_$Diff$\_$subset$\_$Int (fact name)}\\
@{text\<open>card_Un_Int:\<close>}\vspace{-2ex}@{thm[display,indent=2] card_Un_Int}\index{card-Un-Int@card$\_$Un$\_$Int (fact name)}

Many rules about \<open>finite\<close> are known by the automatic proof methods (see
Section~\ref{methods-auto-methods}). Rules about \<open>card\<close> must often be specified explicitly.
\<close>

section "Optional Values"
text_raw\<open>\label{holtypes-option}\<close>

text\<open>\<^bold>\<open>Theories:\<close> {\tt\sl Option}\<close>

text\<open>
A function argument is optional\index{function!argument!optional $\sim$} if it can be omitted. In Isabelle, however, every function has a
fixed number of arguments, it is not possible to omit one or more of them. Instead, the idea is to
have a special value with the meaning of ``no value''. The presence of such a value is no more a
property of the function, it is a property of the function argument's \<^emph>\<open>type\<close>.

Normally, types do not include a ``no value'' value, it must be introduced separately and it must
be different from all existing values. For a type \<open>t\<close> this can be done by defining a new type which
has one more value. However, since the values of the new type are always different from those of \<open>t\<close>
(see Section~\ref{theory-terms-types}), the new type has to include the values of \<open>t\<close> in a
``wrapped'' form.

All this is done by the algebraic type
@{theory_text[display]
\<open>datatype 'a option =
  None
| Some (the: 'a)\<close>}\index{option (type)}\index{None (constant)}\index{Some (constant)}\index{the (constant)}
It is polymorphic with one type parameter \<open>'a\<close> (see Section~\ref{theory-terms-types}), for every
type \<open>t\<close> it provides the new type \<open>t option\<close>.

In this way the type \<open>nat option\<close> can be used to add a ``no value'' to the natural numbers.

The type constructor \<open>option\<close> can also be used to emulate partial functions (which do not exist in
Isabelle) by functions with a result type \<open>t option\<close>.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-option-values}\<close>

text\<open>
Type \<open>option\<close> provides two constructors. The parameterless constructor \<open>None\<close> denotes the ``no
value'' value. The unary constructor \<open>Some\<close> provides the value \<open>Some v\<close> for every value \<open>v\<close> of the
type parameter \<open>'a\<close>. In this way the type \<open>t option\<close> includes all values \<open>v\<close> of \<open>t\<close> wrapped as
\<open>Some v\<close>. Since constructors of algebraic types are injective (see Section~\ref{holtdefs-data-constr})
different values stay different when wrapped. Since different constructors denote different values
the value \<open>None\<close> is different from all wrapped values. Note also, that for different types \<open>t1\<close> and
\<open>t2\<close> the \<open>None\<close> values in \<open>t1 option\<close> and \<open>t2 option\<close> are different, because they belong to
different types.

The type \<open>nat option\<close> provides the value \<open>None\<close> and wrapped natural numbers of the form \<open>Some 5\<close>.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-option-destrs}\<close>

text\<open>
The selector \<open>the\<close> is used to ``unwrap'' the wrapped values: \<open>the (Some v) = v\<close>. As described in
Section~\ref{holtdefs-data-destr} the selector can also be applied to \<open>None\<close>, but the result is
underspecified. The term \<open>the None\<close> denotes a unique value of the parameter type \<open>'a\<close>, but no
information is available about that value.

Although not introduced by the type definition, the function \<open>Option.is_none\<close>\index{is-none@is$\_$none (constant)} plays the role of
a discriminator and tests values for being \<open>None\<close>. Alternatively the equality terms \<open>x = None\<close> and
\<open>x \<noteq> None\<close> can be used.

A \<open>case\<close> term for type \<open>t option\<close> has the form
@{text[display]
\<open>case term of None \<Rightarrow> term\<^sub>1 | Some v \<Rightarrow> term\<^sub>2\<close>}
where \<open>term\<close> is a term of type \<open>t option\<close> and \<open>v\<close> is a variable of type \<open>t\<close> which may occur in
\<open>term\<^sub>2\<close>. Such \<open>case\<close> terms can be used to process a \<open>term\<close> for an optional value. It is tested
whether a (wrapped) value is present, if not \<open>term\<^sub>1\<close> specifies a default, otherwise \<open>term\<^sub>2\<close>
specifies a use of the unwrapped value \<open>v\<close>.

The same effect can be achieved by the term
@{text[display]
\<open>if term = None then term\<^sub>1 else term\<^sub>2'\<close>}
where \<open>term\<^sub>2'\<close> uses \<open>(the term)\<close> instead of \<open>v\<close>. However, proofs may differ depending on which of
both forms is used.
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-option-funcs}\<close>

text\<open>
The function
@{text[display]
\<open>Option.these :: 'a option set \<Rightarrow> 'a set \<equiv>
  \<lambda>A. image the {x\<in>A. x\<noteq>None}\<close>}\index{these (constant)}
extends the selector \<open>the\<close> to sets. It returns the set of unwrapped values from a set of optional
values, ignoring \<open>None\<close> if present in the set.

No orderings or lattice functions (see Section~\ref{holbasic-equal}) are specified for values of
type \<open>'a option\<close>.
\<close>

subsubsection "BNF Functions"
text\<open>
The type constructor \<open>option\<close> is a bounded natural functor as described in
Section~\ref{holbasic-bnf}. Values of type \<open>'a option\<close> can be viewed as containers of a single
value of type \<open>'a\<close>.

The corresponding BNF functions are generated as:
@{text[display]
\<open>set_option :: 'p option \<Rightarrow> 'p set \<equiv>
  \<lambda>x. case x of None \<Rightarrow> {} | Some x' \<Rightarrow> {x'}
map_option :: ('p \<Rightarrow> 'q) \<Rightarrow> 'p option \<Rightarrow> 'q option \<equiv>
  \<lambda>f x. case x of None \<Rightarrow> None | Some x' \<Rightarrow> Some (f x')
pred_option :: ('p \<Rightarrow> bool) \<Rightarrow> 'p option \<Rightarrow> bool \<equiv>
  \<lambda>p x. case x of None \<Rightarrow> True | Some x' \<Rightarrow> p x'
rel_option :: ('p \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow> 'p option \<Rightarrow> 'q option \<Rightarrow> bool \<equiv>
  \<lambda>r x y. case x of None \<Rightarrow> y = None | Some x' \<Rightarrow> 
            (case y of None \<Rightarrow> False | Some y' \<Rightarrow> r x' y')\<close>}

Additionally there is the function
@{text[display]
\<open>combine_options ::
  ('p \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> 'p option \<Rightarrow> 'p option \<Rightarrow> 'p option \<equiv>
  \<lambda>f x y. case x of None \<Rightarrow> y | Some x' \<Rightarrow> 
            (case y of None \<Rightarrow> x | Some y' \<Rightarrow> Some (f x' y'))\<close>}\index{combine-options@combine$\_$options (constant)}
which extends \<open>map_option\<close> to binary functions. It applies its first argument (a binary function)
to two wrapped values without unwrapping them. If one argument is \<open>None\<close> the result is the other
argument.
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-option-rules}\<close>

subsubsection "Algebraic Type Rules"

text\<open>
The simplifier rules for the constructors of type \<open>'a option\<close> are the rule sets \<open>option.inject\<close>, 
\<open>option.distinct\<close> and \<open>option.case\<close> (see Section~\ref{holtdefs-data-rules}):
@{text[display]
\<open>(Some ?x = Some ?y) = (?x = ?y)
None \<noteq> Some ?x
Some ?x \<noteq> None
(case None of None \<Rightarrow> ?t\<^sub>1 | Some x \<Rightarrow> ?t\<^sub>2 x) = ?t\<^sub>1
(case Some ?x of None \<Rightarrow> ?t\<^sub>1 | Some x \<Rightarrow> ?t\<^sub>2 x) = ?t\<^sub>2 ?x\<close>}

The case, split, and induction rules are
@{text[display]
\<open>option.exhaust:
  \<lbrakk>?y = None \<Longrightarrow> ?P; \<And>x. ?y = Some x \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P
option.split:
  ?P (case ?t of None \<Rightarrow> ?t\<^sub>1 | Some x \<Rightarrow> ?t\<^sub>2 x) =
  ((?t = None \<longrightarrow> ?P ?t\<^sub>1) \<and> (\<forall>x. ?t = Some x \<longrightarrow> ?P (?t\<^sub>2 x)))
option.induct:
  \<lbrakk>?P None; \<And>x. ?P (Some x)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}
For the case and induction rule the cases are named \<open>None\<close> and \<open>Some\<close>.
\<close>

subsubsection "Rules About Functions"

text\<open>
For the functions described in Section~\ref{holtypes-option-funcs} most properties are
specified by equations such as

@{text\<open>elem_set:\<close>} @{thm elem_set}\index{elem-set@elem$\_$set (fact name)}\\
@{text\<open>map_option_case:\<close>}\\\hspace*{1em}@{thm map_option_case}\index{map-option-case@map$\_$option$\_$case (fact name)}\\
@{text\<open>Option.is_none_def:\<close>} @{thm Option.is_none_def}\index{is-none-def@is$\_$none$\_$def (fact name)}\\
@{text\<open>rel_option_unfold:\<close>}\vspace{-2ex}@{thm[display,indent=2,margin=70] rel_option_unfold}\index{rel-option-unfold@rel$\_$option$\_$unfold (fact name)}

Many of these equations are members of the simpset, therefore many properties about optional values
can be proved by the simplifier. Remember to configure it with \<open>split: option.split\<close> if \<open>case\<close> terms
occur for type \<open>'a option\<close>.
\<close>

section "Tuples"
text_raw\<open>\label{holtypes-tup}\<close>

text\<open>\<^bold>\<open>Theories:\<close> {\tt\sl Product$\_$Type, Basic$\_$BNFs}\<close>

text \<open>
Tuples\index{tuple} are represented by HOL as nested pairs\index{pair}. The type of pairs is specified equivalent to an
algebraic type (see Section~\ref{holtdefs-data}) of the form
@{theory_text[display]
\<open>datatype ('a, 'b) prod = Pair (fst: 'a) (snd: 'b)\<close>}\index{prod (type)}\index{Pair (constant)}\index{fst (constant)}\index{snd (constant)}
As described in Section~\ref{holtdefs-data}, this type is equivalent to the type of pairs of values
of the type parameters \<open>'a\<close> and \<open>'b\<close>. It is also called the ``product type''\index{product type}\index{type!product $\sim$} of the types \<open>'a\<close> and
\<open>'b\<close>.

HOL supports an alternative syntax for instances of type \<open>('a, 'b) prod\<close>. The type instance
\<open>(t\<^sub>1, t\<^sub>2) prod\<close> where \<open>t\<^sub>1\<close> and \<open>t\<^sub>2\<close> are arbitrary types may be denoted by the type expression
\<open>t\<^sub>1 \<times> t\<^sub>2\<close>\index{/x@\<open>\<times>\<close> (operator)} or \<open>t\<^sub>1 * t\<^sub>2\<close>\index{/times@\<open>*\<close> (operator)} (see Section~\ref{holbasic-tuples}).

A tuple with more than two components is represented in HOL by a pair where the second
component is again a pair or tuple. Hence the type of 4-tuples with component types \<open>t\<^sub>1, t\<^sub>2, t\<^sub>3, t\<^sub>4\<close>
can be denoted by the type expression \<open>t\<^sub>1 \<times> (t\<^sub>2 \<times> (t\<^sub>3 \<times> t\<^sub>4))\<close>. Since \<open>\<times>\<close> is right associative the
parentheses may be omitted as in the equivalent type expression \<open>t\<^sub>1 \<times> t\<^sub>2 \<times> t\<^sub>3 \<times> t\<^sub>4\<close>.

As an example the type \<open>(bool \<times> nat \<times> nat) option\<close> is the type of optional triples of one boolean
value and two natural numbers.

Note that the type \<open>unit\<close>\index{unit (type)} (see Section~\ref{holtypes-unit}) can be used to represent a ``0-tuple''\index{empty tuple}\index{tuple!empty $\sim$},
as the alternative form \<open>()\<close>\index{() (constant)} of its single value suggests.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-tup-values}\<close>

text\<open>
All values of type \<open>('a, 'b) prod\<close> are denoted using the single constructor \<open>Pair\<close>. HOL supports an
alternative syntax\index{syntax!alternative $\sim$!for Pair} for these constructor application terms: the term \<open>Pair term\<^sub>1 term\<^sub>2\<close> may also be
specified in the form \<open>(term\<^sub>1, term\<^sub>2)\<close> (see Section~\ref{holbasic-tuples}).

Iterating this syntax a 4-tuple value may be specified as \<open>(term\<^sub>1, (term\<^sub>2, (term\<^sub>3, term\<^sub>3)))\<close>. Since
the \<open>(\<dots>,\<dots>)\<close> is also right associative the inner parentheses may be omitted resulting in the
equivalent term \<open>(term\<^sub>1, term\<^sub>2, term\<^sub>3, term\<^sub>3)\<close>.

Thus an example value of type \<open>(bool \<times> nat \<times> nat) option\<close> can be specified by the term
\<open>Some (True, 5, 42)\<close>.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-tup-destrs}\<close>

text\<open>
The selectors \<open>fst\<close> and \<open>snd\<close> can be used to access the first or second component in a pair,
respectively.

Note that in a tuple of more than two components \<open>fst\<close> still selects the first component, whereas
\<open>snd\<close> selects the nested tuple with all other components. To access the third component in a 4-tuple
\<open>x\<close> the selectors must be combined accordingly: \<open>fst (snd (snd x))\<close>. The third component in a triple
\<open>x\<close> must be accessed by \<open>snd (snd (snd x))\<close>. Therefore there is no general way of accessing the
\<open>i\<close>th component in an arbitrary tuple. An ``easier'' way for it is to use a \<open>case\<close> term.

A \<open>case\<close> term for type \<open>t\<^sub>1 \<times> t\<^sub>2\<close> (which is equivalent to \<open>(t\<^sub>1, t\<^sub>2) prod\<close>) has the form
@{text[display]
\<open>case term of Pair x\<^sub>1 x\<^sub>2 \<Rightarrow> term\<^sub>1\<close>}
where \<open>term\<close> is a term of type \<open>t\<^sub>1 \<times> t\<^sub>2\<close> and \<open>x\<^sub>1, x\<^sub>2\<close> are variables of type \<open>t\<^sub>1\<close> and \<open>t\<^sub>2\<close>,
respectively, which may occur in \<open>term\<^sub>1\<close>. Using the alternative syntax for pair values the \<open>case\<close>
term may also be specified as
@{text[display]
\<open>case term of (x\<^sub>1, x\<^sub>2) \<Rightarrow> term\<^sub>1\<close>}
Such \<open>case\<close> terms can be used to ``take apart'' a \<open>term\<close> for a pair where the components are not
explicitly specified, such as in the application of a function which returns a pair. The components
are bound to the variables \<open>x\<^sub>1, x\<^sub>2\<close> and can be used separately in \<open>term\<^sub>1\<close>. An example is
the case term
@{text[display]
\<open>case coordinate of (x, y) \<Rightarrow> x + y\<close>}
where \<open>coordinate\<close> is a single variable of type \<open>nat \<times> nat\<close>.

As usual, this also works for tuples with more than two components. The general form of a \<open>case\<close>
term for an n-tuple is
@{text[display]
\<open>case term of (x\<^sub>1, \<dots>, x\<^sub>n) \<Rightarrow> term\<^sub>1\<close>}
where the variables \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> may occur in \<open>term\<^sub>1\<close>.

HOL provides an alternative form for such \<open>case\<close> terms for tuples:
@{text[display]
\<open>let (x\<^sub>1, \<dots>, x\<^sub>n) = term in term\<^sub>1\<close>}\index{let (inner keyword)}\index{in (inner keyword)}
Although this form looks like a generalized \<open>let\<close> term (see Section~\ref{holbasic-let}) this
does not imply that \<open>let\<close> terms\index{let term}\index{term!let $\sim$} support arbitrary patterns on the left side of the \<open>=\<close> sign, like
the \<open>let\<close> statement (see Section~\ref{proof-let-match}). As ``patterns'' only nested tuples of
variables may be used, such \<open>let\<close> terms are always equivalent to a \<open>case\<close> term for a tuple.

The same variable tuple patterns can also be used in other kinds of terms where variables are bound
such as in lambda terms\index{lambda term}\index{term!lambda $\sim$} (e.g., \<open>\<lambda>(a,b) c. a+b+c\<close>), 
\cbstart in description operators\index{description operator} (e.g., \<open>SOME (a,b). a+b=5\<close>),
(but not in logic quantifiers) \cbend and in set comprehensions\index{set comprehension} (e.g., \<open>{(a,b). a=b*b}\<close>). Note that the last example is equivalent to
\<open>{(a,b) | a b. a=b*b}\<close>, only in this form an arbitrary term may be used instead of \<open>(a,b)\<close>.
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-tup-funcs}\<close>

text\<open>
As described in Section~\ref{holtdefs-data-destr} a \<open>case\<close> term for a pair is only an alternative
syntax for the function application term \<open>case_prod (\<lambda> x\<^sub>1 x\<^sub>2. term\<^sub>1) term\<close>. The polymorphic function
\<open>case_prod\<close> is provided as
@{text[display]
\<open>case_prod :: ('a \<Rightarrow> 'b \<Rightarrow> 't) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 't \<equiv>
  \<lambda>f (x,y). f x y\<close>}\index{case-prod@case$\_$prod (constant)}
where \<open>'t\<close> is the type of \<open>term\<^sub>1\<close> and thus of the whole \<open>case\<close> term.

This function is of interest on its own. It converts a binary function \<open>f\<close> specified in the style
described in Section~\ref{theory-terms-multargs} to a function which takes the two arguments in the
form of a single pair. This conversion is generally called ``uncurrying''\index{uncurrying} (see
Section~\ref{holbasic-tuples-funarg}). Tuple patterns in variable bindings, as described in
Section~\ref{holtypes-tup-destrs}, are implemented in this way: The term \<open>\<lambda>(a,b). term\<close> is just
an alternative syntax for \<open>case_prod (\<lambda>a b. term)\<close>.

HOL provides the reverse conversion as the function
@{text[display]
\<open>curry :: ('a \<times> 'b \<Rightarrow> 't) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 't \<equiv>
  \<lambda>f x y. f (x,y)\<close>}\index{curry (constant)}

Additionally there are the functions
@{text[display]
\<open>apfst :: ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'b \<equiv> \<lambda>f (x,y). (f x,y)
apsnd :: ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'c \<equiv> \<lambda>f (x,y). (x,f y)\<close>}\index{apfst (constant)}\index{apsnd (constant)}
which apply their first argument to the first or second component of the second argument,
respectively, and the function
@{text[display]
\<open>prod.swap :: 'a \<times> 'b \<Rightarrow> 'b \<times> 'a \<equiv> \<lambda>(x,y). (y,x)\<close>}\index{swap (constant)}
which interchanges the components of its argument.

The function
@{text[display]
\<open>Product_Type.Times :: 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set \<equiv>
  \<lambda>A B. {(x, y). x\<in>A \<and> y\<in>B}\<close>}\index{Times (constant)}\index{/x@\<open>\<times>\<close> (operator)}
with operator name \<open>(\<times>)\<close> constructs the cartesian product\index{cartesian product} of two sets.

No orderings or lattice functions (see Section~\ref{holbasic-equal}) are specified for values of
type \<open>('a, 'b) prod\<close>.\<close>

subsubsection "BNF Functions"

text\<open>
The type constructor \<open>prod\<close> is a bounded natural functor as described in
Section~\ref{holbasic-bnf}. Values of type \<open>('a, 'b) prod\<close> can be viewed as containers of a
single value of type \<open>'a\<close> and a single value of type  \<open>'b\<close>.

The corresponding BNF functions are generated as:
@{text[display]
\<open>map_prod ::
  ('a\<^sub>1 \<Rightarrow> 'a\<^sub>2) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> ('a\<^sub>1 \<times> 'b\<^sub>1) \<Rightarrow> ('a\<^sub>2 \<times> 'b\<^sub>2) \<equiv>
  \<lambda>f g (x,y). (f x, g y)\<close>}\index{map-prod@map$\_$prod (constant)}\cbstart
@{text[display]
\<open>Basic_BNFs.fsts :: ('a \<times> 'b) \<Rightarrow> 'a set \<equiv> \<lambda>(x,y).{x}
Basic_BNFs.snds :: ('a \<times> 'b) \<Rightarrow> 'b set \<equiv> \<lambda>(x,y).{y}\<close>}\index{fsts (constant)}\index{snds (constant)}\cbend
@{text[display]
\<open>pred_prod ::
  ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool \<equiv>
  \<lambda>f g (x,y). f x \<and> g y
rel_prod ::
  ('a\<^sub>1 \<Rightarrow> 'a\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2 \<Rightarrow> bool) 
    \<Rightarrow> ('a\<^sub>1 \<times> 'b\<^sub>1) \<Rightarrow> ('a\<^sub>2 \<times> 'b\<^sub>2) \<Rightarrow> bool \<equiv>
  \<lambda>f g (x\<^sub>1,y\<^sub>1) (x\<^sub>2,y\<^sub>2). f x\<^sub>1 x\<^sub>2 \<and> g y\<^sub>1 y\<^sub>2\<close>}
\index{pred-prod@pred$\_$prod (constant)}\index{rel-prod@rel$\_$prod (constant)}
\cbdelete
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-tup-rules}\<close>

subsubsection "Algebraic Type Rules"

text\<open>
Since there is only one constructor there are no distinctness rules. The simplifier rules for the
constructor of type \<open>('a, 'b) prod\<close> are the rule sets \<open>prod.inject\<close>, \<open>prod.sel\<close> and \<open>prod.case\<close> (see
Section~\ref{holtdefs-data-rules}):
@{text[display]
\<open>((?x1, ?x2) = (?y1, ?y2)) = (?x1 = ?y1 \<and> ?x2 = ?y2)
fst (?x1, ?x2) = ?x1
snd (?x1, ?x2) = ?x2
(case (?x1, ?x2) of (x, y) \<Rightarrow> ?f x y) = ?f ?x1 ?x2\<close>}

The case, split, and induction rules are
@{text[display]
\<open>prod.exhaust:
  (\<And>x1 x2. ?y = (x1, x2) \<Longrightarrow> ?P) \<Longrightarrow> ?P
prod.split:
  ?P (case ?t of (x, y) \<Rightarrow> ?f x y) = 
  (\<forall>x1 x2. ?t = (x1, x2) \<longrightarrow> ?P (?f x1 x2))
prod.induct:
  (\<And>x1 x2. ?P (x1, x2)) \<Longrightarrow> ?P ?a\<close>}
For the case and induction rule the single case is named \<open>Pair\<close>.

The case and induction rules are also provided for tuples of size 3 to 7 in the form
@{text[display]
\<open>prod_cases3:
  (\<And>x1 x2 x3. ?y = (x1, x2, x3) \<Longrightarrow> ?P) \<Longrightarrow> ?P
prod_induct3:
  (\<And>x1 x2 x3. ?P (x1, x2, x3)) \<Longrightarrow> ?P ?a\<close>}\index{prod-cases3@prod$\_$cases3 (fact name)}\index{prod-induct3@prod$\_$induct3 (fact name)}
In all of them the single case is named \<open>fields\<close>\index{fields (case name)}.

Since all these case and induction rules are associated with the corresponding tuple types a proof
of the form
@{theory_text[display]
\<open>proof (cases x)
case (fields x1 x2 x3)
\<dots>
show ?thesis \<proof>
qed\<close>}
replaces the variable \<open>x\<close> of type \<open>t\<^sub>1 \<times> t\<^sub>2 \<times> t\<^sub>3\<close> by tuple terms \<open>(x1, x2, x3)\<close> and allows to reason
about the components of \<open>x\<close>. 
\<close>

subsubsection "Rules About Functions"

text\<open>
As described in Section~\ref{holtypes-tup-destrs} components of a tuple are easiest accessed by
using a tuple pattern which is equivalent to applying the function \<open>case_prod\<close> (see
Section~\ref{holtypes-tup-funcs}). In proofs it is often necessary to convert a proposition
involving \<open>case_prod\<close> to a proposition for the components. The simplifier rule
@{text[display]
\<open>split_def: case_prod = (\<lambda>c p. c (fst p) (snd p))\<close>}\index{split-def@split$\_$def (fact name)}
allows to directly replace occurrences of \<open>case_prod\<close> by rewriting. It is not part of the simpset
(see Section~\ref{methods-simp-simp}), its use by the simplifier must be explicitly configured.

If tuples are not specified with the help of tuple patterns but by single variables of a tuple
type the case, split, and induction rules described above can be used to convert such variables to
explicit tuples where variables denote the components. Alternatively HOL provides the rule
@{text[display]
\<open>split_paired_all: (\<And>x. ?P x) \<equiv> (\<And>a b. ?P (a, b))\<close>}\index{split-paired-all@split$\_$paired$\_$all (fact name)}
Rewriting by this rule replaces all bound variables of a type \<open>t\<^sub>1 \<times> t\<^sub>2\<close> by two variables for the
components. Since tuples are nested pairs an iterated rewriting does the same for arbitrary tuples.
Again, this rule is not part of the simpset and it should be added with care, an iterated rewriting
is best done by the method \<^theory_text>\<open>(simp only: split_paired_all)\<close> without combining it with other
simplifier rules.

Instead, the rules
@{text[display]
\<open>split_paired_All: (\<forall>x. ?P x) = (\<forall>a b. ?P (a, b))
split_paired_Ex: (\<exists>x. ?P x) = (\<exists>a b. ?P (a, b))\<close>}
\index{split-paired-All@split$\_$paired$\_$All (fact name)}\index{split-paired-Ex@split$\_$paired$\_$Ex (fact name)}
are in the simpset and are thus automatically applied by the simplifier to replace variables of
tuple type bound by logic quantifiers (see Section~\ref{holtypes-bool-funcs}). If that is not
intended these rules must be deactivated in the form \<^theory_text>\<open>(simp del: split_paired_Ex)\<close>.
\<close>

section "Functions"
text_raw\<open>\label{holtypes-func}\<close>

text\<open>\<^bold>\<open>Theories:\<close> {\tt\sl Fun, Orderings, Lattices, Complete$\_$Lattices, Basic$\_$BNFs, Nat}\<close>

text\<open>
The type \<open>('a, 'b) fun\<close>\index{fun (type)} with alternative syntax \<open>'a \<Rightarrow> 'b\<close>\index{=>@\<open>\<Rightarrow>\<close> (operator)} (see Section~\ref{theory-terms-functions})
is not specific for HOL, it is provided by Isabelle at the basis of the whole Isabelle type system.
It is polymorphic and denotes the type of functions with argument type \<open>'a\<close> and result type \<open>'b\<close>.

However, HOL complements this basic support for functions by many functions and rules for the
type \<open>('a, 'b) fun\<close>.

Note that functions introduced by type definitions such as constructors and destructors of
algebraic types (see Section~\ref{holtdefs-data}) or the morphisms of a subtype (see
Section~\ref{holtdefs-sub}) are normal functions of type \<open>('a, 'b) fun\<close> and all mechanisms
described here for functions apply to them as well.

The type \<open>('a, 'b) fun\<close> is not equivalent to an algebraic type. Since functions are always total,
the arguments of a constructor function would have to specify function values for all arguments
of type \<open>'a\<close> which may be infinitely many.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-func-values}\<close>

text\<open>
The values of type \<open>'a \<Rightarrow> 'b\<close> are denoted by lambda terms\index{lambda term}\index{term!lambda $\sim$} (see Section~\ref{theory-terms-lambda}).

HOL introduces the name \<open>id\<close>\index{id (constant)} for the polymorphic identity function\index{identity function}\index{function!identity $\sim$} \<open>\<lambda>x. x\<close>.
\<close>

subsection "Functions on Functions"
text_raw\<open>\label{holtypes-func-funcs}\<close>

text\<open>
The functions \<open>image\<close> \cbstart and \<open>vimage\<close> have already been described in Section~\ref{holtypes-set-funcs},
as mappers for \<open>set\<close> \cbend they can be viewed to ``lift'' functions on values to functions on value sets.

Functions of arbitrary types can be composed by the polymorphic function 
@{text[display]
\<open>comp :: ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c
  \<equiv> \<lambda>f g x. f (g x)\<close>}\index{comp (constant)}
if the ``intermediate'' type \<open>'b\<close> matches. The operator name for infix notation is \<open>(\<circ>)\<close>\index{/comp@\<open>\<circ>\<close> (operator)}.

There is also the variant \<open>fcomp\<close>\index{fcomp (constant)} with reversed arguments where the left argument is applied first
and the function
@{text[display]
\<open>scomp :: ('a \<Rightarrow> 'b \<times> 'c) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'd
  \<equiv> \<lambda>f g x. (case_prod g) (f x))\<close>}\index{scomp (constant)}
which composes a binary function with a function with pairs as values, using the uncurry function
\<open>case_prod\<close> to convert the binary function to a function with argument pairs (see
Section~\ref{holtypes-tup-funcs}). The operator names \<open>(\<circ>>)\<close>\index{/fcomp@\<open>\<circ>>\<close> (operator)} for \<open>fcomp\<close> and \<open>(\<circ>\<rightarrow>)\<close>\index{/scomp@\<open>\<circ>\<rightarrow>\<close> (operator)} for \<open>scomp\<close>
are only available after using the command
@{theory_text[display]
\<open>unbundle state_combinator_syntax\<close>}\index{state-combinator-syntax@state$\_$combinator$\_$syntax (bundle)}
on theory level.

Finite iteration of a function of type \<open>'a \<Rightarrow> 'a\<close> can be specified by the polymorphic function\cbstart
@{text[display]
\<open>compow :: nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a\<close>}\index{compow (constant)}
with operator name \<open>(^^)\<close>\index{/compow@\<open>^^\<close> (operator)} (with reversed arguments) for infix notation. Thus 
\<open>compow 3 f = f ^^ 3 = f \<circ> f \<circ> f\<close>.\cbend
\<close>

subsubsection "Function Updates"

text\<open>
HOL provides the function\index{function!update $\sim$}
@{text[display]
\<open>fun_upd :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)
  \<equiv> \<lambda>f a b x. if x = a then b else f x\<close>}\index{fun-upd@fun$\_$upd (constant)}
which returns a function where the value of a single argument \<open>a\<close> of \<open>f\<close> has been changed to \<open>b\<close>.
Note that this ``function update'' does not ``change'' the function \<open>f\<close>, it returns a new function
which differs from \<open>f\<close> only for the argument \<open>a\<close>.

HOL provides the alternative syntax\index{syntax!alternative $\sim$!for function update}
@{text[display]
\<open>f(terma\<^sub>1 := termb\<^sub>1, \<dots>, terma\<^sub>n := termb\<^sub>n)\<close>}\index{:= (inner keyword)}
for the term \<open>fun_upd \<dots> (fun_upd f terma\<^sub>1 termb\<^sub>1) \<dots> terma\<^sub>n termb\<^sub>n\<close>. The changes are applied from
left to right, i.e. \<open>f(x := y, x := z) = f(x := z)\<close>.

HOL also provides an update on a set of arguments, where the new values are specified by another
function:
@{text[display]
\<open>override_on :: ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b
  \<equiv> \<lambda>f g A x. if x \<in> A then g x else f x\<close>}\index{override-on@override$\_$on (constant)}\<close>

text_raw\<open>\cbdelete\<close>

subsubsection "BNF Functions"

text\<open>
\cbstart
As described in Sections~\ref{holbasic-functor-multi} and \ref{holbasic-bnf-natural} the type
constructor \<open>fun\<close> is a bounded natural functor with one dead and one live type parameter. The
mapper is the function
@{text[display]
\<open>map_fun :: ('b\<^sub>1\<Rightarrow>'a\<^sub>1) \<Rightarrow> ('a\<^sub>2\<Rightarrow>'b\<^sub>2) \<Rightarrow> ('a\<^sub>1\<Rightarrow>'a\<^sub>2) \<Rightarrow> ('b\<^sub>1\<Rightarrow>'b\<^sub>2)
  \<equiv> \<lambda>f\<^sub>1 f\<^sub>2. \<lambda>f. f\<^sub>2 \<circ> f \<circ> f\<^sub>1\<close>}\index{map-fun@map$\_$fun (constant)}
and the set-function for the live type parameter is the function
@{text[display]
\<open>range :: ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<equiv> \<lambda>f. image f UNIV\<close>}\index{range (constant)}
which returns the set of all result values of a function (note that the set of all argument values
of a function is always \<open>UNIV\<close> because functions are total in Isabelle). 

There are the predicator and relator (see Section~\ref{holbasic-bnf-predrel})
@{text[display]
\<open>pred_fun :: ('p\<^sub>1\<Rightarrow>bool) \<Rightarrow> ('p\<^sub>2\<Rightarrow>bool) \<Rightarrow> ('p\<^sub>1\<Rightarrow>'p\<^sub>2) \<Rightarrow> bool
  \<equiv> \<lambda>p\<^sub>1 p\<^sub>2 f. \<forall>x. p\<^sub>1 x \<longrightarrow> p\<^sub>2 (f x)
rel_fun :: ('p\<^sub>1\<Rightarrow>'q\<^sub>1\<Rightarrow>bool) \<Rightarrow> ('p\<^sub>2\<Rightarrow>'q\<^sub>2\<Rightarrow>bool)
  \<Rightarrow> ('p\<^sub>1\<Rightarrow>'p\<^sub>2) \<Rightarrow> ('q\<^sub>1\<Rightarrow>'q\<^sub>2) \<Rightarrow> bool
  \<equiv> \<lambda>r\<^sub>1 r\<^sub>2 f g. \<forall>x y. r\<^sub>1 x y \<longrightarrow> r\<^sub>2 (f x) (g y)\<close>}\index{pred-fun@pred$\_$fun (constant)}\index{rel-fun@rel$\_$fun (constant)}
which include the dead type parameter. The predicator and relator for the live parameter can
be obtained by partial application \<open>pred_fun (\<lambda>_. True) = (\<lambda>p\<^sub>2 f. \<forall>x. p\<^sub>2 (f x))\<close> and \<open>rel_fun (=)
= (\<lambda>r\<^sub>2 f g. \<forall>x. r\<^sub>2 (f x) (g x))\<close>. For these functions HOL does not define separate names. They lift
a predicate or relation by applying it to all function values.\cbend
\<close>

subsubsection "Injectivity and Surjectivity"

text\<open>
For the basic function properties of injectivity, surjectivity, and bijectivity HOL provides the
predicates
@{text[display]
\<open>inj :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> \<lambda>f. \<forall>x y. f x = f y \<longrightarrow> x = y
surj :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> \<lambda>f. range f = UNIV
bij :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> \<lambda>f. inj f \<and> surj f\<close>}\index{inj (constant)}\index{surj (constant)}\index{bij (constant)}
and also the domain-restricted forms
@{text[display]
\<open>inj_on :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool
  \<equiv> \<lambda>f A. \<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y
bij_betw :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool
  \<equiv> \<lambda>f A B. inj_on f A \<and> image f A = B\<close>}\index{inj-on@inj$\_$on (constant)}\index{bij-betw@bij$\_$betw (constant)}

Injective functions can be inverted on their range. HOL provides the more general inversion
function
@{text[display]
\<open>the_inv :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)
  \<equiv> \<lambda>f y. THE x. f x = y\<close>}\index{the-inv@the$\_$inv (constant)}
which returns the argument mapped by function \<open>f\<close> to the value \<open>y\<close>. Note the use of the definite
description operator \<open>THE\<close> (see Section~\ref{holbasic-descr-definite}). If there is no such argument
(because \<open>y\<close> is not in the range of \<open>f\<close>) or if it is not unique (because \<open>f\<close> is not injective), it
causes the function to be underspecified. Thus the partial application \<open>(the_inv f)\<close> is the inverse
of an arbitrary function \<open>f\<close>. It is total but only specified for values of type \<open>'b\<close> where the
inversion exists and is unique. It is only fully specified if \<open>bij f\<close>.

Additionally there is the domain-restricted form
@{text[display]
\<open>the_inv_into :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)
  \<equiv> \<lambda>A f y. THE x. x \<in> A \<and> f x = y\<close>}\index{the-inv-into@the$\_$inv$\_$into (constant)}
where the partial application \<open>(the_inv_into A f)\<close> is the inverse of \<open>f\<close> restricted to arguments in
set \<open>A\<close>. It is only fully specified if \<open>image f A = UNIV\<close> and \<open>inj_on f A\<close>.
\<close>

subsubsection "Functions for Orderings and Lattices"

text\<open>
The ordering relations \cbstart  \<open>(\<le>), (\<ge>)\<close> (see Section~\ref{holbasic-equal-order}) are defined
for functions by lifting
the ordering relations for the function values. Thus the ordering \<open>(\<le>)\<close> on functions is equivalent
to \<open>rel_fun (=) (\<le>)\<close> and analogously for \<open>(\<ge>)\<close>. In other words, \<open>f \<le> g\<close> holds if
\<open>\<forall>x. (f x) \<le> (g x)\<close>. Note that even if \<open>(\<le>)\<close> is a total ordering on the function values, the lifted
ordering is partial, because for some arguments the function values may be less or equal and for other
arguments not.

The strict ordering relations \<open>(<), (>)\<close> on functions, instead, are not lifted, they are derived
from \<open>(\<le>), (\<ge>)\<close> according to \<open>(f < g) = (f \<le> g) \<and> \<not> (g \<le> f)\<close>.\cbend

In a similar way the lattice operations \<open>(\<sqinter>)\<close>, \<open>(\<squnion>)\<close>, \<open>(\<Sqinter>)\<close>, and \<open>(\<Squnion>)\<close> (see
Section~\ref{holbasic-equal-lattice}) are lifted from the function values to functions:
@{text[display]
\<open>f \<sqinter> g \<equiv> \<lambda>x. f x \<sqinter> g x
f \<squnion> g \<equiv> \<lambda>x. f x \<squnion> g x
\<Sqinter>A \<equiv> \<lambda>x. \<Sqinter>f\<in>A. f x
\<Squnion>A \<equiv> \<lambda>x. \<Squnion>f\<in>A. f x\<close>}
Since \<open>(<)\<close> is not a total ordering on functions the functions \<open>min\<close> and \<open>max\<close> are \<^emph>\<open>not\<close> equivalent
to \<open>(\<sqinter>)\<close> and \<open>(\<squnion>)\<close> and the functions \<open>Min\<close> and \<open>Max\<close> are not available for sets of functions.

Since orderings and lattice operations are defined for type \<open>bool\<close> (see
Section~\ref{holtypes-bool-funcs}) so that \<open>(\<le>)\<close> is equivalent to the implication \<open>(\<longrightarrow>)\<close>, the
lifting works specifically for predicates and relations  (see Section~\ref{holbasic-pred}).
Predicates are ordered by the ``stronger as'' relation where \<open>(p\<^sub>1 \<le> p\<^sub>2) \<longleftrightarrow> (\<forall>x. p\<^sub>1 x \<longrightarrow> p\<^sub>2 x)\<close> and
the lattice operations correspond to point-wise conjunction or disjunction, such as
\<open>(p\<^sub>1 \<sqinter> p\<^sub>2) = (\<lambda>x. p\<^sub>1 x \<and> p\<^sub>2 x)\<close>. As described above for functions with multiple arguments the
boolean operations can be lifted in the same way to binary or n-ary relations. Binary relations are
ordered by the ``stronger as'' relation where \<open>(r\<^sub>1 \<le> r\<^sub>2) \<longleftrightarrow> (\<forall>x y. r\<^sub>1 x y \<longrightarrow> r\<^sub>2 x y)\<close> and the
lattice operations are as above, such as \<open>(r\<^sub>1 \<sqinter> r\<^sub>2) = (\<lambda>x y. r\<^sub>1 x y \<and> r\<^sub>2 x y)\<close>.
\<close>

subsubsection "Monotonicity"

text\<open>
Another way to derive predicates on functions is by applying \<open>rel_fun\<close> to compare a function to
itself. HOL supports this by the function
@{text[display]
\<open>monotone :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> 'p\<^sub>2 \<Rightarrow> bool)
  \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool
  \<equiv> \<lambda>r\<^sub>1 r\<^sub>2 f. rel_fun r\<^sub>1 r\<^sub>2 f f\<close>}\index{monotone (constant)}
The partial application \<open>monotone r\<^sub>1 r\<^sub>2\<close> is the predicate which tests a function whether arguments
related by \<open>r\<^sub>1\<close> produce results related by \<open>r\<^sub>2\<close>:
@{text[display]
\<open>monotone r\<^sub>1 r\<^sub>2 = (\<lambda>f. \<forall>x y. r\<^sub>1 x y \<longrightarrow> r\<^sub>2 (f x) (f y))\<close>}

The usual notion of monotonicity results when \<open>monotone\<close> is applied to the ordering relations. HOL
defines the specific predicates on functions
@{text[display]
\<open>mono :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool \<equiv> monotone (\<le>) (\<le>)
strict_mono :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool \<equiv> monotone (<) (<)
antimono :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool \<equiv> monotone (\<le>) (\<ge>)\<close>}\index{mono (constant)}\index{strict-mono@strict$\_$mono (constant)}\index{antimono (constant)}

HOL also provides the domain-restricted variants:
@{text[display]
\<open>monotone_on :: 'p\<^sub>1 set \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> 'p\<^sub>2 \<Rightarrow> bool)
  \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool
mono_on :: 'p\<^sub>1 set \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool
strict_mono_on :: 'p\<^sub>1 set \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool\<close>}\index{monotone-on@monotone$\_$on (constant)}
\index{mono-on@mono$\_$on (constant)}\index{strict-mono-on@strict$\_$mono$\_$on (constant)}
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-func-rules}\<close>

text\<open>
Since functions are the basic type of Isabelle there are several rules which are already built in
and need not be provided by HOL. Some of them are implicitly applied to propositions without the
need of using proof methods, such as the rewriting rule
@{text[display]
\<open>(\<lambda>x. ?P x) ?y = ?P ?y\<close>}
Many others are known by the automatic proof methods (see Section~\ref{methods-auto-methods}) so that
properties relating to functions can usually be proved by them.

The most basic rules provided by HOL about functions are

@{text\<open>ext:\<close>} @{thm ext}\index{ext (fact name)}\\
@{text\<open>fun_cong:\<close>} @{thm fun_cong}\index{fun-cong@fun$\_$cong (fact name)}\\
@{text\<open>arg_cong:\<close>} @{thm arg_cong}\index{arg-cong@arg$\_$cong (fact name)}\\
@{text\<open>cong:\<close>} @{thm cong}\index{cong (fact name)}\<close>

subsubsection "Rules About Functions on Functions"

text\<open>
Reasoning about the functions described in Section~\ref{holtypes-func-funcs} can often be done by
substituting their definition and then using automatic proof methods. Alternatively HOL provides
many rules for direct reasoning about these functions, such as

@{text\<open>comp_assoc:\<close>} @{thm comp_assoc}\index{comp-assoc@comp$\_$assoc (fact name)}\\
@{text\<open>image_comp:\<close>} @{thm image_comp}\index{image-comp@image$\_$comp (fact name)}

and in particular introduction rules (see Section~\ref{methods-rule-intro}) such as

@{text\<open>injI:\<close>} @{thm injI}\index{injI (fact name)}\\
@{text\<open>surjI:\<close>} @{thm surjI}\index{surjI (fact name)}\\
@{text\<open>bijI:\<close>} @{thm bijI}\index{bijI (fact name)}\\
@{text\<open>monoI:\<close>} @{thm monoI}\index{monoI (fact name)}

the destruction (see Section~\ref{methods-forward-dest}) and elimination
(see Section~\ref{case-elim-rules}) rules

@{text\<open>comp_eq_dest:\<close>} @{thm comp_eq_dest}\index{comp-eq-dest@comp$\_$eq$\_$dest (fact name)}\\
@{text\<open>injD:\<close>} @{thm injD}\index{injD (fact name)}\\
@{text\<open>monoD:\<close>} @{thm monoD}\index{monoD (fact name)}\\
@{text\<open>comp_eq_elim:\<close>}\\\hspace*{1em}@{thm comp_eq_elim}\index{comp-eq-elim@comp$\_$eq$\_$elim (fact name)}\\
@{text\<open>surjE:\<close>} @{thm surjE}\index{surjE (fact name)}\\
@{text\<open>monoE:\<close>} @{thm monoE}\index{monoE (fact name)}

and the simplifier equations (see Section~\ref{methods-simp-simplif})

@{text\<open>comp_apply:\<close>} @{thm comp_apply}\index{comp-apply@comp$\_$apply (fact name)}\\
@{text\<open>fun_upd_apply:\<close>}\\\hspace*{1em}@{thm fun_upd_apply}\index{fun-upd-apply@fun$\_$upd$\_$apply (fact name)}\\
@{text\<open>bij_id:\<close>} @{thm bij_id}\index{bij-id@bij$\_$id (fact name)}\\
@{text\<open>override_on_apply_in:\<close>}\\\hspace*{1em}@{thm override_on_apply_in}\index{override-on-apply-in@override$\_$on$\_$apply$\_$in (fact name)}\<close>

section "Relations"
text_raw\<open>\label{holtypes-rel}\<close>

text\<open>
**todo**
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-rel-funcs}\<close>

section "The Sum Type"
text_raw\<open>\label{holtypes-sum}\<close>

text\<open>
**todo**
\<close>

(*
section "Fixed-Size Binary Numbers"
text_raw\<open>\label{holtypes-word}\<close>

text\<open>
**todo**
\<close>
*)

end