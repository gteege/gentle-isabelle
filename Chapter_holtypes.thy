theory Chapter_holtypes
  imports Chapter_holtdefs HOL.BNF_Cardinal_Arithmetic
begin

chapter "Isabelle HOL Types"
text_raw\<open>\label{holtypes}\<close>

text \<open>
This chapter introduces a small basic part of the types available in HOL.

Most of the types are algebraic types (see Section~\ref{holtdefs-data}). Although some of them are
defined differently for technical reasons, they are configured afterwards to behave as if they 
have been defined as algebraic types. Therefore they are described here using the corresponding
datatype definition.

If applicable, the functions described for a type include the specific forms of ordering relations
and lattice operations (see Section~\ref{holbasic-equal}) and functions for binder syntax (see
Section~\ref{holbasic-descr}).

The semantics of the described functions is either given informally for well-known functions or by
a description of the form \<open>name :: type \<equiv> lambda-term\<close>. The latter is often not the actual
definition used by HOL for the function, it is only used here for documentation purpose.
\<close>

section "Boolean Values"
text_raw\<open>\label{holtypes-bool}\<close>

text\<open>
The type of boolean values is specified equivalent to an algebraic type of the form
of the enumeration type (see Section~\ref{holtdefs-data-constr})
@{theory_text[display]
\<open>datatype bool = True | False\<close>}

The type \<open>bool\<close> plays a special role in HOL since it is the type of all terms which are used 
as propositions and facts (see Section~\ref{basic-theory-prop}) in Isabelle. Every object logic
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

As an alternative syntax HOL provides the usual form
@{text[display]
\<open>if term then term\<^sub>1 else term\<^sub>2\<close>}
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-bool-funcs}\<close>

text\<open>
The usual logical functions are defined for type \<open>bool\<close>: \<open>conj, disj, implies, iff\<close>
of type \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> with operator names \<open>(\<and>), (\<or>), (\<longrightarrow>), (\<longleftrightarrow>)\<close> and the unary negation
\<open>Not\<close> of type \<open>bool \<Rightarrow> bool\<close> and operator name \<open>(\<not>)\<close>. Instead of \<open>(\<longleftrightarrow>)\<close> the default is to use \<open>(=)\<close>
as infix operator.
\<close>

subsubsection "Functions for Orderings and Lattices"

text\<open>
The ordering relations (see Section~\ref{holbasic-equal-order}) and the lattice operations (see
Section~\ref{holbasic-equal-lattice}) are defined for type \<open>bool\<close> so that \<open>False < True\<close>. This
implies that \<open>(\<le>)\<close> is equivalent to \<open>(\<longrightarrow>)\<close> and \<open>(\<sqinter>), (\<squnion>)\<close> and also \<open>min, max\<close> are equivalent to
\<open>(\<and>), (\<or>)\<close>.

The lattice operators \<open>(\<Sqinter>)\<close> and \<open>(\<Squnion>)\<close> on sets are provided for \<open>bool\<close> by definitions
\<open>\<Sqinter>A \<equiv> (False \<notin> A)\<close> and \<open>\<Squnion>A \<equiv> (True \<in> A)\<close>, so they correspond to conjunction and disjunction
over sets, respectively. Note that the metalogic quantifier \<open>\<And>\<close> (see
Section~\ref{basic-theory-prop}) does \<^emph>\<open>not\<close> denote a conjunction operation on sets of boolean
values. For nonempty finite sets of boolean values the functions \<open>Min\<close> and \<open>Max\<close> are equivalent to
\<open>(\<Sqinter>)\<close> and \<open>(\<Squnion>)\<close>.
\<close>

subsubsection "Functions for Binder Syntax"

text\<open>
The quantifiers are defined as ``predicates on predicates'':
@{text[display]
\<open>All :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> \<lambda>P. (P = (\<lambda>x. True))
Ex :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> \<lambda>P. (\<not> All (\<lambda>x. \<not> P x))
Uniq :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
  \<lambda>P. (All (\<lambda>x. (All (\<lambda>y. P x \<longrightarrow> P y \<longrightarrow> y = x))))
Ex1 :: ('a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
  \<lambda>P. (Ex (\<lambda>x. P x \<and> (All (\<lambda>y. P y \<longrightarrow> y = x))))\<close>}
with the alternative binder syntax \<open>\<forall>x. bterm\<close> for the application \<open>All (\<lambda>x. bterm)\<close>, \<open>\<exists>x. bterm\<close>
for \<open>Ex (\<lambda>x. bterm)\<close>, \<open>\<exists>\<^sub>\<le>\<^sub>1x. bterm\<close> for \<open>Uniq (\<lambda>x. bterm)\<close>, and \<open>\<exists>!x. bterm\<close> for \<open>Ex1 (\<lambda>x. bterm)\<close>.
The \<open>Uniq\<close> quantifier states that there is atmost one value satisfying the predicate, the \<open>Ex1\<close>
quantifier states that there is exactly one such value.

An iterated application for an n-ary predicate \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. bterm\<close> can be written in the
form \<open>\<forall> x\<^sub>1 \<dots> x\<^sub>n. bterm\<close> for all quantifiers. Like for lambda terms (see
Section~\ref{basic-theory-terms}) types may be specified for (some of) the variables as in
\<open>\<forall> (x\<^sub>1 :: type\<^sub>1) \<dots> (x\<^sub>n :: type\<^sub>n). bterm\<close>.
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-bool-rules}\<close>

text\<open>
The rules described here are the usual rules for an algebraic type and introduction / elimination
/ destruction rules for the functions, and some specific rules for negation. HOL provides
many additional rules, see the Isabelle documentation for how to use them in proofs.

Complex proofs using these rules can often be done automatically by the proof method \<open>blast\<close> (see
Section~\ref{basic-methods-auto}).
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
  \<lbrakk>?Q \<Longrightarrow> ?P; \<not> ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
is used, as described in Section~\ref{basic-case-reasoning}.

For the alternate case term form described in Section~\ref{holtypes-bool-destrs} there is also a
split rule:
@{text[display]
\<open>if_split:
  ?P (if ?t then ?t\<^sub>1 else ?t\<^sub>2) = 
  ((?t \<longrightarrow> ?P ?t\<^sub>1) \<and> (\<not> ?t \<longrightarrow> ?P ?t\<^sub>2))\<close>}
Other than \<open>bool.split\<close> this rule is automatically applied by the simplifier (see
Section~\ref{basic-methods-simp}) for splitting \<open>if\<close>-terms.
\<close>

subsubsection "Rules About Boolean Functions"

text\<open>
For the functions described in Section~\ref{holtypes-bool-funcs} corresponding introduction rules
(see Section~\ref{basic-methods-rule}), destruction rules (see Section~\ref{basic-methods-forward}),
and elimination rules (see Section~\ref{basic-case-elim}) are available. They are present in the
rule sets \<open>intro\<close>, \<open>dest\<close>, or \<open>elim\<close>, respectively.

The introduction rules are:

@{text\<open>conjI:\<close>} @{thm conjI}\\
@{text\<open>disjI1:\<close>} @{thm disjI1}\\
@{text\<open>disjI2:\<close>} @{thm disjI2}\\
@{text\<open>notI:\<close>} @{thm notI}\\
@{text\<open>impI:\<close>} @{thm impI}\\
@{text\<open>iffI:\<close>} @{thm iffI}\\
@{text\<open>allI:\<close>} @{thm allI}\\
@{text\<open>exI:\<close>} @{thm exI}

The destruction rules are:

@{text\<open>conjunct1:\<close>} @{thm conjunct1}\\
@{text\<open>conjunct2:\<close>} @{thm conjunct2}\\
@{text\<open>mp:\<close>} @{thm mp}\\
@{text\<open>spec:\<close>} @{thm spec}\\
@{text\<open>iffD1:\<close>} @{thm iffD1}\\
@{text\<open>iffD2:\<close>} @{thm iffD2}

The rule \<open>mp\<close> is the well known logic rule ``modus ponens''.

The elimination rules are:

@{text\<open>conjE:\<close>} @{thm conjE}\\
@{text\<open>disjE:\<close>} @{thm disjE}\\
@{text\<open>notE:\<close>} @{thm notE}\\
@{text\<open>impE:\<close>} @{thm impE}\\
@{text\<open>iffE:\<close>} @{thm iffE}\\
@{text\<open>allE:\<close>} @{thm allE}\\
@{text\<open>exE:\<close>} @{thm exE}

Additionally, the following four rules can be used for ``proofs by contradiction'':

@{text\<open>contrapos_pn:\<close>} @{thm contrapos_pn}\\
@{text\<open>contrapos_pp:\<close>} @{thm contrapos_pp}\\
@{text\<open>contrapos_nn:\<close>} @{thm contrapos_nn}\\
@{text\<open>contrapos_np:\<close>} @{thm contrapos_np}
\<close>

subsubsection "Equivalence of Derivation Rules and Boolean Terms"

text\<open>
Using these rules every derivation rule (see Section~\ref{basic-theory-prop})
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>}
can be converted to the boolean term
@{text[display]
\<open>\<forall> x\<^sub>1 \<dots> x\<^sub>m. (A\<^sub>1' \<and> \<dots> \<and> A\<^sub>n') \<longrightarrow> C\<close>}
(where each \<open>A\<^sub>i'\<close> is converted in the same way if it is again a derivation rule), and vice versa.

In principle every theorem may be specified in either of both forms. However, its application by
proof methods in other proofs is usually only possible if it is specified in derivation rule form.
Therefore it is usually preferable to specify theorems in this form, where the conclusion \<open>C\<close> does
not use \<open>\<forall>\<close> or \<open>\<longrightarrow>\<close> as its outermost operator.
\<close>

section "The Unit Type"
text_raw\<open>\label{holtypes-unit}\<close>

text\<open>
The unit type has only one value. It is specified equivalent to an algebraic type of the form
of the enumeration type (see Section~\ref{holtdefs-data-constr})
@{theory_text[display]
\<open>datatype unit = Unity\<close>}

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
usual way of denoting it is by its alternative form \<open>()\<close>, which has been chosen because the unit
type is also used to represent empty tuples (see Section~\ref{holtypes-tup}).
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

text\<open>
The type of natural numbers is specified equivalent to a recursive algebraic type (see 
Section~\ref{holtdefs-data}) of the form
@{theory_text[display]
\<open>datatype nat = 0 | Suc nat\<close>}
It is not really defined in this way, because \<open>0\<close> is syntactically not a constructor, but it can
mainly be used in the same way.

The type \<open>nat\<close> denotes the mathematical concept of natural numbers, it has infinitely many values,
there is no upper limit.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-nat-values}\<close>

text\<open>
Values of type \<open>nat\<close> can be denoted in the usual way using constructor expressions such as \<open>Suc 0,
Suc (Suc 0), \<dots>\<close>.

Alternatively they can be denoted by decimal number literals such as \<open>0, 1, 2, \<dots>\<close> of arbitrary size.

However, the decimal number literals are overloaded and may also denote values of other numerical
types, such as type \<open>int\<close> for the integer numbers. Therefore the type of an isolated decimal number
literal is not determined, which may cause unexpected effects. To denote a value of type \<open>nat\<close> its
type may be explicitly specified as described in Section~\ref{basic-theory-terms}, such as \<open>1::nat\<close>.

The lattice constant \<open>bot\<close> (see Section~\ref{holbasic-equal-lattice}) is available for type \<open>nat\<close>
and denotes the value \<open>0\<close>. The constant \<open>top\<close> is not available for type \<open>nat\<close>.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-nat-destrs}\<close>

text\<open>
Since \<open>Suc\<close> plays the role of a constructor, corresponding destructors can be defined.
The selector function which inverts \<open>Suc\<close> is defined as \<open>nat.pred\<close> where \<open>nat.pred x\<close> is equivalent
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
of type \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> with operator names \<open>(+), (-), (*), (div), (mod)\<close> and alternate
operator name \<open>(/)\<close> for \<open>(div)\<close>. Subtraction is truncated at \<open>0\<close>, e.g. \<open>4 - 7\<close> evaluates to \<open>0\<close>.
Also defined is the binary ``divides'' relation \<open>dvd_class.dvd\<close> with operator name \<open>(dvd)\<close>.

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
functions, like for other types. They are usually not sufficient for proofs about natural numbers
and should only give an impression about the type \<open>nat\<close> in comparison with other types.

Proofs for linear arithmetic properties of \<open>nat\<close> values using these and other rules can often be
done automatically by the proof methods \<open>linarith\<close> or \<open>arith\<close> (see Section~\ref{basic-methods-auto}).
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
Note that the last six rules combine induction with elimination, as described in
Section~\ref{basic-case-induction}, and are therefore attributed by \<open>[consumes 1]\<close>.
\<close>

subsubsection "Rules About Functions"

text\<open>
The constructor function \<open>Suc\<close> has result type \<open>nat\<close> and therefore cannot occur as outermost
operator in a proposition. Therefore introduction, destruction, and elimination rules for \<open>Suc\<close>
must embed the application term in a proposition with the help of a predicate. The ordering
relations are used for this purpose, thus only ordering properties can be proved using these rules.

Introduction rules (see Section~\ref{basic-methods-rule}) for \<open>Suc\<close> are

@{text\<open>le_SucI:\<close>} @{thm le_SucI}\\
@{text\<open>less_SucI:\<close>} @{thm less_SucI}\\
@{text\<open>Suc_leI:\<close>} @{thm Suc_leI}\\
@{text\<open>Suc_lessI:\<close>} @{thm Suc_lessI}

Destruction rules (see Section~\ref{basic-methods-forward}) for \<open>Suc\<close> are

@{text\<open>Suc_leD:\<close>} @{thm Suc_leD}\\
@{text\<open>Suc_lessD:\<close>} @{thm Suc_lessD}\\
@{text\<open>Suc_less_SucD:\<close>} @{thm Suc_less_SucD}\\
@{text\<open>Suc_le_lessD:\<close>} @{thm Suc_le_lessD}

An elimination rule (see Section~\ref{basic-case-elim}) for \<open>Suc\<close> is

@{text\<open>less_SucE:\<close>}\\
  @{thm less_SucE}

For the arithmetic functions described in Section~\ref{holtypes-nat-funcs} most properties are
specified by equations such as

@{text\<open>add_Suc_right:\<close>} @{thm add_Suc_right}\\
@{text\<open>mult_Suc_right:\<close>} @{thm mult_Suc_right}\\
@{text\<open>diff_Suc_1:\<close>} @{thm diff_Suc_1}\\
@{text\<open>min_Suc_Suc:\<close>} @{thm min_Suc_Suc}\\
@{text\<open>max_Suc_Suc:\<close>} @{thm min_Suc_Suc}\\
@{text\<open>dvd_diff_nat:\<close>} @{thm dvd_diff_nat}

Many of these equations are members of the simpset, therefore many simple arithmetic properties can
be proved by the simplifier. More complex properties may need the methods \<open>linarith\<close> or \<open>arith\<close>,
or can be proved by induction or a combination thereof.
\<close>

section "Sets"
text_raw\<open>\label{holtypes-set}\<close>

text\<open>
You may think of the type constructor \<open>set\<close> as being specified equivalent to the parameterized
algebraic type
@{theory_text[display]
\<open>datatype 'a set = Collect (contains: 'a \<Rightarrow> bool)\<close>}
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

For such a term HOL provides the alternative ``set comprehension'' syntax (which is a special form
of binder syntax)
@{text[display]
\<open>{x. bterm}\<close>}
and the abbreviations \<open>{}\<close> for the empty set \<open>{x. False}\<close> and \<open>UNIV\<close> for the universal set 
\<open>{x. True}\<close>. Both abbreviations are available for arbitrary types \<open>'a set\<close>.
The universal set is the set of all values of the type \<open>'a\<close>. Examples are \<open>UNIV :: bool set\<close> which
is the set \<open>{True, False}\<close> and \<open>UNIV :: nat set\<close> which is the set of all natural numbers.

The lattice constants \<open>top\<close> and \<open>bot\<close> (see Section~\ref{holbasic-equal-lattice}) are available for
sets and denote the universal set \<open>UNIV\<close> and the empty set \<open>{}\<close>, respectively.

For a set comprehension of the form
@{text[display]
\<open>{x. \<exists> x\<^sub>1 \<dots> x\<^sub>n. x = term \<and> bterm}\<close>}
HOL provides the alternative syntax
@{text[display]
\<open>{term | x\<^sub>1 \<dots> x\<^sub>n. bterm}\<close>}
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
\<open>Set.member :: 'a \<Rightarrow> 'a set \<Rightarrow> bool\<close>}
with alternate operator name \<open>(\<in>)\<close>. It combines unwrapping and applying the predicate and
corresponds to the usual member test predicate for sets.

Since there is only one constructor, discriminators and case terms are not available for sets.
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-set-funcs}\<close>

text\<open>
In addition to the basic function \<open>Set.member\<close> and its negation \<open>Set.not_member\<close> with operator name
\<open>(\<notin>)\<close> HOL provides the other usual functions on sets: the relations \<open>subset\<close>, \<open>subset_eq\<close>,
\<open>supset\<close>, \<open>supset_eq\<close> with operator names \<open>(\<subset>)\<close>, \<open>(\<subseteq>)\<close>, \<open>(\<supset>)\<close>, \<open>(\<supseteq>)\<close> and the operations \<open>inter\<close>,
\<open>union\<close>, \<open>minus\<close> with operator names \<open>(\<inter>)\<close>, \<open>(\<union>)\<close>, \<open>(-)\<close>. The function \<open>minus\<close> is set difference,
there is also the unary set complement (relative to the universal set \<open>UNIV\<close>,
see Section~\ref{holtypes-set-values}) \<open>uminus\<close> which also has the operator name \<open>(-)\<close> for prefix
application. The functions \<open>minus\<close> and \<open>uminus\<close> are overloaded for other types as well, therefore
Isabelle will not automatically derive that their arguments are sets.

Intersection and union of a family of sets is supported by the functions
@{text[display]
\<open>Inter :: 'a set set \<Rightarrow> 'a set
Union :: 'a set set \<Rightarrow> 'a set\<close>}
with operator names \<open>(\<Inter>)\<close> and \<open>(\<Union>)\<close> for prefix notation.

HOL also provides the function
@{text[display]
\<open>insert :: 'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<equiv> \<lambda>a B. {x. x = a \<or> x \<in> B}\<close>}
which inserts a value into a set, together with the set enumeration notation
@{text[display]
\<open>{x\<^sub>1, \<dots>, x\<^sub>n}\<close>}
as abbreviation for \<open>insert x\<^sub>1 (\<dots> (insert x\<^sub>n {}) \<dots>)\<close>.

Moreover HOL provides the functions
@{text[display]
\<open>Pow :: 'a set \<Rightarrow> 'a set set \<equiv> \<lambda>A. {B. B\<subseteq>A}
image :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<equiv> \<lambda>f A. {y. \<exists>x\<in>A. y = f x}
range :: ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<equiv> \<lambda>f. image f UNIV
vimage :: 'a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set \<equiv> \<lambda>f A. {x. f x \<in> A}
is_singleton :: 'a set \<Rightarrow> bool \<equiv> \<lambda>A. (\<exists>x. A = {x})
the_elem :: 'a set \<Rightarrow> 'a \<equiv> \<lambda>A. (THE x. A = {x})
pairwise :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool \<equiv>
  \<lambda>f A. (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> f x y)
disjnt :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool \<equiv> \<lambda>A B. A \<inter> B = {}\<close>}
with operator name \<open>(`)\<close> for \<open>image\<close> and \<open>(-`)\<close> for \<open>vimage\<close>. \<open>Pow\<close> is the powerset operator,
\<open>image\<close> and \<open>vimage\<close> are the image / reverse image of a function. \<open>range\<close> is the set of all result
values of a function (note that the set of all argument values of a function is always \<open>UNIV\<close>
because functions are total in Isabelle). As usual, the result of \<open>the_elem A\<close> is underspecified
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
and the bounded descriptors (see Section~\ref{holbasic-descr-least})
@{text[display]
\<open>LEAST x\<in>sterm. bterm \<equiv> LEAST x. x \<in> sterm \<and> bterm
GREATEST x\<in>sterm. bterm \<equiv> GREATEST x. x \<in> sterm \<and> bterm\<close>}
Unlike for the plain quantifiers only one bounded variable may be specified for these forms. If
there are more, the quantifiers must be nested as in \<open>\<forall>x\<in>sterm\<^sub>1. \<forall>y\<in>sterm\<^sub>2. bterm\<close>.

As set comprehension syntax for the special case of a predicate which includes a member test HOL
provides the syntax
@{text[display]
\<open>{x\<in>sterm. bterm}\<close>}
for a term of the form \<open>{x. x\<in>sterm \<and> bterm}\<close>.

For the operations \<open>(\<Inter>), (\<Union>), (\<Sqinter>), (\<Squnion>), Min, Max\<close> on sets (see Section~\ref{holbasic-equal}) HOL
provides the alternative syntax of the form
@{text[display]
\<open>\<Inter>x\<in>term\<^sub>1. term\<^sub>2\<close>}
where both terms must have a \<open>set\<close> type and \<open>x\<close> may occur free in \<open>term\<^sub>2\<close>. This form is equivalent
to \<open>\<Inter>{term\<^sub>2 | x. x\<in>term\<^sub>1}\<close> which is the intersection over all sets returned by \<open>term\<^sub>2\<close> when \<open>x\<close>
adopts all values in the set \<open>term\<^sub>1\<close>. For \<open>Min\<close> the syntax is 
@{text[display]
\<open>MIN x\<in>term\<^sub>1. term\<^sub>2\<close>}
and analogously for \<open>Max\<close>.

For all these operators HOL also provides the abbreviated syntax of the form
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

subsubsection "Functions for Finite Sets"

text\<open>
HOL defines the predicate \<open>finite\<close> by the inductive definition (see
Section~\ref{holbasic-inductive})
@{theory_text[display]
\<open>inductive finite :: "'a set \<Rightarrow> bool" where
  "finite {}"
| "finite A \<Longrightarrow> finite (insert a A)"\<close>}
So a set is finite if it can be constructed from the empty set by a finite sequence of inserting
single elements.

For iterating through the elements of a finite set HOL introduces the function
@{text[display]
\<open>Finite_Set.fold :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b\<close>}
where \<open>fold f z {x\<^sub>1, \<dots>, x\<^sub>n} = f x\<^sub>1 (\<dots> (f x\<^sub>n z)\<dots>)\<close> if the resulting value is independent of the
order of the \<open>x\<^sub>i\<close>, i.e., the function \<open>f\<close> must be ``left-commutative'' on the values in the set. If
it is not, its result is underspecified, if the set is not finite the result is the starting value
\<open>z\<close>.

The function \<open>Finite_Set.fold\<close> is not intended for direct use, it is used by HOL to provide other
functions. The most basic is
@{text[display]
\<open>card :: 'a set \<Rightarrow> nat \<equiv> \<lambda>A. Finite_Set.fold (\<lambda>_ n. Suc n) 0 A\<close>}
for the cardinality of sets. For finite sets it is the number of elements, for infinite sets, due
to the way \<open>fold\<close> is defined, it is always \<open>0\<close>.
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-set-rules}\<close>

subsubsection "Algebraic Type Rules"

text\<open>
Since HOL does not define the type \<open>'a set\<close> as an algebraic type it does not provide the standard
rules and rule sets. However, the relevant properties are available in slightly different form.

Injectivity of the constructor is not specified as a simplifier equation, instead there is the rule

@{text\<open>Collect_inj:\<close>} @{thm Collect_inj}

Note that the other direction is always satisfied for arbitrary functions (see
Section~\ref{holtypes-func-rules}). It is provided in the form where the predicates are applied to
arguments:

@{text\<open>Collect_eqI:\<close>} @{thm Collect_eqI}

where its name reflects that it has the form of an introduction rule (see
Section~\ref{basic-methods-rule}) for the equality relation \<open>(=)\<close> (see
Section~\ref{holbasic-equal-eq}) on type \<open>'a set\<close>.

Equivalent to a ``defining equation'' for the selector there is the rule
@{text[display]
\<open>mem_Collect_eq: Set.member ?a (Collect ?P) = ?P ?a\<close>}
which is
@{text[display]
\<open>(?a \<in> {x. ?P x}) = ?P ?a\<close>}
in alternative syntax. This rule is also provided in the form of two separate rules for both
dirctions:
@{text[display]
\<open>CollectI: ?P ?a \<Longrightarrow> ?a \<in> {x. ?P x}
CollectD: ?a \<in> {x. ?P x} \<Longrightarrow> ?P ?a\<close>}
having the form of an introduction and a destruction rule (see Section~\ref{basic-methods-forward}).

Due to the simple wrapper structure of type \<open>'a set\<close> no other algebraic type rules apply.
\<close>

subsubsection "Rules About Functions"

text\<open>
Using the rules described above and the definitions of the functions on sets described in
Section~\ref{holtypes-set-funcs} it is possible to convert every proposition about sets to an
equivalent proposition about predicates and boolean operations (see
Section~\ref{holtypes-bool-funcs}) and prove it in this form. Most automatic proof methods described
in Section~\ref{basic-methods-auto} use this conversion and can thus prove many goals which involve
sets and set operations, in particular the method \<^theory_text>\<open>blast\<close>.

Additionally HOL provides rules which directly work for functions on sets such as the introduction
rules (see Section~\ref{basic-methods-rule})

@{text\<open>subsetI:\<close>} @{thm subsetI}\\
@{text\<open>IntI:\<close>} @{thm IntI}\\
@{text\<open>UnI1:\<close>} @{thm UnI1}\\
@{text\<open>PowI:\<close>} @{thm PowI}

the destruction (see Section~\ref{basic-methods-forward}) and elimination
(see Section~\ref{basic-case-elim}) rules

@{text\<open>subsetD:\<close>} @{thm subsetD}\\
@{text\<open>IntD1:\<close>} @{thm IntD1}\\
@{text\<open>UnE:\<close>} @{thm UnE}\\
@{text\<open>PowD:\<close>} @{thm PowD}

and the simplifier rules (see Section~\ref{basic-methods-simp})

@{text\<open>subset_eq:\<close>} @{thm subset_eq}\\
@{text\<open>Int_def: ?A \<inter> ?B = {x. x \<in> ?A \<and> x \<in> ?B}\<close>}\\
@{text\<open>Un_def: ?A \<union> ?B = {x. x \<in> ?A \<or> x \<in> ?B}\<close>}\\
@{text\<open>Pow_def: Pow ?A = {B. B \<subseteq> ?A}\<close>}

where, despite their names, \<open>(\<inter>)\<close> and \<open>(\<union>)\<close> are not really defined in this way.

There are also many rules about \<open>finite\<close> and \<open>card\<close> such as

@{text\<open>finite_subset:\<close>} @{thm finite_subset}\\
@{text\<open>finite_Un:\<close>} @{thm finite_Un}\\
@{text\<open>finite_Int:\<close>} @{thm finite_Int}\\
@{text\<open>card_mono:\<close>} @{thm card_mono}\\
@{text\<open>card_Diff_subset_Int:\<close>}\\\hspace*{1em}@{thm card_Diff_subset_Int}\\
@{text\<open>card_Un_Int:\<close>}\vspace{-2ex}@{thm[display,indent=2] card_Un_Int}

Many rules about \<open>finite\<close> are known by the automatic proof methods (see
Section~\ref{basic-methods-auto}). Rules about \<open>card\<close> must often be specified explicitly.
\<close>

section "Optional Values"
text_raw\<open>\label{holtypes-option}\<close>

text\<open>
A function argument is optional if it can be omitted. In Isabelle, however, every function has a
fixed number of arguments, it is not possible to omit one or more of them. Instead, the idea is to
have a special value with the meaning of ``no value''. The presence of such a value is no more a
property of the function, it is a property of the function argument's \<^emph>\<open>type\<close>.

Normally, types do not include a ``no value'' value, it must be introduced separately and it must
be different from all existing values. For a type \<open>t\<close> this can be done by defining a new type which
has one more value. However, since the values of the new type are always different from those of \<open>t\<close>
(see Section~\ref{basic-theory-types}), the new type has to include the values of \<open>t\<close> in a
``wrapped'' form.

All this is done by the algebraic type
@{theory_text[display]
\<open>datatype 'a option =
  None
| Some (the: 'a)\<close>}
It is polymorphic with one type parameter \<open>'a\<close> (see Section~\ref{basic-theory-types}), for every
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

Although not introduced by the type definition, the function \<open>Option.is_none\<close> plays the role of
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
  \<lambda>A. image the {x\<in>A. x\<noteq>None}\<close>}
extends the selector \<open>the\<close> to sets. It returns the set of unwrapped values from a set of optional
values, ignoring \<open>None\<close> if present in the set.

No orderings or lattice functions (see Section~\ref{holbasic-equal}) are specified for values of
type \<open>'a option\<close>.
\<close>

subsubsection "BNF Functions"
text\<open>
The type constructor \<open>option\<close> is a bounded natural functor as described in
Section~\ref{holtdefs-data-bnf}. Values of type \<open>'a option\<close> can be viewed as containers of a single
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
            (case y of None \<Rightarrow> x | Some y' \<Rightarrow> Some (f x' y'))\<close>}
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

@{text\<open>elem_set:\<close>} @{thm elem_set}\\
@{text\<open>map_option_case:\<close>}\\\hspace*{1em}@{thm map_option_case}\\
@{text\<open>Option.is_none_def:\<close>} @{thm Option.is_none_def}\\
@{text\<open>rel_option_unfold:\<close>}\vspace{-2ex}@{thm[display,indent=2,margin=70] rel_option_unfold}

Many of these equations are members of the simpset, therefore many properties about optional values
can be proved by the simplifier. Remember to configure it with \<open>split: option.split\<close> if \<open>case\<close> terms
occur for type \<open>'a option\<close>.
\<close>

section "Tuples"
text_raw\<open>\label{holtypes-tup}\<close>

text \<open>
Tuples are represented by HOL as nested pairs. The type of pairs is specified equivalent to an
algebraic type (see Section~\ref{holtdefs-data}) of the form
@{theory_text[display]
\<open>datatype ('a, 'b) prod = Pair (fst: 'a) (snd: 'b)\<close>}
As described in Section~\ref{holtdefs-data}, this type is equivalent to the type of pairs of values
of the type parameters \<open>'a\<close> and \<open>'b\<close>. It is also called the ``product type'' of the types \<open>'a\<close> and
\<open>'b\<close>.

HOL supports an alternative syntax for instances of type \<open>('a, 'b) prod\<close>. The type instance
\<open>(t\<^sub>1, t\<^sub>2) prod\<close> where \<open>t\<^sub>1\<close> and \<open>t\<^sub>2\<close> are arbitrary types may be denoted by the type expression
\<open>t\<^sub>1 \<times> t\<^sub>2\<close> or \<open>t\<^sub>1 * t\<^sub>2\<close> (see Section~\ref{holbasic-tuples}).

A tuple with more than two components is represented in HOL by a pair where the second
component is again a pair or tuple. Hence the type of 4-tuples with component types \<open>t\<^sub>1, t\<^sub>2, t\<^sub>3, t\<^sub>4\<close>
can be denoted by the type expression \<open>t\<^sub>1 \<times> (t\<^sub>2 \<times> (t\<^sub>3 \<times> t\<^sub>4))\<close>. Since \<open>\<times>\<close> is right associative the
parentheses may be omitted as in the equivalent type expression \<open>t\<^sub>1 \<times> t\<^sub>2 \<times> t\<^sub>3 \<times> t\<^sub>4\<close>.

As an example the type \<open>(bool \<times> nat \<times> nat) option\<close> is the type of optional triples of one boolean
value and two natural numbers.

Note that the type \<open>unit\<close> (see Section~\ref{holtypes-unit}) can be used to represent a ``0-tuple'',
as the alternative form \<open>()\<close> of its single value suggests.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-tup-values}\<close>

text\<open>
All values of type \<open>('a, 'b) prod\<close> are denoted using the single constructor \<open>Pair\<close>. HOL supports an
alternative syntax for these constructor application terms: the term \<open>Pair term\<^sub>1 term\<^sub>2\<close> may also be
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
are bound to the variables \<open>x\<^sub>1, x\<^sub>2\<close> and can be used separately in \<open>term\<^sub>1\<close>.

As usual, this also works for tuples with more than two components. The general form of a \<open>case\<close>
term for an n-tuple is
@{text[display]
\<open>case term of (x\<^sub>1, \<dots>, x\<^sub>n) \<Rightarrow> term\<^sub>1\<close>}
where the variables \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> may occur in \<open>term\<^sub>1\<close>.

HOL provides an alternative form for such \<open>case\<close> terms for tuples:
@{text[display]
\<open>let (x\<^sub>1, \<dots>, x\<^sub>n) = term in term\<^sub>1\<close>}
Although this form looks like a generalized \<open>let\<close> term (see Section~\ref{holbasic-let}) this
does not imply that \<open>let\<close> terms support arbitrary patterns on the left side of the \<open>=\<close> sign, like
the \<open>let\<close> statement (see Section~\ref{basic-proof-let}). As ``patterns'' only nested tuples of
variables may be used, such \<open>let\<close> terms are always equivalent to a \<open>case\<close> term for a tuple.

The same variable tuple patterns can also be used in other kinds of terms where variables are bound
such as in lambda terms (e.g., \<open>\<lambda>(a,b) c. a+b+c\<close>), in logic quantifiers (e.g., \<open>\<forall>(a,b) c. a+b=c\<close>),
and in set comprehensions (e.g., \<open>{(a,b). a=b*b}\<close>). Note that the last example is equivalent to
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
  \<lambda>f (x,y). f x y\<close>}
where \<open>'t\<close> is the type of \<open>term\<^sub>1\<close> and thus of the whole \<open>case\<close> term.

This function is of interest on its own. It converts a binary function \<open>f\<close> specified in the style
described in Section~\ref{basic-theory-terms} to a function which takes the two arguments in the
form of a single pair. This conversion is generally called ``uncurrying'' (see
Section~\ref{holbasic-tuples-funarg}). Tuple patterns in variable bindings, as described in
Section~\ref{holtypes-tup-destrs}, are implemented in this way: The term \<open>\<lambda>(a,b). term\<close> is just
an alternative syntax for \<open>case_prod (\<lambda>a b. term)\<close>.

HOL provides the reverse conversion as the function
@{text[display]
\<open>curry :: ('a \<times> 'b \<Rightarrow> 't) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 't \<equiv>
  \<lambda>f x y. f (x,y)\<close>}

Additionally there are the functions
@{text[display]
\<open>apfst :: ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c \<times> 'b \<equiv> \<lambda>f (x,y). (f x,y)
apsnd :: ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'c \<equiv> \<lambda>f (x,y). (x,f y)\<close>}
which apply their first argument to the first or second component of the second argument,
respectively, and the function
@{text[display]
\<open>prod.swap :: 'a \<times> 'b \<Rightarrow> 'b \<times> 'a \<equiv> \<lambda>(x,y). (y,x)\<close>}
which interchanges the components of its argument.

The function
@{text[display]
\<open>Product_Type.Times :: 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set \<equiv>
  \<lambda>A B. {(x, y). x\<in>A \<and> y\<in>B}\<close>}
with operator name \<open>(\<times>)\<close> constructs the cartesian product of two sets.

No orderings or lattice functions (see Section~\ref{holbasic-equal}) are specified for values of
type \<open>('a, 'b) prod\<close>.

\<close>

subsubsection "BNF Functions"

text\<open>
The type constructor \<open>prod\<close> is a bounded natural functor as described in
Section~\ref{holtdefs-data-bnf}. Values of type \<open>('a, 'b) prod\<close> can be viewed as containers of a
single value of type \<open>'a\<close> and a single value of type  \<open>'b\<close>.

The corresponding BNF functions are generated as:
@{text[display]
\<open>map_prod ::
  ('a\<^sub>1 \<Rightarrow> 'a\<^sub>2) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2) \<Rightarrow> ('a\<^sub>1 \<times> 'b\<^sub>1) \<Rightarrow> ('a\<^sub>2 \<times> 'b\<^sub>2) \<equiv>
  \<lambda>f g (x,y). (f x, g y) 
pred_prod ::
  ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool \<equiv>
  \<lambda>f g (x,y). f x \<and> g y
rel_prod ::
  ('a\<^sub>1 \<Rightarrow> 'a\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('b\<^sub>1 \<Rightarrow> 'b\<^sub>2 \<Rightarrow> bool) 
    \<Rightarrow> ('a\<^sub>1 \<times> 'b\<^sub>1) \<Rightarrow> ('a\<^sub>2 \<times> 'b\<^sub>2) \<Rightarrow> bool \<equiv>
  \<lambda>f g (x\<^sub>1,y\<^sub>1) (x\<^sub>2,y\<^sub>2). f x\<^sub>1 x\<^sub>2 \<and> g y\<^sub>1 y\<^sub>2\<close>}
No set functions are generated, they are trivial, returning the corresponding singleton set.
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
  (\<And>x1 x2 x3. ?P (x1, x2, x3)) \<Longrightarrow> ?P ?a\<close>}
In all of them the single case is named \<open>fields\<close>.

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
\<open>split_def: case_prod = (\<lambda>c p. c (fst p) (snd p))\<close>}
allows to directly replace occurrences of \<open>case_prod\<close> by rewriting. It is not part of the simpset
(see Section~\ref{basic-methods-simp}), its use by the simplifier must be explicitly configured.

If tuples are not specified with the help of tuple patterns but by single variables of a tuple
type the case, split, and induction rules described above can be used to convert such variables to
explicit tuples where variables denote the components. Alternatively HOL provides the rule
@{text[display]
\<open>split_paired_all: (\<And>x. ?P x) \<equiv> (\<And>a b. ?P (a, b))\<close>}
Rewriting by this rule replaces all bound variables of a type \<open>t\<^sub>1 \<times> t\<^sub>2\<close> by two variables for the
components. Since tuples are nested pairs an iterated rewriting does the same for arbitrary tuples.
Again, this rule is not part of the simpset and it should be added with care, an iterated rewriting
is best done by the method \<^theory_text>\<open>(simp only: split_paired_all)\<close> without combining it with other
simplifier rules.

Instead, the rules
@{text[display]
\<open>split_paired_All: (\<forall>x. ?P x) = (\<forall>a b. ?P (a, b))
split_paired_Ex: (\<exists>x. ?P x) = (\<exists>a b. ?P (a, b))\<close>}
are in the simpset and are thus automatically applied by the simplifier to replace variables of
tuple type bound by logic quantifiers (see Section~\ref{holtypes-bool-funcs}). If that is not
intended these rules must be deactivated in the form \<^theory_text>\<open>(simp del: split_paired_Ex)\<close>.
\<close>

section "Functions"
text_raw\<open>\label{holtypes-func}\<close>

text\<open>
The type \<open>('a, 'b) fun\<close> with alternative syntax \<open>'a \<Rightarrow> 'b\<close> (see Section~\ref{basic-theory-terms})
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
The values of type \<open>'a \<Rightarrow> 'b\<close> are denoted by lambda terms (see Section~\ref{basic-theory-terms}).

HOL introduces the name \<open>id\<close> for the polymorphic identity function \<open>\<lambda>x. x\<close>.
\<close>

subsection "Functions on Functions"
text_raw\<open>\label{holtypes-func-funcs}\<close>

text\<open>
The functions \<open>image\<close>, \<open>vimage\<close>, and \<open>range\<close> have already been described in
Section~\ref{holtypes-set-funcs}, they can be viewed to ``lift'' functions on values to functions
on value sets.

Functions of arbitrary types can be composed by the polymorphic function 
@{text[display]
\<open>comp :: ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c
  \<equiv> \<lambda>f g x. f (g x)\<close>}
if the ``intermediate'' type \<open>'b\<close> matches. The operator name for infix notation is \<open>(\<circ>)\<close>.

There is also the variant \<open>fcomp\<close> with reversed arguments where the left argument is applied first
and the function
@{text[display]
\<open>scomp :: ('a \<Rightarrow> 'b \<times> 'c) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'd
  \<equiv> \<lambda>f g x. (case_prod g) (f x))\<close>}
which composes a binary function with a function with pairs as values, using the uncurry function
\<open>case_prod\<close> to convert the binary function to a function with argument pairs (see
Section~\ref{holtypes-tup-funcs}). The operator names \<open>(\<circ>>)\<close> for \<open>fcomp\<close> and \<open>(\<circ>\<rightarrow>)\<close> for \<open>scomp\<close>
are only available after using the command
@{theory_text[display]
\<open>unbundle state_combinator_syntax\<close>}
on theory level.

Finite iteration of a function of type \<open>'a \<Rightarrow> 'a\<close> can be specified by the polymorphic function
@{text[display]
\<open>funpow :: nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a\<close>}
with operator name \<open>(^^)\<close> (with reversed arguments) for infix notation. Thus 
\<open>funpow 3 f = f ^^ 3 = f \<circ> f \<circ> f\<close>.
\<close>

subsubsection "Injectivity and Surjectivity"

text\<open>
For the basic function properties of injectivity, surjectivity, and bijectivity HOL provides the
predicates
@{text[display]
\<open>inj :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> \<lambda>f. \<forall>x y. f x = f y \<longrightarrow> x = y
surj :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> \<lambda>f. range f = UNIV
bij :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> \<lambda>f. inj f \<and> surj f\<close>}
and also the domain-restricted forms
@{text[display]
\<open>inj_on :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool
  \<equiv> \<lambda>f A. \<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y
bij_betw :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool
  \<equiv> \<lambda>f A B. inj_on f A \<and> image f A = B\<close>}

Injective functions can be inverted on their range. HOL provides the more general inversion
function
@{text[display]
\<open>the_inv :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)
  \<equiv> \<lambda>f y. THE x. f x = y\<close>}
which returns the argument mapped by function \<open>f\<close> to the value \<open>y\<close>. Note the use of the definite
description operator \<open>THE\<close> (see Section~\ref{holbasic-descr-definite}). If there is no such argument
(because \<open>y\<close> is not in the range of \<open>f\<close>) or if it is not unique (because \<open>f\<close> is not injective), it
causes the function to be underspecified. Thus the partial application \<open>(the_inv f)\<close> is the inverse
of an arbitrary function \<open>f\<close>. It is total but only specified for values of type \<open>'b\<close> where the
inversion exists and is unique. It is only fully specified if \<open>bij f\<close>.

Additionally there is the domain-restricted form
@{text[display]
\<open>the_inv_into :: 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)
  \<equiv> \<lambda>A f y. THE x. x \<in> A \<and> f x = y\<close>}
where the partial application \<open>(the_inv_into A f)\<close> is the inverse of \<open>f\<close> restricted to arguments in
set \<open>A\<close>. It is only fully specified if \<open>image f A = UNIV\<close> and \<open>inj_on f A\<close>.
\<close>

subsubsection "Function Updates"

text\<open>
HOL provides the function
@{text[display]
\<open>fun_upd :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)
  \<equiv> \<lambda>f a b x. if x = a then b else f x\<close>}
which returns a function where the value of a single argument \<open>a\<close> of \<open>f\<close> has been changed to \<open>b\<close>.
Note that this ``function update'' does not ``change'' the function \<open>f\<close>, it returns a new function
which differs from \<open>f\<close> only for the argument \<open>a\<close>.

HOL provides the alternative syntax
@{text[display]
\<open>f(terma\<^sub>1 := termb\<^sub>1, \<dots>, terma\<^sub>n := termb\<^sub>n)\<close>}
for the term \<open>fun_upd \<dots> (fun_upd f terma\<^sub>1 termb\<^sub>1) \<dots> terma\<^sub>n termb\<^sub>n\<close>. The changes are applied from
left to right, i.e. \<open>f(x := y, x := z) = f(x := z)\<close>.

HOL also provides an update on a set of arguments, where the new values are specified by another
function:
@{text[display]
\<open>override_on :: ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b
  \<equiv> \<lambda>f g A x. if x \<in> A then g x else f x\<close>}\<close>

subsubsection "The Type Constructor \<open>fun\<close> as a Functor"

text\<open>
The type constructor \<open>fun\<close> is no bounded natural functor. Values of type \<open>('p\<^sub>1, 'p\<^sub>2) fun\<close> can be
viewed as containers for the function values of type \<open>'p\<^sub>2\<close>. Since there may be a separate function
value for every argument value of type \<open>'p\<^sub>1\<close> the set of contained values may be arbitrary large
depending on the type \<open>'p\<^sub>1\<close>, it is not bounded.

However, \<open>fun\<close> is still a functor and has the map function
@{text[display]
\<open>map_fun :: ('q\<^sub>1 \<Rightarrow> 'p\<^sub>1) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> 'q\<^sub>2) \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> 'q\<^sub>1 \<Rightarrow> 'q\<^sub>2
  \<equiv> \<lambda>f\<^sub>1 f\<^sub>2 f = f\<^sub>1 \<circ> f \<circ> f\<^sub>2\<close>}
which lifts two functions \<open>f\<^sub>1, f\<^sub>2\<close> to a function \<open>(map_fun f\<^sub>1 f\<^sub>2)\<close> on functions and which satisfies
the laws for a functor:

@{text\<open>map_fun.id:\<close>} @{thm map_fun.id}\\
@{text\<open>map_fun.comp:\<close>}\\\hspace*{1em}@{thm map_fun.comp}

Note the different treatment of the first type parameter \<open>'p\<^sub>1\<close> by reversing the direction of the
application of function \<open>f\<^sub>1\<close>.

Additionally there are functions which lift predicates and relations (see
Section~\ref{holbasic-pred}) in a similar way as the predicators and relators described for
algebraic types in Section~\ref{holtdefs-data-bnf}. These are
@{text[display]
\<open>pred_fun :: ('p\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool
  \<equiv> \<lambda>p\<^sub>1 p\<^sub>2 f. \<forall>x. p\<^sub>1 x \<longrightarrow> p\<^sub>2 (f x)\<close>}
and
@{text[display]
\<open>rel_fun :: ('p\<^sub>1 \<Rightarrow> 'q\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> 'q\<^sub>2 \<Rightarrow> bool)
  \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> ('q\<^sub>1 \<Rightarrow> 'q\<^sub>2) \<Rightarrow> bool
  \<equiv> \<lambda>r\<^sub>1 r\<^sub>2 f g. \<forall>x y. r\<^sub>1 x y \<longrightarrow> r\<^sub>2 (f x) (g y)\<close>}
Note again the different treatment of the first type parameter \<open>'p\<^sub>1\<close> by combining it with the
second by implication \<open>\<longrightarrow>\<close> instead of conjunction.

As an example using the predicate \<open>evn\<close> from Section~\ref{holbasic-inductive-defrules}, the partial
application \<open>pred_fun evn evn\<close> is the predicate of type \<open>(nat \<Rightarrow> nat) \<Rightarrow> bool\<close> which tests whether
a function on natural numbers maps all even numbers to even numbers.
\<close>

subsubsection "BNF Functions"

text\<open>
Although the type constructor \<open>fun\<close> is no bounded natural functor, it becomes one if the first
type parameter is fixed, such as for the type \<open>(nat, 'p\<^sub>2) fun\<close> or \<open>nat \<Rightarrow> 'p\<^sub>2\<close>. It has only one
type parameter for the function values, the type of the function arguments is always the same. Now
for a function \<open>f\<close> of this type the set of contained values is simply its range \<open>range f\<close> and that
is bounded by the cardinality of the argument type.

This situation is described by saying that \<open>fun\<close> is a bounded natural functor with one ``dead''
type parameter (the first one). The second type parameter is called ``live''. In general a bounded
natural functor may have several dead and live type parameters. A set function only exists for
each live type parameter and the map function and the predicator and relator lift only functions for
the live type parameters.

Therefore \<open>fun\<close> has the set function (see Section~\ref{holtypes-set-funcs})
@{text[display]
\<open>range :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> 'p\<^sub>2 set \<equiv> \<lambda>f. {y. \<exists>x. y = f x}\<close>}
and the map function, predicator and relator can be constructed by the partial applications
@{text[display]
\<open>(map_fun id) = (\<lambda>f\<^sub>2 f x. f\<^sub>2 (f x))
(pred_fun (\<lambda>_. True)) = (\<lambda>p\<^sub>2 f. \<forall>x. p\<^sub>2 (f x))
(rel_fun (=)) = (\<lambda>r\<^sub>2 f g. \<forall>x. r\<^sub>2 (f x) (g x))\<close>}
The map function is equivalent to the composition \<open>(\<circ>)\<close>. For the predicator and relator HOL does not
define separate names. Note that they are also polymorphic for the argument type, so they can be used 
for functions of arbitrary types \<open>'p\<^sub>1 \<Rightarrow> 'p\<^sub>2\<close>. They lift a predicate or relation by applying it to
all function values.

Since functions with multiple arguments in curried form (see Section~\ref{holbasic-tuples-funarg})
have functions as intermediate result values the lifting can be iterated over multiple arguments.
For example, a relation \<open>r\<close> on the result type \<open>t\<close> can be lifted to binary functions of type
\<open>t\<^sub>1 \<Rightarrow> t\<^sub>2 \<Rightarrow> t\<close> by \<open>rel_fun (=) (rel_fun (=) r)\<close> which is equivalent to the relation on functions
\<open>\<lambda>f g. \<forall>x y. r (f x y) (g x y))\<close>.
\<close>

subsubsection "Functions for Orderings and Lattices"

text\<open>
The ordering relations (see Section~\ref{holbasic-equal-order}) are defined for functions by lifting
the ordering relations for the function values. Thus the ordering \<open>(<)\<close> on functions is equivalent
to \<open>rel_fun (=) (<)\<close> and analogously for \<open>(\<le>), (>), (\<ge>)\<close>. In other words, \<open>f < g\<close> holds if
\<open>\<forall>x. (f x) < (g x)\<close>. Note that even if \<open>(<)\<close> is a total ordering on the function values, the lifted
ordering is partial, because for some arguments the function values may be less and for other
arguments not.

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
Section~\ref{holtypes-bool-funcs} so that \<open>(\<le>)\<close> is equivalent to the implication \<open>(\<longrightarrow>)\<close>, the
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
  \<equiv> \<lambda>r\<^sub>1 r\<^sub>2 f. rel_fun r\<^sub>1 r\<^sub>2 f f\<close>}
The partial application \<open>monotone r\<^sub>1 r\<^sub>2\<close> is the predicate which tests a function whether arguments
related by \<open>r\<^sub>1\<close> produce results related by \<open>r\<^sub>2\<close>:
@{text[display]
\<open>monotone r\<^sub>1 r\<^sub>2 = (\<lambda>f. \<forall>x y. r\<^sub>1 x y \<longrightarrow> r\<^sub>2 (f x) (f y))\<close>}

The usual notion of monotonicity results when \<open>monotone\<close> is applied to the ordering relations. HOL
defines the specific predicates on functions
@{text[display]
\<open>mono :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool \<equiv> monotone (\<le>) (\<le>)
strict_mono :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool \<equiv> monotone (<) (<)
antimono :: ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool \<equiv> monotone (\<le>) (\<ge>)\<close>}

HOL also provides the domain-restricted variants:
@{text[display]
\<open>monotone_on :: 'p\<^sub>1 set \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>1 \<Rightarrow> bool) \<Rightarrow> ('p\<^sub>2 \<Rightarrow> 'p\<^sub>2 \<Rightarrow> bool)
  \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool
mono_on :: 'p\<^sub>1 set \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool
strict_mono_on :: 'p\<^sub>1 set \<Rightarrow> ('p\<^sub>1 \<Rightarrow> 'p\<^sub>2) \<Rightarrow> bool\<close>}
\<close>

(*
thm card_Un_Int
print_bundles
print_syntax
unbundle cardinal_syntax
thm card_Un_Int
lemma "card_of A = |A::(nat set)|"

declare [[show_types=true]]
lemma "mono f = monotone (\<le>) (\<le>) f" sorry

unbundle cardinal_syntax
typedef ('d, 'a) fn = "UNIV :: ('d \<Rightarrow> 'a) set "
  by simp
setup_lifting type_definition_fn
lift_definition map_fn :: "('a \<Rightarrow> 'b) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn " is "(\<circ>)" .
lift_definition set_fn :: "('d, 'a) fn \<Rightarrow> 'a set " is range .
lift_definition pred_fn :: "('a \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fn \<Rightarrow> bool " is "pred_fun (\<lambda>_. True)" .
lift_definition rel_fn :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fn \<Rightarrow> ('d, 'b) fn \<Rightarrow> bool " is "rel_fun (=)" .
bnf fn2: "('d, 'a) fn "
map: map_fn
sets: set_fn
bd: "natLeq +c card_suc | UNIV :: 'd set|"
rel: rel_fn
pred: pred_fn defer
sorry
print_theorems
print_bnfs
thm card_suc_def

functor map_fun2: map_fun sorry

datatype ('a, 'b, 'c) mydat =
  C1 'a "'b option"
  | C2 'c 'b 'a 'b
  | C3 'a "('a, 'b, 'c) mydat"

datatype ('a) mydat2 =
  C1 'a "'a option"
declare [[show_types=true]]
lemma "rel_mydat2 (BNF_Def.Grp A f) = BNF_Def.Grp {x. (set_mydat2 x \<subseteq> A)} (map_mydat2 f)" sorry
lemma "rel_mydat2 R a b =
    (\<exists>z. z \<in> { x. (set_mydat2 x \<subseteq> {(x, y)| x y. (R x y)})} \<and>
         map_mydat2 fst z = a \<and> map_mydat2 snd z = b)" using mydat2.in_rel by auto
lemma "rel_mydat R1 R2 R3 a b =
    (\<exists>z. z \<in> {x.
               (set1_mydat x \<subseteq> { (x, y)| x y. (R1 x y)} \<and>
                set2_mydat x \<subseteq> { (x, y)| x y. (R2 x y)} \<and> 
                set3_mydat x \<subseteq> { (x, y)| x y. (R3 x y)})} \<and>
         map_mydat fst fst fst z = a \<and> map_mydat snd snd snd z = b)" sorry

record ('a, 'b) myrec = fld1 :: "'a " fld2 :: "'b"
*)

subsection "Rules"
text_raw\<open>\label{holtypes-func-rules}\<close>

text\<open>
Since functions are the basic type of Isabelle there are several rules which are already built in
and need not be provided by HOL. Some of them are implicitly applied to propositions without the
need of using proof methods, such as the rewriting rule
@{text[display]
\<open>(\<lambda>x. ?P x) ?y = ?P ?y\<close>}
Many others are known by the automatic proof methods (see Section~\ref{basic-methods-auto}) so that
properties relating to functions can usually be proved by them.

The most basic rules provided by HOL about functions are

@{text\<open>ext:\<close>} @{thm ext}\\
@{text\<open>fun_cong:\<close>} @{thm fun_cong}\\
@{text\<open>arg_cong:\<close>} @{thm arg_cong}\\
@{text\<open>cong:\<close>} @{thm cong}\<close>

subsubsection "Rules About Functions on Functions"

text\<open>
Reasoning about the functions described in Section~\ref{holtypes-func-funcs} can often be done by
substituting their definition and then using automatic proof methods. Alternatively HOL provides
many rules for direct reasoning about these functions, such as

@{text\<open>comp_assoc:\<close>} @{thm comp_assoc}\\
@{text\<open>image_comp:\<close>} @{thm image_comp}

and in particular introduction rules (see Section~\ref{basic-methods-rule}) such as

@{text\<open>injI:\<close>} @{thm injI}\\
@{text\<open>surjI:\<close>} @{thm surjI}\\
@{text\<open>bijI:\<close>} @{thm bijI}\\
@{text\<open>monoI:\<close>} @{thm monoI}

the destruction (see Section~\ref{basic-methods-forward}) and elimination
(see Section~\ref{basic-case-elim}) rules

@{text\<open>comp_eq_dest:\<close>} @{thm comp_eq_dest}\\
@{text\<open>injD:\<close>} @{thm injD}\\
@{text\<open>monoD:\<close>} @{thm monoD}\\
@{text\<open>comp_eq_elim:\<close>}\\\hspace*{1em}@{thm comp_eq_elim}\\
@{text\<open>surjE:\<close>} @{thm surjE}\\
@{text\<open>monoE:\<close>} @{thm monoE}

and the simplifier rules (see Section~\ref{basic-methods-simp})

@{text\<open>comp_apply:\<close>} @{thm comp_apply}\\
@{text\<open>fun_upd_apply:\<close>}\\\hspace*{1em}@{thm fun_upd_apply}\\
@{text\<open>bij_id:\<close>} @{thm bij_id}\\
@{text\<open>override_on_apply_in:\<close>}\\\hspace*{1em}@{thm override_on_apply_in}\<close>

section "Relations"
text_raw\<open>\label{holtypes-rel}\<close>

text\<open>
**todo**
\<close>

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