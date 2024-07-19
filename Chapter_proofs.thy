theory Chapter_proofs
  imports Chapter_theories
begin

chapter "Isabelle Proofs"
text_raw\<open>\label{proof}\<close>

text \<open>
Every proposition stated as a fact in an Isabelle theory must be proved
immediately by specifying a proof for it. A proof may have a complex structure of several steps 
and nested subproofs, its structure is part of the outer syntax.
\<close>

section "Maintaining Proof State"
text_raw\<open>\label{proof-state}\<close>

text \<open>
Usually it is necessary during a proof to collect information for later use in the proof. For every
proof such state\index{proof!state} is maintained in two structures: the ``proof context''\index{proof!context} and the ``goal state''\index{goal!state}.
At the end of a proof all proof state is disposed, only the proved fact remains in the enclosing
environment.
\<close>

subsection "Proof Context"
text_raw\<open>\label{proof-state-context}\<close>

text \<open>
The proof context is similar to a temporary theory which collects facts and other proof elements.
It may contain
 \<^item> Facts: as usual, facts are valid propositions. However, they need not be globally valid, 
  they can be assumed to be only valid locally\index{fact!local $\sim$} during the proof. As in a theory facts and fact
  sets may be named in a proof context.
 \<^item> Fixed variables: fixed variables\index{variable!fixed $\sim$}\index{fixed variable} are used to denote the ``arbitrary but fixed'' objects 
  often used in a proof. They can be used in all facts in the same proof context. They
  can be roughly compared to the constants in a theory.
 \<^item> Term abbreviations:\index{abbreviation!for term}\index{term!abbreviation} these are names introduced locally for terms. They can be roughly compared
  to abbreviations defined in a theory. Using such names for terms
  occurring in propositions it is often possible to denote propositions in a more concise form.

As in a theory the names for facts and fixed variables have the same form, they can always be
distinguished by their usage context. The names for term abbreviations have the form of unknowns (see
Section~\ref{theory-theorem-unknowns}) and are thus always different from variable names.

Since the proof context is usually populated by explicitly specifying its elements it is visible
in the proof text and also in the session document. In the interactive editor a list of all elements
of the proof context at the cursor position can be obtained in the Query panel\index{panel!query $\sim$}
(see Section~\ref{system-jedit-query}) in tab ``Print Context'' by checking ``terms'' (for term
abbreviations) and/or ``theorems'' (for facts).
\<close>

subsection "Goal State"
text_raw\<open>\label{proof-state-goal}\<close>

text \<open>
The goal state\index{goal!state} is used to collect propositions which have not yet been proved. It is used in the
form of a ``to-do list''. It is the duty of a proof to prove all goals in its goal state.
During the proof goals may be removed from the goal state or may be added. A proof may be terminated
when its goal state is empty.

The content of the goal state is not maintained by explicit specifications of the proof writer, it
is updated implicitly by the Isabelle proof mechanism. As a consequence it is usually not visible
in the session document. In the interactive editor it is displayed in the State panel\index{panel!state $\sim$} (see
Section~\ref{system-jedit-state}) or in the Output panel\index{panel!output $\sim$} (see Section~\ref{system-jedit-output}).

If a subproof is nested in another proof the goal state of the inner proof hides the goal state of
the outer proof until the inner proof is complete.
\<close>

subsection "Initial Proof State"
text_raw\<open>\label{proof-state-initial}\<close>

text \<open>
The initial proof state\index{proof!state!initial $\sim$} in a theorem of the form
@{theory_text[display]
\<open>theorem "\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<^sub>1 &&& \<dots> &&& C\<^sub>h" \<proof>\<close>}
has the proposition \<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close>  as the only goal in the goal
state and an empty proof context. In particular, the explicitly bound variables\index{variable!bound $\sim$}
\<open>x\<^sub>1 \<dots> x\<^sub>m\<close> are not added as fixed variables to the proof state.

If the proposition of a theorem is specified in structured form
@{theory_text[display]
\<open>theorem "C" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
or
@{theory_text[display]
\<open>theorem 
  fixes x\<^sub>1 \<dots> x\<^sub>m assumes "A\<^sub>1" \<dots> "A\<^sub>n" shows "C" \<proof>\<close>}
the initial goal state only contains the conclusion \<open>C\<close>, whereas the initial proof context contains
the assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> as (assumed) facts and the variables \<open>x\<^sub>1 \<dots> x\<^sub>m\<close> as fixed variables.

Since variables occurring free in an \<open>A\<^sub>i\<close> or in \<open>C\<close>\index{free occurrence}\index{variable!free occurrence of $\sim$} (i.e., not being explicitly bound by \<open>\<And>\<close>) are
automatically by a \<^theory_text>\<open>for\<close> part (see Section~\ref{theory-theorem-spec}), they will also be added to
the initial proof state as fixed variables.

If the theorem has multiple conclusions such as
@{theory_text[display]
\<open>theorem "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
the initial goal state contains the single conclusion \<open>C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close>, i.e., the ``meta
conjunction''\index{conjunction!meta $\sim$} of the separate conclusions. This will be split into separate goals for the individual
conclusions upon the first application of a proof method (see Chapter~\ref{methods}).\<close>

subsubsection "Assumption Naming"

text\<open>
Both structured forms support naming the assumptions\index{name!for assumption}\index{assumption!name} in the proof context.
Every assumption group\index{assumption!group} separated by \<^theory_text>\<open>and\<close> may be given a name, i.e., the assumptions
may be specified in the form
@{theory_text[display]
\<open>if name\<^sub>1: "A\<^sub>1\<^sub>,\<^sub>1" \<dots> "A\<^latex>\<open>$_{1,m_1}$\<close>" and \<dots> and name\<^sub>n: "A\<^sub>n\<^sub>,\<^sub>1" \<dots> "A\<^latex>\<open>$_{n,m_n}$\<close>"\<close>}
or
@{theory_text[display]
\<open>assumes name\<^sub>1: "A\<^sub>1\<^sub>,\<^sub>1" \<dots> "A\<^latex>\<open>$_{1,m_1}$\<close>" and \<dots> and name\<^sub>n: "A\<^sub>n\<^sub>,\<^sub>1" \<dots> "A\<^latex>\<open>$_{n,m_n}$\<close>"\<close>}
respectively, in the same way as the conclusion groups may be named. However, the assumption names
are only valid in the proof context, whereas the conclusion names are only valid outside of the
proof context after the proof is complete.

Additionally, Isabelle always automatically names the assumptions in all groups together. For the
structured form beginning with \<^theory_text>\<open>if\<close> it uses the name \<open>that\<close>\index{that (assumption name)}, for the structured form beginning
with \<^theory_text>\<open>assumes\<close> it uses the name \<open>assms\<close>\index{assms (assumption name)}.

Since the assumption names are only defined in the proof context they can only be used locally
in the proof of the theorem. Therefore, if the general structured form of a proposition beginning 
with \<^theory_text>\<open>if\<close> is used in a context where no proof is required, such as in an \<^theory_text>\<open>assume\<close> statement (see
Section~\ref{proof-assume-add}), it is not possible to specify names for the assumption groups.
\<close>

section "Proof Procedure"
text_raw\<open>\label{proof-proc}\<close>

text \<open>
Assume you want to prove a derivation rule \<open>A \<Longrightarrow> C\<close> with a single assumption \<open>A\<close> and a single
conclusion \<open>C\<close>. There are several different ways how to proceed.\<close>

subsection "Constructing a Proof"
text_raw\<open>\label{proof-proc-construct}\<close>

text\<open>
The basic procedure to build a proof for it is to construct a sequence of the form
\<open>F\<^sub>1 \<Longrightarrow> F\<^sub>2, F\<^sub>2 \<Longrightarrow> F\<^sub>3, F\<^sub>3 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<^sub>-\<^sub>1, F\<^sub>n\<^sub>-\<^sub>1 \<Longrightarrow> F\<^sub>n\<close>  where \<open>F\<^sub>1\<close> matches with \<open>A\<close>
and \<open>F\<^sub>n\<close> matches with \<open>C\<close> (for the exact meaning of ``matches'' see Section~\ref{proof-proc-unif}
below). The sequence is constructed from derivation rules \<open>R\<^sub>i\<close> for \<open>i=1\<dots>n-1\<close>
which are already known to be valid (i.e., facts). Every rule \<open>R\<^sub>i\<close> has the form \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>
where \<open>RA\<^sub>i\<close> denotes the assumption of the rule and \<open>RC\<^sub>i\<close> denotes its conclusion. Every assumption
\<open>RA\<^sub>i\<close> matches with \<open>F\<^sub>i\<close> in the sequence and every conclusion \<open>RC\<^sub>i\<close> matches with \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>.

The sequence can be constructed from left to right (called ``forward reasoning''\index{forward reasoning}\index{reasoning!forward $\sim$}) or from right 
to left (called ``backward reasoning''\index{backward reasoning}\index{reasoning!backward $\sim$}) or by a combination of both. 

Consider the rule \<open>(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close>. A proof can be constructed from the two 
example rules \<open>example1\<close> and \<open>example2\<close> from the previous sections as the sequence
\<open>(x::nat) < 5 \<Longrightarrow> 2*x \<le> 2*5, 2*x \<le> 2*5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close> consisting of three facts.\<close>

subsubsection "Forward Reasoning"

text\<open>
Forward reasoning starts by assuming \<open>A\<close> to be the local fact \<open>F\<^sub>1\<close> and incrementally constructs the
sequence from it. An intermediate result is a part \<open>A, F\<^sub>2, \<dots>, F\<^sub>i\<close> of
the sequence, here \<open>F\<^sub>i\<close> is the ``current fact''\index{fact!current $\sim$}. A forward reasoning step consists of
stating a proposition \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and proving it to be a new local fact from the current fact \<open>F\<^sub>i\<close> 
using a valid rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>. The step results in the extended sequence
\<open>A, F\<^sub>2, \<dots>, F\<^sub>i, F\<^sub>i\<^sub>+\<^sub>1\<close> with new current fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. When a step successfully 
proves a current fact \<open>F\<^sub>n\<close> which matches the conclusion \<open>C\<close> the proof is complete.\<close>

subsubsection "Backward Reasoning"

text\<open>
Backward reasoning starts at the conclusion \<open>C\<close> and incrementally 
constructs the sequence from it backwards. An intermediate result is a part \<open>F\<^sub>i, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close> of the
sequence, here \<open>F\<^sub>i\<close> is the ``current goal''\index{goal!current $\sim$}. A backward reasoning step consists of constructing a
new current goal \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> and the extended sequence \<open>F\<^sub>i\<^sub>-\<^sub>1, F\<^sub>i, \<dots>, F\<^sub>n\<^sub>-\<^sub>1, C\<close> using a valid
rule \<open>RA\<^sub>i\<^sub>-\<^sub>1 \<Longrightarrow> RC\<^sub>i\<^sub>-\<^sub>1\<close>. When a step produces a new current goal \<open>F\<^sub>1\<close>, which matches the assumption
\<open>A\<close>, the proof is complete.
\<close>

subsection "Unification"
text_raw\<open>\label{proof-proc-unif}\<close>

text \<open>
The matching at the beginning and end of the sequence and when joining the used rules is done
by ``unification''\index{unification}. Two propositions \<open>P\<close> and \<open>Q\<close> are unified by substituting terms 
for unknowns\index{unknown} in \<open>P\<close> and \<open>Q\<close> so that the results become syntactically equal.

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

subsection "Storing Facts During a Proof"
text_raw\<open>\label{proof-proc-store}\<close>

text \<open>
In a proof for a derivation rule \<open>A \<Longrightarrow> C\<close> the assumption \<open>A\<close>, the conclusion \<open>C\<close> and the
intermediate facts \<open>F\<^sub>1, F\<^sub>2, \<dots>, F\<^sub>n\<close> constructed by the proof steps must be stored. There
are mainly two ways how this can be done in an Isabelle proof.\<close>

subsubsection "Storing Facts in the Context"

text\<open>
The first way is to store the facts at the beginning of the sequence in the proof context and
the facts at the end of the sequence in the goal state. Initially, \<open>A\<close> is the only fact in the
proof context\index{proof!context} and \<open>C\<close> is the only goal in the goal state\index{goal!state}. A forward reasoning step consists of
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
irrelevant for detecting whether a proof is complete.\<close>

subsubsection "Storing Facts as Assumptions in the Goal State"

text\<open>
The second way is to store all facts in the goal state by using a current goal of the form
\<open>\<lbrakk>F\<^sub>1; \<dots>; F\<^sub>i\<rbrakk> \<Longrightarrow> F\<^sub>i\<^sub>+\<^sub>j\<close>, i.e., a derivation rule. The proof context
is not used at all. Initially, the goal state contains the goal \<open>A \<Longrightarrow> C\<close>. A forward reasoning step
consists of adding fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> as assumption to the current goal and proving its validness as above.
A backward reasoning step consists of replacing the conclusion \<open>F\<^sub>i\<^sub>+\<^sub>j\<close> of the current goal by \<open>F\<^sub>i\<^sub>+\<^sub>j\<^sub>-\<^sub>1\<close>
and proving that it implies \<open>F\<^sub>i\<^sub>+\<^sub>j\<close> as above. The proof is complete when the conclusion of the current
goal unifies with one of its assumptions.

Note that these two ways correspond to the initial proof states\index{proof!state!initial $\sim$} prepared by the different forms
of theorems. The basic form \<^theory_text>\<open>theorem "A \<Longrightarrow> C"\<close> puts \<open>A \<Longrightarrow> C\<close> into the goal state and leaves the
proof context empty, as required for the second way. The structured forms, such as 
\<^theory_text>\<open>theorem "C" if "A"\<close> put \<open>A\<close> into the proof context and \<open>C\<close> into the goal state, as required for
the first way.
\<close>

subsection "Multiple Assumptions"
text_raw\<open>\label{proof-proc-multassms}\<close>

text \<open>
If the rule to be proved has more than one assumption \<open>A\<close> the sequence to be constructed becomes
a tree where the branches start at (copies of) the assumptions \<open>A\<^sub>1,\<dots>,A\<^sub>n\<close> and merge to finally 
lead to the conclusion \<open>C\<close>. Two branches which end in facts \<open>F\<^sub>1\<^sub>,\<^sub>n\<close> and \<open>F\<^sub>2\<^sub>,\<^sub>m\<close> are joined by
a step \<open>\<lbrakk>F\<^sub>1\<^sub>,\<^sub>n;F\<^sub>2\<^sub>,\<^sub>m\<rbrakk> \<Longrightarrow> F\<^sub>1\<close> to a common branch which continues from fact \<open>F\<^sub>1\<close>.

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

subsection "Proving from External Facts"
text_raw\<open>\label{proof-proc-ext}\<close>

text \<open>
The branches in the fact tree need not always start at an assumption \<open>A\<^sub>i\<close>, they may also start
at an ``external'' fact which is not part of the local proof context. In such cases the used 
external facts\index{fact!external $\sim$} are referenced by their names. In that way a proof can use facts from the 
enclosing theory and a subproof can use facts from the enclosing proof(s) and the enclosing 
toplevel theory.

In particular, if the proposition of a theorem has no assumptions, i.e., the proposition is a
formula and consists only of the conclusion \<open>C\<close>, every proof must start at one or more external facts
(if \<open>C\<close> is no tautology which is valid by itself).
\<close>

section "Basic Proof Structure"
text_raw\<open>\label{proof-struct}\<close>

text \<open>
A proof\index{proof} is written in outer syntax and mainly describes how the fact tree is constructed which
leads from the assumptions or external facts to the conclusion.
\<close>

subsection "Statements and Methods"
text_raw\<open>\label{proof-struct-stat}\<close>

text \<open>
There are two possible operations for modifying the proof state: statements and method applications.

A statement\index{statement} adds one or more elements to the proof context. In particular,
a statement may ``state a fact'', i.e., add a fact to the proof context, this is the reason for
its name. A statement normally does not modify the goal state, there is one specific statement
which may remove a goal from the goal state.

A method application\index{method!application} modifies the goal state but normally leaves the proof context
unchanged. The goal state is always modified so that, if all goals in the new state can be proved,
then also all goals in the old state can be proved. This kind of goal state modification is also
called a ``refinement step''\index{refinement step}.\<close>

subsubsection "Proof Mode"

text\<open>
When writing a proof the ``proof mode''\index{proof!mode} determines the kind of operation which may be written next:
whether a statement (mode: \<open>proof(state)\<close>)\index{proof(state) (proof mode)} or a method application (mode: \<open>proof(prove)\<close>)\index{proof(prove) (proof mode)} is
admissible.

At the beginning of a proof the mode is always \<open>proof(prove)\<close>, i.e., a method application is expected.
In the course of the proof it is possible to switch to mode \<open>proof(state)\<close> for entering statements, 
but not back again. After switching to statement mode the proof must be completed without further
modifications to the goal state other than removing goals, only at the end a last method may be
applied.

However, for every statement that states a fact a (sub-)proof must be specified, which
again starts in mode \<open>proof(prove)\<close>. This way it is possible to freely switch between 
both modes in the course of a proof with nested subproofs.\<close>

subsubsection "Choosing Between Statements and Methods"

text\<open>
A backward reasoning step always modifies the goal state, therefore it must be expressed by a
method application. A forward reasoning step may be expressed by a statement, if intermediate facts
are stored in the proof context. If intermediate facts are stored as assumptions in rules in the
goal state, forward reasoning steps must also be expressed by method applications. 

This implies that a sequence of statements can only represent a proof by forward reasoning where
intermediate facts are stored in the proof context, whereas a sequence of method applications can
represent an arbitrary proof where all facts are stored using rules in the goal state.

As described in Section~\ref{proof-state-context} statements have the advantage that the facts added
to the proof context are explicitly specified by the proof writer and are visible in the session
document. That makes it easier to write and read a proof which consists only of statements. Method
applications specify an operation on the goal state by name, the resulting new goal state is
determined by Isabelle. It is visible for the proof writer in the interactive editor, but it is not
visible in the session document for a reader of the proof. Therefore proofs consisting of method
applications are difficult to understand and the proof writer must anticipate the effect of a
method on the goal state when writing a proof step.
\<close>

subsection "Proof Syntax"
text_raw\<open>\label{proof-struct-syntax}\<close>

text \<open>
If \<open>MA\<^sub>i\<close> denote method applications and \<open>ST\<^sub>i\<close> denote statements, the general form of a proof is
@{theory_text[display]
\<open>MA\<^sub>1 \<dots> MA\<^sub>n
proof `MA\<^sub>n\<^sub>+\<^sub>1`
  ST\<^sub>1 \<dots> ST\<^sub>m
qed `MA\<^sub>n\<^sub>+\<^sub>2`\<close>}\index{proof (keyword)}\index{qed (keyword)}
The last step \<open>MA\<^sub>n\<^sub>+\<^sub>2\<close> may be omitted if it is not needed.

The part \<^theory_text>\<open>proof `MA\<^sub>n\<^sub>+\<^sub>1`\<close> switches from method application mode \<open>proof(prove)\<close> to statement mode
\<open>proof(state)\<close>.\<close>
 
subsubsection "Proof Scripts"

text\<open>
The part \<^theory_text>\<open>proof \<dots> qed\<close> can be omitted and replaced by \<^theory_text>\<open>done\<close>, then the proof only consists of 
method applications and has the form \<^theory_text>\<open>MA\<^sub>1 \<dots> MA\<^sub>n done\<close>. Such proofs are called ``proof scripts''\index{proof!script}.

Since a proof script does not contain statements it cannot use the proof context to store facts.
Proof scripts are intended to store facts as assumptions in the goal state or to apply only
backward reasoning, where no intermediate facts need to be stored in addition to the goals
(see Section~\ref{proof-proc-store}).\<close>

subsubsection "Structured Proofs"

text\<open>
If the method applications \<open>MA\<^sub>1 \<dots> MA\<^sub>n\<close> are omitted the proof only consists of 
the statements part and has the form
@{theory_text[display]
\<open>proof `MA\<^sub>1`
  ST\<^sub>1 \<dots> ST\<^sub>m
qed `MA\<^sub>2`\<close>}
where \<open>MA\<^sub>2\<close> can also be omitted. Such proofs are called ``structured proofs''\index{proof!structured $\sim$}\index{structured proof} and the syntactic
elements used to write them are denoted as ``Isar sublanguage''\index{Isar language} of the Isabelle outer syntax.

Since structured proofs consist nearly completely of statements, they are intended to use forward
reasoning and store all assumptions and intermediate facts in the proof context.

A structured proof can be so simple, that it has no statements. For this case the syntax
@{theory_text[display]
\<open>by `MA\<^sub>1` `MA\<^sub>2`\<close>}\index{by (keyword)}
abbreviates the form \<^theory_text>\<open>proof `MA\<^sub>1` qed `MA\<^sub>2`\<close>. Again, \<open>MA\<^sub>2\<close> can be omitted which
leads to the form
@{theory_text[display]
\<open>by `MA\<^sub>1`\<close>}
In this form the proof consists of a single method application which directly leads 
from the assumptions and used external facts to the conclusion \<open>C\<close>.\<close>

subsubsection "Use Proof Scripts or Structured Proofs?"

text\<open>
As described in the previous section, a structured proof is usually easier to read and write
than a proof script, since in the former case the sequence of the facts \<open>F\<^sub>i\<close> is explicitly
specified in the proof text, whereas in the latter case the sequence of the facts \<open>F\<^sub>i\<close> is
implicitly constructed and the proof text specifies only the methods.

However, since every statement for a forward reasoning step again requires a proof as its part (a
``subproof'' for the stated fact), no proof can be written using statements alone. The main idea of
writing ``good'' proofs is to use nested structured proofs\index{proof!nested $\sim$} until every subproof is simple enough
to be done in a single method application, i.e., the applied method directly goes from the 
assumptions to the conclusion of the subproof. Such a simple proof can always be written in
the form \<^theory_text>\<open>by `MA`\<close>.
\<close>

subsection "Bogus Proofs"
text_raw\<open>\label{proof-struct-bogus}\<close>

subsubsection "Fake Proofs"

text\<open>
A proof can also be specified as
@{theory_text[display]
\<open>sorry\<close>}\index{sorry (keyword)}
This is a ``fake proof''\index{proof!fake $\sim$}\index{fake proof} which turns the proposition to a fact without actually proving it.

A fake proof can be specified at any point in method application mode, so it can be used to
abort a proof script in the form \<^theory_text>\<open>MA\<^sub>1 \<dots> MA\<^sub>n sorry\<close>.

A structured proof in statement mode cannot be aborted in this way, however, subproofs
can be specified as fake proofs. This makes it possible to interactively develop a structured
proof in a top-down way, by first stating all required facts for the sequence from the assumptions
to the goal with fake subproofs and then replacing the fake proofs by actual subproofs.

Fake proofs are dangerous. Isabelle blindly registers the proposition as valid, so that it can be
used for other proofs. If it is not valid, everything can be proved from it. That sounds nicely but
is not what you really want.\<close>

subsubsection "Aborted Proofs"

text\<open>
There is a second way to abort a proof script by specifying a proof\index{proof!aborted $\sim$} as
@{theory_text[display]
\<open>oops\<close>}\index{oops (keyword)}
Other than by using \<open>sorry\<close> Isabelle will \<^emph>\<open>not\<close> turn the proposition to a fact, instead, it
ignores it. This can be used to document in a theory that you have tried to prove a proposition
but you did not succeed.
\<close>

subsection "Nested Proof Contexts"
text_raw\<open>\label{proof-struct-nesting}\<close>

text \<open>
Instead of a single proof context a proof may use a set of nested proof contexts\index{proof!context!nested $\sim$}, starting
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
block structure\index{block structure}: A name can be redefined in a nested context, then the named object in the outer
context becomes inaccessible (``shadowed'')\index{name!shadowed $\sim$} in the inner context, but becomes accessible again when
the inner context ends.\<close>

subsubsection "Sequencing Nested Contexts"

text\<open>
When two nested contexts follow each other immediately, this has the effect of ``clearing''
the content of the inner contexts: the content of the first context is removed and the second
context starts being empty. This can be denoted by the keyword
@{theory_text[display]
\<open>next\<close>}\index{next (keyword)}
which can be thought of being equivalent to a pair \<open>} {\<close> of adjacent braces.\<close>

subsubsection "Automatic Nesting of Statements"

text\<open>
Moreover the syntax \<^theory_text>\<open>proof `method\<^sub>1` ST\<^sub>1 \<dots> ST\<^sub>n qed `method\<^sub>2`\<close> automatically wraps the statements
\<open>ST\<^sub>1 \<dots> ST\<^sub>n\<close> in a nested context. Therefore it is possible to denote a structured proof 
which only consists of a sequence of nested contexts without braces as
@{theory_text[display]
\<open>proof `method\<^sub>1`
  ST\<^sub>1\<^sub>,\<^sub>1 \<dots> ST\<^latex>\<open>$_{1,m_1}$\<close> next ST\<^sub>2\<^sub>,\<^sub>1 \<dots> ST\<^latex>\<open>$_{2,m_2}$\<close> next \<dots> next ST\<^sub>n\<^sub>,\<^sub>1 \<dots> ST\<^latex>\<open>$_{n,m_n}$\<close>
qed `method\<^sub>n\<^sub>+\<^sub>2`\<close>}
where each occurrence of \<^theory_text>\<open>next\<close> clears the content of the inner context.

Another consequence of this wrapping is that no statement can add elements directly to the outermost
proof context. The outermost proof context\index{proof!context!outermost $\sim$} can only be filled by the initializations done by the
structured theorem forms as described in Section~\ref{proof-state-initial}. The resulting content of
the context is not affected by clearing nested contexts and remains present until the end of the
proof.

Also the goal state of a proof is not affected by the begin or end of a nested context. The goal
state can be considered to be in the scope of the outermost context, it may use fixed variables
from it. However, it is outside of all nested contexts and cannot contain elements from them.
\<close>

subsection "Subproofs"
text_raw\<open>\label{proof-struct-sub}\<close>

text \<open>
A subproof\index{subproof}\index{proof!sub-} takes a single goal and solves it as part of another proof. It has its own goal state
which hides the goal state of the enclosing proof until the subproof is complete.

The outermost proof context used by the subproof is nested in the context of the
enclosing proof, therefore all content of the enclosing proof context is available there and can be
referenced by name, as long as the name is not shadowed by a redefinition in the subproof.\<close>

subsubsection "Kinds of Subproofs"

text\<open>
There are mainly two kinds of subproofs: specifying a new goal which becomes a fact in the proof
context after proving it, or proving a goal which is already in the goal state of the enclosing
proof.

The first kind of subproof occurs as part of some statements, as described in
Section~\ref{proof-statefact}.

The second kind of subproof has the form
@{theory_text[display]
\<open>subgoal \<proof>\<close>}\index{subgoal (keyword)}
and may be specified in method application mode \<open>proof(prove)\<close> in place of a single method
application. Its initial goal state contains a copy of the first goal from the goal state of the
enclosing proof. If the subproof is successfully terminated it removes that goal from the goal state
of the enclosing proof.\<close>

subsubsection "Structured Subproofs"

text\<open>
There is also the ``structured form''
@{theory_text[display]
\<open>subgoal premises name \<proof>\<close>}\index{premises (keyword)}
If the goal processed by the subproof is a derivation rule \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> it takes the
assumptions \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close>, and adds them as assumed facts into the outermost proof context of the
subproof, like the structured forms of theorems do for their assumptions (see
Section~\ref{proof-state-initial}). If \<open>name\<close> is specified it is used for naming the set of
assumptions, if it is omitted the default name \<open>prems\<close>\index{prems (assumption name)} is used.

Using this form a subproof can be written as a structured proof which stores its facts
in its proof context, although the enclosing proof is a proof script and stores its facts as rule
assumptions in the goal state.
\<close>

section "Method Application"
text_raw\<open>\label{proof-method}\<close>

text \<open>
A method application\index{method!application} mainly specifies a proof method to be applied.
\<close>

subsection "Proof Methods"
text_raw\<open>\label{proof-method-methods}\<close>

text \<open>
Proof methods\index{proof!method} are basically denoted by method names\index{method!name}\index{name!for method}, such as \<^theory_text>\<open>standard\<close>, \<^theory_text>\<open>simp\<close>, or \<^theory_text>\<open>rule\<close>. A
proof method name can also be a symbol, such as \<open>-\<close>.

A method may have arguments\index{method!argument}, then it usually must be delimited by parentheses such as in \<open>(rule
example1)\<close> or \<^theory_text>\<open>(simp add: example2)\<close>, where \<open>example1\<close> and \<open>example2\<close> are fact names.

Isabelle supports a large number of proof methods. A selection of proof methods used in
this manual is described in Chapter~\ref{methods}. 
\<close>

subsection "Method Application"
text_raw\<open>\label{proof-method-apply}\<close>

text \<open>
A standalone method application step is denoted as
@{theory_text[display]
\<open>apply method\<close>}\index{apply (keyword)}
where \<open>method\<close> denotes the proof method to be applied, together with its arguments.

The method applications which follow \<^theory_text>\<open>proof\<close> and \<^theory_text>\<open>qed\<close> in a structured proof
are simply denoted by the applied method. Hence the general form of a proof is 
@{theory_text[display]
\<open>apply `method\<^sub>1` \<dots> apply `method\<^sub>n`
proof `method\<^sub>n\<^sub>+\<^sub>1`
  ST\<^sub>1 \<dots> ST\<^sub>m
qed `method\<^sub>n\<^sub>+\<^sub>2`\<close>}
where \<open>ST\<^sub>1 \<dots> ST\<^sub>m\<close> are statements. The method \<open>method\<^sub>n\<^sub>+\<^sub>1\<close> is called the ``initial method''\index{method!initial $\sim$}
of the structured proof part.
\<close>

section "Stating Facts"
text_raw\<open>\label{proof-statefact}\<close>

text \<open>
The most basic kind of statements is used to add a fact to the proof context.
\<close>

subsection "Adding a Fact to the Proof Context"
text_raw\<open>\label{proof-statefact-have}\<close>

text \<open>
A fact is added to the (innermost enclosing) proof context by a statement of the form
@{theory_text[display]
\<open>have "prop" \<proof>\<close>}\index{have (keyword)}
where \<open>prop\<close> is a proposition in inner syntax and \<^theory_text>\<open>\<proof>\<close> is a (sub-) proof for it. This form
is similar to the specification of a theorem in a theory and has a similar effect in the local 
proof context.

As for a theorem the fact can be named:
@{theory_text[display]
\<open>have name: "prop" \<proof>\<close>}
The scope of the name is the innermost proof context enclosing the statement. In their scope named
facts can be displayed and searched as described for theorems in Section~\ref{theory-theorem-search}.

As for a theorem, if the fact is a derivation rule with possibly multiple conclusions it may also
be specified in structured form\index{structured form}:
@{theory_text[display]
\<open>have "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m \<proof>\<close>}
where the conclusions,  assumptions and variables may be grouped by \<^theory_text>\<open>and\<close>,  conclusion and  assumption
groups may be named, and a type may be specified for each variable group.
 
Note, however, that the structured form using \<^theory_text>\<open>fixes\<close>, \<^theory_text>\<open>assumes\<close>, and \<^theory_text>\<open>shows\<close> (see 
Section~\ref{theory-theorem-altsynt}) is not available for stating facts in a proof.

The \<^theory_text>\<open>have\<close> statement is called a ``goal statement''\index{goal!statement}, because it states the
proposition \<open>prop\<close> as a (local) goal which is then proved by the subproof \<^theory_text>\<open>\<proof>\<close>.

Note that  the names given to facts by naming conclusion groups cannot be used to access them in the
subproof, because they  are only assigned after the proof has been finished, whereas names given to
assumption groups can only be used in the subproof because their scope is the proof context of the
subproof.
\<close>

subsection "Proving a Goal"
text_raw\<open>\label{proof-statefact-goal}\<close>

text \<open>
A proof using only forward reasoning ends, if the last stated fact \<open>F\<^sub>n\<close> unifies with the conclusion
\<open>C\<close>. If the facts are stored in the proof context, \<open>F\<^sub>n\<close> will be added by a statement. Therefore
a special form of stating a fact exists, which, after proving the fact, tries to unify it with a
goal in the goal state of the enclosing proof, and, if successful, removes the goal from that goal
state. This is done by the statement
@{theory_text[display]
\<open>show "prop" \<proof>\<close>}\index{show (keyword)}
which is the only statement which may affect the goal state\index{goal!state} of the enclosing proof. Its syntax is
the same as for \<^theory_text>\<open>have\<close>, including naming and structured form. Like \<^theory_text>\<open>have\<close> it is also called a
``goal statement''\index{goal!statement}.\<close>

subsubsection "Exporting the Fact"

text\<open>
As described in Section~\ref{proof-struct-nesting}, statements are always wrapped by a nested proof
context. When the \<^theory_text>\<open>show\<close> statement tries to unify its fact with a goal from the goal state it
replaces all variables fixed\index{variable!fixed $\sim$} in an enclosing nested proof context by unknowns\index{unknown} (which is called
``exporting the fact''\index{fact!export} from the proof context) so that they can match arbitrary subterms (of the
correct type) in the goal.

If the unification of the exported fact with some goal is not successful the step is erroneous and
the proof cannot be continued, in the interactive editor an error message is displayed.

If a goal has the form of a derivation rule, the exported fact is only unified with the conclusion
of the goal. If also the exported fact is a derivation rule, additionally each of its assumptions
must unify with an assumption of the goal.

This is a special case of a refinement step\index{refinement step} in the sense of Section~\ref{proof-struct-stat}.
Whenever the exported fact can be proved, also the matching goal can be proved. Since the exported
fact has just been proved by the subproof, the matching goal has been proved as well and may be
removed from the enclosing goal state. So the condition for a successful \<^theory_text>\<open>show\<close> statement can be
stated as ``the exported fact must refine a goal'' (this term is used in error messages).

To test whether a proposition refines a goal in the enclosing goal state, a
\<^theory_text>\<open>show\<close> statement can be specified with a fake proof\index{proof!fake $\sim$}\index{fake proof} (see Section~\ref{proof-struct-bogus}):
@{theory_text[display]
\<open>show "prop" sorry\<close>}
If that statement is accepted, the proposition refines a goal and removes it. Do not forget to
replace the fake proof by a genuine proof to make sure that the proposition is actually valid.\<close>

subsubsection "The term abbreviation \<open>?thesis\<close>"

text\<open>
Note that in a proof using only forward reasoning the proposition \<open>prop\<close> in a \<^theory_text>\<open>show\<close> statement is
the same proposition which has been specified as conclusion \<open>C\<close> in the proposition \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>
which shall be proved by the proof. To avoid repeating it, Isabelle automatically provides the
term abbreviation \<open>?thesis\<close>\index{?thesis (term abbreviation)} for it in the outermost proof context. So in the simplest case the last
step of a structured proof by forward reasoning can be written as
@{theory_text[display]
\<open>show ?thesis \<proof>\<close>}
The abbreviation \<open>?thesis\<close> is a single identifier, therefore it needs not be quoted. If the
proposition has multiple conclusions the abbreviation \<open>?thesis\<close> is not introduced.

If, however, the application of the initial method\index{method!initial $\sim$} \<open>method\<close> in a structured proof \<^theory_text>\<open>proof method \<dots> \<close> 
modifies the original goal, this modification is not reflected in \<open>?thesis\<close>. So a statement \<^theory_text>\<open>show 
?thesis \<proof>\<close> will usually not work, because \<open>?thesis\<close> no more refines the  
modified goal. Instead, the proof writer must know the modified goal and specify it
explicitly as proposition in the \<^theory_text>\<open>show\<close> statement. If the \<open>method\<close> splits the goal into several new 
goals, several \<^theory_text>\<open>show\<close> statements may be needed to remove them.\<close>
 
section "Facts as Proof Input"
text_raw\<open>\label{proof-this}\<close>

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

Isabelle supports an alternative way by passing facts as input\index{fact!input $\sim$}\index{input facts} to a proof.
\<close>

subsection "Using Input Facts in a Proof"
text_raw\<open>\label{proof-this-use}\<close>

text \<open>
The input facts are passed as input to the first method applied\index{proof!method!input} in the proof. In a proof script
it is the method applied in the first \<^theory_text>\<open>apply\<close> step, in a structured proof \<^theory_text>\<open>proof method \<dots>\<close> it 
is the initial method \<open>method\<close>. 

Every proof method accepts a set of facts as input. Whether it processes them and how it uses
them depends on the kind of method. Therefore input facts for a proof only work in the desired 
way, if a corresponding method is used at the beginning of the proof. See Chapter~\ref{methods}
for descriptions how methods process input facts.
\<close>

subsection "Inputting Facts into a Proof"
text_raw\<open>\label{proof-this-input}\<close>

subsubsection "Method Application Mode"

text \<open>
In method application mode \<open>proof(prove)\<close> facts can be input to the remaining proof 
\<^theory_text>\<open>\<proof>\<close> by
@{theory_text[display]
\<open>using name\<^sub>1 \<dots> name\<^sub>n \<proof>\<close>}\index{using (keyword)}
where the \<open>name\<^sub>i\<close> are names of facts or fact sets. The sequence of all referred facts is input 
to the proof following the \<^theory_text>\<open>using\<close> specification. In a proof script it is input to the next
\<^theory_text>\<open>apply\<close> step. If a structured proof follows, it is input to its initial method. Since in 
method application mode no local facts are stated by previous steps, the facts can only be initial
facts in the outermost proof context (see Section~\ref{proof-state-initial}), or they may be external
facts from the enclosing theory, or, if in a subproof, they may be facts from contexts of enclosing
proofs.\<close>

subsubsection "Statement Mode"

text\<open>
In statement mode \<open>proof(state)\<close> fact input is supported with the help of the special
fact set name \<open>this\<close>\index{this (fact set name)}. The statement
@{theory_text[display]
\<open>then\<close>}\index{then (keyword)}
inputs the facts named \<open>this\<close> to the proof of the following goal statement. 

The statement \<^theory_text>\<open>then\<close>
must be immediately followed by a goal statement (\<^theory_text>\<open>have\<close> or \<^theory_text>\<open>show\<close>). This is enforced by
a special third proof mode \<open>proof(chain)\<close>\index{proof(chain) (proof mode)}. In it only a goal statement is allowed, \<^theory_text>\<open>then\<close> 
switches to this mode, the goal statement switches back to mode \<open>proof(state)\<close> after its proof.

Note that \<^theory_text>\<open>then\<close> is allowed in statement mode, although it does not state a fact. There
are several other such auxiliary statements allowed in mode \<open>proof(state)\<close> in addition to the
goal statements \<^theory_text>\<open>have\<close> and \<^theory_text>\<open>show\<close>.

The fact set \<open>this\<close> can be set by the statement
@{theory_text[display]
\<open>note name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{note (keyword)}
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
\<open>from name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{from (keyword)}
Like \<^theory_text>\<open>then\<close> it switches to mode \<open>proof(chain)\<close> and it inputs the sequence of the facts referred by 
\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> to the proof of the following goal statement.
\<close>

section "Fact Chaining"
text_raw\<open>\label{proof-chain}\<close>

text \<open>
In both cases described for fact input until now, the facts still have been referred by names.
This can be avoided by automatically using a stated fact as input to the proof of the next
stated fact. That is called ``fact chaining''\index{fact!chaining}. 
\<close>

subsection "Automatic Update of the Current Facts"
text_raw\<open>\label{proof-chain-update}\<close>

text\<open>
Fact chaining is achieved, because Isabelle automatically updates the fact set \<open>this\<close>.
Whenever a new fact is added to the proof context, the set \<open>this\<close> is redefined to contain (only)
this fact. In particular, after every goal statement \<open>this\<close> names the new proved fact. Therefore
the fact set \<open>this\<close> is also called the ``current facts''\index{fact!current $\sim$}.

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
Section~\ref{proof-state-initial}) the proof consists of the statement sequence
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
\<open>with name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{with (keyword)}
Like \<^theory_text>\<open>then\<close> it switches to mode \<open>proof(chain)\<close> and it inputs the sequence of the facts referred by 
\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> together with the current facts to the proof of the following goal statement.

If a proof consists of a fact tree with several branches, every branch can be constructed this
way. Before switching to the next branch the last fact must be named, so that it can later be used
to prove the fact where the branches join. A corresponding proof pattern for two branches which
join at fact \<open>F\<close> is
@{theory_text[display]
\<open>have "F\<^sub>1\<^sub>,\<^sub>1" `\<proof>\<^sub>1\<^sub>,\<^sub>1`
then have "F\<^sub>1\<^sub>,\<^sub>2" `\<proof>\<^sub>1\<^sub>,\<^sub>2`
\<dots>
then have name\<^sub>1: "F\<^sub>1\<^sub>,\<^sub>m" `\<proof>\<^sub>1\<^sub>,\<^sub>m`
have "F\<^sub>2\<^sub>,\<^sub>1" `\<proof>\<^sub>2\<^sub>,\<^sub>1`
then have "F\<^sub>2\<^sub>,\<^sub>2" `\<proof>\<^sub>2\<^sub>,\<^sub>2`
\<dots>
then have "F\<^sub>2\<^sub>,\<^sub>n" `\<proof>\<^sub>2\<^sub>,\<^sub>n`
with name\<^sub>1 have "F" \<proof>
\<close>}

If the theorem has been specified in structured form \<^theory_text>\<open>theorem "C" if "A\<^sub>1" \<dots> "A\<^sub>n"\<close> every branch
can be started in the form
@{theory_text[display]
\<open>from that have "F\<^sub>1\<^sub>,\<^sub>1"
\<dots>\<close>}
which will input all assumptions to every branch. This works since unneeded assumptions usually do
not harm in a proof, but it is often clearer for the reader to explicitly name the assumptions
@{theory_text[display]
\<open>theorem "C" if a\<^sub>1: "A\<^sub>1" and \<dots> and a\<^sub>n: "A\<^sub>n"\<close>}
and specify only the relevant assumption by name in the proof:
@{theory_text[display]
\<open>from a\<^sub>1 have "F\<^sub>1\<^sub>,\<^sub>1"
\<dots>\<close>}\<close>

subsection "Naming and Grouping Current Facts"
text_raw\<open>\label{proof-chain-nameing}\<close>

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
In the case of a \<^theory_text>\<open>note\<close> statement every group\index{fact!group} can be given an additional explicit name as in
@{theory_text[display]
\<open>note name\<^sub>1 = name\<^sub>1\<^sub>,\<^sub>1 \<dots> name\<^latex>\<open>$_{1,m_1}$\<close> and \<dots> and name\<^sub>n = name\<^sub>n\<^sub>,\<^sub>1 \<dots> name\<^latex>\<open>$_{n,m_n}$\<close>\<close>}\<close>

subsection "Accessing Input Facts in a Proof"
text_raw\<open>\label{proof-chain-access}\<close>

text \<open>
At the beginning of a proof the set name \<open>this\<close> is undefined, the name cannot be used
to refer to the input facts (which are the current facts in the enclosing proof). To access
the input facts other than by the first proof method they must be named before they are chained to
the goal statement, then they can be referenced in the subproof by that name. For example in
@{theory_text[display]
\<open>note input = this
then have "prop" \<proof>\<close>}\index{input (example fact set)}
the input facts can be referenced by the name \<open>input\<close> in \<^theory_text>\<open>\<proof>\<close>.
\<close>

subsection "Exporting the Current Facts of a Nested Context"
text_raw\<open>\label{proof-chain-export}\<close>

text \<open>
At the end of a nested context\index{proof!context!nested $\sim$} (see Section~\ref{proof-struct-nesting}) the current facts are
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

section "Assuming Facts"
text_raw\<open>\label{proof-assume}\<close>

text \<open>
Facts can be added to the proof context without proving them, then they are only assumed\index{fact!assumed $\sim$}.
\<close>

subsection "Introducing Assumed Facts"
text_raw\<open>\label{proof-assume-add}\<close>

text \<open>
A proposition is inserted as assumption in the proof context by a statement of the form
@{theory_text[display]
\<open>assume "prop"\<close>}\index{assume (keyword)}

Assumed facts may be derivation rules with possibly multiple conclusions, then they may be specified
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
other named facts (see Section~\ref{theory-theorem-search}).

Like goal statements an \<^theory_text>\<open>assume\<close> statement makes the assumed facts current, i.e. it updates
the set \<open>this\<close> to contain the specified propositions as facts, so that they can be chained
to a following goal statement:
@{theory_text[display]
\<open>assume "C"
then have "prop" \<proof>
\<dots>\<close>}\<close>

subsection "Exporting Facts with Assumptions"
text_raw\<open>\label{proof-assume-export}\<close>

text\<open>
Assumed facts may be used to prove other local facts, so that arbitrary local facts may depend on
the validness of the assumed facts. This is taken into account when local facts are exported from
a proof context (see Section~\ref{proof-statefact-goal}). Whenever a local fact \<open>F\<close> is exported\index{fact!export}
it is combined with copies of all locally assumed facts \<open>AF\<^sub>1,\<dots>,AF\<^sub>n\<close> to the derivation rule
\<open>\<lbrakk>AF\<^sub>1;\<dots>;AF\<^sub>n\<rbrakk> \<Longrightarrow> F\<close>, so that \<open>F\<close> still depends on the assumptions after leaving the context.

If the fact \<open>F\<close> is itself a derivation rule \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> then the locally assumed facts
are prepended, resulting in the exported rule \<open>\<lbrakk>AF\<^sub>1;\<dots>;AF\<^sub>n;A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>.

If the fact \<open>F\<close> has been proved in a \<^theory_text>\<open>show\<close> statement it is also exported in this way, resulting
in a derivation rule with all local assumptions added. Therefore it will only refine a goal if
every local assumption unifies with an assumption present in the goal, (see
Section~\ref{proof-statefact-goal}).

If in a previous part of a proof facts have been stored as rule assumptions in the goal state (see
Section~\ref{proof-proc-store}), they can be ``copied'' to the proof context with the help of
\<^theory_text>\<open>assume\<close> statements and will be ``matched back'' by the \<^theory_text>\<open>show\<close> statements used to remove the
goals.

In particular, if a theorem specifies a rule \<open>A \<Longrightarrow> C\<close> directly as proposition it will become the
initial goal, as described in Section~\ref{proof-state-initial}. Then a structured proof using the
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

subsection "Presuming Facts"
text_raw\<open>\label{proof-assume-presume}\<close>

text \<open>
It is also possible to use a proposition as assumed fact\index{fact!assumed $\sim$} which does not unify with an
assumption in a goal, but can be proved from them. In other words, the proof is started
somewhere in the middle of the fact tree, works by forward reasoning, and when 
it reaches the conclusion the assumed fact remains to be proved. The statement
@{theory_text[display]
\<open>presume "prop"\<close>}\index{presume (keyword)}
inserts such a presumed fact into the proof context. As for \<^theory_text>\<open>assume\<close> the structured form with
\<^theory_text>\<open>if\<close> and \<^theory_text>\<open>for\<close> is supported.

When a fact is exported from a context with presumed facts, they do not become a part of
the exported rule. Instead, at the end of the context for each presumed fact \<open>F\<^sub>p\<close> a new goal
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> F\<^sub>p\<close> is added to the goal state of the enclosing proof where \<open>A\<^sub>1,\<dots>,A\<^sub>n\<close> are the
facts assumed in the ended context. So the proof has to continue after 
proving all original goals and is only finished when all such goals for presumed facts 
have been proved as well.
\<close>

section "Fixing Variables"
text_raw\<open>\label{proof-fix}\<close>

text \<open>
As described in Section~\ref{proof-state-initial} variables occurring free\index{free occurrence}\index{variable!free occurrence of $\sim$} in the
assumptions or conclusions of a theorem are automatically added as
fixed variables\index{fixed variable}\index{variable!fixed $\sim$} to the outermost proof context. Thus they can be used everywhere in the proof where
they are not shadowed. If, instead, they are explicitly bound\index{variable!bound $\sim$} in the proposition (see
Section~\ref{theory-prop-bind}), their use is restricted to the proposition itself. Thus in
@{theory_text[display]
\<open>theorem "\<And>x::nat. x < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
the variable \<open>x\<close> is restricted to the proposition and is not accessible in \<^theory_text>\<open>\<proof>\<close>, whereas in 
@{theory_text[display]
\<open>theorem "(x::nat) < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
the variable \<open>x\<close> is accessible in \<^theory_text>\<open>\<proof>\<close>. If the theorem is specified in structured form,
variables may be explicitly specified to be fixed in the outermost proof context using \<^theory_text>\<open>for\<close> or
\<^theory_text>\<open>fixes\<close>, respectively (see Section~\ref{proof-state-initial}). Therefore the forms
@{theory_text[display]
\<open>theorem "x < 3 \<Longrightarrow> x < 5" for x::nat \<proof>\<close>}
and
@{theory_text[display]
\<open>theorem fixes x::nat shows "x < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
are completely equivalent to the previous form.
\<close>

subsection "Local Variables"
text_raw\<open>\label{proof-fix-local}\<close>

text\<open>
Additional variables can be added as fixed to the innermost enclosing proof context by the statement
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>n\<close>}\index{fix (keyword)}
As usual the variables can be grouped by \<^theory_text>\<open>and\<close> and types can be specified for (some of) the groups. 

A fixed variable in a proof context denotes a specific value of its type. However, if the variable
has been introduced by \<^theory_text>\<open>fix\<close>, \<^theory_text>\<open>for\<close> or \<^theory_text>\<open>fixes\<close> it is underspecified in the same way as a constant
introduced by \<^theory_text>\<open>consts\<close> in a theory (see Section~\ref{theory-terms-consts}): no information is given
about its value. In this sense it denotes an ``arbitrary but fixed value''.

If a variable name is used in a proof context without explicitly fixing it, it either refers to a
variable in an enclosing context or it is free. If it is explicitly fixed it names a variable which
is different from all variables with the same name in enclosing contexts.

If a variable is free in the proof for a theorem its value cannot be proved to be related in any
way to values used in the theorem. Therefore it is useless for the proof and its occurrence should
be considered to be an error. In the interactive editor Isabelle marks free variables by a light red
background as an alert for the proof writer. 

A fixed local variable\index{variable!local $\sim$} is common to the whole local context. If it occurs in several local facts 
it always is the same variable and denotes the same value, it is not automatically restricted to
every fact, as for toplevel theorems. Hence in
@{theory_text[display]
\<open>fix x::nat
assume a: "x < 3"
have "x < 5" \<proof>\<close>}
the \<^theory_text>\<open>\<proof>\<close> may refer to fact \<open>a\<close> because the \<open>x\<close> is the same variable in both propositions.
\<close>

subsection "Exporting Facts with Local Variables"
text_raw\<open>\label{proof-fix-export}\<close>

text \<open>
Explicitly fixing variables in a proof context is not only important for avoiding name clashes.
If a fact is exported\index{fact!export} from a proof context, all fixed local variables are replaced by unknowns\index{unknown},
other variables remain unchanged. Since unification only works for unknowns, it makes a difference
whether a fact uses a local variable or a variable which origins from an enclosing context or
is free.

The proposition \<open>x < 3 \<Longrightarrow> x < 5\<close> can be proved by the statements 
@{theory_text[display]
\<open>fix y::nat
assume "y < 3"
then show "y < 5" \<proof>\<close>}
because when the fact \<open>y < 5\<close> is exported, the assumption is added (as described in 
Section~\ref{proof-assume-export}) and then variable \<open>y\<close> is replaced by the unknown \<open>?y\<close>
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

If variables are explicitly bound\index{variable!bound $\sim$} in the proposition of a theorem they are not accessible in the
proof. Instead, corresponding new local variables (which may have the same names) must be fixed in
the proof context and used for the proof. Upon export by a \<^theory_text>\<open>show\<close> statement these variables will
be replaced by unknowns which then are unified with the variables in the goal. A corresponding
proof for the proposition \<open>\<And>x::nat. x < 3 \<Longrightarrow> x < 5\<close> is
@{theory_text[display]
\<open>fix y::nat
assume "y < 3"
then show "y < 5" \<proof>\<close>}\<close>

section "Defining Variables"
text_raw\<open>\label{proof-define}\<close>

text \<open>
Local variables may also be introduced together with specifying a value for them. This is done
using a statement of the form
@{theory_text[display]
\<open>define x\<^sub>1 \<dots> x\<^sub>m where "x\<^sub>1\<equiv>term\<^sub>1" \<dots> "x\<^sub>m\<equiv>term\<^sub>m"\<close>}\index{define (keyword)}\index{where (keyword)}
which specifies a defining equation for every defined variable\index{variable!definition}\index{definition!for variable}.
As usual, the variables and equations may be grouped by \<^theory_text>\<open>and\<close>, equation groups may be named, and
types may be specified for (some of) the variable groups. In the object logic HOL
(see Chapter~\ref{holbasic}) also the normal equality operator \<open>=\<close> may be used instead of \<open>\<equiv>\<close>.

The variable \<open>x\<^sub>i\<close> may not occur free in \<open>term\<^sub>i\<close>, otherwise an error is signaled. However, the other
variables are allowed in \<open>term\<^sub>i\<close>. This may lead to cyclic definitions which is not checked by
Isabelle, but then the definition cannot be used to determine the defined value for the
corresponding variables, it is underspecified.
\<close>

subsection "Defining Equations Viewed as Local Facts"
text_raw\<open>\label{proof-define-equations}\<close>

text \<open>
If there is already a previous definition for an \<open>x\<^sub>i\<close> in the same proof context the former \<open>x\<^sub>i\<close> is
shadowed and becomes inaccessible and a new local variable \<open>x\<^sub>i\<close> is introduced.

Thus a defining equation can never contradict any existing fact in the proof context and Isabelle
safely adds all defining equations as facts to the proof context enclosing the \<^theory_text>\<open>define\<close> statement.
The collection of all these facts is automatically named\index{name!of defining equation} \<open>x\<^sub>1_\<dots>_x\<^sub>m_def\<close>\index{def@$\_$def (fact name suffix)}, replacing this name if it
already exists in the local proof context. Explicit names specified for equation groups are used
to name the corresponding facts.
\<close>

subsection "Exporting Facts after Defining Variables"
text_raw\<open>\label{proof-define-export}\<close>

text\<open>
Unlike facts assumed by an \<^theory_text>\<open>assume\<close> statement (see Section~\ref{proof-assume-add}) the 
facts created by a \<^theory_text>\<open>define\<close> statement are \<^emph>\<open>not\<close> added as assumptions when a fact \<open>F\<close> is 
exported\index{fact!export} from the local context. Instead, if a locally defined variable \<open>x\<^sub>i\<close> occurs in \<open>F\<close> it
is replaced by the \<open>term\<^sub>i\<close> according to its defining equation.

If the definition of \<open>x\<^sub>i\<close> is cyclic the occurrences of \<open>x\<^sub>i\<close> in \<open>F\<close> are not replaced and become
an unknown during export, however, then the fact \<open>F\<close> usually is invalid and cannot be proved.
\<close>


section "Obtaining Variables"
text_raw\<open>\label{proof-obtain}\<close>

text \<open>
Local variables may also be introduced together with  an arbitrary proposition which allows to
specify additional information about their values. This is done using a statement of the form
@{theory_text[display]
\<open>obtain x\<^sub>1 \<dots> x\<^sub>m where "prop" \<proof>\<close>}\index{obtain (keyword)}\index{where (keyword)}
where \<open>prop\<close> is a proposition in inner syntax which contains the variables \<open>x\<^sub>1 \<dots> x\<^sub>m\<close>. 
As for variables introduced by \<^theory_text>\<open>fix\<close>  or \<^theory_text>\<open>define\<close>  the variables may be grouped by \<^theory_text>\<open>and\<close> and
types may be specified for (some of) the groups.

If the proposition \<open>prop\<close> is a derivation rule with possibly multiple conclusions it may be
specified in structured form (see Section~\ref{theory-prop-struct}) using several separate
propositions:
@{theory_text[display]
\<open>obtain x\<^sub>1 \<dots> x\<^sub>m where "C\<^sub>1" \<dots> "C\<^sub>h" if "A\<^sub>1" \<dots> "A\<^sub>n" for y\<^sub>1 \<dots> y\<^sub>p \<proof>\<close>}
As usual, the conclusions, assumptions, and bound variables may be grouped by \<^theory_text>\<open>and\<close>, the assumption
and conclusion groups may be named and types may be specified for (some of) the groups of bound
variables.

The proposition(s) usually relate the values of the new variables to values of existing variables 
(which may be local or come from enclosing contexts). In the simplest case the proposition(s) directly 
specify terms for the new variables, like a \<^theory_text>\<open>define\<close> statement (see
Section~\ref{proof-define}) such as in
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

subsection \<open>Proving {\sl obtain} Statements\<close>
text_raw\<open>\label{proof-obtain-prove}\<close>

text\<open>
An \<^theory_text>\<open>obtain\<close> statement has a similar meaning as the statements
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>m 
assume "prop"\<close>}
but there is one important difference: the proposition in an \<^theory_text>\<open>obtain\<close> statement must be redundant
in the local proof context.

That is the reason why an \<^theory_text>\<open>obtain\<close> statement is a goal statement\index{goal!statement} and includes a proof. The proof 
must prove the redundancy of the proposition, which may be stated in the following way: if any other
proposition can be derived from it in the local proof context it must be possible to also derive it
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

Note that after a successful proof of an \<^theory_text>\<open>obtain\<close> statement the current fact is the proposition
specified in the statement, not the proved redundancy goal. If the proposition is specified in
structured form with multiple conclusions the current facts are the collection of facts
corresponding to the conclusions and if names are specified for conclusion groups they are used
to name the resulting facts.

Input facts may be passed to
\<^theory_text>\<open>obtain\<close> statements. As for the other goal statements, they are input to the \<open>\<proof>\<close>.
\<close>

subsection "Exporting Facts after Obtaining Variables"
text_raw\<open>\label{proof-obtain-export}\<close>

text\<open>
Unlike facts assumed by an \<^theory_text>\<open>assume\<close> statement (see Section~\ref{proof-assume-add}) the 
propositions in an \<^theory_text>\<open>obtain\<close> statement are \<^emph>\<open>not\<close> added as assumptions when a fact \<open>F\<close> is 
exported\index{fact!export} from the local context. This is correct, since they have been proved to be redundant,
therefore they can be omitted. Also, unlike variables introduced by a \<^theory_text>\<open>define\<close> statement (see
Section~\ref{proof-define}) occurrences of obtained variables in \<open>F\<close> are not replaced
by defining terms, since such terms are not available in the general case.

That implies that an exported fact \<open>F\<close> may not refer to variables introduced by an
\<^theory_text>\<open>obtain\<close> statement, because the information provided by the proposition about them gets
lost during the export. Otherwise an error is signaled.
\<close>

section "Term Abbreviations"
text_raw\<open>\label{proof-let}\<close>

text \<open>
A term abbreviation\index{abbreviation!for term}\index{term abbreviation} is a name for a proposition or a term in it. 
\<close>

subsection "Defining Term Abbreviations"
text_raw\<open>\label{proof-let-define}\<close>

text\<open>A term abbreviation can be defined by a statement of the form
@{theory_text[display]
\<open>let ?name = "term"\<close>}\index{let (keyword)}
Afterwards the name is ``bound'' to the term\index{name!for term} and can be used in place of the term in 
propositions and other terms, as in:
@{theory_text[display]
\<open>let ?lhs = "2*x+3"
let ?rhs = "2*5+3"
assume "x < 5"
have "?lhs \<le> ?rhs" \<proof>\<close>}

The name \<open>?thesis\<close>\index{?thesis (term abbreviation)} (see Section~\ref{proof-statefact-goal}) is a term abbreviation of this
kind. It is defined automatically for every proof in the outermost proof context.

A \<^theory_text>\<open>let\<close> statement can define several term abbreviations in the form
@{theory_text[display]
\<open>let ?name\<^sub>1 = "term\<^sub>1" and \<dots> and ?name\<^sub>n = "term\<^sub>n"\<close>}

A \<^theory_text>\<open>let\<close> statement can occur everywhere in mode \<open>proof(state)\<close>. However, it does not preserve
the current facts, the fact set \<open>this\<close> becomes undefined by it. 
\<close>

subsection "Pattern Matching"
text_raw\<open>\label{proof-let-match}\<close>

text \<open>
Note that term abbreviations have the form of ``unknowns'' (see Section~\ref{theory-theorem-unknowns}),
although they are defined (``bound''). The reason is that they are actually defined by unification\index{unification}.

The more general form of a \<^theory_text>\<open>let\<close> statement is
@{theory_text[display]
\<open>let "pattern" = "term"\<close>}
where \<open>pattern\<close> is a term\index{term!pattern} which may contain unbound unknowns. As usual, if the pattern consists of
a single unknown, the quotes may be omitted. The \<^theory_text>\<open>let\<close> statement unifies \<open>pattern\<close>
and \<open>term\<close>, i.e., it determines terms to substitute for the unknowns, so that the pattern becomes
syntactically equal to \<open>term\<close>. If that is not possible, an error is signaled, otherwise the
unknowns are bound to the substituting terms. Note that the equals sign belongs to the outer syntax,
therefore both the pattern and the term must be quoted separately.

The \<^theory_text>\<open>let\<close> statement
@{theory_text[display]
\<open>let "?lhs \<le> ?rhs" = "2*x+3 \<le> 2*5+3"\<close>}
binds the unknowns to the same terms as the two \<^theory_text>\<open>let\<close> statements above.

If a part of the term is irrelevant and need not be bound the dummy unknown\index{unknown!dummy $\sim$} ``\_'' (underscore)
can be used to match it in the pattern without binding an unknown to it:
@{theory_text[display]
\<open>let "_ \<le> ?rhs" = "2*x+3 \<le> 2*5+3"\<close>}
will only bind \<open>?rhs\<close> to the term on the righthand side.\<close>

subsubsection "Parameterized Term Abbreviations"

text\<open>
Pattern matching can be used to define parameterized abbreviations\index{term!abbreviation!parameterized $\sim$}. If the pattern has the form of
a function application where the unknown is the function, it will be bound to a function which,
after substituting the arguments, will be equal to the \<open>term\<close>. So it can be applied to other
arguments to yield terms where the corresponding parts have been replaced. This kind of pattern
matching is called ``higher order unification''\index{unification!higher order $\sim$} and only succeeds if the pattern and \<open>term\<close> are
not too complex.

The \<^theory_text>\<open>let\<close> statement
@{theory_text[display]
\<open>let "?lhs x \<le> ?rhs 5" = "2*x+3 \<le> 2*5+3"\<close>}
binds both unknowns to the lambda term \<open>\<lambda>a. 2 * a + 3\<close>. Thus afterwards the use \<open>?lhs 7\<close> results
in the term \<open>2 * 7 + 3\<close>.\<close>

subsubsection "Already Bound Unknowns"

text\<open>
The \<open>term\<close> may contain unknowns which are already bound\index{unknown!bound $\sim$}. They are substituted 
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
terms must be equal, they are completely independent.\<close>

subsubsection "Bound Variables in the Matched Term"

text\<open>
If the term internally binds variables which are used in a subterm, the subterm cannot be matched
separately by an unknown because then the variable bindings would be lost. Thus the statement
@{theory_text[display]
\<open>let "\<lambda>x. ?t" = "\<lambda>x. x+1"\<close>} 
will fail to bind \<open>?t\<close> to \<open>x+1\<close> whereas
@{theory_text[display]
\<open>let "\<lambda>x. x+?t" = "\<lambda>x. x+1"\<close>} 
will successfully bind \<open>?t\<close> to \<open>1\<close> since the bound variable \<open>x\<close> does not occur in it.
\<close>

subsection "Casual Term Abbreviations"
text_raw\<open>\label{proof-let-casual}\<close>

text \<open>
Term abbreviations\index{term!abbreviation!casual $\sim$} may also be defined in a ``casual way'' by appending a pattern to a proposition
which is used for some other purpose in the form
@{theory_text[display]
\<open>"prop" (is "pattern")\<close>}\index{is (keyword)}
The pattern is matched with the proposition \<open>prop\<close> and if successful the unknowns in the pattern
are bound as term abbreviations.

This is possible for all propositions used in a theorem  (see Section~\ref{theory-theorem}),
such as in
@{theory_text[display]
\<open>theorem "prop" (is ?p) \<proof>
theorem fixes x::nat and c and n 
  assumes asm1: "x < c" (is ?a1) and "n > 0" (is ?a2)
  shows "n*x < n*c" (is "?lhs < ?rhs")
  \<proof>\<close>}
and also in the structured form using \<^theory_text>\<open>if\<close> (see Section~\ref{theory-prop-struct}). The unknowns
will be bound as term abbreviations in the outermost proof context in the proof of the theorem.

Note the difference between the fact name \<open>asm1\<close> and the term abbreviation name \<open>?a1\<close> in the
example. The fact name refers to the proposition \<open>x < c\<close> as a valid fact, it can only be used to
work with the proposition as a logical entity. The abbreviation name \<open>?a1\<close>, instead, refers to the
proposition as a syntactic term of type \<open>bool\<close>, it can be used to construct larger terms such as
in \<open>?a1 \<and> ?a2\<close> which is equivalent to the term \<open>x < c \<and> n > 0\<close>.

Casual term abbreviations may also be defined for propositions used in goal statements (see
Sections~\ref{proof-statefact} and~\ref{proof-obtain}) and in \<^theory_text>\<open>assume\<close>,  \<^theory_text>\<open>presume\<close>,
and \<^theory_text>\<open>define\<close> statements (see Sections~\ref{proof-assume} and~\ref{proof-define}). Then
the unknowns will be bound as term abbreviations in the \<^emph>\<open>enclosing\<close> proof context, so that they
are available after the statement (and also in the nested subproof of the goal statements). 
\<close>

section "Accumulating Facts"
text_raw\<open>\label{proof-moreover}\<close>

text \<open>
Instead of giving individual names to facts in the proof context, facts can be collected in
named fact sets\index{fact!set}. Isabelle supports the specific fact set named \<open>calculation\<close>\index{calculation (fact set name)} and provides
statements for managing it.

The fact set \<open>calculation\<close> is intended to accumulate current facts\index{fact!accumulation}\index{fact!current $\sim$} for later use. Therefore
it is typically initialized by the statement
@{theory_text[display]
\<open>note calculation = this\<close>}
and afterwards it is extended by several statements
@{theory_text[display]
\<open>note calculation = calculation this\<close>}
After the last extension the facts in the set are chained to the next proof:
@{theory_text[display]
\<open>note calculation = calculation this then have \<dots>\<close>}\<close>

subsection "Support for Fact Accumulation"
text_raw\<open>\label{proof-moreover-support}\<close>

text\<open>
Isabelle supports this management of \<open>calculation\<close> with two  specific  statements. The statement 
@{theory_text[display]
\<open>moreover\<close>}\index{moreover (keyword)}
is equivalent to \<^theory_text>\<open>note calculation = this\<close> when it occurs the first time in a context, 
afterwards it behaves like \<^theory_text>\<open>note calculation = calculation this\<close> but without making 
\<open>calculation\<close> current, instead, it leaves the current fact(s) unchanged. The statement
@{theory_text[display]
\<open>ultimately\<close>}\index{ultimately (keyword)}
is equivalent to \<^theory_text>\<open>note calculation = calculation this then\<close>, i.e., it adds the current 
facts to the set, makes the set current, and chains it to the next goal statement.

Due to the block structure of nested proof contexts, the \<open>calculation\<close> set can be reused in nested
contexts without affecting the set in the enclosing context. The first occurrence of 
\<^theory_text>\<open>moreover\<close> in the nested context initializes a fresh local \<open>calculation\<close> set. Therefore
fact accumulation is always local to the current proof context.
\<close>

subsection "Accumulating Facts in a Nested Context"
text_raw\<open>\label{proof-moreover-nesting}\<close>

text\<open>
Fact accumulation can be used for collecting the facts in a nested context\index{proof!context!nested $\sim$} for export
(see Section~\ref{proof-chain-export}) without using explicit names for them:
@{theory_text[display]
\<open>\<dots> { 
  have "prop\<^sub>1" `\<proof>\<^sub>1` 
  moreover have "prop\<^sub>2" `\<proof>\<^sub>2`
  \<dots>
  moreover have "prop\<^sub>n" `\<proof>\<^sub>n` 
  moreover note calculation 
  } \<dots>\<close>}
\<close>

subsection "Accumulating Facts for Joining Branches"
text_raw\<open>\label{proof-moreover-join}\<close>

text\<open>
Fact accumulation can also be used for collecting the facts at the end of joined fact branches
in a proof and inputting them to the joining step. A corresponding proof pattern for two branches
which join at fact \<open>F\<close> is
@{theory_text[display]
\<open>have "F\<^sub>1\<^sub>,\<^sub>1" `\<proof>\<^sub>1\<^sub>,\<^sub>1`
then have "F\<^sub>1\<^sub>,\<^sub>2" `\<proof>\<^sub>1\<^sub>,\<^sub>2`
\<dots>
then have "F\<^sub>1\<^sub>,\<^sub>m" `\<proof>\<^sub>1\<^sub>,\<^sub>m`
moreover have "F\<^sub>2\<^sub>,\<^sub>1" `\<proof>\<^sub>2\<^sub>,\<^sub>1`
then have "F\<^sub>2\<^sub>,\<^sub>2" `\<proof>\<^sub>2\<^sub>,\<^sub>2`
\<dots>
then have "F\<^sub>2\<^sub>,\<^sub>n" `\<proof>\<^sub>2\<^sub>,\<^sub>n`
ultimately have "F" \<proof>
\<close>}
The \<^theory_text>\<open>moreover\<close> statement starts the second branch and saves the fact \<open>F\<^sub>1\<^sub>,\<^sub>m\<close> to \<open>calculation\<close>.
The \<^theory_text>\<open>ultimately\<close> statement adds the fact \<open>F\<^sub>2\<^sub>,\<^sub>n\<close> to \<open>calculation\<close> and then inputs the set to
the proof of \<open>F\<close>. 

Note that \<^theory_text>\<open>moreover\<close> does not chain the current facts to the following goal statement.

Using nested contexts sub-branches can be constructed and joined in the same way.
\<close>

section "Equational Reasoning"
text_raw\<open>\label{proof-equational}\<close>

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
``equational reasoning''\index{reasoning!equational $\sim$}\index{equational reasoning} which is a specific form of forward reasoning.
\<close>

subsection "Transitivity Rules"
text_raw\<open>\label{proof-equational-transitivity}\<close>

text\<open>
The full example proof needs additional facts which must be inserted into the sequence. From the
first two facts the fact \<open>2*(x+3) \<le> 3*x+6\<close> is derived, then with the third fact the fact 
\<open>2*(x+3) < 3*x+9\<close> is derived, and finally with the fourth fact the conclusion \<open>2*(x+3) < 3*(x+3)\<close>
is reached. The general pattern of these additional derivations can be stated as the derivation
rules
\<open>\<lbrakk>a = b; b \<le> c\<rbrakk> \<Longrightarrow> a \<le> c\<close>, \<open>\<lbrakk>a \<le> b; b < c\<rbrakk> \<Longrightarrow> a < c\<close>, and \<open>\<lbrakk>a < b; b = c\<rbrakk> \<Longrightarrow> a < c\<close>.

Rules of this form are called ``transitivity rules''\index{rule!transitivity $\sim$}. They are valid for relations such as equality,
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

subsection "Support for Equational Reasoning"
text_raw\<open>\label{proof-equational-support}\<close>

text \<open>
Isabelle supports equational reasoning in the following form. It provides the statement
@{theory_text[display]
\<open>also\<close>}\index{also (keyword)}
which expects that the set \<open>calculation\<close> contains the fact \<open>F\<^sub>i\<close> and the current fact
\<open>this\<close> is the fact \<open>H\<^sub>i\<close>. It automatically selects an adequate transitivity rule, uses it to
derive the fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and replaces \<open>F\<^sub>i\<close> in \<open>calculation\<close> by it. Upon its first use in a proof
context \<^theory_text>\<open>also\<close> simply stores the current fact \<open>this\<close> in \<open>calculation\<close>. The statement
@{theory_text[display]
\<open>finally\<close>}\index{finally (keyword)}
behaves in the same way but additionally makes the resulting fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> current, i.e., puts it
into the set \<open>this\<close>, and chains it into the next goal statement. In other words, \<^theory_text>\<open>finally\<close> is 
equivalent to \<^theory_text>\<open>also from calculation\<close>.

Note that \<^theory_text>\<open>also\<close> behaves like \<^theory_text>\<open>moreover\<close> and \<^theory_text>\<open>finally\<close> behaves like \<^theory_text>\<open>ultimately\<close>, both with 
additional application of the transitivity rule.

Additionally, Isabelle automatically maintains the term abbreviation \<open>\<dots>\<close>\index{...@\<open>\<dots>\<close> (term abbreviation)} (which is the 
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

subsection "Determining Transitivity Rules"
text_raw\<open>\label{proof-equational-rules}\<close>

text\<open>
To automatically determine the transitivity rule used by \<^theory_text>\<open>also\<close> or \<^theory_text>\<open>finally\<close>, Isabelle
maintains the dynamic fact set (see Section~\ref{theory-theorem-named}) named \<open>trans\<close>\index{trans (fact set name)}.
It selects a rule from that set according to the relation symbols used in the facts in 
\<open>calculation\<close> and \<open>this\<close>.

A transitivity rule which is not in \<open>trans\<close> can be explicitly specified by name in the
form
@{theory_text[display]
\<open>also (name)
finally (name)\<close>}
\<close>

end