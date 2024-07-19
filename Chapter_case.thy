theory Chapter_case
  imports Chapter_methods
begin
chapter "Case Based Proofs"
text_raw\<open>\label{case}\<close>

text \<open>
If during a proof the goal state contains several goals they are often proved sequentially. Although
there are proof methods which process several goals at once (see examples in
Section~\ref{methods-auto-methods}) most methods only process the first goal. In a proof script, when
a method has solved and removed the first goal, the next goal will become the first and will be
processed by the next method application steps. In a structured proof (see
Section~\ref{proof-struct-syntax}) it is not so simple. To prove a goal which is in the goal state
its bound variables and assumptions have to be inserted into the local proof context (by \<^theory_text>\<open>fix\<close> and
\<^theory_text>\<open>assume\<close> statements) and its conclusion must be stated by a \<^theory_text>\<open>show\<close> statement and must be proved.
Isabelle provides some support for simplifying these tasks for working on a sequence of goals.
\<close>

section "Named Proof Contexts"
text_raw\<open>\label{case-context}\<close>

text \<open>
Isabelle supports some methods which are able to create ``cases''\index{case} for goals. A case contains bound
variables and assumptions from a goal and it may contain other context elements, such as names for
assumptions or assumption groups and an abbreviation for the conclusion of a goal. The cases are
named. Using these names a proof context can be populated with all content of a case in a single
step.

Since a case contains context elements it can be seen as a named
context\index{named context}\index{proof!context!named $\sim$} which has been prepared by a method for later use, but has not been ``activated'' yet.
Usually a named context is used to initialize a new nested proof context\index{proof!context!nested $\sim$} immediately after its
beginning by inserting the content of the named context into the new context.
\<close>

subsection \<open>The {\sl case} Statement\<close>
text_raw\<open>\label{case-context-case}\<close>

text \<open>
The content of a case may be inserted into the current proof context by the statement
@{theory_text[display]
\<open>case name\<close>}\index{case (keyword)}
where \<open>name\<close> is the case name\index{case!name}\index{name!for case}. It mainly has the effect of the sequence
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>k
let ?a\<^sub>1 = t\<^sub>1 and \<dots> ?a\<^sub>m = t\<^sub>m
assume name: "A\<^sub>1" \<dots> "A\<^sub>n"\<close>}
where \<open>x\<^sub>1 \<dots> x\<^sub>k\<close> are the local variables, \<open>?a\<^sub>1, \<dots>, ?a\<^sub>m\<close> are the term abbreviations, and
\<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> are the facts in the named context of the case. The facts are inserted as assumptions
and the set of these assumptions is named using the case name. Moreover, like the \<^theory_text>\<open>assume\<close>
statement, the \<^theory_text>\<open>case\<close> statement makes the assumed facts current.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Explicit Assumption Naming"
text_raw\<open>\cbend\<close>

text\<open>
Instead of using the case name for naming the assumptions an explicit assumption name\index{assumption!name}\index{name!for assumption} \<open>aname\<close> may be 
specified:
@{theory_text[display]
\<open>case aname: name\<close>}
If defined in the case, other names for single assumptions or assumption groups may be automatically
introduced.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Naming Local Variables"
text_raw\<open>\cbend\<close>

text\<open>
The local variables \<open>x\<^sub>1 \<dots> x\<^sub>k\<close> are fixed by the \<^theory_text>\<open>case\<close> statement but are hidden, they cannot be
used in the subsequent proof text. If they should be used, explicit names must be specified for
them in the form
@{theory_text[display]
\<open>case (name y\<^sub>1 \<dots> y\<^sub>j)\<close>}
Then the names \<open>y\<^sub>1 \<dots> y\<^sub>j\<close> can be used to reference the fixed variables\index{name!for fixed variable}\index{fixed variable!name} in the current proof 
context. If fewer names are specified only the first variables are named, if more names are
specified than there are local variables in the case an error is signaled.

When methods create a named context for a goal they usually only define the term abbreviation
\<open>?case\<close>\index{?case (term abbreviation)} for the conclusion of the goal.
\<close>

subsection "Proof Structure with Cases"
text_raw\<open>\label{case-context-struct}\<close>

text \<open>
The usual proof structure using cases\index{proof!case based $\sim$} consists of an initial method which creates cases and of a
sequence of nested contexts (see Section~\ref{proof-struct-nesting}). At its beginning each context
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
the corresponding goal.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Determining the Cases Introduced by a Method Application"
text_raw\<open>\cbend\<close>

text\<open>
To find out which cases have been introduced by a method application, the command
@{theory_text[display]
\<open>print_cases\<close>}\index{print-cases@print$\_$cases (keyword)}
can be used at arbitrary places in the following proof to display the cases in the Output panel\index{panel!output $\sim$}.

In the interactive editor also the Query panel\index{panel!query $\sim$} (see Section~\ref{system-jedit-query}) can be used
to display the cases available at the cursor position by selecting the tab ``Print Context'' and
checking ``cases''.

Also in the interactive editor, when the cursor is positioned on \<^theory_text>\<open>proof `method`\<close> where the method
supports cases, a skeleton\index{proof!case based $\sim$!skeleton} of a proof using the specific cases provided by the method is 
displayed in the Output panel. By clicking on it it may be copied into the text area immediately
after the method specification.
\<close>

section \<open>The {\sl goal$\_$cases} Method\<close>
text_raw\<open>\label{case-goalcases}\<close>

text\<open>
The simplest method with support for cases is
@{theory_text[display]
\<open>goal_cases\<close>}\index{goal-cases@goal$\_$cases (method)}
Without modifying the goal state it creates a named case\index{case} for every existing goal. Input facts
are ignored.

For a goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> the created named context contains the local variables
\<open>x\<^sub>1 \<dots> x\<^sub>m\<close>, the facts \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close>, and the term abbreviation \<open>?case\<close>\index{?case (term abbreviation)} bound to \<open>C\<close>. If the goal
contains variables which are not explicitly bound by \<open>\<And>\<close> these variables are not added to the
context.

The effect is that if no other variables are fixed and no other facts are assumed a statement
\<^theory_text>\<open>show ?case\<close> after the corresponding \<^theory_text>\<open>case\<close> statement will refine the goal and remove it from the
goal state.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Case Naming"
text_raw\<open>\cbend\<close>

text\<open>
The cases are named\index{case!name}\index{name!for case} by numbers starting with \<open>1\<close>. If other names should be used they may be
specified as arguments to the method:
@{theory_text[display]
\<open>goal_cases name\<^sub>1 \<dots> name\<^sub>n\<close>}
If fewer names are specified than goals are present, only for the first \<open>n\<close> goals cases are created.
If more names are specified an error is signaled.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Composed Methods"
text_raw\<open>\cbend\<close>

text\<open>
When \<^theory_text>\<open>goal_cases\<close> is used in a composed proof method\index{method!composed $\sim$} it can provide cases for the goals produced
by arbitrary other methods:
@{theory_text[display]
\<open>proof (method, goal_cases)\<close>}
provides cases for all goals existing after \<^theory_text>\<open>method\<close> has been applied. If \<^theory_text>\<open>method\<close> does not split
the goal there will be only one case. This can be useful to work with a goal produced by 
\<^theory_text>\<open>method\<close>. In particular, the conclusion of that goal is available as \<open>?case\<close>.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Inspecting the Cases"
text_raw\<open>\cbend\<close>

text\<open>
Note that the proof state(s) resulting from \<^theory_text>\<open>goal_cases\<close> are not visible for the reader of the proof.
Therefore it should only be applied if the goals produced by \<^theory_text>\<open>method\<close> are apparent. In a case the
goal conclusion can be shown partially or fully by defining a possibly abbreviated form of it by
@{theory_text[display]
\<open>let "pattern" = ?case\<close>}
where the \<open>pattern\<close> may contain unknowns which abbreviate sub terms of the conclusion.

A better way to use cases is together with a method which combines both: creating new goals in a
simple and expected way, and immediately creating cases only for these goals.
\<close>

section "Case Based Reasoning"
text_raw\<open>\label{case-reasoning}\<close>

text\<open>
Case based proofs are especially convenient for implementing case based reasoning.
The technique of ``case based reasoning''\index{reasoning!case based $\sim$} uses a specific kind of forward reasoning steps
(see Section~\ref{proof-proc-construct}). It adds a new fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> to the proof context ``out of the
blue'' without proving it from the existing facts. For the proof to stay correct, this must be done
for ``all possible cases'' of \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>, and the proof must be completed separately for each of them.

In its simplest form this can be done by adding an arbitrary fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and its negation \<open>\<not> F\<^sub>i\<^sub>+\<^sub>1\<close>,
this covers all possibilities, since \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> may be either \<open>True\<close> or \<open>False\<close>.

Consider the derivation rule \<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> named \<open>example1\<close> in
Section~\ref{theory-theorem-named}. To prove it using case based reasoning the
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

Note that this technique extends the proof procedure described in Section~\ref{proof-proc-construct}.
There a proof consisted of a single tree of facts which started at the assumptions and all branches
joined to finally reach the conclusion. With case based reasoning at any position the remaining
tree may be split into several ``copies'' with additional assumptions which then must all be
completed separately.
\<close>

subsection "Case Rules"
text_raw\<open>\label{case-reasoning-rules}\<close>

text\<open>
This splitting of a goal into goals for different cases\index{case!split} can be done by applying a single meta rule
of the specific form
@{text[display]
\<open>\<lbrakk>Q\<^sub>1 \<Longrightarrow> ?P; \<dots>; Q\<^sub>k \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
where \<open>Q\<^sub>1 \<dots> Q\<^sub>k\<close> are all cases of the additional assumption. Such rules are called ``case rules''\index{rule!case $\sim$}\index{case!rule}.

When this case rule is applied to the goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> as described in 
Section~\ref{methods-rule-method}, it unifies \<open>?P\<close> with the conclusion \<open>C\<close> and replaces the goal
in the way described above.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Validity of Case Rules"
text_raw\<open>\cbend\<close>

text\<open>
A case rule is only valid, if the \<open>Q\<^sub>i\<close> together cover all possibilities, i.e., if 
\<open>Q\<^sub>1 \<or> \<dots> \<or> Q\<^sub>k\<close> holds. If this has been proved the case rule is available as a fact which can be
applied. Since the whole conclusion is the single unknown \<open>?P\<close> it unifies with every proposition
used as conclusion in a goal, hence a case rule can always be applied to arbitrary goals. It 
depends on the \<open>Q\<^sub>i\<close> whether splitting a specific goal with the case rule is useful for proving
the goal.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Examples"
text_raw\<open>\cbend\<close>

text\<open>
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
the term \<open>n = 0\<close> for \<open>?Q\<close> the rule is prepared to be applied in the same way as above.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "General Form of Case Rules"
text_raw\<open>\cbend\<close>

text\<open>
Case rules may even be more general than shown above. Instead of a single proposition \<open>Q\<^sub>i\<close> every 
case may have locally bound variables and an arbitrary number of assumptions, resulting in a
meta rule of the form
@{text[display]
\<open>\<lbrakk>P\<^sub>1; \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> ?P\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form\cbstart
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>,\<^sub>1\<dots>x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1;\<dots>;Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> ?P\<close>}\cbend
That means, the \<open>P\<^sub>i\<close> may be arbitrary rules but they must all have as conclusion the unknown \<open>?P\<close>
which is also the conclusion of the overall case rule. When such a case rule is applied to a goal
it splits\index{case!split} the goal into \<open>k\<close> cases and adds the variables \cbstart \<open>x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>\<close> and the assumptions
\<open>Q\<^sub>i\<^sub>,\<^sub>1 \<dots> Q\<^latex>\<open>$_{i,q_i}$\<close>\<close>\cbend to the \<open>i\<close>th case.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Case Rules and \<^theory_text>\<open>obtain\<close> Statements"
text_raw\<open>\cbend\<close>

text\<open>
Note that the goal which must be proved for an \<^theory_text>\<open>obtain\<close>\index{obtain (keyword)} statement (see
Section~\ref{proof-obtain}) has the form of a case rule with only one case of the form
\<open>\<And>x\<^sub>1 \<dots> x\<^sub>m. prop \<Longrightarrow> P\<close>. Thus a proof for this goal shows that \<open>prop\<close> covers all cases, i.e., it
is redundant.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Specifying Case Rules"
text_raw\<open>\cbend\<close>

text\<open>
Remember that to write your own case rule you have to specify a theorem which uses variables in
place of the unknowns, such as
@{theory_text[display]
\<open>theorem mycaserule: "\<lbrakk>n = 0 \<Longrightarrow> P; n \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" \<proof>\<close>}\index{mycaserule (example fact)}
which will be converted to unknowns upon turning the proposition to a fact after the proof.
\<close>

subsection \<open>The {\sl cases} Method\<close>
text_raw\<open>\label{case-reasoning-cases}\<close>

text\<open>
Case based reasoning can be performed in a structured proof using the method \<^theory_text>\<open>cases\<close> in the form
@{theory_text[display]
\<open>cases "term" rule: name\<close>}\index{cases (method)}\index{rule: (method argument)}
where \<open>name\<close> is the name of a valid case rule. The method prepares the rule by substituting the
specified \<open>term\<close> for the first unknown in the assumptions, and applies the rule to the first goal
in the goal state.

Additionally, the method creates a named context\index{named context} for every goal resulting from the rule
application. The context contains (only) the variables and assumptions specified in the corresponding
case\index{case} in the case rule. For the most general form depicted above the context for the \<open>i\<close>th case 
contains the variables \cbstart \<open>x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>\<close> and the assumptions \<open>Q\<^sub>i\<^sub>,\<^sub>1 \<dots> Q\<^latex>\<open>$_{i,q_i}$\<close>\<close>\cbend. No term abbreviation
\<open>?case\<close> is defined, because the conclusion of every new goal is the same as that of the original 
goal, thus the existing abbreviation \<open>?thesis\<close>\index{?thesis (term abbreviation)} can be used instead.

The names\index{name!for case}\index{case name} used for the contexts created by the \<^theory_text>\<open>cases\<close> method can be specified by attributing
the case rule. Therefore, predefined case rules often create cases with names which are easy to
understand by a proof writer.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Examples"
text_raw\<open>\cbend\<close>

text\<open>
In Isabelle HOL (see Section~\ref{holtypes}) the rule \<open>\<lbrakk>?Q \<Longrightarrow> ?P; \<not> ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close> is available
under the name \<open>case_split\<close>\index{case-split@case$\_$split (fact name)}. It is attributed to use the case names \<open>True\<close>\index{True (case name)} and \<open>False\<close>\index{False (case name)}. Note that
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
Section~\ref{proof-assume}) if needed for the proof.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Case Rules with Several Unknowns"
text_raw\<open>\cbend\<close>

text\<open>
Often a case rule has only one unknown in the case assumptions. If there are more, several terms
may be specified in the \<^theory_text>\<open>cases\<close> method for preparing the rule. If less terms are specified than
there are unknowns in the case assumptions the resulting goals will contain unbound unknowns which
must be instantiated in the rest of the proof (e.g., by method \<^theory_text>\<open>drule\<close>). If more terms are
specified an error is signaled.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Input Facts for the \<^theory_text>\<open>cases\<close> Method"
text_raw\<open>\cbend\<close>

text\<open>
The \<^theory_text>\<open>cases\<close> method treats input facts like the empty method (see Section~\ref{methods-empty})
by inserting them as assumptions into the original goal before splitting it. Therefore it can be
used both in proof scripts, where facts are stored as rule assumptions in the goal state, and in
structured proofs where facts are stored in the proof context and are input to the initial methods
of subproofs.

However, if the \<^theory_text>\<open>cases\<close> method is specified in the form
@{theory_text[display]
\<open>cases "term"\<close>}
without explicitly naming a case rule and the first input fact has the form of a case rule, it is
used as case rule to split the goal and create the named cases. Therefore in a proof the example
goal can be proved as local fact by inputting (see Section~\ref{proof-this-input}) the case rule in
the form
@{theory_text[display]
\<open>from case_split
have "(x::nat) < c \<Longrightarrow> n*x \<le> n*c"
proof (cases "n = 0")
\<dots>\<close>}\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Automatic Case Rule Selection"
text_raw\<open>\cbend\<close>

text\<open>
Like the \<^theory_text>\<open>rule\<close> method (see Section~\ref{methods-rule-method}) the \<^theory_text>\<open>cases\<close> method supports
automatic rule selection for the case rule, if no case rule is specified or input to the method.
Normally the rule is selected according to the type of the specified \<open>term\<close>. In Isabelle HOL (see 
Section~\ref{holbasic}) most types have an associated case rule\index{case!rule!associated $\sim$}\index{rule!case $\sim$!associated $\sim$}. Only case rules with a single 
unknown in the case assumptions can be automatically selected in this way.

The rule \<open>case_split\<close> is associated with type \<open>bool\<close>. Therefore the example sub proof shown above
also works without inputting the method to the \<^theory_text>\<open>have\<close> statement, because then it is selected
automatically because the term \<open>n = 0\<close> has type \<open>bool\<close>.

The proof writer may not know the case names specified by an automatically selected case rule.
However, they can be determined using the command \<^theory_text>\<open>print_cases\<close> or from the proof skeleton which
is displayed in the interactive editor when the cursor is positioned on the \<^theory_text>\<open>cases\<close> method (see
Section~\ref{case-context-struct}).
\<close>

subsection "Alternative Syntax for Case Rules"
text_raw\<open>\label{case-reasoning-altsynt}\<close>

text\<open>
A case rule as described above always uses an unknown \<open>?P\<close> (or with any other name) as conclusion
and as conclusion in all assumptions. It is used technically to preserve the original conclusion
when a goal is split by applying the rule. Therefore Isabelle supports an alternative syntax for
specifying case rules\index{syntax!alternative $\sim$!for case rules} as theorems which omits the variable for this unknown and specifies only the
information which becomes the content of the named cases.

In a theorem specified in structured form using \<^theory_text>\<open>shows\<close> (see Section~\ref{theory-theorem-altsynt})
the part of the form \<^theory_text>\<open>shows "C"\<close> may alternatively be specified in the form
@{theory_text[display]
\<open>obtains C\<^sub>1 | \<dots> | C\<^sub>k\<close>}\index{obtains (keyword)}
where every case \<open>C\<^sub>i\<close> has the form\cbstart
@{theory_text[display]
\<open>x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close> where "Q\<^sub>i\<^sub>,\<^sub>1" \<dots> "Q\<^latex>\<open>$_{i,q_i}$\<close>"\<close>}\index{where (keyword)}
As usual, the variables \<open>x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>\<close> and the propositions \<open>Q\<^sub>i\<^sub>,\<^sub>1 \<dots> Q\<^latex>\<open>$_{i,q_i}$\<close>\<close>\cbend may be grouped by \<open>and\<close>, for
every variable group a type may be specified and the proposition groups may be named. The keywords
and the \<open>|\<close> separators belong to the outer syntax, the propositions must be individually quoted.

This form is mainly equivalent to
@{theory_text[display]
\<open>shows "\<lbrakk>P\<^sub>1;  \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> thesis"\<close>}
where every \<open>P\<^sub>i\<close> is a rule\cbstart
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>,\<^sub>1\<dots>x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1;\<dots>;Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> thesis\<close>}\cbend
which is exactly the general form of a case rule stated by the \<^theory_text>\<open>shows\<close> clause, using, after proof,
the unknown \<open>?thesis\<close> for all conclusions.

For its own proof the \<^theory_text>\<open>obtains\<close> form creates the same goal as the \<^theory_text>\<open>shows\<close> form, but additionally
it adds all \<open>P\<^sub>i\<close> as assumed facts to the outermost proof context and names this set \<open>that\<close>\index{that (assumption name)}.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Specifying Explicit Case Names"
text_raw\<open>\cbend\<close>

text\<open>
When the theorem is applied as case rule by the \<^theory_text>\<open>cases\<close> method the named context created for case
\<open>C\<^sub>i\<close> is simply named \<open>i\<close>. An explicit name\index{case!name}\index{name!for case} may be specified for it by using the extended form\cbstart
@{theory_text[display]
\<open>(name\<^sub>i) x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close> where "Q\<^sub>i\<^sub>,\<^sub>1" \<dots> "Q\<^latex>\<open>$_{i,q_i}$\<close>"\<close>}\cbend
For its own proof the \<^theory_text>\<open>obtains\<close> form uses \<open>name\<^sub>i\<close>, if present, as additional name for \<open>P\<^sub>i\<close> in its
proof context.

If a case \<open>C\<^sub>i\<close> has no bound variables it has simply the form\cbstart
@{theory_text[display]
\<open>"Q\<^sub>i\<^sub>,\<^sub>1" \<dots> "Q\<^latex>\<open>$_{i,q_i}$\<close>"\<close>}\cbend
which omits the keyword \<^theory_text>\<open>where\<close>, also if an explicit name is specified.

As an example, the rule \<open>case_split\<close> may be defined and proved as
@{theory_text[display]
\<open>theorem case_split:
  obtains (True) "Q" | (False) "\<not> Q"
  by blast\<close>}
using the case names \<open>True\<close> and \<open>False\<close>, as described above, and using the \<^theory_text>\<open>blast\<close> method (see
Section~\ref{methods-auto-methods}) for the proof.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "The \<^theory_text>\<open>consider\<close> Statement"
text_raw\<open>\cbend\<close>

text\<open>
There is also a statement for stating a case rule on the fly in a structured proof. It has the form
@{theory_text[display]
\<open>consider C\<^sub>1 | \<dots> | C\<^sub>k \<proof>\<close>}\index{consider (keyword)}
where the cases \<open>C\<^sub>i\<close> are as above. It is mainly equivalent to the statement
@{theory_text[display]
\<open>have "\<lbrakk>P\<^sub>1;  \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> thesis" \<proof>\<close>}
with \<open>P\<^sub>i\<close> as above and is thus also a goal statement\index{goal!statement}.

However, it is not possible to introduce additional unknowns in the \<open>P\<^sub>i\<close> in a \<^theory_text>\<open>consider\<close> statement.
All variables occurring free in the \<open>P\<^sub>i\<close> are assumed to be bound in the context and are not
converted to unknowns at the end of the statement. Therefore the statement cannot be used to
define general case rules like \<open>case_split\<close> which contains the additional unknown \<open>?Q\<close>. It can only
be used to state that specific propositions cover all (remaining) possibilities in the local proof
context. They need not cover all globally possible cases, if some cases have already been excluded
using locally assumed or proved facts, only the remaining possibilities need to be covered.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Chaining a \<^theory_text>\<open>consider\<close> Statement"
text_raw\<open>\cbend\<close>

text\<open>
Since case rules can be input as fact to a proof by case based reasoning, fact chaining\index{fact!chaining} can be used
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
unknowns in the \<open>C\<^sub>i\<close> which can be instantiated.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Example"
text_raw\<open>\cbend\<close>

text\<open>
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

section "Elimination"
text_raw\<open>\label{case-elim}\<close>

text\<open>
The proof technique of ``(generalized) elimination''\index{elimination} can be seen as a combination of applying a
destruction rule\index{rule!destruction $\sim$} (see Section~\ref{methods-forward-dest}) and an optional case split\index{case!split}. It removes an
assumption with a function application from a goal and splits the rest into cases with additional
assumptions.
\<close>

subsection \<open>The Method {\sl erule}\<close>
text_raw\<open>\label{case-elim-erule}\<close>

text\<open>
Like destruction rule application and case splitting such a step can be implemented by applying a
rule in a specific way to a goal. This is done by the method
@{theory_text[display]
\<open>erule name\<close>}\index{erule (method)}
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
in the resulting goal, as described for the \<^theory_text>\<open>rule\<close> method in Section~\ref{methods-rule-method}.

As for  rules applied by \<^theory_text>\<open>frule\<close> or \<^theory_text>\<open>drule\<close> (see Section~\ref{methods-forward-frule}) the first
assumption \<open>RA\<^sub>1\<close> in the rule is called the ``major premise''\index{major premise} in this context.

The method \<^theory_text>\<open>erule\<close> does not support input facts.
\<close>

subsection "Elimination Rules"
text_raw\<open>\label{case-elim-rules}\<close>

text\<open>
An elimination rule\index{rule!elimination $\sim$} is a generalized combination of a destruction rule and a case rule. It has the
specific form
@{text[display]
\<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>n\<rbrakk> \<Longrightarrow> ?P\<close>}
where the first assumption contains the application of a specific function \<open>f\<close> (perhaps written
using an operator name) which may only occur in different form in the other assumptions. The
conclusion is a single unknown which must not occur in the first assumption and may only occur as
conclusion in other assumption (\cbstart as \cbend in an assumption in a case rule).

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
where every \<open>P\<^sub>i\<close> is a rule of the form\cbstart
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>,\<^sub>1\<dots>x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1;\<dots>;Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> P\<close>}\cbend
and the variable \<open>P\<close> does not occur in the \<open>RA\<^sub>1 \<dots> RA\<^sub>m\<close>.

Analogous to the \<open>intro\<close> set for introduction rules there is an internal fact set \<open>elim\<close>\index{elim (fact set name)} for
elimination rules. It is used by some automatic methods, however, it is not used for automatically
selecting rules for \<open>erule\<close>.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Example"
text_raw\<open>\cbend\<close>

text\<open>
As an example consider the elimination rule specified as
@{theory_text[display]
\<open>theorem elimexmp: "\<lbrakk>(x::nat) \<le> c; x < c \<Longrightarrow> P; x = c \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"\<close>}\index{elimexmp (example fact)}
It replaces an assumption \<open>x \<le> c\<close> by two cases with assumptions \<open>x < c\<close> and \<open>x = c\<close>. If applied to
the goal \<open>(x::nat) \<le> 5 \<Longrightarrow> C\<close> by
@{theory_text[display]
\<open>apply (erule elimexmp)\<close>}
it replaces the goal by the two goals
@{text[display]
\<open>x < 5 \<Longrightarrow> C
x = 5 \<Longrightarrow> C\<close>}\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Searching Elimination Rules"
text_raw\<open>\cbend\<close>

text\<open>
If the cursor in the text area is positioned in a proof, elimination rules applicable to the first
goal in the goal state of the enclosing proof can be searched\index{search!for elimination rules} using the keyword \<open>elim\<close> as criterion
for a search by \<^theory_text>\<open>find_theorems\<close> or in the Query panel, as described in
Section~\ref{theory-theorem-search}. It finds all named facts which can be applied by the \<open>erule\<close>
method to the first goal, i.e., the major premise unifies with a goal assumption and the conclusions
unify as well.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "The \<open>elim\<close> Method"
text_raw\<open>\cbend\<close>

text\<open>
Elimination rule application can be iterated by the method
@{theory_text[display]
\<open>elim name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{elim (method)}
where \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> refer to valid rules. It iterates applying rules by \<^theory_text>\<open>erule\<close> from the given
set to a goal in the goal state as long as this is possible. It is intended to be used with
elimination rules. Then it automatically eliminates functions from assumptions in the goals as much
as possible with the given rules. Note that the method does not use the \<open>elim\<close> set.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Destruction Rules as Elimination Rules"
text_raw\<open>\cbend\<close>

text\<open>
Every destruction rule\index{rule!destruction $\sim$} \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> can be re-stated as the elimination rule
\<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>n;C\<Longrightarrow>?P\<rbrakk> \<Longrightarrow> ?P\<close>. If that is applied by \<^theory_text>\<open>erule\<close> it has the same effect as if the
original rule is applied by method \<^theory_text>\<open>drule\<close>.
\<close>

subsection "Alternative Syntax for Elimination Rules"
text_raw\<open>\label{case-elim-altsynt}\<close>

text\<open>
The alternative syntax available for case rules described in Section~\ref{case-reasoning-altsynt} can
be extended for elimination rules\index{syntax!alternative $\sim$!for elimination rules}. An elimination rule
@{theory_text[display]
\<open>theorem "\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m; P\<^sub>1; \<dots>; P\<^sub>k\<rbrakk> \<Longrightarrow> P" \<proof>\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form\cbstart
@{text[display]
\<open>\<And>x\<^sub>i\<^sub>,\<^sub>1\<dots>x\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1;\<dots>;Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> P\<close>}\cbend
 can be specified using the alternative syntax
@{theory_text[display]
\<open>theorem
assumes "RA\<^sub>1" \<dots> "RA\<^sub>m"
obtains C\<^sub>1 | \<dots> | C\<^sub>k
\<proof>\<close>}\index{obtains (keyword)}
where every \<open>C\<^sub>i\<close> is\cbstart
@{theory_text[display]
\<open>x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close> where "Q\<^sub>i\<^sub>,\<^sub>1" \<dots> "Q\<^latex>\<open>$_{i,q_i}$\<close>"\<close>}\cbend
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

subsection "Elimination in Structured Proofs"
text_raw\<open>\label{case-elim-struct}\<close>

text\<open>
The method \<open>erule\<close> is intended to be used in proof scripts, therefore it does not process input
facts and does not create named cases. In structured proofs elimination can be done using the
\<open>cases\<close> method.

The \<open>cases\<close> method\index{cases (method)} applies a rule by elimination, if the rule is attributed by \<open>[consumes 1]\<close>. This
means the rule will ``consume'' one assumption by unifying it with its major premise and removing
it. A rule may be attributed upon definition in the form
@{theory_text[display]
\<open>theorem [consumes 1]: "prop" \<proof>\<close>}\index{consumes (attribute)}
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
  \<proof>\<close>}\index{elimexmp (example fact)}
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

section "Induction"
text_raw\<open>\label{case-induction}\<close>

text\<open>
With induction\index{induction} a goal is proved by processing ``all possible cases'' for certain values which
occur in it. If the goal can be proved for all these cases and the cases cover all
possibilities, the goal holds generally. A specific
technique is to assume the goal for some values and then prove it for other values. In this
way it is possible to cover infinite value sets by proofs for only a finite number of values and 
steps from values to other values.

Perhaps the best known example of induction is a proposition which is proved for the natural number
\<open>0\<close> and the step from a number \<open>n\<close> to its successor \<open>n+1\<close>, which together covers the whole infinite
set of natural numbers. 

As a (trivial) example consider the proposition \<open>0\<le>n\<close>. To prove that it is valid for all natural numbers
\<open>n\<close> we prove the ``base case''\index{induction!base case} where \<open>n\<close> is \<open>0\<close>, which is true because \<open>0\<le>0\<close>. Then we prove the
``induction step''\index{induction!step}, by assuming that \<open>0\<le>n\<close> (the ``induction hypothesis''\index{induction!hypothesis}) and proving that \<open>0\<le>n+1\<close> 
follows, which is true because addition increases the value.
\<close>

subsection "Induction Rules"
text_raw\<open>\label{case-induction-rules}\<close>

text\<open>
\cbstart As \cbend for case based reasoning (see Section~\ref{case-reasoning}) a goal is split into these
cases\index{case!split} by applying a meta rule. For induction the splitting can be done by a meta rule of the form
@{text[display]
\<open>\<lbrakk>P\<^sub>1 ; ...; P\<^sub>n \<rbrakk> \<Longrightarrow> ?P ?a\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form\cbstart
@{text[display]
\<open>\<And>y\<^sub>i\<^sub>,\<^sub>1 \<dots> y\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<rbrakk> \<Longrightarrow> ?P term\<^sub>i\<close>}
where the assumptions \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> may contain the unknown \<open>?P\<close> but no other unknowns, in particular not
\<open>?a\<close>. A rule for a base case usually has no bound variables \<open>y\<^sub>i\<^sub>,\<^sub>j\<close> and no assumptions
\<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>, at least the \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> do not contain \<open>?P\<close>. The remaining rules mostly have only a single
assumption \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>\cbend which contains \<open>?P\<close>.

\cbstart Rules of this form are called ``induction rules''\index{induction!rule}\index{rule!induction $\sim$}\cbend. Note that the unknown \<open>?a\<close> only occurs once in the conclusion of the meta rule and nowhere else. Like
the case rules induction rules must be ``prepared'' for use, this is done by replacing \<open>?a\<close>
by a specific term \<open>term\<close>. This is the term for which all possible cases shall be processed
in the goal. It must have the same type as all \<open>term\<^sub>i\<close> in the \<open>P\<^sub>i\<close>.

Usually, ``all possible cases'' means all values of the type of \<open>term\<close>, then \<open>term\<close> consists of a 
single variable which may adopt any values of its type. There are also other forms of induction where
more complex terms are used, but they are not presented in this introduction, refer to other 
Isabelle documentations \cbstart \<^cite>\<open>"isar-ref" and "prog-prove"\<close> \cbend for them. In the following the unknown \<open>?a\<close> will always be replaced by a
variable \<open>x\<close>.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Applying Induction Rules"
text_raw\<open>\cbend\<close>

text\<open>
When a prepared induction rule is applied to a goal \<open>C\<close> without bound variables and assumptions as 
described in Section~\ref{methods-rule-method}, it unifies \<open>?P x\<close> with the conclusion \<open>C\<close>. This has
the effect of abstracting \<open>C\<close> to a (boolean) function \<open>PC\<close> by identifying all places where \<open>x\<close>
occurs in \<open>C\<close> and replacing it by the function argument. The function \<open>PC\<close> is then bound to the 
unknown \<open>?P\<close>, so that applying \<open>?P\<close> to the argument \<open>x\<close> again yields \<open>C\<close>. The function
\<open>PC\<close> is the property to be proved for all possible argument values. Therefore the cases of the proof
can be described by applying \<open>?P\<close> to the terms \<open>term\<^sub>i\<close> for the specific values in the rules \<open>P\<^sub>i\<close> for 
the cases. 

The application of the prepared rule results in the \<open>n\<close> goals\cbstart
@{text[display]
\<open>\<And> y\<^sub>1\<^sub>,\<^sub>1 \<dots> y\<^latex>\<open>$_{1,p_1}$\<close>. \<lbrakk>Q\<^sub>1\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{1,q_1}$\<close>\<rbrakk> \<Longrightarrow> PC term\<^sub>1
\<dots>
\<And> y\<^sub>n\<^sub>,\<^sub>1 \<dots> y\<^latex>\<open>$_{n,p_n}$\<close>. \<lbrakk>Q\<^sub>n\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{n,q_n}$\<close>\<rbrakk> \<Longrightarrow> PC term\<^sub>n\<close>}\cbend

The induction rule is only valid if the terms \<open>term\<^sub>i\<close> cover all possible values of their associated
type. If this has been proved the induction rule is available as a fact which can be applied.
After preparing the induction rule for application, its conclusion \<open>?P x\<close> 
matches all propositions which contain the variable \<open>x\<close> in one or more copies. It depends 
on the \<open>P\<^sub>i\<close> in the rule whether splitting a specific goal with the induction rule is useful for 
proving the goal.

The real power of induction rules emerges, when a \cbstart \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> contains the unknown \<open>?P\<close>. Due to the
type associated with \<open>?P\<close> it must be applied to an argument \<open>term\<^sub>i\<^sub>,\<^sub>j\<close> of the same type as \<open>x\<close> and
the \<open>term\<^sub>i\<close>. Then the goal resulting from \<open>P\<^sub>i\<close> states the property that if \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> holds when
specialized to \<open>PC term\<^sub>i\<^sub>,\<^sub>j\<close>, \<open>PC\<close> holds for \<open>term\<^sub>i\<close> (an ``induction step''\index{induction!step}). Thus, for covering the
possible values of \<open>x\<close>, the step from \<open>term\<^sub>i\<^sub>,\<^sub>j\<close>\cbend to \<open>term\<^sub>i\<close> can be repeated arbitrarily often which
allows to cover some types with infinite value sets.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Example"
text_raw\<open>\cbend\<close>

text\<open>
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
which correspond to the base case and induction step as described above.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "General Form of Induction Rules"
text_raw\<open>\cbend\<close>

text\<open>
Induction rules\index{induction!rule}\index{rule!induction $\sim$} may even be more general than shown above. Instead of applying \<open>?P\<close> to a single 
argument it may have several arguments and the conclusion becomes \<open>?P ?a\<^sub>1 \<dots> ?a\<^sub>r\<close>. Also in the
\<open>P\<^sub>i\<close> every occurrence of \<open>?P\<close> then has \<open>r\<close> terms as arguments. Such an induction rule is valid if it
covers all possible cases for all combinations of the \<open>r\<close> argument values. Finally, in addition
to the assumptions \<open>P\<^sub>i\<close> an induction rule may have assumptions about the argument \<open>?a\<close>
or the arguments \<open>?a\<^sub>1 \<dots> ?a\<^sub>r\<close>.

Note, however, that there is no alternative syntax for induction rules, such as the \<^theory_text>\<open>obtains\<close> form
for case rules.
\<close>

subsection \<open>The {\sl induction} Method\<close>
text_raw\<open>\label{case-induction-method}\<close>

text\<open>
Induction can be performed in a structured proof using the method \<^theory_text>\<open>induction\<close> in the form
@{theory_text[display]
\<open>induction x rule: name\<close>}\index{induction (method)}\index{rule: (method argument)}
where \<open>name\<close> is the name of a valid induction rule. The method prepares the rule by substituting the
specified variable \<open>x\<close> for the unknown \<open>?a\<close> and applies the rule to the first goal in the
goal state. 

Additionally, the method creates a named context\index{named context} for every goal resulting from the rule
application. The context contains the variables and assumptions specified in the corresponding
case in the induction rule. For the general form depicted above the context for the \<open>i\<close>th case 
contains the variables \cbstart \<open>y\<^sub>i\<^sub>,\<^sub>1 \<dots> y\<^latex>\<open>$_{i,p_i}$\<close>\<close> and the assumptions \<open>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>\<close>\cbend. 
The term abbreviation \<open>?case\<close>\index{?case (term abbreviation)} is defined for the case conclusion \<open>PC term\<^sub>i\<close> which is to
be proved for the case.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Input Facts"
text_raw\<open>\cbend\<close>

text\<open>
The \<^theory_text>\<open>induction\<close> method treats input facts like the empty method (see Section~\ref{methods-empty})
and the \<^theory_text>\<open>cases\<close> method (see Section~\ref{case-reasoning-cases}) by inserting them as assumptions 
into the original goal before splitting it.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Automatic Rule Selection"
text_raw\<open>\cbend\<close>

text\<open>
Also like the \<^theory_text>\<open>cases\<close> method the \<^theory_text>\<open>induction\<close> method supports
automatic rule selection for the induction rule. This is only possible if \<open>?P\<close> is applied to a single
argument, which means that only one variable is specified in the method:
@{theory_text[display]
\<open>induction x\<close>}
Then the rule is selected according to the type of \<open>x\<close>. In Isabelle HOL (see 
Section~\ref{holbasic}) most types have an associated induction rule.\<close>

text_raw\<open>\cbstart\<close>
subsubsection "Examples"
text_raw\<open>\cbend\<close>

text\<open>
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

\cbstart As \cbend for the \<^theory_text>\<open>cases\<close> method (see Section~\ref{case-reasoning-cases}) the names used for the contexts 
created by the \<^theory_text>\<open>induction\<close> method can be specified by attributing the induction rule. They can be 
determined from the proof skeleton which is displayed in the interactive editor
when the cursor is positioned on the \<^theory_text>\<open>induction\<close> method (see Section~\ref{case-context-struct}).

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

subsection "Case Assumption Naming and the \<^theory_text>\<open>induct\<close> Method"
text_raw\<open>\label{case-induction-naming}\<close>

text\<open>
As usual, the \<^theory_text>\<open>case\<close> statement uses the case name as name for the assumptions \cbstart \<open>Q\<^sub>i\<^sub>,\<^sub>1 \<dots> Q\<^latex>\<open>$_{i,q_i}$\<close>\<close>\cbend in the
\<open>i\<close>th case or an explicit name\index{name!for assumption}\index{assumption!name} may be specified for them (see Section~\ref{case-context-case}).
Additionally, the \<open>induction\<close> method arranges the named context for a case so that the set of
assumptions is split into those which in the rule contain the unknown \<open>?P\<close> and those which do not.
These sets are separately named, so that they can be referenced individually.

The set of assumptions which originally contained \<open>?P\<close> now contain an application of \<open>PC\<close> to
a value \cbstart \<open>term\<^sub>i\<^sub>,\<^sub>j\<close>\cbend and allow the step from this value to value \<open>term\<^sub>i\<close> by induction. These assumptions
are called ``induction hypotheses'' and are named \<open>"cname.IH"\<close>\index{IH@.IH (fact name suffix)} where \<open>cname\<close> is the case name or the
explicit name for the case assumptions. The other assumptions are independent from \<open>PC\<close>, they are 
additional hypotheses and are named \<open>"cname.hyps"\<close>\index{hyps@.hyps (fact name suffix)}. Both forms of names
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

There is a method \<^theory_text>\<open>induct\<close>\index{induct (method)} which behaves like \<^theory_text>\<open>induction\<close> with the only difference that it does 
not introduce the name \<open>"cname.IH"\<close>, it uses \<open>"cname.hyps"\<close> for all assumptions \<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>q\<^sub>i\<close>, whether
they contain \<open>?P\<close> or not.
\<close>

subsection "Goals with Assumptions"
text_raw\<open>\label{case-induction-assms}\<close>

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
or in a \cbstart \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>\cbend in the rule by an application \<open>PC term\<close> together with assumptions \<open>PA\<^sub>1 term; \<dots>;
PA\<^sub>m term\<close>.

The assumptions for a direct occurrence of \<open>?P term\<^sub>i\<close> as conclusion in a \<open>P\<^sub>i\<close> are added after all \cbstart
\<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>, so that the \<open>i\<close>th goal created by the \<open>induction\<close> method now has the form
@{text[display]
\<open>\<And> y\<^sub>i\<^sub>,\<^sub>1 \<dots> y\<^latex>\<open>$_{i,p_i}$\<close>. \<lbrakk>Q\<^sub>i\<^sub>,\<^sub>1; \<dots>; Q\<^latex>\<open>$_{i,q_i}$\<close>; PA\<^sub>1 term\<^sub>i; \<dots>; PA\<^sub>m term\<^sub>i\<rbrakk> \<Longrightarrow> PC term\<^sub>i\<close>}
Additionally, the assumptions for occurrences of a \<open>?P term\<close> in a \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> must be added which usually
can be done by replacing \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> by the rule \<open>Q\<^sub>i\<^sub>,\<^sub>j'\<close> of the form \<open>\<lbrakk>PA\<^sub>1 term; \<dots>; PA\<^sub>m term\<rbrakk> \<Longrightarrow> Q\<^sub>i\<^sub>,\<^sub>j''\<close>
where \<open>Q\<^sub>i\<^sub>,\<^sub>j''\<close> results by substituting \<open>?P term\<close> in \<open>Q\<^sub>i\<^sub>j\<close> by \<open>PC term\<close>. If \<open>?P\<close> is applied to several
different terms in \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close>, several sets of corresponding assumptions are added in \<open>Q\<^sub>i\<^sub>,\<^sub>j'\<close>\cbend.

Moreover, the \<open>induction\<close> method (and also the \<open>induct\<close> method) arranges the named contexts in a
way that the assumptions \<open>PA\<^sub>1 term\<^sub>i; \<dots>; PA\<^sub>m term\<^sub>i\<close> which originate from the goal are named by
\<open>"cname.prems"\<close>\index{prems@.prems (fact name suffix)} and can thus be referenced separate from the \<open>Q\<^sub>i\<^sub>j'\<close> which are named \<open>"cname.hyps"\<close>
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

subsection "Induction with Elimination"
text_raw\<open>\label{case-induction-elim}\<close>

text\<open>
Like case rules, induction rules can be extended to include elimination\index{elimination} (see
Section~\ref{case-elim-rules}). Such induction rules have an additional first assumption which is
used as major premise\index{major premise} to unify with a goal assumption and eliminate it, before processing the
remaining goal assumptions and splitting the goal into cases.

Like case rules such extended induction rules must be attributed by \<open>[consumes 1]\<close>\index{consumes (attribute)}, then the methods
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

subsection "Arbitrary Variables"
text_raw\<open>\label{case-induction-arbitrary}\<close>

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
\<open>induction x arbitrary: x\<^sub>1 \<dots> x\<^sub>k rule: name\<close>}\index{arbitrary: (method argument)}
and in the same form for the \<open>induct\<close> method.

In particular, if a theorem or goal statement is specified in structured form the free variables
are not bound in the goal but in the outermost proof context (see Section~\ref{proof-state-initial})
and the goal only consists of the conclusion \<open>C\<close>. To apply induction as initial proof method the
assumptions must be input to it and the variables must be specified as arbitrary:
@{theory_text[display]
\<open>theorem 
  fixes x\<^sub>1 \<dots> x\<^sub>k
  assumes "A\<^sub>1" \<dots> "A\<^sub>m"
  shows "C"
using assms
proof (induction \<dots> arbitrary: x\<^sub>1 \<dots> x\<^sub>k \<dots>) \<dots> qed\<close>}\<close>


end