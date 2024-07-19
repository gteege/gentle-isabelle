theory Chapter_methods
  imports Chapter_proofs
begin
chapter "Proof Methods"
text_raw\<open>\label{methods}\<close>

text \<open>
The basic building blocks of Isabelle proofs are the proof methods\index{proof!method} which modify the goal state.
If there are several goals in the goal state it depends on the specific method which goals 
are affected by it. In most cases only the first goal is affected.
\<close>

section "The empty Method"
text_raw\<open>\label{methods-empty}\<close>

text\<open>
The empty method\index{method!empty $\sim$} is denoted by a single minus sign
@{theory_text[display]
\<open>-\<close>}\index{-@\<open>-\<close> (method)}
If no input facts are passed to it, it does nothing, it does not alter the goal state.  An exception
is a goal of the form \<open>C\<^sub>1 &&& \<dots> &&& C\<^sub>h\<close> which is always split to separate goals \<open>C\<^sub>i\<close> whenever a
method is applied (see section~\ref{proof-state-initial}).

The empty method is useful at the beginning of a structured proof of the form
@{theory_text[display]
\<open>proof method ST\<^sub>1 \<dots> ST\<^sub>n qed\<close>}
If the statements \<open>ST\<^sub>1 \<dots> ST\<^sub>n\<close> shall process the unmodified original goal the 
empty method must be specified for \<open>method\<close>, thus the structured proof becomes
@{theory_text[display]
\<open>proof - ST\<^sub>1 \<dots> ST\<^sub>n qed\<close>}

Note that it is possible to syntactically omit the \<open>method\<close> completely, but then it defaults to the 
method named \<open>standard\<close> which alters the goal state  (see Section~\ref{methods-rule-standard}).

If input facts are passed to the empty method, it affects all goals by inserting the input facts as 
assumptions after the existing assumptions. If the input facts are \<open>F\<^sub>1,\<dots>,F\<^sub>m\<close> a goal of the form 
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> is replaced by the goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n;F\<^sub>1,\<dots>,F\<^sub>m\<rbrakk> \<Longrightarrow> C\<close>.

This makes it possible to transfer facts stored in the proof context to the goal state where they
are stored as rule assumptions (see Section~\ref{proof-proc-store}). Since this way of storing facts
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

section "Terminating Proof Scripts"
text_raw\<open>\label{methods-assumption}\<close>

text\<open>
As described in Section~\ref{proof-state-goal} a proof is complete when its goal state is empty.
In a structured proof goals are removed from the goal state by successful \<^theory_text>\<open>show\<close> statements.
Therefore a structured proof is usually terminated by a \<^theory_text>\<open>show\<close> statement which removes the last
goal in the goal state.

Proof scripts, instead, are intended to store facts as rule assumptions in the goal state (see
Section~\ref{proof-struct-syntax}). Then the proof of a goal is complete when the conclusion of the
current goal unifies with one of its assumptions (see Section~\ref{proof-proc-construct}).
\<close>

subsection \<open>The {\sl assumption} Method\<close>
text_raw\<open>\label{methods-assumption-method}\<close>

text\<open>
Such goals are removed from the goal state by the method
@{theory_text[display]
\<open>assumption\<close>}\index{assumption (method)}
The method only affects the first goal. If that goal has the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and one
assumption \<open>A\<^sub>i\<close> unifies with \<open>C\<close> the method removes the goal, otherwise an error is signaled.

The \<^theory_text>\<open>assumption\<close> method is automatically applied by a proof part of the form
@{theory_text[display]
\<open>qed method\<close>}
after applying the specified \<open>method\<close>. The application of the \<^theory_text>\<open>assumption\<close> method is repeated as
long as it is applicable, thus \<^theory_text>\<open>qed\<close>\index{qed (keyword)} removes all goals from the goal state where the conclusion
matches an assumption. The same holds for the abbreviated forms \<^theory_text>\<open>by method\<close> and \<^theory_text>\<open>by method\<^sub>1
method\<^sub>2\<close> (see Section~\ref{proof-struct-syntax}).

Therefore a proof script consisting of method applications \<open>MA\<^sub>1 \<dots> MA\<^sub>n\<close> can be terminated by \<^theory_text>\<open>by -\<close>
if the method applications refine all goals to the form where the conclusion unifies with an
assumption. Note that \<^theory_text>\<open>done\<close> does not remove such goals, when it is used to terminate a proof it
expects that the goal state is already empty.
\<close>

section "Basic Rule Application"
text_raw\<open>\label{methods-rule}\<close>

text \<open>
As described in Section~\ref{proof-proc-construct} the basic step in the construction of a proof
is to establish the connection between a fact \<open>F\<^sub>i\<close> and a fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> in the fact sequence. Assume
that there is already a valid derivation rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> named \<open>r\<^sub>i\<close> where \<open>RA\<^sub>i\<close> unifies with 
\<open>F\<^sub>i\<close> and \<open>RC\<^sub>i\<close> unifies with \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. Then the connection can be established by applying that rule\index{rule!application}.
\<close>

subsection \<open>The {\sl rule} Method\<close>
text_raw\<open>\label{methods-rule-method}\<close>

text\<open>
A rule is applied by the method
@{theory_text[display]
\<open>rule name\<close>}\index{rule (method)}
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
Section~\ref{proof-proc-store}) an application of method \<^theory_text>\<open>rule\<close> preserves these facts and copies
them to every new goal.

If an assumption \<open>RA\<^sub>j\<close> is again a rule (i.e., the applied rule is a meta rule) and has the form
\<open>\<lbrakk>B\<^sub>1;\<dots>;B\<^sub>k\<rbrakk> \<Longrightarrow> B\<close> the \<open>j\<close>th new goal becomes \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> (\<lbrakk>B\<^sub>1';\<dots>;B\<^sub>k'\<rbrakk> \<Longrightarrow> B')\<close> which by
definition of the \<open>\<lbrakk>\<dots>;\<dots> \<rbrakk>\<close> syntax (see Section~\ref{theory-prop-altsynt}) is equivalent to
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n;B\<^sub>1';\<dots>;B\<^sub>k'\<rbrakk> \<Longrightarrow> B')\<close>. In this way the rule can introduce additional assumptions in the
resulting goals, which are inserted after the existing assumptions.
\<close>

subsection \<open>Using the {\sl rule} Method for Backward Reasoning Steps\<close>
text_raw\<open>\label{methods-rule-backwards}\<close>

text\<open>
Assume that during a proof for \<open>A \<Longrightarrow> C\<close> as described in Section~\ref{proof-proc-construct} the
intermediate fact sequence \<open>F\<^sub>i\<^sub>+\<^sub>1, \<dots> F\<^sub>n\<^sub>-\<^sub>1, C\<close> has already been constructed by backward
reasoning\index{backward reasoning}\index{reasoning!backward $\sim$}, i.e., the current goal is \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. If \<open>r\<^sub>i\<close> names a rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>, the successful
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

Note that we used the \<^theory_text>\<open>assumption\<close>\index{assumption (method)} method to remove the goal \<open>A \<Longrightarrow> F\<^sub>1\<close> by unifying \<open>F\<^sub>1\<close> with \<open>A\<close>.
Alternatively we can use the form
@{theory_text[display]
\<open>apply (rule `r\<^sub>n\<^sub>-\<^sub>1`)
\<dots>
apply(rule r\<^sub>1)
by -\<close>} 
where the \<^theory_text>\<open>assumption\<close> method is applied implicitly, as described in
Section~\ref{methods-assumption-method}, or even shorter
@{theory_text[display]
\<open>apply (rule `r\<^sub>n\<^sub>-\<^sub>1`)
\<dots>
by (rule r\<^sub>1)\<close>}

If the example from Section~\ref{proof-proc-construct} is proved this way the theorem is written
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

subsection "Automatic Rule Selection"
text_raw\<open>\label{methods-rule-select}\<close>

text\<open>
The \<open>rule\<close> method can be specified in the form
@{theory_text[display]
\<open>rule\<close>}
without naming the rule to be applied. Then it selects a rule automatically. It uses the first
rule from the internal fact set \<open>intro\<close>\index{intro (fact set name)} for which the conclusion unifies with the goal conclusion.
If there is no such rule in the set an error is signaled.

If the rules \<open>example1\<close> and \<open>example2\<close> would be in the \<open>intro\<close> set, the example proof could
be written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
  apply rule
  by rule\<close>}
\<close>

subsection "Introduction Rules"
text_raw\<open>\label{methods-rule-intro}\<close>

text\<open>
The set \<open>intro\<close> is intended by Isabelle for a specific kind of rules called ``introduction rules''\index{rule!introduction $\sim$}.
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

A rule is also called an introduction rule for a function \<open>f\<close> if \<open>f\<close> occurs in some assumption(s)
but in a different form (usually applied to other arguments). Then an application by the \<^theory_text>\<open>rule\<close>
method will replace a term containing \<open>f\<close> by a different term containing \<open>f\<close>. The idea is to replace
terms in several steps using one or more introduction rules until finally removing \<open>f\<close> completely.\<close>

subsubsection "The \<open>intro\<close> Method"

text\<open>
This proof technique can also be applied by the method
@{theory_text[display]
\<open>intro name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{intro (method)}
where \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> refer to valid rules. It iterates applying rules from the given set to a goal
in the goal state as long as this is possible. It is intended to be used with introduction rules.
Then it automatically deconstructs the goals as much as possible with the given rules. Note that
the method does not use the \<open>intro\<close> set.\<close>

subsubsection "Examples"

text\<open>
The rule \<open>example1\<close> from Section~\ref{theory-theorem-named} is an introduction rule for both
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
Section~\ref{methods-auto-methods}.\<close>

subsubsection "Searching Introduction Rules"

text\<open>
If the cursor in the text area is positioned in a proof, introduction rules applicable to the first
goal in the goal state of the enclosing proof can be searched\index{search!for introduction rules} using the keyword \<open>intro\<close> as criterion
for a search by \<^theory_text>\<open>find_theorems\<close> or in the Query panel\index{panel!query $\sim$}, as described in
Section~\ref{theory-theorem-search}. It finds all named facts which can be applied by the \<open>rule\<close>
method to the first goal, i.e., the conclusions can be unified.
\<close>

subsection \<open>The {\sl standard} Method\<close>
text_raw\<open>\label{methods-rule-standard}\<close>

text\<open>
The method
@{theory_text[display]
\<open>standard\<close>}\index{standard (method)}
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
the proof anymore.\<close>

subsubsection "The \<open>..\<close> Proof"

text\<open>
In the abbreviated form \<^theory_text>\<open>by method\<close> of a structured proof the method cannot be omitted, but
the proof \<^theory_text>\<open>by standard\<close> can be abbreviated to
@{theory_text[display]
\<open>..\<close>}\index{.. (keyword)}
(two dots). It can be used as complete proof for a proposition which can be proved by a single
automatic rule application. Since in the example proof also rule \<open>example1\<close> could be automatically
selected by the \<^theory_text>\<open>standard\<close> method, it could be further abbreviated as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof
  show "x < 5 \<Longrightarrow> 2*x \<le> 2*5" ..
qed\<close>}\<close>

section "Rule Application in Forward Reasoning"
text_raw\<open>\label{methods-forward}\<close>

text\<open>
Assume that during a proof for \<open>A \<Longrightarrow> C\<close> as described in Section~\ref{proof-proc-construct} the
intermediate fact sequence \<open>A, F\<^sub>2, \<dots>, F\<^sub>i\<close> has already been constructed by forward reasoning\index{forward reasoning}\index{reasoning!forward $\sim$} and has
been stored in the proof context. Then the next step is to state fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and prove it using a
rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> named \<open>r\<^sub>i\<close>. \<close>

subsection \<open>Using the {\sl rule} Method for Forward Reasoning Steps\<close>
text_raw\<open>\label{methods-forward-rule}\<close>

text\<open>
Using method \<^theory_text>\<open>rule\<close>\index{rule (method)} the step can be started by the statement
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" proof (rule r\<^sub>i)\<close>}
The goal of this subproof is simply \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>, so applying the \<^theory_text>\<open>rule\<close> method with \<open>r\<^sub>i\<close> will result
in the new goal \<open>RA\<^sub>i'\<close> which unifies with \<open>F\<^sub>i\<close>. The subproof is not finished, since its goal state 
is not empty. But the goal unifies with an already known fact. Solving a goal which
resulted from an assumption of an applied rule is also called ``discharging an assumption''.\<close>

subsubsection "Discharging Assumptions Using the \<open>fact\<close> Method"

text\<open>
The proof method
@{theory_text[display]
\<open>fact name\<close>}\index{fact (method)}
can be used to remove that goal. The method only affects the first goal. If the fact referred by
\<open>name\<close> unifies with it, the goal is removed, otherwise an error is signaled.

Using this method the forward reasoning step can be completed as
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" proof (rule r\<^sub>i) qed (fact f\<^sub>i)\<close>}
if \<open>F\<^sub>i\<close> has been named \<open>f\<^sub>i\<close>. This can be abbreviated (see Section~\ref{proof-struct-syntax}) to
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

If the example from Section~\ref{proof-proc-construct} is proved this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume a: "x < 5"
  have f\<^sub>2: "2*x \<le> 2*5" by (rule example1) (fact a)
  show ?thesis by (rule example2) (fact f\<^sub>2)
qed\<close>}\<close>

subsubsection "Automatic Fact Selection"

text\<open>
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

subsection \<open>Input Facts for the {\sl rule} Method\<close>
text_raw\<open>\label{methods-forward-input}\<close>

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
that the corresponding goals are never created.\<close>

subsubsection "Discharging Assumptions Using Explicit Fact Input"

text\<open>
This allows to establish the connection from a fact \<open>F\<^sub>i\<close> to \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> in a fact chain by a
forward reasoning step of the form
@{theory_text[display]
\<open>from f\<^sub>i have "F\<^sub>i\<^sub>+\<^sub>1" by (rule r\<^sub>i)\<close>}
where \<open>f\<^sub>i\<close> names the fact \<open>F\<^sub>i\<close>. When it is input to the goal statement it is passed to
the \<^theory_text>\<open>rule\<close> method and removes the assumption from the applied rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>, resulting
in the assumption-less ``rule'' \<open>RC\<^sub>i\<close>. When it is applied to the goal \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> it unifies and
removes the goal, thus the subproof is complete.\<close>

subsubsection "Discharging Assumptions Using Chaining"

text\<open>
For the fact sequence chaining can be used to write a structured proof without naming the facts:
@{theory_text[display]
\<open>proof -
assume "F\<^sub>1"
then have "F\<^sub>2" by (rule r\<^sub>1)
\<dots>
then have "F\<^sub>n\<^sub>-\<^sub>1" by (rule `r\<^sub>n\<^sub>-\<^sub>2`)
then show "F\<^sub>n" by (rule `r\<^sub>n\<^sub>-\<^sub>1`)
qed\<close>}
As described in Section~\ref{methods-rule-standard} the subproof \<open>by (rule r\<^sub>i)\<close> can be abbreviated as
\<open>..\<close> if the rule \<open>r\<^sub>i\<close> is in the \<open>intro\<close> rule set.

If the example from Section~\ref{proof-proc-construct} is proved this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume "x < 5"
  then have "2*x \<le> 2*5" by (rule example1)
  then show ?thesis by (rule example2)
qed\<close>}
\<close>

subsection \<open>The Method {\sl this}\<close>
text_raw\<open>\label{methods-forward-this}\<close>

text\<open>
Rule application can also be done by the method
@{theory_text[display]
\<open>this\<close>}\index{this (method)}
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
the subproof.\<close>

subsubsection "The \<open>.\<close> Proof"

text\<open>
The proof
@{theory_text[display]
\<open>by this\<close>}
can be abbreviated by \<open>.\<close>\index{. (keyword)} (a single dot).

Therefore the example from Section~\ref{proof-proc-construct} can also be proved in the form
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume "x < 5"
  with example1 have "2*x \<le> 2*5" .
  with example2 show ?thesis .
qed\<close>}\<close>

subsection \<open>The Methods {\sl frule} and {\sl drule}\<close>
text_raw\<open>\label{methods-forward-frule}\<close>

text\<open>
Instead of storing facts in the proof context and using a structured proof for a forward reasoning
proof the facts may be stored as rule assumptions in the goal state and the forward reasoning proof
may be written as a proof script (see Section~\ref{proof-struct-syntax}). 

To construct a proof for the goal \<open>A \<Longrightarrow> C\<close> as fact sequence \<open>A, F\<^sub>2 \<dots> F\<^sub>n\<close> by forward reasoning as
described in Section~\ref{proof-proc-construct} in this way, the intermediate fact sequence
\<open>A, F\<^sub>2, \<dots>, F\<^sub>i\<close> is stored in the extended goal \<open>\<lbrakk>A; F\<^sub>2; \<dots>; F\<^sub>i\<rbrakk> \<Longrightarrow> C\<close> where the last assumption is
the current fact \<open>F\<^sub>i\<close>. Then the next forward reasoning step consists of adding the fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> as
new assumption to the goal and prove it using a rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> named \<open>r\<^sub>i\<close>. When the fact
sequence is complete the goal is \<open>\<lbrakk>A; F\<^sub>2; \<dots>; F\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and \<open>F\<^sub>n\<close> unifies with \<open>C\<close>, thus an
application of method \<^theory_text>\<open>assumption\<close> will remove the goal and terminate the proof
(see Section~\ref{methods-assumption-method}).\<close>

subsubsection "The \<open>frule\<close> Method"

text\<open>
A rule is applied for forward reasoning by the method
@{theory_text[display]
\<open>frule name\<close>}\index{frule (method)}
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
called the ``major premise''\index{major premise} of the rule.

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

If the example from Section~\ref{proof-proc-construct} is proved this way the theorem is written
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
assumption into account.\<close>

subsubsection "The \<open>drule\<close> Method"

text\<open>
The second drawback can be compensated for by using another method for applying the rule. This is
done by the method
@{theory_text[display]
\<open>drule name\<close>}\index{drule (method)}
where \<open>name\<close> is the name of a valid rule. The method works like \<^theory_text>\<open>frule\<close>, but instead of adding 
\<open>RC'\<close> to the assumptions it replaces \<open>A\<^sub>k\<close> by it. Thus the method replaces the goal by the \<open>m-1\<close> new
goals \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>k\<^sub>-\<^sub>1; A\<^sub>k\<^sub>+\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>j'\<close> for  \<open>j > 1\<close> and the goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>k\<^sub>-\<^sub>1;A\<^sub>k\<^sub>+\<^sub>1;\<dots>;A\<^sub>n;RC'\<rbrakk> \<Longrightarrow> C\<close>.

When using \<^theory_text>\<open>drule\<close> for constructing a proof in the way described above, it always replaces the
current fact by the next one in the fact sequence. The intermediate fact sequence is represented by
the goal \<open>F\<^sub>i \<Longrightarrow> C\<close>. Since the current fact is the only assumption present in the goal, the step
\<^theory_text>\<open>apply (drule r\<^sub>i)\<close> is always applied to it and replaces the goal by \<open>F\<^sub>i\<^sub>+\<^sub>1 \<Longrightarrow> C\<close>, as intended.

The methods \<^theory_text>\<open>frule\<close> and \<^theory_text>\<open>drule\<close> do not support input facts.
\<close>

subsection "Destruction Rules"
text_raw\<open>\label{methods-forward-dest}\<close>

text\<open>
Not all rules can always usefully be applied by \<^theory_text>\<open>frule\<close> and \<^theory_text>\<open>drule\<close>. Since both methods only
unify their first assumption (the major premise) of the rule with a term in the goal and then replace
it by the conclusion, the first assumption should have some effect on the conclusion. In particular,
the conclusion should not be a single unknown which does not occur in the first assumption.

If additionally a specific function \<open>f\<close> (perhaps written using an operator name) occurs only in the
first assumption and neither in the conclusion, nor in other assumptions, the rule is called a
``destruction rule''\index{rule!destruction $\sim$} for \<open>f\<close>. If it is applied in forward direction, such as with  \<^theory_text>\<open>frule\<close>
and \<^theory_text>\<open>drule\<close>, \<open>f\<close> will be removed from the goal, it will be ``destructed''.

Similar to introduction rules (see Section~\ref{methods-rule-intro}) \<open>f\<close> may occur in the
conclusion if it has a different form, so that it may be removed by several steps through
intermediate forms.

Analogous to the \<open>intro\<close> set for introduction rules there is an internal fact set \<open>dest\<close>\index{dest (fact set name)} for
destruction rules. It is used by some automatic methods, however, it is not used for automatically
selecting rules for \<^theory_text>\<open>frule\<close> and \<^theory_text>\<open>drule\<close>.\<close>

subsubsection "Searching Destruction Rules"

text\<open>
If the cursor in the text area is positioned in a proof, destruction rules applicable to the first
goal in the goal state of the enclosing proof can be searched\index{search!for destruction rules} using the keyword \<open>dest\<close> as criterion
for a search by \<^theory_text>\<open>find_theorems\<close> or in the Query panel, as described in
Section~\ref{theory-theorem-search}. It finds all named facts which can be applied by the \<open>frule\<close>
or \<open>drule\<close> method to the first goal, i.e., the major premise unifies with a goal assumption.\<close>

subsubsection "Examples"

text\<open>
The rule \<open>example1\<close> from Section~\ref{theory-theorem-named} is a
destruction rule for function \<open>(<)\<close>, but it is also only applicable to special uses of it and it
replaces it by the functions \<open>(\<le>)\<close>, \<open>(*)\<close>, and \<open>(+)\<close> which does not help for most proofs.
In the rule \<open>example2\<close> the operator \<open>(\<le>)\<close> also occurs in the conclusion, but in different form.
Therefore it can be considered as destruction rule for \<open>(\<le>)\<close>, although the form in the conclusion
is more complex which also does not help for most proofs.
\<close>

section "Composed Proof Methods"
text_raw\<open>\label{methods-composed}\<close>

text \<open>
Proof methods can be composed\index{method!composed $\sim$} from simpler methods with the help of ``method expressions''\index{method!expression}.
A method expression has one of the following forms:
 \<^item> \<open>m\<^sub>1, \<dots>, m\<^sub>n\<close> : a sequence of methods which are applied in their order,
 \<^item> \<open>m\<^sub>1; \<dots>; m\<^sub>n\<close> : a sequence of methods where each is applied to the goals created by the previous method,
 \<^item> \<open>m\<^sub>1| \<dots>| m\<^sub>n\<close> : a sequence of methods where only the first applicable method is applied,
 \<^item> \<open>m[n]\<close> : the method \<open>m\<close> is applied to the first \<open>n\<close> goals,
 \<^item> \<open>m?\<close> : the method \<open>m\<close> is applied if it is applicable,
 \<^item> \<open>m+\<close> : the method \<open>m\<close> is applied once and then repeated as long as it is applicable.

Parentheses\index{parentheses} are used to structure and nest composed methods.

Composed methods can be used to combine method applications to a single step. Using composed 
methods the example backward reasoning proof script from Section~\ref{methods-rule-backwards} can be
written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
  apply(rule example2,rule example1,assumption)
  done\<close>}

In particular, it is also possible to apply an arbitrarily complex composed method as initial 
method in a structured proof. Using composed methods the example forward reasoning proof in
Section~\ref{methods-forward-rule} can be written as
@{theory_text[display]
\<open>theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3"
proof -
  assume a: "x < 5"
  have f\<^sub>2: "2*x \<le> 2*5" by (rule example1,fact a)
  show ?thesis by (rule example2,fact f\<^sub>2)
qed\<close>}
\<close>

section "The Simplifier"
text_raw\<open>\label{methods-simp}\<close>

text \<open>
A common proof technique is ``rewriting''\index{rewriting}. If it is known that a term \<open>a\<close> is equal to a term
\<open>b\<close>, some occurrences of \<open>a\<close> in a proposition can be replaced by \<open>b\<close> without changing the 
validity of the proposition.

Equality of two terms \<open>a\<close> and \<open>b\<close> can be expressed by the proposition \<open>a = b\<close>. If that 
proposition has been proved to be valid, i.e., is a fact, \<open>a\<close> can be substituted by \<open>b\<close>
and vice versa in goals during a proof.
\<close>

subsection \<open>The {\sl subst} Method\<close>
text_raw\<open>\label{methods-simp-subst}\<close>

text \<open>
Rewriting is performed by the method
@{theory_text[display]
\<open>subst name\<close>}\index{subst (method)}
where \<open>name\<close> references an equality fact. The method only affects the first goal. If the
referenced fact has the form \<open>a = b\<close> the method replaces the first occurrence of \<open>a\<close> in
the goal conclusion by \<open>b\<close>. The order of the terms in the equality fact matters, the 
method always substitutes the term on the left by that on the right. 

If the equality contains unknowns unification is used: \<open>a\<close> is
unified with every sub-term of the goal conclusion, the first match is replaced by \<open>b'\<close>
which is \<open>b\<close> after substituting unknowns in the same way as in \<open>a\<close>. If there is no match
of \<open>a\<close> in the goal conclusion an error is signaled.\<close>

subsubsection "Rewriting in Goal Assumptions"

text\<open>
For a goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> the method only rewrites in the conclusion \<open>C\<close>. The first
match in the assumptions \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> can be substituted by the form
@{theory_text[display]
\<open>subst (asm) name\<close>}\<close>

subsubsection "Rewriting Specific Sub-Term Occurrences"

text\<open>
If not only the first match shall be substituted, a number of the match or a range of numbers
may be specified in both forms as in
@{theory_text[display]
\<open>subst (asm) (i..j) name\<close>}\<close>

subsubsection "Rewriting With Defining Equations"

text\<open>
The equality fact can also be a meta equality of the form \<open>a \<equiv> b\<close>. Therefore the method can
be used to expand constant definitions. After the definition
@{theory_text[display]
\<open>definition "inc x \<equiv> x + 1"\<close>}
the method \<^theory_text>\<open>subst inc_def\<close> will rewrite the first occurrence of a function application 
\<open>(inc t)\<close> in the goal conclusion to \<open>(t + 1)\<close>. Remember from Section~\ref{theory-theorem-defs}
that the defining equation is automatically named \<open>inc_def\<close>. Note the use of unification to
handle the actual argument term \<open>t\<close>.\<close>

subsubsection "Rewriting With Conditional Equations"

text\<open>
The equality fact may be conditional, i.e., it may be a derivation rule with assumptions of the
form \<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>m\<rbrakk> \<Longrightarrow> a = b\<close>. When the \<open>subst\<close> method applies a conditional equation of this
form to a goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>, it adds the goals \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>i'\<close> to the goal state
after rewriting, where \<open>RA\<^sub>i'\<close> result from \<open>RA\<^sub>i\<close> by the unification of \<open>a\<close> in \<open>C\<close>. These
goals are inserted before the original goal, so the next method application will usually process
the goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>1'\<close>.\<close>

subsubsection "Examples"

text\<open>
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

subsection "Simplification" 
text_raw\<open>\label{methods-simp-simplif}\<close>

text\<open>
If the term \<open>b\<close> in an equation \<open>a = b\<close> is in some sense ``simpler'' than \<open>a\<close>, the goal will
also become simpler by successful rewriting with the equation. If there are several
such equations a goal can be replaced by successively simpler goals by rewriting with these
equations. This technique can contribute to the goal's proof and is called ``simplification''\index{simplification}.

Basically, simplification uses a set of equations and searches an equation in the set where 
the left hand side unifies with a sub-term in the goal, then substitutes it. This step is 
repeated until no sub-term in the goal unifies with a left hand side in an equation in the set.\<close>

subsubsection "Non-Terminating Simplification"

text\<open>
It is apparent that great care must be taken when populating the set of equations, otherwise 
simplification may not terminate. If two equations \<open>a = b\<close> and \<open>b = a\<close> are in the set simplification
will exchange matching terms forever. If an equation \<open>a = a+0\<close> is in the set, a term matching
\<open>a\<close> will be replaced by an ever growing sum with zeroes.\<close>

subsubsection "Simplification With Definitional Equations"

text\<open>
Simplification with a set of definitional equations from constant definitions (see 
Section~\ref{theory-definition-defs}) always terminates. Since constant definitions cannot 
be recursive, every substitution removes one occurrence of a defined constant from the goal. 
Simplification terminates if no defined constant from the set remains in the goal.
Although the resulting goal usually is larger than the original goal, it is simpler in the 
sense that it uses fewer defined constants.\<close>

subsubsection "Simplification and Trivial Goals"

text\<open>
If the set contains conditional equations, simplification may produce additional goals. Then 
simplification is applied to these goals as well. Together, simplification may turn a single
complex goal into a large number of simple goals, but it cannot reduce the number of goals.
Therefore simplification is usually complemented by methods which remove trivial goals 
like \<open>x = x\<close>, \<open>A \<Longrightarrow> A\<close>, and \<open>True\<close>. Such an extended simplification may completely solve and remove 
the goal to which it is applied.
\<close>

subsection \<open>The {\sl simp} Method\<close>
text_raw\<open>\label{methods-simp-simp}\<close>

text\<open>
Isabelle supports simplification by the method
@{theory_text[display]
\<open>simp\<close>}\index{simp (method)}
which is also called ``the simplifier''\index{simplifier}. It uses the dynamic fact set \<open>simp\<close>\index{simp (fact set name)} as the set of 
equations, which is also called ``the simpset''\index{simpset}. The method only affects the first goal. 
If no equation in the simpset is applicable to it or it is not modified by the applicable equations 
an error is signaled.

The \<open>simp\<close> method simplifies the whole goal, i.e., it applies rewriting to the conclusion and 
to all assumptions.\<close>

subsubsection "Simplification Using Arbitrary Facts"

text\<open>
The simpset may contain facts which are not directly equations, but can be converted to an
equation. In particular, an arbitrary derivation rule \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> can always be converted
to the conditional equation \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C = True\<close>. The simplifier (and also the \<open>subst\<close> method)
performs this conversion if no other conversion technique applies, therefore the simpset may
actually contain arbitrary facts.

The \<open>simp\<close> method also detects several forms of trivial goals and removes them. Thus a complete
proof may be performed by a single application of the simplifier in the form
@{theory_text[display]
\<open>by simp\<close>}\<close>

subsubsection "Simplification in HOL"

text\<open>
In Isabelle HOL (see Section~\ref{holbasic}) the simpset is populated with a large number of facts
which make the simplifier a very useful proof tool. Actually all examples of facts used
in the previous sections can be proved by the simplifier:
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" by simp
theorem example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m" by simp
theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" by simp
theorem eq1: "n = 10 \<Longrightarrow> n+3 = 13" for n::nat by simp
theorem eq2: "n = 5 \<Longrightarrow> 2*n = 10" for n::nat by simp\<close>}\<close>

subsection "Configuring the Simplifier"
text_raw\<open>\label{methods-simp-config}\<close>

text \<open>
The simplifier can be configured by modifying the equations it uses. The form
@{theory_text[display]
\<open>simp add: name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{add: (method argument)}
uses the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close> in addition to the facts in the simpset for its rewriting
steps. The form 
@{theory_text[display]
\<open>simp del: name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{del: (method argument)}
uses only the facts from the simpset without the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close>, and the form
@{theory_text[display]
\<open>simp only: name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{only: (method argument)}
uses only the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close>. The three forms can be arbitrarily combined.

As usual, a theorem may be added permanently to the simpset as described in 
Section~\ref{theory-theorem-named} by specifying it as
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

subsection "Splitting Terms"
text_raw\<open>\label{methods-simp-split}\<close>

text \<open>
There are certain terms in which the simplifier will not apply its simpset rules. A typical
example are terms with an internal case distinction (see Section~\ref{holtdefs-data-destr}). To 
process such terms in a goal conclusion the terms must be split. Splitting a term\index{term!splitting} usually results
in several new goals with simpler terms which are then further processed by the simplifier.\<close>

subsubsection "Split Rules"

text\<open>
Term splitting is done by applying specific rules to the goal. These rules are called ``split
rules''\index{rule!split $\sim$}. Usually split rules are not automatically determined and applied by the simplifier, this 
must be configured explicitly in the form
@{theory_text[display]
\<open>simp split: name\<^sub>1 \<dots> name\<^sub>n\<close>}\index{split: (method argument)}
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
goal. See the Isabelle/Isar reference manual \<^cite>\<open>"isar-ref"\<close> for other forms which split
terms in assumptions of a goal.
\<close>

subsection "Searching Simplifier Equations"
text_raw\<open>\label{methods-simp-search}\<close>

text \<open>
Named facts applicable for simplification may be searched\index{search!for simplifier equations} using the command \<^theory_text>\<open>find_theorems\<close> or in
the Query panel\index{panel!query $\sim$}, as described in Section~\ref{theory-theorem-search}, using a \<open>criterion\<^sub>i\<close> of the
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

subsection \<open>Input Facts for the {\sl simp} Method\<close>
text_raw\<open>\label{methods-simp-input}\<close>

text \<open>
As usual, facts may be input to the \<open>simp\<close> method. Like the empty method (see 
Section~\ref{methods-empty}) it inserts these facts as assumptions into the goal,
before it starts simplification. Since simplification is also applied to the assumptions,
the input facts will be simplified as well.

As a possible effect of this behavior, after simplifying an input fact and the goal conclusion
the results may unify, leading to the situation where the goal is removed by the \<open>assumption\<close>
method (see Section~\ref{methods-assumption-method}). This is also done by the simplifier, hence in
this way the input fact may contribute to prove the goal.
\<close>

subsection \<open>The {\sl simp$\_$all} Method\<close>
text_raw\<open>\label{methods-simp-all}\<close>

text \<open>
The method
@{theory_text[display]
\<open>simp_all\<close>}\index{simp-all@simp$\_$all (method)}
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

subsection "Debugging the Simplifier"
text_raw\<open>\label{methods-simp-debug}\<close>

text \<open>
If the simplifier fails, it may be difficult to find out the reason. There are several debugging
techniques which may help.

The content of the simpset can be displayed by the command
@{theory_text[display]
\<open>print_simpset\<close>}\index{print-simpset@print$\_$simpset (keyword)}
which may be specified in the proof text in modes \<open>proof(prove)\<close> and \<open>proof(state)\<close> and outside 
of proofs. In the interactive editor the result is displayed in the Output panel\index{panel!output $\sim$} (see 
Section~\ref{system-jedit-output}).

There is also a simplifier trace\index{simplifier!trace} which displays the successful rewrite steps. It is activated
by the command
@{theory_text[display]
\<open>declare [[simp_trace_new depth=n]]\<close>}
outside a theorem or definition. The number \<open>n\<close> should be atleast \<open>2\<close>. When the cursor is
positioned on an application of the \<open>simp\<close> method the button ``Show trace'' can be used
in the Simplifier Trace panel to display the trace in a separate window. See the Isabelle/Isar
reference manual \<^cite>\<open>"isar-ref"\<close> for more information about how to use the trace.

Another technique is to replace the \<open>simp\<close> method by a sequence of \<open>subst\<close> method applications
and explicitly specify the equations which should have been used. To do this for a structured
proof, replace it by a proof script for the \<open>subst\<close> method applications.
\<close>

section "Other Automatic Proof Methods"
text_raw\<open>\label{methods-auto}\<close>

text\<open>
Isabelle provides several other proof methods which internally perform several steps,
like the simplifier.
\<close>

subsection "Automatic Methods"
text_raw\<open>\label{methods-auto-methods}\<close>

text\<open>
The following list contains automatic methods other than \<open>simp\<close>:
\<^item> \<open>blast\<close>\index{blast (method)} mainly applies logical rules and can be used to solve complex logical formulas.
\<^item> \<open>clarify\<close>\index{clarify (method)} is similar but does not split goals and does not follow unsafe paths. It can
be used to show the problem if \<open>blast\<close> fails.
\<^item> \<open>auto\<close>\index{auto (method)} combines logical rule application with simplification. It processes all goals and
leaves those it cannot solve.
\<^item> \<open>clarsimp\<close>\index{clarsimp (method)} combines \<open>clarify\<close> with simplification. It processes only the first goal and
usually does not split goals.
\<^item> \<open>fastforce\<close>\index{fastforce (method)} uses more techniques than \<open>auto\<close>, but processes only the first goal.
\<^item> \<open>force\<close>\index{force (method)} uses even more techniques and tries to solve the first goal.
\<^item> \<open>linarith\<close>\index{linarith (method)} solves linear arithmetic problems (on integer and real numbers) for the first goal.
It is automatically included by the simplifier.
\<^item> \<open>arith\<close>\index{arith (method)} uses more techniques than \<open>linarith\<close> but may be slower.
\<close>

text\<open>
The methods which do simplification can be configured like the simplifier by adding 
specifications \<open>simp add:\<close>, \<open>simp del:\<close>, \<open>simp only:\<close>, and \<open>split:\<close>. For example, additional
simplification rules can be specified for the \<open>auto\<close> method in the form
@{theory_text[display]
\<open>auto simp add: name\<^sub>1 \<dots> name\<^sub>n\<close>}

For more information about these methods see the Isabelle/Isar reference manual \<^cite>\<open>"isar-ref"\<close>.
\<close>

subsection "Trying Methods"
text_raw\<open>\label{methods-auto-try}\<close>

text\<open>
Instead of manually trying several automatic methods it is possible to specify the command
@{theory_text[display]
\<open>try\<close>}\index{try (keyword)}
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

end