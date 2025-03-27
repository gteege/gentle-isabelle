theory Chapter_holtdefs
  imports Chapter_holbasic
begin

chapter "Isabelle/HOL Type Definitions"
text_raw\<open>\label{holtdefs}\<close>

text \<open>
This chapter introduces mechanisms defined by HOL which are used to populate HOL\index{HOL (object logic)} with many of its
mathematical objects and functions and which can also be used to extend HOL to additional kinds of
objects. Basically these mechanisms support the definition of new types in outer syntax.
\<close>

section "Algebraic Types"
text_raw\<open>\label{holtdefs-data}\<close>

text\<open>
Roughly an algebraic type\index{algebraic type}\index{type!algebraic $\sim$} is equivalent to a union of tuples with support for recursion, which
allows nested tuples. In this way most data types used in programming languages can be covered, such
as records, unions, enumerations, and pointer structures. Therefore HOL also uses the notion
``datatype'' for algebraic types.
\<close>

subsection "Definition of Algebraic Types"
text_raw\<open>\label{holtdefs-data-def}\<close>

text\<open>
Basically, an algebraic type is defined\index{definition!algebraic type $\sim$}\index{definition!datatype $\sim$} in the form
@{theory_text[display]
\<open>datatype name = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>}\index{datatype (keyword)}\index{/bar@\<open>|\<close> (keyword)}
where \<open>name\<close> is the name of the new algebraic type and every alternative \<open>alt\<^sub>i\<close> is a ``constructor
specification''\index{constructor!specification} of the form
@{theory_text[display]
\<open>cname\<^sub>i "type\<^sub>i\<^sub>,\<^sub>1" \<dots> "type\<^latex>\<open>$_{i,k_i}$\<close>"\<close>}
The \<open>cname\<^sub>i\<close> are names and the \<open>type\<^sub>i\<^sub>,\<^sub>j\<close> are types.
The types are specified in inner syntax and must be quoted, if they are not a single type name. All 
other parts belong to the outer syntax. 

As a convention, capitalized names are used in HOL for the \<open>cname\<^sub>i\<close>.

An example for a datatype definition with two constructor specifications is
@{theory_text[display]
\<open>datatype coord = 
  Dim2 nat nat
| Dim3 nat nat nat\<close>}\index{coord (example type)}\index{Dim2 (example constant)}\index{Dim3 (example constant)}
Its value set is equivalent to the union of pairs and triples of natural numbers.
\<close>

subsubsection "Recursive Algebraic Types"

text\<open>
Recursion\index{recursion} is supported for the types, i.e., the name \<open>name\<close> of the defined type may occur in the 
type specifications \<open>type\<^sub>i\<^sub>,\<^sub>j\<close>. However, there must be atleast one constructor specification which
is not recursive, otherwise the definition does not ``terminate''. Isabelle checks this condition
and signals an error if it is not satisfied.

An example for a recursive datatype definition with two constructor specifications is
@{theory_text[display]
\<open>datatype tree = 
  Leaf nat
| Tree nat tree tree\<close>}\index{tree (example type)}\index{Leaf (example constant)}\index{Tree (example constant)}
Its value set is equivalent to the set of all binary trees with a natural number in every node.

Moreover, recursive occurrences of \<open>name\<close> are only allowed on live parameter positions
(see Section~\ref{holbasic-bnf-natural}) of a bounded natural functor \<open>type\<^sub>i\<^sub>,\<^sub>j\<close> (see
Section~\ref{holbasic-bnf-bounded}). Due to composability of BNFs this means
that all type constructors in which the recursive occurrence is nested must be bounded
natural functors. If this is not the case an error is signaled. 

In the definition of \<open>tree\<close> above the recursive occurrences are not nested in other type
constructors, therefore the condition is satisfied. If the second constructor specification is
modified to
@{theory_text[display]
\<open>\<dots> | Tree nat "tree set" tree\<close>}
an error will result because \<open>set\<close> is not registered as BNF (it cannot, because
it is none, see Section~\ref{holbasic-bnf-bounded}). If the constructor specification is modified to
@{theory_text[display]
\<open>\<dots> | Tree nat "tree \<Rightarrow> bool" tree\<close>}
another error will result because \<open>tree \<Rightarrow> bool\<close> is an abbreviation of \<open>(tree, bool) fun\<close> and \<open>fun\<close>
is a BNF (see Section~\ref{holbasic-bnf-bounded}), but \<open>tree\<close> occurs on its
dead parameter's position. If the constructor specification is modified to
@{theory_text[display]
\<open>\<dots> | Tree nat "nat \<Rightarrow> tree" tree\<close>}
everything is fine because now the recursive occurrence is on the live parameter position.
\<close>

subsubsection "Parameterized Algebraic Types"

text\<open>
Like declared types algebraic types may be parameterized (see Section~\ref{theory-terms-types}):
@{theory_text[display]
\<open>datatype ('name\<^sub>1,\<dots>,'name\<^sub>m) name = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>}
where the \<open>'name\<^sub>i\<close> are the type parameters. They may occur in the type specifications \<open>type\<^sub>i\<^sub>,\<^sub>j\<close>, i.e.,
the \<open>type\<^sub>i\<^sub>,\<^sub>j\<close> may be polymorphic (see Section~\ref{theory-terms-types}). Recursive
occurrences of \<open>name\<close> must always be applied to the type parameters, no other types are allowed as 
arguments. As usual, the parentheses may be omitted if there is only one type parameter.

An example for a parameterized datatype definition with one type parameter is
@{theory_text[display]
\<open>datatype 'a coordx = 
  Dim2 'a 'a
| Dim3 'a 'a 'a\<close>}\index{coordx (example type)}\index{Dim2 (example constant)}\index{Dim3 (example constant)}
Its value set is equivalent to the union of pairs and triples of values of the type parameter. The
type \<open>coord\<close> is equivalent to the type \<open>nat coordx\<close>. The type \<open>real coordx\<close> is equivalent to the
union of pairs and triples of values of type \<open>real\<close> of the real numbers.

An example for a parameterized recursive datatype definition with one type parameter is
@{theory_text[display]
\<open>datatype 'a treex = 
  Leaf 'a
| Tree 'a "'a treex" "'a treex"\<close>}\index{treex (example type)}
With this definition the type \<open>tree\<close> is equivalent to the type \<open>nat treex\<close>.\<close>

subsection "Constructors"
text_raw\<open>\label{holtdefs-data-constr}\<close>

text\<open>
Every \<open>cname\<^sub>i\<close> is used by the definition to introduce a ``(value) constructor function''\index{constructor}\index{constructor!function}\index{function!constructor $\sim$},
i.e., a constant
@{text[display]
\<open>cname\<^sub>i :: "type\<^sub>i\<^sub>,\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> type\<^latex>\<open>$_{i,k_i}$\<close> \<Rightarrow> name"\<close>}
which is a function with \<open>k\<^sub>i\<close> arguments mapping their arguments to values of the new type \<open>name\<close>.

Every datatype definition constitutes a separate namespace for the functions it introduces. Therefore
the same names may be used in constructor specifications of different datatype definitions. If used
directly, a name refers to the constructor function of the nearest preceding datatype definition.
To refer to constructor functions with the same name of other datatypes the name may be qualified
by prefixing it with the type name in the form \<open>name.cname\<^sub>i\<close>.

The definition of type \<open>coord\<close> above introduces the two constructor functions
\<open>Dim2 :: nat \<Rightarrow> nat \<Rightarrow> coord\<close> and \<open>Dim3 :: nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> coord\<close>. Their qualified names are
\<open>coord.Dim2\<close> and \<open>coord.Dim3\<close>.
\<close>

subsubsection "Constructing Values"

text\<open>
These constructor functions are assumed to be injective, thus their result values differ if atleast
one argument value differs. This implies that the set of all values of the constructor function
\<open>cname\<^sub>i\<close> is equivalent to the tuples\index{tuple} of the value sets of \<open>type\<^sub>i\<^sub>,\<^sub>1 \<dots> type\<^latex>\<open>$_{i,k_i}$\<close>\<close>: for every
tuple of arguments there is a constructed value and vice versa. Note, however, that as usual the
values of the new type are distinct from the values of all other types, in particular, they are
distinct from the argument tuples.

Moreover the result values of different constructor functions are also assumed to be different.
Together the set of all values of the defined type is equivalent to the (disjoint) union of the
cartesian products of all constructor argument types. Moreover, every value of the type may be 
denoted by a term
@{text[display]
\<open>cname\<^sub>i term\<^sub>1 \<dots> term\<^latex>\<open>$_{k_i}$\<close>\<close>}
where each \<open>term\<^sub>j\<close> is of type  \<open>type\<^sub>i\<^sub>,\<^sub>j\<close> and specifies an argument for the constructor function
application.

Together, datatypes have what is called ``free constructors''\index{constructor!free $\sim$} in Isabelle: the constructors are
injective, disjoint, and exhaustive (they cover all values of the type).

Values of type \<open>coord\<close> as defined above are denoted by terms such as \<open>Dim2 0 1\<close> and \<open>Dim3 10 5 21\<close>.
\<close>

subsubsection "Constant Constructors and Enumeration Types"

text\<open>
A constructor specification may consist of a single constructor name \<open>cname\<^sub>i\<close>, then the constructor 
function has no arguments and always constructs the same single value. The constructor is equivalent 
to a constant of type \<open>name\<close>. As a consequence an ``enumeration type''\index{enumeration type}\index{type!enumeration $\sim$} can be defined in the form
@{theory_text[display]
\<open>datatype three = Zero | One | Two\<close>}\index{three (example type)}\index{Zero (example constant)}\index{One (example constant)}\index{Two (example constant)}
This type \<open>three\<close> has three values denoted by \<open>Zero\<close>, \<open>One\<close>, and \<open>Two\<close>.
\<close>

subsubsection "Types with a Single Constructor"

text\<open>
If a datatype definition consists of a single constructor specification its value set is equivalent 
to the constructor argument tuples. The corresponding tuples have a separate component for every
constructor argument type. As a consequence a ``record type''\index{record type}\index{type!record $\sim$} can be defined in the form 
@{theory_text[display]
\<open>datatype recrd = MkRecrd nat "nat set" bool\<close>}\index{recrd (example type)}\index{MkRecrd (example constant)}
Its values are equivalent to triples where the first component is a natural number, the second
component is a set of natural numbers, and the third component is a boolean value. An example value
is denoted by \<open>MkRecrd 5 {1,2,3} True\<close>.

Since there must be atleast one nonrecursive constructor specification, definitions with a single
constructor specification cannot be recursive.

For more comfortable record implementations in Isabelle see Section~\ref{holtdefs-record}.\<close>

subsection "Destructors"
text_raw\<open>\label{holtdefs-data-destr}\<close>

text\<open>
Since constructor functions are injective it is possible to determine for every value of the defined
type the value of each constructor argument used to construct it. Corresponding mechanisms are 
called ``destructors''\index{destructor}\index{destructor function}\index{function!destructor $\sim$}, there are three different types of them.
\<close>

subsubsection "Selectors"

text\<open>
The most immediate form of a destructor is a selector function\index{selector}\index{selector function}\index{function!selector $\sim$}. For the constructor argument specified
by \<open>type\<^sub>i\<^sub>,\<^sub>j\<close> the selector function is a function of type \<open>name \<Rightarrow> type\<^sub>i\<^sub>,\<^sub>j\<close>. For every value constructed
by \<open>cname\<^sub>i term\<^sub>1 \<dots> term\<^latex>\<open>$_{k_i}$\<close>\<close> it returns the value denoted by \<open>term\<^sub>j\<close>.

The names of selector functions must be specified explicitly. This is done using the extended form
of a constructor specification
@{theory_text[display]
\<open>cname\<^sub>i (sname\<^sub>i\<^sub>,\<^sub>1 : "type\<^sub>i\<^sub>,\<^sub>1") \<dots> (sname\<^latex>\<open>$_{i,k_i}$\<close> : "type\<^latex>\<open>$_{i,k_i}$\<close>")\<close>}
where the \<open>sname\<^sub>i\<^sub>,\<^sub>j\<close> are the names used for the corresponding selector functions. Selector names
may be specified for all or only for some constructor arguments. As for constructors, selector names
belong to the namespace of the defined type and may be qualified by prefixing the type name.

An example datatype definition with selectors is
@{theory_text[display]
\<open>datatype recrd = MkRecrd (n:nat) (s:"nat set") (b:bool)\<close>}
It shows that the selector functions correspond to the field names used in programming languages 
in record types to access the components. For every term \<open>r\<close> of type \<open>recrd\<close> the selector term
\<open>s r\<close> denotes the set component of \<open>r\<close>.

An example for a datatype with multiple constructor specifications is
@{theory_text[display]
\<open>datatype coord = 
  Dim2 (x:nat) (y:nat)
| Dim3 (x:nat) (y:nat) (z:nat)\<close>}
Note that the selectors \<open>x\<close> and \<open>y\<close> are specified in both alternatives. Therefore a single selector
function \<open>x :: coord \<Rightarrow> nat\<close> is defined which yields the first component both for a two-dimensional
and a three-dimensional coordinate and analogously for \<open>y\<close>. If instead the definition is specified as
@{theory_text[display]
\<open>datatype coord = 
  Dim2 (x2:nat) (y:nat)
| Dim3 (x3:nat) (y:nat) (z:nat)\<close>}
two separate selector functions \<open>x2\<close> and \<open>x3\<close> are defined where the first one is only applicable to 
two-dimensional coordinates and the second one only to three-dimensional coordinates.

If a selector name does not occur in all constructor specifications, the selector function is still
total, like all functions in Isabelle, but it is underspecified (see Section~\ref{theory-terms-consts}).
It maps values constructed by other constructors to a unique value of its result type, even if that
other constructor has no argument of this type. However, no information is available about that value.

For the type \<open>coord\<close> the selector function \<open>z :: coord \<Rightarrow> nat\<close> is also applicable to two-dimensional
coordinates, however, the values it returns for them is not specified.

Such selector values are called ``default selector values''\index{default selector}\index{selector!default $\sim$}. They may be specified in the extended
form of a datatype definition
@{theory_text[display]
\<open>datatype name = alt\<^sub>1 | \<dots> | alt\<^sub>n
where "prop\<^sub>1" | \<dots> | "prop\<^sub>m"\<close>}
where every \<open>prop\<^sub>p\<close> is a proposition of the form
@{text[display]
\<open>sname\<^sub>i\<^sub>,\<^sub>j (cname\<^sub>q var\<^sub>1 \<dots> var\<^latex>\<open>$_{k_q}$\<close>) = term\<^sub>p\<close>}
and specifies \<open>term\<^sub>p\<close> as the default value of selector \<open>sname\<^sub>i\<^sub>,\<^sub>j\<close> for values constructed by \<open>cname\<^sub>q\<close>.
If a default value is specified for a \<open>cname\<^sub>i\<close> where the selector is already defined, the
default specification is ignored.

The definition
@{theory_text[display]
\<open>datatype coord = 
  Dim2 (x:nat) (y:nat)
| Dim3 (x:nat) (y:nat) (z:nat)
where "z (Dim2 a b) = 0"\<close>}
specifies \<open>0\<close> as default value for selector \<open>z\<close> if applied to a two-dimensional coordinate.
\<close>

subsubsection "Discriminators"

text\<open>
If an underspecified selector is applied to a datatype value it may be useful to determine which
constructor has been used to construct the value. This is supported by discriminator functions\index{discriminator}\index{discriminator function}\index{function!discriminator $\sim$}.
For every constructor specification for \<open>cname\<^sub>i\<close> the discriminator function has type \<open>name \<Rightarrow> bool\<close>
and returns true for all values constructed by \<open>cname\<^sub>i\<close>. Like selector names, discriminator names
must be explicitly specified using the extended form of a datatype definition
@{theory_text[display]
\<open>datatype name = dname\<^sub>1: alt\<^sub>1 | \<dots> | dname\<^sub>n: alt\<^sub>n\<close>}
Discriminator names may be specified for all alternatives or only for some of them. Note that for
a datatype with a single constructor the discriminator returns always \<open>True\<close> and for a datatype
with two constructors one discriminator is the negation of the other.

An example datatype definition with discriminators is
@{theory_text[display]
\<open>datatype coord =
  is_2dim: Dim2 nat nat
| is_3dim: Dim3 nat nat nat\<close>}
In a datatype definition both discriminators and selectors may be specified.
\<close>

subsubsection \<open>The {\sl case} Term\<close>

text\<open>
Additionally to using discriminators and selectors HOL supports \<open>case\<close> terms\index{case!term}\index{term!case $\sim$}. A \<open>case\<close>
term specifies depending on a datatype value a separate term variant for every constructor of the
datatype. In these variants the constructor arguments are available as bound variables. 

A \<open>case\<close> term for a datatype \<open>name\<close> defined as in Section~\ref{holtdefs-data-def} has the form
@{text[display]
\<open>case term of 
  cname\<^sub>1 var\<^sub>1\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{1,k_1}$\<close> \<Rightarrow> term\<^sub>1 
| \<dots>
| cname\<^sub>n var\<^sub>n\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{n,k_n}$\<close> \<Rightarrow> term\<^sub>n\<close>}\index{case (inner keyword)}\index{of (inner keyword)}
where \<open>term\<close> is of type \<open>name\<close> and the \<open>term\<^sub>i\<close> have an arbitrary but common type which is also the
type of the \<open>case\<close> term. In the alternative for constructor \<open>cname\<^sub>i\<close> the \<open>var\<^sub>1\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{1,k_1}$\<close>\<close> must be 
distinct variables, they are bound to the constructor arguments and may be used in \<open>term\<^sub>i\<close> to access
them. The value of \<open>var\<^sub>i\<^sub>,\<^sub>j\<close> is the same as the value selected by \<open>sname\<^sub>i\<^sub>,\<^sub>j term\<close>.

Actually, a \<open>case\<close> term is only an alternative syntax for the function application term
@{text[display]
\<open>case_name 
  (\<lambda> var\<^sub>1\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{1,k_1}$\<close>. term\<^sub>1)
  \<dots>
  (\<lambda> var\<^sub>n\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{n,k_n}$\<close>. term\<^sub>n)
  term\<close>}
Here \<open>case_name\<close>\index{case-@case$\_$ (constant name prefix)} is the ``case combinator''\index{case!combinator function} function for the datatype \<open>name\<close>. It takes as arguments
\<open>n\<close> functions which map the corresponding constructor arguments to the term variant (or the term
variant itself if the constructor has no arguments) and the \<open>term\<close> of type \<open>name\<close> as final argument.
Note that the constructor names \<open>cname\<^sub>i\<close> do not occur here, the constructor corresponding to a term
variant is only determined by the argument position \<open>i\<close> compared with the position of the
constructor in the datatype definition.

If \<open>cv\<close> is a variable or constant of type \<open>coord\<close> an example \<open>case\<close> term for it is
@{text[display]
\<open>case cv of 
  Dim2 a b \<Rightarrow> a + b
| Dim3 a b c \<Rightarrow> a + b + c\<close>}
It denotes the sum of the coordinates of \<open>cv\<close>, irrespective whether \<open>cv\<close> is two-dimensional or
three-dimensional. The corresponding case combinator application term is
@{text[display]
\<open>case_coord (\<lambda> a b. a+b) (\<lambda> a b c. a+b+c) cv\<close>}

A \<open>case\<close> term is useful even for a datatype with a single constructor. If \<open>rv\<close> is of type \<open>recrd\<close>
as defined in Section~\ref{holtdefs-data-destr} the \<open>case\<close> term
@{text[display]
\<open>case rv of MkRecrd nv sv bv \<Rightarrow> term\<close>}
makes the components of \<open>rv\<close> locally available in \<open>term\<close> as \<open>nv\<close>, \<open>sv\<close>, \<open>bv\<close>. It is equivalent to
\<open>term\<close> where \<open>nv\<close>, \<open>sv\<close>, and \<open>bv\<close> have been substituted by the selector applications \<open>(n rv)\<close>, 
\<open>(s rv)\<close>, and \<open>(b rv)\<close>.

The variant terms in a \<open>case\<close> term cannot be matched directly by a \<^theory_text>\<open>let\<close> statement in a proof (see 
Section~\ref{proof-let-define}). The statement 
@{theory_text[display]
\<open>let "case rv of MkRecrd nv sv bv \<Rightarrow> ?t" 
   = "case rv of MkRecrd nv sv bv \<Rightarrow> term"\<close>}
will fail to bind \<open>?t\<close> to \<open>term\<close> because then the variables \<open>nv\<close>, \<open>sv\<close>, and \<open>bv\<close> would occur free
in it and the relation to the constructor arguments would be lost. Instead, the statement
@{theory_text[display]
\<open>let "case rv of MkRecrd nv sv bv \<Rightarrow> ?t nv sv bv"
   = "case rv of MkRecrd nv sv bv \<Rightarrow> term"\<close>}
successfully binds \<open>?t\<close> to the lambda term \<open>\<lambda>nv sv bv. term\<close> which denotes the function which
results in \<open>term\<close> when applied to the constructor arguments and occurs as argument of the case
combinator function.
\<close>

subsection "Parameterized Algebraic Types as Bounded Natural Functors"
text_raw\<open>\label{holtdefs-data-bnf}\<close>

text\<open>
Every algebraic type can be considered to be a disjoint union (specified by the alternatives) of
tuples (denoted by the constructor specifications). A disjoint union corresponds to a sum type
(see Section~\ref{holtypes-sum}), a tuple to a product type (see Section~\ref{holtypes-tup}). Seen
as type constructors both are BNFs (see Section~\ref{holbasic-bnf-bounded}).
Due to composability of BNFs this implies that an algebraic type is a bounded
natural functor as soon as all constructor argument types \<open>type\<^sub>i\<^sub>,\<^sub>j\<close> are BNFs.
This is even true for recursive algebraic types.

HOL checks every datatype definition whether it satisfies this condition by checking whether all
type constructors used in the \<open>type\<^sub>i\<^sub>,\<^sub>j\<close> have been registered as BNF (see
Section~\ref{holbasic-bnf-register}) or are a recursive occurrence of the defined datatype. If that
is the case the datatype is itself registered as BNF, all required goals are
automatically proved. If it is not the case the datatype is registered as if all parameters are dead
(see Section~\ref{holbasic-bnf-natural}).

Like the \<^theory_text>\<open>bnf\<close> command a datatype definition does not register the generated mapper \<open>m\<close> as functor.
If needed this must be done explicitly using the \<^theory_text>\<open>functor\<close> command (see
Section~\ref{holbasic-bnf-register}).

Both example types \<open>coordx\<close> and \<open>treex\<close> specified in Section~\ref{holtdefs-data-def} are detected
and registered by HOL as BNFs with one live type parameter. The datatype
@{theory_text[display]
\<open>datatype 'a nobnf = Dim2 'a 'a | Dimset "'a set"\<close>}
is not recognized by HOL as BNF, because it uses the type constructor \<open>set\<close> in
its second constructor specification, which is not a BNF (see
Section~\ref{holbasic-bnf-bounded}).

Since (bounded) natural functors model container types (see Section~\ref{holbasic-bnf-natural}), the
same is true for corresponding datatypes. As an example, every value of the polymorphic datatype
\<open>'a coordx\<close> contains two or three values of the type parameter \<open>'a\<close> as its content. For a recursive
datatype the content consists of the values at all direct occurrences of the type parameters united
with the content of all recursive occurrences of datatype values.
\<close>

subsubsection "BNF Functions"

text\<open>
If HOL detects that a datatype is a BNF, it also generates definitions for the
mapper (see Section~\ref{holbasic-functor-mapper}), the set-function(s) (see
Section~\ref{holbasic-bnf-natural}), the predicator and the relator (see
Section~\ref{holbasic-bnf-predrel}). The names are generated from the datatype name as \<open>map_name\<close>, 
\<open>seti_name\<close>, \<open>pred_name\<close>, and \<open>rel_name\<close>, where \<open>i\<close> is the position number of the corresponding
type parameter \<open>'name\<^sub>i\<close> (see Section~\ref{holtdefs-data-def}). So, if there are two type parameters
the set-functions are named \<open>set1_name\<close> and \<open>set2_name\<close>. If the datatype has only one type
parameter the (single) set-function is named \<open>set_name\<close>.

If a datatype is not recognized as a BNF, none of these functions are defined
by HOL.

For the type \<open>coordx\<close> the mapper \<open>map_coordx\<close> has type \<open>('p \<Rightarrow> 'q) \<Rightarrow> 'p coordx \<Rightarrow> 'q coordx\<close>. For
instance, if \<open>f :: real \<Rightarrow> nat\<close> is the function that rounds every real number to the next natural
number, the application \<open>map_coordx f cv\<close> replaces the real coordinates in \<open>cv\<close> of type \<open>real coordx\<close>
by rounded natural coordinates, resulting in a value of type \<open>nat coordx\<close>.

For \<open>coordx\<close> the only set function is \<open>set_coordx\<close>. It maps every value of a type \<open>T coordx\<close> to the
set of either two or three coordinate values of type \<open>T\<close>.

The predicator \<open>pred_coordx\<close> has type \<open>('p \<Rightarrow> bool) \<Rightarrow> 'p coordx \<Rightarrow> bool\<close>. For
instance, if \<open>cv\<close> is of type \<open>nat coordx\<close> the term \<open>pred_coordx (\<lambda>n. n=0) cv\<close> tests whether
all coordinates of \<open>cv\<close> are \<open>0\<close>.

The relator \<open>rel_coordx\<close> has type \<open>('p \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow> 'p coordx \<Rightarrow> 'q coordx \<Rightarrow> bool\<close>. For
instance, if \<open>cv\<^sub>1\<close> and \<open>cv\<^sub>2\<close> are of type \<open>nat coordx\<close> the term \<open>rel_coordx (\<le>) cv\<^sub>1 cv\<^sub>2\<close> tests
whether \<open>cv\<^sub>1\<close> and \<open>cv\<^sub>2\<close> have the same dimension and every coordinate in \<open>cv\<^sub>1\<close> is lower or equal to
the corresponding coordinate in \<open>cv\<^sub>2\<close>.

Similar as for the command \<^theory_text>\<open>lift_bnf\<close> (see Section~\ref{holbasic-quotlift-bnf}) the 
form
@{theory_text[display]
\<open>datatype (sname\<^sub>1: 'p\<^sub>1,\<dots>, sname\<^sub>m: 'p\<^sub>m) name = alt\<^sub>1 | \<dots> | alt\<^sub>n
  for map: mname pred: pname rel: rname\<close>}\index{for (keyword)}
of a datatype definition allows to define alternate names \<open>sname\<^sub>i\<close>, \<open>mname\<close>, \<open>pname\<close>, \<open>rname\<close>
for (some of) the set-, mapper, predicator, and relator functions. If the datatype is not recognized
as BNF by HOL the names are ignored.
\<close>

subsection "Rules"
text_raw\<open>\label{holtdefs-data-rules}\<close>

text\<open>
A datatype definition also introduces a large number of named facts about the constructors and 
destructors of the defined type. All fact names belong to the namespace of the datatype definition.
Since the fact names cannot be specified explicitly, all datatype definitions use the same fact
names, therefore the fact names must always be qualified by prefixing the type name.

Several rules are configured for automatic application, e.g., they are added to the simpset for
automatic application by the simplifier (see Section~\ref{methods-simp-simp}). Other rules must
be explicitly used by referring them by their name. 

Only some basic rules are described here, for more information refer to \<^cite>\<open>datatypes\<close>. 
All introduced rules can be displayed using the ``Print Context'' tab in the Query panel
\index{panel!query $\sim$} as described in Section~\ref{theory-theorem-search}, if the cursor is
positioned after the \<^theory_text>\<open>datatype\<close> definition.
\<close>

subsubsection "Simplifier Rules"

text\<open>
The rules added by a definition for a datatype \<open>name\<close> to the simpset (see
Section~\ref{methods-simp-simp}) support many ways for the simplifier to process terms with
constructors and destructors.

The rule set \<open>name.inject\<close>\index{inject@.inject (fact name suffix)} states that every non-constant constructor is injective,
the rules are of the form
@{text[display]
\<open>((cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^latex>\<open>$_{k_i}$\<close>) = (cname\<^sub>i ?y\<^sub>1 \<dots> ?y\<^latex>\<open>$_{k_i}$\<close>)) =
  (?x\<^sub>1 = ?y\<^sub>1 \<and> \<dots> \<and> ?x\<^latex>\<open>$_{k_i}$\<close> = ?y\<^latex>\<open>$_{k_i}$\<close>)\<close>}

The rule set \<open>name.distinct\<close>\index{distinct@.distinct (fact name suffix)} states that values constructed by different constructors are different,
the rules are of the form
@{text[display]
\<open>(cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^latex>\<open>$_{k_i}$\<close>) \<noteq> (cname\<^sub>j ?y\<^sub>1 \<dots> ?y\<^latex>\<open>$_{k_j}$\<close>)\<close>}
where \<open>i \<noteq> j\<close>.

The rule set \<open>name.sel\<close>\index{sel@.sel (fact name suffix)} provides ``defining equations'' for the selectors of the form
@{text[display]
\<open>sname\<^sub>i\<^sub>j (cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^sub>k\<^sub>i) = ?x\<^sub>j\<close>}

The rule set \<open>name.case\<close>\index{case@.case (fact name suffix)} provides equations for simplifying \<open>case\<close> terms where the discriminating
term is directly specified by a constructor application. They have the form
@{text[display]
\<open>(case (cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^latex>\<open>$_{k_i}$\<close>) of 
    cname\<^sub>1 var\<^sub>1\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{1,k_1}$\<close> \<Rightarrow> ?f\<^sub>1 var\<^sub>1\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{1,k_1}$\<close>
  | \<dots>
  | cname\<^sub>n var\<^sub>n\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{n,k_n}$\<close> \<Rightarrow> ?f\<^sub>n var\<^sub>n\<^sub>,\<^sub>1 \<dots> var\<^latex>\<open>$_{n,k_n}$\<close>)
= ?f\<^sub>i ?x\<^sub>1 \<dots> ?x\<^latex>\<open>$_{k_i}$\<close>\<close>}
Note that each branch is specified as an application of a function \<open>?f\<^sub>i\<close> so that the variables
bound in the branch can be substituted by the arguments of the constructor application.

Depending on the datatype definition there may be additional simplifier rules. In particular, if
the datatype is parameterized, simplifier rules are generated for the functions described in
Section~\ref{holtdefs-data-bnf}.
The set of all rules added to the simpset is named \<open>name.simps\<close>\index{simps@.simps (fact name suffix)}. By displaying it using the
\<^theory_text>\<open>thm\<close> command (see Section~\ref{theory-theorem-search}) it can be inspected to get an idea how
the simplifier processes terms for a specific datatype. 
\<close>

subsubsection "Case Rule"

text\<open>
Every definition for a datatype \<open>name\<close> introduces a rule corresponding to the exhaustiveness of
the free constructors (see Section~\ref{holtdefs-data-constr}). It has the form
@{text[display]
\<open>name.exhaust:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_1}$\<close>. ?y = cname\<^sub>1 x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_1}$\<close> \<Longrightarrow> ?P;
   \<dots> ;
   \<And>x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_n}$\<close>. ?y = cname\<^sub>n x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_n}$\<close> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}\index{exhaust@.exhaust (fact name suffix)}

According to Section~\ref{case-reasoning-rules} this rule is a case rule. It is automatically
associated with the datatype for use by the \<^theory_text>\<open>cases\<close> method. Therefore the application of the method
@{theory_text[display]
\<open>cases "term"\<close>}
where \<open>term\<close> is of type \<open>name\<close> splits an arbitrary goal into \<open>n\<close> subgoals where every subgoal uses
a different constructor to construct the \<open>term\<close>.

The names for the named contexts created by the \<^theory_text>\<open>cases\<close> method are simply the constructor names 
\<open>cname\<^sub>i\<close>. Therefore a structured proof using case based reasoning for a \<open>term\<close> of datatype \<open>name\<close>
has the form
@{theory_text[display]
\<open>proof (cases "term")
  case (cname\<^sub>1 x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_1}$\<close>) \<dots> show ?thesis \<proof>
next
\<dots>
next
  case (cname\<^sub>n x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_n}$\<close>) \<dots> show ?thesis \<proof>
qed\<close>}
The names \<open>x\<^sub>i\<close> of the locally fixed variables can be freely selected, they denote the constructor
arguments of the corresponding constructor. Therefore the case specification \<open>(cname\<^sub>i x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_i}$\<close>)\<close>
looks like a constructor application to variable arguments, although it is actually a context name
together with locally fixed variables.
\<close>

subsubsection "Split Rule"

text\<open>
A \<open>case\<close> term (see Section~\ref{holtdefs-data-destr}) is only processed automatically by the
simplifier, if the discriminating term is a constructor application (see the \<open>name.case\<close> rule set
above). Otherwise it is only processed if a corresponding split rule is configured for it (see
Section~\ref{methods-simp-config}). Every definition for a datatype \<open>name\<close> introduces such a split
rule\index{rule!split $\sim$}. It has the form
@{text[display]
\<open>name.split:
  ?P(case ?t of 
     cname\<^sub>1 x\<^sub>1\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{1,k_1}$\<close> \<Rightarrow> ?t\<^sub>1 x\<^sub>1\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{1,k_1}$\<close>
   | \<dots>
   | cname\<^sub>n x\<^sub>n\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{n,k_n}$\<close> \<Rightarrow> ?t\<^sub>n x\<^sub>n\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{n,k_n}$\<close>) = 
  (  (?t = cname\<^sub>1 x\<^sub>1\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{1,k_1}$\<close> \<longrightarrow> ?P(?t\<^sub>1 x\<^sub>1\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{1,k_1}$\<close>))
   \<and> \<dots>
   \<and> (?t = cname\<^sub>n x\<^sub>n\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{n,k_n}$\<close> \<longrightarrow> ?P(?t\<^sub>n x\<^sub>n\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{n,k_n}$\<close>)))\<close>}\index{split@.split (fact name suffix)}
As described in Section~\ref{methods-simp-split} the rule splits a goal with a \<open>case\<close> term for type
\<open>name\<close> in the conclusion into goals where the \<open>case\<close> term is replaced by the terms in the cases.
Note that the sub-terms of the \<open>case\<close> term are specified by unknowns, so the rule unifies with
arbitrary \<open>case\<close> terms for type \<open>name\<close>. Also note, that the \<open>?t\<^sub>i\<close> are specified with arguments, so
that they will be matched by functions depending on the constructor arguments \<open>x\<^sub>i\<^sub>,\<^sub>1,\<dots>,x\<^latex>\<open>$_{i,k_i}$\<close>\<close>, as
described in Section~\ref{holtdefs-data-destr}.

As an example, let \<open>cv\<close> be a variable or constant of type \<open>coord\<close>, as above. Then the goal
@{text[display]
\<open>sum = (case cv of Dim2 a b \<Rightarrow> a + b | Dim3 a b c \<Rightarrow> a + b + c)\<close>}
is split by the split rule \<open>coord.split\<close> into the goals
@{text[display]
\<open>cv = Dim2 a b \<Longrightarrow> sum = a + b
cv = Dim3 a b c \<Longrightarrow> sum = a + b + c\<close>}
\<close>

subsubsection "Induction Rule"

text\<open>
Every definition for a datatype \<open>name\<close> introduces an induction rule\index{induction!rule}\index{rule!induction $\sim$} (see Section~\ref{case-induction-rules})
of the form
@{text[display]
\<open>name.induct:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_1}$\<close>. \<lbrakk>?P x\<^latex>\<open>$_{l_1}$\<close>; \<dots> ?P x\<^latex>\<open>$_{l_{m_1}}$\<close>\<rbrakk> \<Longrightarrow> ?P (cname\<^sub>1 x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_1}$\<close>);
   \<dots> ;
   \<And>x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_n}$\<close>. \<lbrakk>?P x\<^latex>\<open>$_{l_n}$\<close>; \<dots> ?P x\<^latex>\<open>$_{l_{m_n}}$\<close>\<rbrakk> \<Longrightarrow> ?P (cname\<^sub>n x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_n}$\<close>)\<rbrakk>
  \<Longrightarrow> ?P ?a\<close>}\index{induct@.induct (fact name suffix)}
where the \<open>x\<^latex>\<open>$_{l_1}$\<close> \<dots> x\<^latex>\<open>$_{l_{m_i}}$\<close>\<close> are those \<open>x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_i}$\<close>\<close> which have type \<open>name\<close> (i.e., the recursive
occurrences of the type name). Like the case rule it is valid because the constructor applications 
cover all possibilities of constructing a value \<open>?a\<close> of the datatype.

If the datatype \<open>name\<close> is not recursive there are no \<open>x\<^latex>\<open>$_{l_1}$\<close> \<dots> x\<^latex>\<open>$_{l_{m_i}}$\<close>\<close> and the assumptions of all
inner rules are empty, then the induction rule is simply a specialization of the case rule and is
redundant. However, for a recursive datatype \<open>name\<close> induction using rule \<open>name.induct\<close> is the
standard way of proving a property to hold for all values.

The rule \<open>name.induct\<close> is associated with datatype \<open>name\<close> for use by the methods \<^theory_text>\<open>induction\<close> and
\<^theory_text>\<open>induct\<close> (see Section~\ref{case-induction-naming}). Therefore the application of the method
@{theory_text[display]
\<open>induction x\<close>}
where \<open>x\<close> is a variable of type \<open>name\<close> splits a goal into \<open>n\<close> subgoals where every subgoal uses
a different constructor term in the place of \<open>x\<close>.

As for the case rule and the \<^theory_text>\<open>cases\<close> method, the names for the named contexts created by the 
methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close> are simply the constructor names \<open>cname\<^sub>i\<close>. Therefore a structured
proof using induction for a variable \<open>x\<close> of datatype \<open>name\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (cname\<^sub>1 x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_1}$\<close>) \<dots> show ?case \<proof>
next
\<dots>
next
  case (cname\<^sub>n x\<^sub>1 \<dots> x\<^latex>\<open>$_{k_n}$\<close>) \<dots> show ?case \<proof>
qed\<close>}

In the rule \<open>name.induct\<close> all inner assumptions are of the form \<open>?P x\<^latex>\<open>$_{l_i}$\<close>\<close>, i.e., they are induction
hypotheses and are named \<open>"cname\<^sub>i.IH"\<close> by the \<^theory_text>\<open>induction\<close> method, the assumption set \<open>"cname\<^sub>i.hyps"\<close>
is always empty. The \<^theory_text>\<open>induct\<close> method instead names all inner assumptions by \<open>"cname\<^sub>i.hyps"\<close>.

As an example, the induction rule for the recursive datatype \<open>tree\<close> defined in 
Section~\ref{holtdefs-data-def} is
@{text[display]
\<open>tree.induct:
  \<lbrakk>\<And>x. ?P (Leaf x);
   \<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. \<lbrakk>?P x\<^sub>2; ?P x\<^sub>3\<rbrakk> \<Longrightarrow> ?P (Tree x\<^sub>1 x\<^sub>2 x\<^sub>3)\<rbrakk>
  \<Longrightarrow> ?P ?a\<close>}
If \<open>p :: tree \<Rightarrow> bool\<close> is a predicate for values of type \<open>tree\<close> the goal \<open>p x\<close> which states
that \<open>p\<close> holds for all values is split by applying the method \<open>(induction x)\<close> into the goals
@{text[display]
\<open>\<And>x. p (Leaf x)
\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. \<lbrakk>p x\<^sub>2; p x\<^sub>3\<rbrakk> \<Longrightarrow> p (Tree x\<^sub>1 x\<^sub>2 x\<^sub>3)\<close>}

A structured proof for goal \<open>p x\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (Leaf x) \<dots> show ?case \<proof>
next
  case (Tree x\<^sub>1 x\<^sub>2 x\<^sub>3) \<dots> show ?case \<proof>
qed\<close>}
and in the second case the assumptions \<open>p x\<^sub>2, p x\<^sub>3\<close> are named \<open>Tree.IH\<close>.
\<close>

subsubsection "BNF Rules"

text\<open>
If HOL detects a datatype to be a BNF (see Section~\ref{holtdefs-data-bnf}) it
also provides the rules which are provided by the \<^theory_text>\<open>bnf\<close> command (see
Section~\ref{holbasic-bnf-register}) with their names in the namespace of the datatype.
\<close>

subsection "Recursive Functions on Algebraic Types"
text_raw\<open>\label{holtdefs-data-recursive}\<close>

text\<open>
A term is called a ``constructor pattern''\index{constructor!pattern} if it only consists of variables and constructor function
applications. Note that this includes terms consisting of a single variable. More generally, a
constructor pattern may be a sequence of such terms used as arguments in a function application.
A constructor pattern is called ``linear''\index{constructor!pattern!linear $\sim$}\index{linear constructor pattern} if every variable occurs only once.

HOL provides specific support for recursive definitions\index{definition!recursive $\sim$}\index{recursive definition} (see
Section~\ref{holbasic-recursive}) of functions \<open>name :: t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type\<close> where every
defining equation \<open>eq\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^latex>\<open>$_{i,p_i}$\<close>. name term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k = term\<^sub>i\<close>}
without assumptions \<open>Q\<^sub>i\<^sub>,\<^sub>j\<close> and the sequence \<open>term\<^sub>i\<^sub>,\<^sub>1 \<dots> term\<^sub>i\<^sub>,\<^sub>k\<close> on the left side is a linear
constructor pattern.

Since the type of a constructor application term is always an algebraic type, an argument type \<open>t\<^sub>j\<close>
may only be a non-algebraic type if the corresponding \<open>term\<^sub>i\<^sub>,\<^sub>j\<close> is a single variable in all \<open>eq\<^sub>i\<close>.
\<close>

subsubsection "The Proof Method \<open>pat_completeness\<close>"

text\<open>
For recursive definitions where all \<open>eq\<^sub>i\<close> are without assumptions and using a linear constructor
pattern on their left side HOL provides the proof method
@{theory_text[display]
\<open>pat_completeness\<close>}\index{pat-completeness@pat$\_$completeness (method)}
for the proof of equation completeness (see Section~\ref{holbasic-recursive-cover}), i.e. for
solving the first goal created by the recursive definition. The remaining goals for uniqueness
can be solved by using the injectivity of the constructor functions which is usually done by the
proof method \<^theory_text>\<open>auto\<close>. Therefore if a recursive definition uses only linear patterns its proof
can be specified as
@{theory_text[display]
\<open>by pat_completeness auto\<close>}
\<close>

subsubsection "Automatic Uniqueness by Sequential Equations"

text\<open>
A constructor pattern \<open>a\<close> is more specific than a constructor pattern \<open>b\<close> if \<open>a\<close> can be constructed
from \<open>b\<close> by replacing some variables by constructor applications (and renaming variables). If
corresponding function arguments \<open>term\<^sub>i\<^sub>j\<close> are specified by such patterns \<open>a\<close> and \<open>b\<close> in two defining
equations, the spaces of both equations overlap and the defined value must be the same for
uniqueness. Alternatively, uniqueness can be guaranteed by replacing the equation with the more
general pattern \<open>b\<close> by equations with more specific patterns using the remaining constructors, so
that the argument spaces do not overlap anymore.

This can be done automatically for a recursive definition where all \<open>eq\<^sub>i\<close> are without assumptions
and using a linear constructor pattern on their left side by specifying it in the form
@{theory_text[display]
\<open>function (sequential) name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n \<proof>\<close>}\index{sequential (keyword)}
Here the defining equations must be ordered such that equations with more specific patterns precede
those with more general patterns. HOL automatically replaces the latter equations so that the
argument spaces of all equations are pairwise disjoint. Note that the resulting equations are used
for the completeness and compatibility proofs and also in the rules provided for the recursive
definition such as \<open>name.cases\<close> or \<open>name.psimps\<close>.

If the equations do not cover all possible arguments because some constructors are omitted,
additional equations are added with patterns using the omitted constructors. These equations use
\<open>undefined\<close>\index{undefined (constant)} (see Section~\ref{holbasic-undefined}) as \<open>term\<^sub>i\<close> on the right side.

The completeness and compatibility proof must still be specified explicitly, although it always
works in the form \<^theory_text>\<open>by pat_completeness auto\<close>.
\<close>

subsubsection "The \<open>fun\<close> Command"

text\<open>
HOL supports the abbreviation
@{theory_text[display]
\<open>fun name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n\<close>}\index{fun (keyword)}
for the recursive definition
@{theory_text[display]
\<open>function (sequential) name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n
by pat_completeness auto
termination by lexicographic_order\<close>}
which includes the completeness and compatibility proof and a termination proof. If the termination
proof cannot be done by the proof method \<^theory_text>\<open>lexicographic_order\<close> (see
Section~\ref{holbasic-recursive-term}) an error is signaled, then the long form must be used to
specify a different termination proof.

The faculty function definitions in Section~\ref{holbasic-recursive-defeqs} are not of the required
form: the definition(s) of \<open>fac\<close> use an assumption in their second equation, the definition of
\<open>fac2\<close> uses the argument term \<open>n+1\<close> on the left side which is no constructor pattern because the
function \<open>(+)\<close> is not a constructor. However, type \<open>nat\<close> is actually defined in a way equivalent
to an algebraic type with constructors \<open>0\<close> and \<open>Suc\<close> (see Section~\ref{holtypes-nat}) where the
term \<open>Suc n\<close> is equivalent to \<open>n+1\<close>. Therefore the faculty function can be defined as
@{theory_text[display]
\<open>fun fac3 :: "nat \<Rightarrow> nat" where
  "fac3 0 = 1"
| "fac3 (Suc n) = (Suc n) * fac3 n"\<close>}\index{fac3 (example constant)}
because \<open>0\<close> and \<open>(Suc n)\<close> are linear constructor patterns.
\<close>

subsubsection "Primitive Recursion"

text\<open>
A linear constructor pattern consisting of a sequence of terms is called ``primitive''\index{constructor!pattern!primitive linear $\sim$}\index{linear constructor pattern!primitive $\sim$} if exactly
one term is a constructor application and all constructor arguments in this term are single
variables. Thus a primitive constructor pattern has the general form
@{text[display]
\<open>x\<^sub>1 \<dots> x\<^sub>i\<^sub>-\<^sub>1 (cname x\<^sub>i\<^sub>,\<^sub>1 \<dots> x\<^sub>i\<^sub>,\<^sub>n) x\<^sub>i\<^sub>+\<^sub>1 \<dots> x\<^sub>k\<close>}
where all \<open>x\<^sub>i\<close> and \<open>x\<^sub>i\<^sub>,\<^sub>j\<close> are variables. In particular, if a linear constructor pattern consists of
a single term it is always primitive.

A recursive function definition
@{theory_text[display]
\<open>fun name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n\<close>}
is called primitive\index{primitive recursive definition}\index{definition!primitive recursive $\sim$}\index{recursion!primitive $\sim$}
\index{function!primitive recursive $\sim$} if all defining equations \<open>eq\<^sub>i\<close> use a primitive constructor pattern on their
left side and all arguments of recursive calls in \<open>term\<^sub>i\<close> on the right side are single variables. 

Note that since the equations must be ordered so that equations with more specific patterns precede
equations with more general patterns all constructor application terms must occur at the same
argument position in the patterns. Therefore only one argument type \<open>t\<^sub>i\<close> must be an algebraic type,
all others may be arbitrary types because the corresponding arguments are denoted by single
variables in all patterns.

For primitive recursive function definitions HOL provides the alternative syntax
@{theory_text[display]
\<open>primrec name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n\<close>}\index{primrec (keyword)}

Its difference to the form using the \<^theory_text>\<open>fun\<close> command is that it only provides the rule set
\<open>name.simps\<close> and none of the other rules. The reason is that the \<open>cases\<close> and \<open>induct\<close> rules are
mainly equivalent to the case and induction rules provided for the algebraic type of the used
constructors (see Section~\ref{holtdefs-data-rules}).

Since every such definition can also be written using the \<^theory_text>\<open>fun\<close> command the use of \<^theory_text>\<open>primrec\<close> is
mainly a documentation that the definition is primitive recursive.

Since the faculty function has only one argument the constructor patterns in the definition of
\<open>fac3\<close> above are both primitive. Moreover, since \<open>fac3\<close> is only applied to the plain variable \<open>n\<close>
on the right side of the second equation it is a primitive recursive function definition and may be
written
@{theory_text[display]
\<open>primrec fac3 :: "nat \<Rightarrow> nat" where
  "fac3 0 = 1"
| "fac3 (Suc n) = (Suc n) * fac3 n"\<close>}\index{fac3 (example constant)}\<close>

section "Subtypes"
text_raw\<open>\label{holtdefs-sub}\<close>

text \<open>
A subtype\index{subtype} specifies the values of a new type \<open>T'\<close> by a set of values
of an existing type \<open>T\<close>. However,
since the values of different types are always disjoint, the values in the set are not directly the
values of the new type, instead, there is a 1-1 relation between them.

A subtype is defined\index{definition!subtype $\sim$} in the form
@{theory_text[display]
\<open>typedef name = "term" \<proof>\<close>}\index{typedef (keyword)}
where \<open>name\<close> is the name of the new type \<open>T'\<close> and \<open>term\<close> is a term for the representing set. The
\<open>\<proof>\<close> must prove that the representing set is not empty. A subtype definition implies that
for every value in the representing set there is a unique value in the defined subtype.

Note that the concept of subtypes actually depends on the specific HOL type \<open>set\<close> for specifying
the representing set. See Section~\ref{holtypes-set} for how to denote terms for this set. Also
note that the set is always of type \<open>T set\<close> where \<open>T\<close> is the common type of all set elements.
This implies that the representing set is always a subset of the set of all values of \<open>T\<close>
which explains the designation of type \<open>T'\<close> as ``subtype'' of \<open>T\<close>.

A simple example is the type
@{theory_text[display]
\<open>typedef threesub = "{0::nat,1,2}" by auto\<close>}\index{threesub (example type)}
which has three values. The representing set contains three natural numbers. As usual,
their type \<open>nat\<close> must be explicitly specified because the constants \<open>0, 1, 2\<close> may also denote values
of other types. However, they do not denote the values of the new type \<open>threesub\<close>, the type definition
does not introduce constants for them.\<close>

subsection "Subtypes as Quotients"
text_raw\<open>\label{holtdefs-sub-quot}\<close>

text \<open>
The values of type \<open>T\<close> in the representing set can be related to their corresponding values of the
new type \<open>T'\<close> by a relation \<open>R :: T \<Rightarrow> T' \<Rightarrow> bool\<close>. Since there is a unique value in \<open>T'\<close> for every
set member and all values of \<open>T'\<close> are related with a set member, \<open>R\<close> is right-unique and right-total.

As described in Section~\ref{holbasic-quotlift} this means that \<open>T'\<close> is a quotient of \<open>T\<close> with
transfer relation \<open>R\<close>. This observation implies the existence of all other items related to a
quotient: the morphisms \<open>abs_T', rep_T'\<close>, the domain \<open>D\<close> of \<open>R\<close> and the equivalence relation \<open>E\<close>
(see Section~\ref{holbasic-quotlift}). As usual for a quotient, \<open>T'\<close> is called ``abstract type''
and \<open>T\<close> is called ``raw type''.

Since the relation between \<open>D\<close> and \<open>T'\<close> is 1-1, the transfer relation \<open>R\<close> is also left-unique
(see Section~\ref{holbasic-quotlift-quot})

The domain \<open>D\<close> of \<open>R\<close> is the set of all values in \<open>T\<close> related to a value in \<open>T'\<close>, so it is exactly
the representing set used to define the subtype. The abstraction function \<open>abs_T' :: T \<Rightarrow> T'\<close> maps
all values in \<open>D\<close> to their corresponding value in \<open>T'\<close> and is underspecified otherwise. The
representation function \<open>rep_T' :: T' \<Rightarrow> T\<close> is uniquely determined and maps all values of \<open>T'\<close> to
their corresponding value in \<open>D\<close>. As usual, the values in \<open>D\<close> are called representation values for
the values of \<open>T'\<close>. The equivalence relation \<open>E\<close> is the equality restricted to the representing set
\<open>eq_onp (\<lambda>x. x\<in>D)\<close>.
\<close>

subsubsection "The Morphism Names"

text\<open>
The subtype definition \<^theory_text>\<open>typedef T' = D \<proof>\<close> introduces the constants \<open>Abs_T'\<close>
\index{Abs-@Abs$\_$ (constant name prefix)} and \<open>Rep_T'\<close>\index{Rep-@Rep$\_$ (constant name prefix)}
for the morphisms (note the capitalization of the names). The function \<open>Abs_T'\<close> can be used to
denote the values of the subtype. Thus, \<open>Abs_T'\<close> plays the role of a constructor for type \<open>T'\<close>,
whereas \<open>Rep_T'\<close> can be thought of being a destructor for \<open>T'\<close>.

In the example the morphisms are \<open>Abs_threesub :: nat \<Rightarrow> threesub\<close> and \<open>Rep_threesub :: threesub \<Rightarrow> nat\<close>. The
values of type \<open>threesub\<close> may be denoted as \<open>(Abs_threesub 0)\<close>, \<open>(Abs_threesub 1)\<close>, and \<open>(Abs_threesub 2)\<close>.
The term \<open>(Abs_threesub 42)\<close> is a valid term of type \<open>threesub\<close>, however, no information about its value
is available.

Alternative names may be specified for the morphisms in the form
@{theory_text[display]
\<open>typedef name = "term" morphisms rname aname \<proof>\<close>}\index{morphisms (keyword)}
where \<open>rname\<close> replaces \<open>Rep_name\<close> and \<open>aname\<close> replaces \<open>Abs_name\<close>.
\<close>

subsection "Parameterized Subtypes"
text_raw\<open>\label{holtdefs-sub-param}\<close>

text\<open>
Like declared types subtypes may be parameterized (see Section~\ref{theory-terms-types}):
@{theory_text[display]
\<open>typedef ('name\<^sub>1,\<dots>,'name\<^sub>n) name = "term" \<proof>\<close>}
where the \<open>'name\<^sub>i\<close> are the type parameters. They may occur in the type of the \<open>term\<close>, i.e., the 
\<open>term\<close> may be polymorphic (see Section~\ref{theory-terms-consts}). Then it does not
denote a fixed set of values, it denotes for every instantiation of the type parameters a different
set of values from a different type.

As an example the type
@{theory_text[display]
\<open>typedef 'a eqpair = "{(x::'a,y::'a). x = y}" by auto\<close>}\index{eqpair (example type)}
has the set of all pairs (see Section~\ref{holbasic-tuples}) as its representing set, where the
first and second components are equal. The type of both components is the type parameter \<open>'a\<close>, thus
the raw type is the type \<open>'a \<times> 'a\<close> of pairs of values of the same type. If \<open>'a\<close> is instantiated
by type \<open>bool\<close> the representing set is \<open>{(True,True),(False,False)}\<close> whereas if \<open>'a\<close> is instantiated
by type \<open>nat\<close> the representing set is infinite.
\<close>

subsection "Type Copies"
text_raw\<open>\label{holtdefs-sub-copies}\<close>

text \<open>
A type copy\index{type!copy} is the special case of a subtype definition where the representing set
is the universal set (see Section~\ref{holtypes-set-values}) of the raw type:
@{theory_text[display]
\<open>typedef name = "UNIV :: T set" by auto\<close>}
The non-emptiness proof can always be performed by the \<open>auto\<close> method, since the universal set covers
all values in type \<open>T\<close> and types are always non-empty.

As described at the end of Section~\ref{holbasic-quotlift-setup} a type copy is the case where the
transfer relation \<open>R\<close> is left-unique and left-total and thus the new type \<open>name\<close> is ``isomorphic''
to \<open>T\<close>. The values are in 1-1 relation, although, as usual for distinct types, the value sets are
disjoint. The equivalence relation \<open>E\<close> is the equality \<open>(=)\<close> on \<open>T\<close>.

For a parameterized type copy the raw type \<open>T\<close> is some type expression constructed from the type
parameters. An example is the type copy
@{theory_text[display]
\<open>typedef ('a, 'b) cpyfun = "UNIV :: ('a \<Rightarrow> 'b) set" by simp\<close>}\index{cpyfun (example type)}
of the type of functions from \<open>'a\<close> to \<open>'b\<close>.\<close>

subsection "Subtype Rules"
text_raw\<open>\label{holtdefs-sub-rules}\<close>

text \<open>
A subtype definition only introduces a small number of rules, no rules are added to the simpset.
All introduced rules can be displayed using the ``Print Context'' tab in the Query panel
\index{panel!query $\sim$} as described in Section~\ref{theory-theorem-search}, if the cursor is
positioned after the subtype definition.
\<close>

subsubsection "Basic Morphism Rules"

text\<open>
As described in Section~\ref{holbasic-quotlift-quot} for a left-unique transfer relation the
morphisms are inverse of each other. For a subtype definition \<^theory_text>\<open>typedef T' = D \<proof>\<close> this is
expressed by two rules of the form
@{text[display]
\<open>Abs_T'_inverse:
  ?y \<in> D \<Longrightarrow> Rep_T' (Abs_T' ?y) = ?y
Rep_T'_inverse:
  Abs_T' (Rep_T' ?x) = ?x\<close>}\index{inverse@$\_$inverse (fact name suffix)}

This also implies that both morphisms are injective which is stated explicitly by two rules of the form
@{text[display]
\<open>Abs_T'_inject:
  \<lbrakk>?y\<^sub>1 \<in> D; ?y\<^sub>2 \<in> D\<rbrakk> \<Longrightarrow> (Abs_T' ?y\<^sub>1 = Abs_T' ?y\<^sub>2) = (?y\<^sub>1 = ?y\<^sub>2)
Rep_T'_inject:
  (Rep_T' ?x\<^sub>1 = Rep_T' ?x\<^sub>2) = (?x\<^sub>1 = ?x\<^sub>2)\<close>}\index{inject@$\_$inject (fact name suffix)}

Since all values of type \<open>T'\<close> can be denoted as \<open>Abs_T' y\<close> for some \<open>y\<close> in the representing set \<open>D\<close>,
the rule \<open>Abs_T'_inject\<close> can be used to prove equality or inequality for values of type \<open>T'\<close> based on
the equality for values in \<open>D\<close>.
\<close>

subsubsection "Case Rules"

text\<open>
Every subtype definition \<^theory_text>\<open>typedef T' = D \<proof>\<close> introduces a case rule (see
Section~\ref{case-reasoning-rules}) of the form
@{text[display]
\<open>Abs_T'_cases:
  (\<And>y. \<lbrakk>?x = Abs_T' y; y \<in> D\<rbrakk> \<Longrightarrow> ?P) \<Longrightarrow> ?P\<close>}\index{cases@$\_$cases (fact name suffix)}
It is valid because the \<open>Abs_T'\<close> application covers all possibilities of constructing a
value \<open>?x\<close> of \<open>T'\<close>.

The rule \<open>Abs_T'_cases\<close> is associated with the new subtype \<open>T'\<close> for use by the \<^theory_text>\<open>cases\<close> method
(see Section~\ref{case-reasoning-cases}). Therefore the application of the method
@{theory_text[display]
\<open>cases "term"\<close>}
where \<open>term\<close> is of type \<open>T'\<close> applies \<open>Abs_T'_cases\<close> to replace the current goal. Since the rule has
only one case, it does not split the goal. Applying it to a goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>
as described in Section~\ref{case-reasoning-cases} results in the single new goal
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m y. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; term = Abs_T' y; y \<in> D\<rbrakk> \<Longrightarrow> C\<close>}
where the variable \<open>y\<close> and the two assumptions from the case rule have been added. Together the new
goal provides a representation of \<open>term\<close> by applying \<open>Abs_T'\<close> to a value \<open>y\<close> from the representing
set \<open>D\<close>. This may allow to use facts about \<open>y\<close> to prove the goal.

The name for the named context created by the \<^theory_text>\<open>cases\<close> method is simply the morphism name
\<open>Abs_T'\<close>. Therefore a structured proof using case based reasoning for a \<open>term\<close> of subtype \<open>T'\<close>
has the form
@{theory_text[display]
\<open>proof (cases "term")
  case (Abs_T' y) \<dots> show ?thesis \<proof>
qed\<close>}
The name \<open>y\<close> of the locally fixed variable can be freely selected, it denotes the morphism
argument, i.e., the representation value for \<open>term\<close>.

Every subtype definition \<^theory_text>\<open>typedef T' = D \<proof>\<close> also introduces an elimination rule (see
Section~\ref{case-elim-rules}) of the form
@{text[display]
\<open>Rep_T'_cases:
  \<lbrakk>?y \<in> D; \<And>x. ?y = Rep_T' x \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
It is valid because the \<open>Rep_T'\<close> application covers all possibilities to determine a representation
value \<open>?y\<close> in \<open>D\<close>.

With the help of this rule it is possible to introduce an abstraction value \<open>x\<close> corresponding to
a representation value \<open>?y\<close>, consuming an assumption or input fact that \<open>?y\<close> is in \<open>D\<close>. For
application by the method \<^theory_text>\<open>cases\<close> the rule is annotated by \<open>[consumes 1]\<close> and the name for the
created named context is the morphism name \<open>Rep_T'\<close>. As described in Section~\ref{case-elim-struct}
a pattern for using the rule in a structured proof is
@{theory_text[display]
\<open>theorem "C" if "y \<in> D"
  using that
proof (cases rule: Rep_T'_cases)
  case (Rep_T' x) \<dots> show ?thesis \<proof>
qed\<close>}\<close>

subsubsection "Induction Rules"

text\<open>
Every subtype definition \<^theory_text>\<open>typedef T' = D \<proof>\<close> introduces two induction rules (see
Section~\ref{case-induction-rules}) of the form
@{text[display]
\<open>Abs_T'_induct:
  (\<And>y. y \<in> D \<Longrightarrow> ?P (Abs_T' y)) \<Longrightarrow> ?P ?a
Rep_T'_induct:
  \<lbrakk>?a \<in> D; \<And>x. ?P (Rep_T' x)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}\index{induct@$\_$induct (fact name suffix)}
The former rule is a plain induction rule, the latter is an induction rule with elimination where
the major premise states that the value \<open>?a\<close> is in \<open>D\<close>. Both rules only contain a ``base case''
and no ``induction step'' with a recursive occurrence of values of the defined type \<open>T'\<close>. As for
the case rules they are valid because the morphism applications cover all possibilities of
constructing values of \<open>T'\<close> or values in \<open>D\<close>, respectively.

Since the rules only consist of a base case they are mainly equivalent to the case rules. However,
when applied by the \<open>induct\<close> method, they not only provide a representation by a morphism for a
specified variable, they also substitute every occurrence of the variable by the morphism
representation.

The rule \<open>Abs_T'_induct\<close> is associated with subtype \<open>T'\<close> for use by the methods \<^theory_text>\<open>induction\<close> and
\<^theory_text>\<open>induct\<close> (see Section~\ref{case-induction}). Therefore the application of the method
@{theory_text[display]
\<open>induction x\<close>}
where \<open>x\<close> is a variable of type \<open>T'\<close> replaces a goal by a goal where every occurrence of \<open>x\<close> is
substituted by the term \<open>Abs_T' y\<close> and \<open>y\<close> is a new bound variable with the additional assumption
\<open>y \<in> D\<close> named \<open>Abs_T'.hyps\<close>. As usual for the induction methods, \<open>x\<close> is substituted in the goal
conclusion and also in all goal assumptions.

As for the case rule and the \<^theory_text>\<open>cases\<close> method, the name for the named context created by the 
methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close> is simply the morphism name \<open>Abs_T'\<close>. Therefore a structured
proof using induction for a variable \<open>x\<close> of subtype \<open>T'\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (Abs_T' y) \<dots> show ?case \<proof>
qed\<close>}

As an example, the induction rule for the subtype \<open>threesub\<close> defined above is
@{text[display]
\<open>Abs_threesub_induct:
  "\<And>y. y \<in> {0, 1, 2} \<Longrightarrow> ?P (Abs_threesub y)) \<Longrightarrow> ?P ?a\<close>}
By applying the method \<open>(induction x)\<close> the goal \<open>x = Abs_threesub 0 \<Longrightarrow> x \<noteq> Abs_threesub 1\<close> is replaced by
the goal \<open>\<And>y.  \<lbrakk>y \<in> {0, 1, 2}; Abs_threesub y = Abs_threesub 0\<rbrakk> \<Longrightarrow> Abs_threesub y \<noteq> Abs_threesub 1\<close>
(which does not help for the proof, but shows the effect of the induction rule).

The rule \<open>Rep_T'_induct\<close> is annotated by \<open>[consumes 1]\<close> for application by the methods \<^theory_text>\<open>induction\<close>
and \<^theory_text>\<open>induct\<close> and the name for the created named context is the morphism name \<open>Rep_T'\<close>. As described
in Section~\ref{case-induction-elim} a pattern for using the rule in a structured proof is
@{theory_text[display]
\<open>theorem "C" if "y \<in> D"
  using that
proof (induction rule: Rep_T'_induct)
  case (Rep_T' x) \<dots> show ?case \<proof>
qed\<close>}

As an example, the induction rule with elimination for the subtype \<open>threesub\<close> defined above is
@{text[display]
\<open>Rep_threesub_induct:
  \<lbrakk>?a \<in> {0, 1, 2}; \<And>x. ?P (Rep_threesub x)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}\<close>

subsection "Registering Subtypes as Quotients"
text_raw\<open>\label{holtdefs-sub-setup}\<close>

text \<open>
Although every subtype defined by \<^theory_text>\<open>typedef T' = D \<proof>\<close> is a quotient, HOL does not
automatically register it as such (see Section~\ref{holbasic-quotlift-setup}). However, it
generates and proves the fact
@{text[display]
\<open>type_definition_T':
  type_definition Rep_T' Abs_T' D\<close>}
This is a type-definition theorem (see Section~\ref{holbasic-quotlift-quot}) and can be used for
registering \<open>T'\<close> as quotient using the command
@{theory_text[display]
\<open>setup_lifting type_definition_T'\<close>}
As usual, the command prepares for defining functions on the subtype by lifting them from the raw
type (see Section~\ref{holbasic-quotlift-lift}) and introduces transfer rules for transferring terms
from the subtype to the raw type (see Section~\ref{holbasic-quotlift-setup}).

This use of the predicate \<open>type_definition\<close> for characterizing types introduced by the \<^theory_text>\<open>typedef\<close>
command is the reason for its name.

As described in Section~\ref{holbasic-quotlift-setup}, if the raw type \<open>T\<close> of a polymorphic subtype
is no BNF or has dead type parameters, the relator \<open>rel_T\<close> cannot be used to provide full transfer
support, the \<^theory_text>\<open>setup_lifting\<close> command will issue a warning in this case.
\<close>

subsection "Lifting Functions to Subtypes"
text_raw\<open>\label{holtdefs-sub-lift}\<close>

text \<open>
After registering a subtype as quotient as described in Section~\ref{holtdefs-sub-setup}, functions
can be lifted from the raw type to the subtype as described in Section~\ref{holbasic-quotlift-lift}.

Since the transfer relation for a subtype is left-unique, the respectfulness property required for
a function to be lifted is based on closedness of the representing set. For a subtype defined by
\<^theory_text>\<open>typedef T' = D \<proof>\<close> the respectfulness property for an operation \<open>f::T\<Rightarrow>T\<close> is
@{text[display]
\<open>\<And>x::T. x \<in> D \<Longrightarrow> f x \<in> D\<close>}
and for a function \<open>f::u\<Rightarrow>T\<close> where only the results shall be lifted it is
@{text[display]
\<open>\<And>x::u. f x \<in> D\<close>}
For a function \<open>f::T\<Rightarrow>u\<close> where only the arguments shall be lifted respectfulness is always satisfied.

For the example type \<open>threesub\<close> as defined above, after registering it as quotient by
@{theory_text[display]
\<open>setup_lifting type_definition_threesub\<close>}
example functions can be lifted from type \<open>nat\<close> as follows:
@{theory_text[display]
\<open>lift_definition suc3 :: "threesub \<Rightarrow> threesub"
  is "\<lambda>x. (x+1) mod 3" by auto
lift_definition mod3 :: "nat \<Rightarrow> threesub"
  is "\<lambda>x. x mod 3" by auto
lift_definition evn3 :: "threesub \<Rightarrow> bool"
  is "\<lambda>x. x mod 2 = 0" done\<close>}
The first example defines a cyclic successor function on \<open>threesub\<close>. Here the argument and result
type are lifted, the goal to be proved for respectfulness is
\<open>\<And>n. n \<in> {0, 1, 2} \<Longrightarrow> (n + 1) mod 3 \<in> {0, 1, 2}\<close> which can be proved by the \<open>auto\<close> method. The
second example calculates the remainder modulo \<open>3\<close> and represents the result in type \<open>threesub\<close>,
the goal to be proved is \<open>\<And>n. n mod 3 \<in> {0, 1, 2}\<close>. The third example defines a predicate for
evenness on \<open>threesub\<close>, no goal needs to be proved because only the argument type is lifted,
therefore the proof is empty and can immediately be terminated by \<open>done\<close>.

As described in Section~\ref{holbasic-quotlift-lift} HOL provides automatic support for transferring
terms containing functions defined by lifting to the raw type. As an example in the theorem
@{theory_text[display]
\<open>theorem "evn3 (suc3 (mod3 7))" apply(transfer) by simp\<close>}
the \<open>transfer\<close> method replaces the goal by the proposition \<open>(7 mod 3 + 1) mod 3 mod 2 = 0\<close> which is
simply a property of natural numbers and can be proved by the simplifier using the existing rules
about the natural numbers. No rules about the subtype \<open>threesub\<close> are required.

This is a typical way of working with a subtype using the lifting package: All functions on the
subtype are introduced by lifting, then all theorems specified for the subtype can be proved using
transfer and the existing facts about the raw type.

In the case of a type copy (see Section~\ref{holtdefs-sub-copies}) the representing set contains all
values of the raw type and is closed for all functions. Therefore arbitrary functions can be lifted
from the raw type to a type copy using an empty proof.\<close>

subsection "Subtypes of Bounded Natural Functors"
text_raw\<open>\label{holtdefs-sub-bnf}\<close>

text \<open>
As described in Section~\ref{holbasic-quotlift-bnf} a subtype \<open>T'\<close> of a BNF \<open>T\<close> (the type of the
elements of the representing set) may again be a BNF. In that case the \<^theory_text>\<open>lift_bnf\<close> command can be
used to register \<open>T'\<close> as BNF. Note that before using the command it is necessary to explicitly
register \<open>T'\<close> as quotient by the command \<^theory_text>\<open>setup_lifting type_definition_T'\<close> (see
Section~\ref{holtdefs-sub-setup}).

If the representing set does not contain all values of \<open>T\<close> the nonemptiness witness of \<open>T\<close> (see
Section~\ref{holbasic-quotlift-bnf}) may get
lost in \<open>T'\<close>. Therefore usually a new witness which belongs to the representing set must be
specified in the command:
@{theory_text[display]
\<open>lift_bnf ('a\<^sub>1,\<dots>,'a\<^sub>n) T' [wits: "term"] \<proof>\<close>}
where \<open>term\<close> specifies a function from arguments of types \<open>'a\<^sub>1,\<dots>,'a\<^sub>n\<close> to values which must be
in the representing set.

After registering the example type \<open>eqpair\<close> defined in Section~\ref{holtdefs-sub-param} as
quotient using
@{theory_text[display]
\<open>setup_lifting type_definition_eqpair\<close>}
it can be registered as BNF using the command
@{theory_text[display]
\<open>lift_bnf 'a eqpair [wits: "\<lambda>(x::'a). (x,x)"] by auto\<close>}
because the pair \<open>(x,x)\<close> has equal components and is thus in the representing set of \<open>eqpair\<close>.

For a type copy \<open>T'\<close> (see Section~\ref{holtdefs-sub-copies}) of a BNF \<open>T\<close> the transfer relation is
also left-total and the \<^theory_text>\<open>copy_bnf\<close> command (see Section~\ref{holbasic-quotlift-bnf}) can be used to
register \<open>T'\<close> as BNF (after registering it as quotient). No proof is required, a type copy of a BNF
is always a BNF.

After registering the example type \<open>cpyfun\<close> defined in Section~\ref{holtdefs-sub-copies} as
quotient using
@{theory_text[display]
\<open>setup_lifting type_definition_cpyfun\<close>}
it can be registered as BNF using the command
@{theory_text[display]
\<open>copy_bnf ('a, 'b) cpyfun\<close>}
\<close>

section "Quotient Types"
text_raw\<open>\label{holtdefs-quot}\<close>

text \<open>
A quotient type\index{quotient!type}\index{type!quotient $\sim$} specifies the values of a new type
\<open>T'\<close> by equivalence classes of an equivalence relation \<open>E\<close> on an existing type \<open>T\<close>. As usual, the
equivalence classes are not directly the values of the new type, instead, there is a 1-1 relation
between them.

A quotient type is defined\index{definition!quotient type $\sim$} in the form
@{theory_text[display]
\<open>quotient_type name = "type" / "term" \<proof>\<close>}\index{quotient-type@quotient$\_$type (keyword)}
where \<open>name\<close> is the name of the new type \<open>T'\<close>, \<open>type\<close> specifies the existing type \<open>T\<close>, and \<open>term\<close>
specifies the equivalence relation \<open>E\<close> which must be of type \<open>T \<Rightarrow> T \<Rightarrow> bool\<close>. The
\<open>\<proof>\<close> must prove that \<open>E\<close> is an equivalence relation which is stated by the predicate
application \<open>equivp E\<close>\index{equivp (constant)} (see Section~\ref{holtypes-rel-funcs}).

A simple example is the quotient type
@{theory_text[display]
\<open>quotient_type rem3 = nat / "\<lambda>x y. x mod 3 = y mod 3"
  by (simp add: equivp_def) metis\<close>}\index{rem3 (example type)}
which has three values related to the remainder classes of natural numbers modulo \<open>3\<close>.

If the \<open>type\<close> specified in a \<^theory_text>\<open>quotient_type\<close> definition has not been registered as functor
(see Section~\ref{holbasic-functor-reg}) the \<^theory_text>\<open>quotient_type\<close> definition signals a warning, that
no map function has been defined for it. As described in Section~\ref{holbasic-bnf-register} this
also happens for types registered as BNF, they have a defined mapper, but it is not registered.\<close>

subsection "Quotient Types as Quotients"
text_raw\<open>\label{holtdefs-quot-quot}\<close>

text \<open>
As the name suggests, a quotient type \<open>T'\<close> defined for \<open>T\<close> and \<open>E\<close> is a quotient of \<open>T\<close>. The
corresponding transfer relation \<open>R :: T \<Rightarrow> T' \<Rightarrow> bool\<close> relates all values in an equivalence class
of \<open>E\<close> with the value in \<open>T'\<close> which corresponds to that class. Since there is a unique value in \<open>T'\<close>
for every member of a class and all values of \<open>T'\<close> are related with a class member, \<open>R\<close> is
right-unique and right-total, i.e., \<open>T'\<close> is a quotient of \<open>T\<close>.

This observation implies the existence of all other items related to a quotient: the morphisms
\<open>abs_T', rep_T'\<close>, the domain \<open>D\<close> of \<open>R\<close> and the equivalence relation \<open>E\<close> (which is used in the
definition) (see Section~\ref{holbasic-quotlift}). As usual for a quotient, \<open>T'\<close> is called
``abstract type'' and \<open>T\<close> is called ``raw type''.

In contrast to a subtype definition (see Section~\ref{holtdefs-sub-setup}) a quotient type
definition immediately registers the quotient type \<open>T'\<close> as quotient of its raw type \<open>T\<close> using an
internal \<^theory_text>\<open>setup_lifting\<close> command (see Section~\ref{holbasic-quotlift-setup}).

The property \<open>equivp E\<close> implies the reflexivity rule \<open>reflp E\<close> (see Section~\ref{holbasic-quotlift}),
i.e., for a quotient type definition as above the transfer relation \<open>R\<close> is always left-total. HOL
automatically proves the reflexivity rule and uses it in the internal \<^theory_text>\<open>setup_lifting\<close> command as
described for left-total transfer relations in Section~\ref{holbasic-quotlift-setup}.

A more general quotient type where \<open>R\<close> needs not be left-total can be defined in the form
@{theory_text[display]
\<open>quotient_type name = "type" / partial: "term" \<proof>\<close>}\index{partial: (keyword)}
Here the \<open>\<proof>\<close> has only to prove the weaker property \<open>part_equivp E\<close>
\index{part_equivp@part$\_$equivp (constant)} (see Section~\ref{holtypes-rel-funcs}) which does not 
imply \<open>reflp E\<close> and allows \<open>E\<close> to be partial in the sense that there may be values in \<open>T\<close> which are
not even equivalent by \<open>E\<close> to themselves. In this case the domain \<open>D\<close> of \<open>R\<close> is the set of values
which are equivalent to themselves: \<open>D = {x. E x x}\<close>. Such a quotient type corresponds to the most
general case of quotient described in Section~\ref{holbasic-quotlift}. It is also automatically
registered as quotient by an internal \<^theory_text>\<open>setup_lifting\<close> command but with omitted reflexivity rule.\<close>

subsubsection "The Morphism Names"

text\<open>
The quotient type definition \<^theory_text>\<open>quotient_type T' = T / E\<close> introduces the constants \<open>abs_T'\<close> and
\<open>rep_T'\<close> for the morphisms (note the lowercase names in contrast to the morphism names described
for subtypes in Section~\ref{holtdefs-sub-quot}).

Additionally it introduces the constants \<open>Abs_T' :: (T set) \<Rightarrow> T'\<close> and
\<open>Rep_T' :: T' \<Rightarrow> (T set)\<close>. The former maps each equivalence class of \<open>E\<close> to the corresponding
value in the quotient type, it is underspecified for all other sets of values of type \<open>T\<close>. The
latter maps all values in the quotient type to the corresponding equivalence class of \<open>E\<close>.\<close>

subsubsection "Quotient Types and Subtypes"

text\<open>
In general, for a quotient type the equivalence classes of \<open>E\<close> are no singletons, therefore the
transfer relation \<open>R\<close> is not left-unique. Only if \<open>E\<close> is the equality \<open>(=)\<close> or the restricted
equality \<open>eq_onp (\<lambda>x. x\<in>D)\<close> (see Section~\ref{holbasic-equal-eq}) this would be the case.

Since every subtype (see Section~\ref{holtdefs-sub}) is a quotient with a left-unique transfer
relation, for every subtype defined by \<^theory_text>\<open>typedef T' = D\<close> with a representing set \<open>D :: T set\<close>
the quotient type definition
@{theory_text[display]
\<open>quotient_type T' = T / partial: "eq_onp (\<lambda>x. x\<in>D)" \<proof>\<close>}
has nearly the same effect as the subtype definition together with the \<^theory_text>\<open>setup_lifting\<close> command for
it. The main differences are the morphism names and the rules generated for them (see
Section~\ref{holtdefs-quot-rules}).

In the same way for every type copy \<^theory_text>\<open>typedef T' = (UNIV::T)\<close> (see Section~\ref{holtdefs-sub-copies})
the quotient type definition
@{theory_text[display]
\<open>quotient_type T' = T / "(=)" \<proof>\<close>}
has nearly the same effect as the type copy definition together with the \<^theory_text>\<open>setup_lifting\<close> command
for it.\<close>

subsection "Parameterized Quotient Types"
text_raw\<open>\label{holtdefs-quot-param}\<close>

text\<open>
Like declared types quotient types may be parameterized (see Section~\ref{theory-terms-types}):
@{theory_text[display]
\<open>quotient_type ('name\<^sub>1,\<dots>,'name\<^sub>n) name = "type" / "term" \<proof>\<close>}
where the \<open>'name\<^sub>i\<close> are the type parameters. They may occur in \<open>type\<close> i.e., the \<open>type\<close> (and also the
\<open>term\<close>) may be polymorphic (see Section~\ref{theory-terms-consts}).

As an example the type
@{theory_text[display]
\<open>quotient_type 'a quotpair = "'a \<times> 'a" / "\<lambda>(x\<^sub>1,x\<^sub>2) (y\<^sub>1,y\<^sub>2). x\<^sub>2 = y\<^sub>2"
  by(simp add: equivp_def split_beta) (metis case_prod_conv)\<close>}\index{quotpair (example type)}
is defined using the equivalence relation on pairs (see Section~\ref{holbasic-tuples}), where pairs
are equivalent if they have the same second component (i.e., the first component is ignored). Note
that this means the resulting quotient type is isomorphic to the type parameter \<open>'a\<close> itself.

As described in Section~\ref{holbasic-quotlift-setup}, if the raw type \<open>T\<close> of a polymorphic quotient
type is no BNF or has dead type parameters, the relator \<open>rel_T\<close> cannot be used to provide full
transfer support. The quotient type definition will issue a warning in this case, caused by the
internal \<^theory_text>\<open>setup_lifting\<close> command.\<close>

subsection "Quotient Type Rules"
text_raw\<open>\label{holtdefs-quot-rules}\<close>

text \<open>
Since a quotient type definition includes the \<^theory_text>\<open>setup_lifting\<close> command, it introduces all
corresponding rules as described in Section~\ref{holbasic-quotlift-setup}. Additionally, it
introduces similar rules like a subtype definition (see Section~\ref{holtdefs-sub-rules}), these
are described in the following subsections. No rules are added to the simpset.

All introduced rules can be displayed using the ``Print Context'' tab in the Query panel
\index{panel!query $\sim$} as described in Section~\ref{theory-theorem-search}, if the cursor is
positioned after the \<^theory_text>\<open>quotient_type\<close> definition.
\<close>

subsubsection "Basic Morphism Rules"

text\<open>
Other than for subtypes the basic morphism rules for a quotient type defined by
\<^theory_text>\<open>quotient_type T' = T / E \<proof>\<close> are not directly defined for the morphisms, but instead for
the functions \<open>Abs_T'\<close> and \<open>Rep_T'\<close> which map between values of \<open>T'\<close> and equivalence classes
of \<open>E\<close>. Whenever \<open>Abs_T'\<close> is applied to a variable in a rule, the rule must contain the additional
assumption that the variable belongs to the set of equivalence classes of \<open>E\<close>. This set is specified
in the rules by a complex term, for better presentation this term is abbreviated by \<open>\<C>(E)\<close> in the
following subsections.

As mappings to/from equivalence classes the functions are inverse of each other. This is expressed
by two rules of the form
@{text[display]
\<open>Abs_T'_inverse:
  ?y \<in> \<C>(E) \<Longrightarrow> Rep_T' (Abs_T' ?y) = ?y
Rep_T'_inverse:
  Abs_T' (Rep_T' ?x) = ?x\<close>}\index{inverse@$\_$inverse (fact name suffix)}

This also implies that both functions are injective which is stated explicitly by two rules of the form
@{text[display]
\<open>Abs_T'_inject:
  \<lbrakk>?y\<^sub>1 \<in> \<C>(E); ?y\<^sub>2 \<in> \<C>(E)\<rbrakk> \<Longrightarrow> (Abs_T' ?y\<^sub>1 = Abs_T' ?y\<^sub>2) = (?y\<^sub>1 = ?y\<^sub>2)
Rep_T'_inject:
  (Rep_T' ?x\<^sub>1 = Rep_T' ?x\<^sub>2) = (?x\<^sub>1 = ?x\<^sub>2)\<close>}\index{inject@$\_$inject (fact name suffix)}

Since all values of type \<open>T'\<close> can be denoted as \<open>Abs_T' y\<close> for some equivalence class \<open>y\<close>,
the rule \<open>Abs_T'_inject\<close> can be used to prove equality or inequality for values of type \<open>T'\<close>
based on the equality of equivalence classes of \<open>E\<close>.\<close>

subsubsection "Case Rules and Induction Rules"

text\<open>
Every quotient type definition \<^theory_text>\<open>quotient_type T' = T / E \<proof>\<close> introduces case rules (see
Section~\ref{case-reasoning-rules}) and induction rules (see Section~\ref{case-induction-rules})
similar to those described for subtypes (see Section~\ref{holtdefs-sub-rules}), where again the
single values in the representing set \<open>D\<close> are replaced by equivalence classes of \<open>E\<close>. All other
remarks given for the subtype rules also apply here. The rules are
@{text[display]
\<open>Abs_T'_cases:
  (\<And>y. \<lbrakk>?x = Abs_T' y; y \<in> \<C>(E)\<rbrakk> \<Longrightarrow> ?P) \<Longrightarrow> ?P
Rep_T'_cases:
  \<lbrakk>?y \<in> \<C>(E); \<And>x. ?y = Rep_T' x \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P
Abs_T'_induct:
  (\<And>y. y \<in> \<C>(E) \<Longrightarrow> ?P (Abs_T' y)) \<Longrightarrow> ?P ?a
Rep_T'_induct:
  \<lbrakk>?a \<in> \<C>(E); \<And>x. ?P (Rep_T' x)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}
\index{cases@$\_$cases (fact name suffix)}\index{induct@$\_$induct (fact name suffix)}

Additionally the quotient type definition introduces the induction rule
@{text[display]
\<open>T'.abs_induct: (\<And>y. ?P (abs_T' y)) \<Longrightarrow> ?P ?a\<close>}
It can be used to replace values of \<open>T'\<close> based on values of \<open>T\<close> instead of equivalence classes.\<close>

subsubsection "Morphism Definitions"

text\<open>
For the actual morphisms the quotient type definition generates definitions based on \<open>Abs_T'\<close> and
\<open>Rep_T'\<close>.

The morphism \<open>abs_T'\<close> is defined in the form 
@{text[display]
\<open>abs_T'_def: abs_T' x \<equiv> Abs_T' {y. E x y}\<close>}
Here for the argument \<open>x\<close> the class \<open>{y. E x y}\<close> of all equivalent values is mapped by \<open>Abs_T'\<close> to
the corresponding value in \<open>T'\<close>.

The morphism \<open>rep_T'\<close> is defined in the form 
@{text[display]
\<open>rep_T'_def: rep_T' x \<equiv> SOME y. y \<in> Rep_T' x\<close>}
using the choice operator (see Section~\ref{holbasic-descr-choice}). In this way, although the
representation function is normally not unique, HOL can provide a single definition without the need
to decide which specific representation values to use.\<close>

subsubsection "Quotient Theorem"

text\<open>
Every quotient type definition \<^theory_text>\<open>quotient_type T' = T / E \<proof>\<close> introduces the quotient theorem
(see Section~\ref{holbasic-quotlift-quot})
@{text[display]
\<open>Quotient_T': Quotient E abs_T' rep_T' cr_T'\<close>}
and provides the definition
@{text[display]
\<open>cr_T'_def: cr_T' = \<lambda>x y. abs_T' x = y\<close>}
for the transfer relation \<open>R\<close> named \<open>cr_T'\<close>. The quotient theorem is then used in the internal
\<^theory_text>\<open>setup_lifting\<close> command to register \<open>T'\<close> as quotient.

The quotient type definition also introduces the type-definition theorem
@{text[display]
\<open>type_definition_T': type_definition Rep_T' Abs_T' \<C>(E)\<close>}
which allows to view \<open>T'\<close> as subtype of the type \<open>T set\<close> with the equivalence classes \<open>\<C>(E)\<close> of
\<open>E\<close> as representing set. However, since every type can only be registered once as a quotient, the
type-definition theorem cannot be used for a corresponding registration.\<close>

subsection "Lifting Functions to Quotient Types"
text_raw\<open>\label{holtdefs-quot-lift}\<close>

text \<open>
Since the definition of a quotient type includes its registration as quotient, functions can be
lifted immediately after the definition from the raw type to the quotient type as described in
Section~\ref{holbasic-quotlift-lift}.

As described in Section~\ref{holbasic-quotlift-lift} the respectfulness property required for
a function to be lifted corresponds to preserving the equivalence used to define the quotient type.
For a quotient type defined by \<^theory_text>\<open>quotient_type T' = T / E \<proof>\<close> the respectfulness property
for an operation \<open>f::T\<Rightarrow>T\<close> is
@{text[display]
\<open>\<And>x y. E x y \<Longrightarrow> E (f x) (f y)\<close>}
and for a function \<open>f::T\<Rightarrow>u\<close> where only the arguments shall be lifted it is
@{text[display]
\<open>\<And>x y. E x y \<Longrightarrow> (f x) = (f y)\<close>}
For a function \<open>f::u\<Rightarrow>T\<close> where only the results shall be lifted respectfulness is always satisfied.

For the example type \<open>rem3\<close> as defined above, example functions can be lifted from type \<open>nat\<close> as
follows:
@{theory_text[display]
\<open>lift_definition add3 :: "rem3 \<Rightarrow> rem3 \<Rightarrow> rem3"
  is "(+)" using mod_add_cong by blast
lift_definition zro3 :: "rem3 \<Rightarrow> bool"
  is "\<lambda>x. x mod 3 = 0" by simp
lift_definition sub3 :: "nat \<Rightarrow> nat \<Rightarrow> rem3"
  is "(-)" done\<close>}
The first example defines addition of remainder classes. Here the argument and result
types are lifted, the goal to be proved for respectfulness is
@{text[display]
\<open>\<And>n\<^sub>1 n\<^sub>2 m\<^sub>1 m\<^sub>2. \<lbrakk>n\<^sub>1 mod 3 = n\<^sub>2 mod 3; m\<^sub>1 mod 3 = m\<^sub>2 mod 3\<rbrakk>
  \<Longrightarrow> (n\<^sub>1 + m\<^sub>1) mod 3 = (n\<^sub>2 + m\<^sub>2) mod 3\<close>}
which can be proved using the fact \<open>mod_add_cong\<close> provided by HOL. The second example defines a
predicate for being the zero remainder class, the goal to be proved is 
\<open>\<And>n\<^sub>1 n\<^sub>2. n\<^sub>1 mod 3 = n\<^sub>2 mod 3 \<Longrightarrow> (n\<^sub>1 mod 3 = 0) = (n\<^sub>2 mod 3 = 0)\<close>.
The third example calculates the difference and represents the result in type \<open>rem3\<close>, no goal needs
to be proved because only the result type is lifted, therefore the proof is empty and can
immediately by terminated by \<open>done\<close>.\<close>

subsubsection "Support for Transfer"

text\<open>
As described in Section~\ref{holbasic-quotlift-lift} HOL provides automatic support for transferring
terms containing functions defined by lifting to the raw type. As an example in the theorem
@{theory_text[display]
\<open>theorem "zro3 (add3 (sub3 10 5) (sub3 3 2))" apply(transfer) by simp\<close>}
the \<open>transfer\<close> method replaces the goal by the proposition \<open>(10 - 5 + (3 - 2)) mod 3 = 0\<close> which is
simply a property of natural numbers and can be proved by the simplifier using the existing rules
about the natural numbers. No rules about the quotient type \<open>rem3\<close> are required.

This is a typical way of working with a quotient type using the lifting package: All functions on the
quotient type are introduced by lifting, then all theorems specified for the quotient type can be
proved using transfer and the existing facts about the raw type.\<close>

subsubsection "Lifting Functions to Partial Quotient Types"

text\<open>
If the quotient type has been defined by \<^theory_text>\<open>quotient_type T' = T / partial: E \<proof>\<close> lifting
functions works mainly in the same way as described above. However, in the case of a function
\<open>f::u\<Rightarrow>T\<close> where only the results shall be lifted, respectfulness is no more automatically satisfied.
The respectfulness property to be proved here is \<open>\<And>x. E (f x) (f x)\<close> which means that all result
values \<open>(f x)\<close> must belong to the domain \<open>D\<close> of the transfer relation (see
Section~\ref{holbasic-quotlift-absraw}).\<close>

subsection "Quotient Types for Bounded Natural Functors"
text_raw\<open>\label{holtdefs-quot-bnf}\<close>

text \<open>
As described in Section~\ref{holbasic-quotlift-bnf} a quotient type \<open>T'\<close> of a BNF \<open>T\<close> may again be
a BNF. If \<open>T'\<close> has been defined by \<^theory_text>\<open>quotient_type T' = T / E \<proof>\<close> the \<^theory_text>\<open>lift_bnf\<close> command can
be used to register \<open>T'\<close> as BNF. If, instead, \<open>T'\<close> has been defined by
\<^theory_text>\<open>quotient_type T' = T / partial: E \<proof>\<close> where the transfer relation need not be left-total,
the \<^theory_text>\<open>lift_bnf\<close> command is not supported, it signals an error message about a missing reflexivity
rule (which is only available for a left-total transfer relation).

The example type \<open>quotpair\<close> defined in Section~\ref{holtdefs-quot-param} can be registered as BNF
using the command
@{theory_text[display]
\<open>lift_bnf 'a quotpair by force auto\<close>}\<close>

section "Record Types"
text_raw\<open>\label{holtdefs-record}\<close>

text\<open>
Record types\index{record!type}\index{type!record $\sim$} resemble algebraic types in that they are roughly equivalent to tuple types,
however, they are defined in a completely different way. They do not support recursion, instead
they support a simple form of inheritance\index{inheritance}. They can be used to model ``record types'' in programming
languages and object data in object oriented programming languages.
\<close>

subsection "Record Definitions"
text_raw\<open>\label{holtdefs-record-def}\<close>

text \<open>
A record type is defined in the form\index{definition!record type $\sim$}
@{theory_text[display]
\<open>record rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close>}\index{record (keyword)}
where \<open>rname\<close> is the name of the new type, the \<open>fname\<^sub>i\<close> are the pairwise distinct names of the
record components\index{record!component} (also called ``fields'')\index{record!field} and the \<open>ftype\<^sub>i\<close> are the corresponding component types.
Atleast one component must be specified. The resulting type \<open>rname\<close> is mainly equivalent to the
tuple type \<open>ftype\<^sub>1 \<times> \<dots> \<times> ftype\<^sub>n\<close> (see Section~\ref{holbasic-tuples}), however, every record type
definition introduces a new type, even if the component names and types are the same.

The record type defined as above can either be denoted by its \<open>rname\<close> or by its ``record type
expression''\index{record!type expression}\index{type!expression!record $\sim$} (in inner syntax)
@{theory_text[display]
\<open>\<lparr>fname\<^sub>1 :: ftype\<^sub>1, \<dots>, fname\<^sub>n :: ftype\<^sub>n\<rparr>\<close>}
Note that a record type expression may only be used after a corresponding record type definition.
If there are several record type definitions with the same field names and types the record type
expression refers to the syntactically latest previous matching record type definition.

If a field name \<open>fname\<^sub>i\<close> occurs in several record type definitions it may be referred uniquely as
a qualified name by prepending the record type name in the form \<open>rname.fname\<^sub>i\<close>.

An example record definition is
@{theory_text[display]
\<open>record recrd = 
  num :: nat 
  nums :: "nat set" 
  nice :: bool\<close>}\index{recrd (example type)}
It has an equivalent structure as the datatype \<open>recrd\<close> with the single constructor defined in
Section~\ref{holtdefs-data-constr}. The record type expression for it is
@{theory_text[display]
\<open>\<lparr>num :: nat, nums :: nat set, nice :: bool\<rparr>\<close>}
Alternatively the field names may be qualified:
@{theory_text[display]
\<open>\<lparr>recrd.num :: nat, recrd.nums :: nat set, recrd.nice :: bool\<rparr>\<close>}
\<close>

subsubsection "Record Type Schemes"

text \<open>
To be able to extend a record type by additional fields, a record type definition
\<^theory_text>\<open>record rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close> actually
defines a parameterized type \<open>rname_scheme\<close>\index{scheme@$\_$scheme (type name suffix)}
with a single type parameter and an additional component of that type which is called the ``more
part''\index{more part}. Every instantiation of \<open>('a rname_scheme)\<close> is called
a record type scheme\index{type!record $\sim$!scheme}\index{record!type scheme}, the most general one is \<open>('a rname_scheme)\<close> where the
more part has an arbitrary type \<open>'a\<close>. For the defined record type the more part has type
\<open>unit\<close> (see Section~\ref{holtypes-unit}), i.e., type \<open>rname\<close> is the same as \<open>(unit rname_scheme)\<close>.

Like record types, record type schemes may be denoted by record type expressions. They have the
same form, the more part is denoted by the pseudo field name \<open>\<dots>\<close>\index{...@\<open>\<dots>\<close> (field name)} (three-dot symbol). Therefore
the polymorphic type scheme \<open>('a rname_scheme)\<close> can be denoted by the record type expression
@{theory_text[display]
\<open>\<lparr>fname\<^sub>1 :: ftype\<^sub>1, \<dots>, fname\<^sub>n :: ftype\<^sub>n, \<dots> :: 'a\<rparr>\<close>}
and the record type expression
\<open>\<lparr>fname\<^sub>1 :: ftype\<^sub>1, \<dots>, fname\<^sub>n :: ftype\<^sub>n\<rparr>\<close> is simply an abbreviation for
\<open>\<lparr>fname\<^sub>1 :: ftype\<^sub>1, \<dots>, fname\<^sub>n :: ftype\<^sub>n, \<dots> :: unit\<rparr>\<close>.

The polymorphic record type scheme for the record type \<open>recrd\<close> defined above is denoted by
\<open>'a recrd_scheme\<close> or by the record type expression 
\<open>\<lparr>num :: nat, nums :: nat set, nice :: bool, \<dots> :: 'a\<rparr>\<close>.

Record type schemes may be used to define functions which are applicable to a record and all its
extensions, similar to methods in object oriented programming.
\<close>

subsubsection "Extending Record Types"

text \<open>
A record type is extended by instantiating the more part to a ``record fragment type''\index{record!fragment type}\index{type!record fragment $\sim$}. Like a
record type it consists of a sequence of one or more fields, however it cannot be used on its
own, it must always be embedded as more part in another record.

A record type is extended\index{definition!record type extension $\sim$}\index{record type extension} by the definition:
@{theory_text[display]
\<open>record rname = "rtype"
          + efname\<^sub>1 :: "eftype\<^sub>1" \<dots> efname\<^sub>m :: "eftype\<^sub>m"\<close>}
where \<open>rtype\<close> is a previously defined record type. The fields specified by the \<open>efname\<^sub>i\<close> and
\<open>eftype\<^sub>i\<close> comprise the record fragment which is appended after the fields of \<open>rtype\<close>, even if 
(some of) the same field names have already been used for \<open>rtype\<close>. Type \<open>rtype\<close> is called the 
``parent type''\index{parent type}\index{type!parent $\sim$} of type \<open>rname\<close>. A record type which does not extend another record type (has no 
parent type) is called a ``root record type''\index{root record type}\index{type!record $\sim$!root $\sim$}.

If necessary, the field names \<open>efname\<^sub>i\<close> must be qualified by \<open>rname\<close>, whereas the field names of
the parent type \<open>rtype\<close> must be qualified by the name of \<open>rtype\<close>, even if they occur in an
extension of \<open>rtype\<close>.

The record fragment type defined by the extension above may be denoted by the record type
expression \<open>\<lparr>efname\<^sub>1::eftype\<^sub>1, \<dots>, efname\<^sub>m::eftype\<^sub>m\<rparr>\<close>. If \<open>\<lparr>fname\<^sub>1::ftype\<^sub>1, \<dots>, fname\<^sub>n::ftype\<^sub>n\<rparr>\<close>
is an expression for the parent type, the extended record type may be denoted by the type scheme
expression
@{text[display]
\<open>\<lparr>fname\<^sub>1::ftype\<^sub>1, \<dots>, fname\<^sub>n::ftype\<^sub>n, 
   \<dots> ::\<lparr>efname\<^sub>1::eftype\<^sub>1, \<dots>, efname\<^sub>m::eftype\<^sub>m\<rparr>\<rparr>\<close>}
or by the type expression
@{text[display]
\<open>\<lparr>fname\<^sub>1::ftype\<^sub>1, \<dots>, fname\<^sub>n::ftype\<^sub>n, 
   efname\<^sub>1::eftype\<^sub>1, \<dots>, efname\<^sub>m::eftype\<^sub>m\<rparr>\<close>}

The example record type defined above can be extended by
@{theory_text[display]
\<open>record recrd2 = recrd + full :: bool num :: nat\<close>}\index{recrd2 (example type)}
Note that the resulting record type has two fields with name \<open>num\<close> and type \<open>nat\<close>, they must always
be referred by the qualified field names \<open>recrd.num\<close> and \<open>recrd2.num\<close>. A record type expression for
\<open>recrd2\<close> is
@{text[display]
\<open>\<lparr>recrd.num :: nat, nums :: nat set, nice :: bool, 
    full :: bool, recrd2.num :: nat\<rparr>\<close>}
\<close>

subsubsection "Parameterized Record Types"

text \<open>
Like declared types record types may be parameterized\index{record!type!parameterized $\sim$}\index{type!record $\sim$!parameterized $\sim$} (see Section~\ref{theory-terms-types}):
@{theory_text[display]
\<open>record ('name\<^sub>1,\<dots>,'name\<^sub>m) rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots>
                                    fname\<^sub>n :: "ftype\<^sub>n"\<close>}
where the \<open>'name\<^sub>j\<close> are the type parameters. They may occur in the component types \<open>ftype\<^sub>i\<close>, i.e.,
the \<open>ftype\<^sub>i\<close> may be polymorphic (see Section~\ref{theory-terms-types}). As usual, the parentheses
may be omitted if there is only one type parameter.

For a parameterized record type a record type expression may be specified for every possible
instance. As usual, a record type expression with type variables denotes a polymorphic type.

In the record type scheme the parameter for the more part follows all other type parameters.

As an example, a parameterized record type with two type parameters is defined by
@{theory_text[display]
\<open>record ('a, 'b) recrdp = f1 :: 'a f2:: "'a set" f3 :: 'b\<close>}\index{recrdp (example type)}
The most general record type scheme is \<open>('a, 'b, 'c) recrdp_scheme\<close> where \<open>'c\<close> is the parameter
for the more part.

After this definition valid record type expressions are \<open>\<lparr>f1::nat, f2::nat set, f3::bool\<rparr>\<close> which
is equivalent to \<open>(nat, bool) recrdp\<close>, and \<open>\<lparr>f1::bool, f2::bool set, f3::'a\<rparr>\<close> which is equivalent
to \<open>(bool, 'a) recrdp\<close>, but not \<open>\<lparr>f1::nat, f2::bool set, f3::bool\<rparr>\<close>, because here the type
parameter \<open>'a\<close> has been substituted by the two different types \<open>nat\<close> and \<open>bool\<close>.
\<close>

subsection "Record Constructors"
text_raw\<open>\label{holtdefs-record-constr}\<close>

text \<open>
Every record type definition \<^theory_text>\<open>record rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close> defines the
record constructor function
@{theory_text[display]
\<open>make :: ftype\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ftype\<^sub>n \<Rightarrow> rname\<close>}\index{make (constant)}
which constructs values of the record type from values to be used for all fields.
If more than one record type has been defined the name of the constructor function must be
qualified by the record type name as \<open>rname.make\<close>.

For an extended record type defined by \<^theory_text>\<open>record rname2 = rname + efname\<^sub>1 :: "eftype\<^sub>1" \<dots>
efname\<^sub>m :: "eftype\<^sub>m"\<close> the constructor function is
@{theory_text[display]
\<open>make :: ftype\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ftype\<^sub>n \<Rightarrow> eftype\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> eftype\<^sub>m \<Rightarrow> rname2\<close>}
It takes values for \<^emph>\<open>all\<close> fields and constructs a full record of type \<open>rname2\<close>.

Every definition for a (root or extended) record type \<open>rname\<close> also defines the constructor function
@{theory_text[display]
\<open>extend :: rname \<Rightarrow> 'a \<Rightarrow> ('a rname_scheme)\<close>}\index{extend (constant)}
It replaces the more part of a record of type \<open>rname\<close> (which is the unit value) by a value of an
arbitrary type \<open>'a\<close>. The result will only be a proper record if \<open>'a\<close> is a record fragment type for
a defined extension of \<open>rname\<close>.

Additionally the definition of the extended record type \<open>rname2\<close> defines the constructor function
@{theory_text[display]
\<open>fields :: `ftype\<^sub>n\<^sub>+\<^sub>1` \<Rightarrow> \<dots> \<Rightarrow> ftype\<^sub>m \<Rightarrow>
       \<lparr>`fname\<^sub>n\<^sub>+\<^sub>1`::`ftype\<^sub>n\<^sub>+\<^sub>1`, \<dots>, fname\<^sub>m :: ftype\<^sub>m\<rparr>\<close>}\index{fields (constant)}
for the record fragment used as the more part of \<open>rname\<close>. For a root record type \<open>fields\<close> is
the same function as \<open>make\<close>.
\<close>

subsubsection "Constructing Values"

text\<open>
As for a datatype every record constructor function is assumed to be injective, thus their result
values differ if atleast one argument value differs. This implies that the set of all values of the
constructor function \<open>make\<close> is equivalent to the set of all tuples of values of
the field types, which is equivalent to the set of all possible values of the record type \<open>rname\<close>.
Thus every value of \<open>rname\<close> may be denoted by a term
@{text[display]
\<open>rname.make term\<^sub>1 \<dots> term\<^sub>n\<close>}
where each \<open>term\<^sub>i\<close> is of type  \<open>ftype\<^sub>i\<close> and specifies the value for field \<open>i\<close>.

There is an alternative Syntax for applications of record constructors. The record expression\index{record!expression}
@{text[display]
\<open>\<lparr>fname\<^sub>1 = term\<^sub>1, \<dots>, fname\<^sub>n = term\<^sub>n\<rparr>\<close>}
denotes the same record value as the constructor application
above. If the name \<open>fname\<^sub>1\<close> of the first field has been used in more than one record type it must be
qualified. The record schema expression\index{record!schema expression}
@{text[display]
\<open>\<lparr>fname\<^sub>1 = term\<^sub>1, \<dots>, fname\<^sub>n = term\<^sub>n, \<dots>= mterm\<rparr>\<close>}
denotes a value for the record type scheme where \<open>mterm\<close> denotes the value for the more part.

Values of the record fragment type defined for \<open>rname2\<close> are constructed by the application
@{text[display]
\<open>rname2.fields term\<^sub>1 \<dots> term\<^sub>m\<close>}
or equivalently by the record fragment expression \<open>\<lparr>efname\<^sub>1= term\<^sub>1, \<dots>, efname\<^sub>m = term\<^sub>m\<rparr>\<close>.

Values of the extended record type \<open>rname2\<close> itself can be constructed from a value \<open>r\<close>
of type \<open>rname\<close> by \<open>rname.extend r (rname2.fields term\<^sub>1 \<dots> term\<^sub>m)\<close> or
\<open>rname.extend r \<lparr>rname2.efname\<^sub>1= term\<^sub>1, \<dots>, efname\<^sub>m = term\<^sub>m\<rparr>\<close>. 

Values of type \<open>recrd\<close> as defined above are denoted by terms such as \<open>recrd.make 2 {5,7} True\<close>
or the equivalent record expression \<open>\<lparr>num = 2, nums = {5,7}, nice = True\<rparr>\<close> or the record scheme
expression \<open>\<lparr>num = 2, nums = {5,7}, nice = True, \<dots> = ()\<rparr>\<close>. Values of the extension \<open>recrd2\<close> as
defined above are denoted by terms such as \<open>recrd2.make 2 {5,7} True True 42\<close> or
\<open>\<lparr>recrd.num = 2, nums = {5,7}, nice = True, full= True, recrd2.num= 42\<rparr>\<close> or
\<open>\<lparr>recrd.num = 2, nums = {5,7}, nice = True, \<dots>= \<lparr>full= True, recrd2.num= 42\<rparr>\<rparr>\<close>.
\<close>

subsection "Record Destructors"
text_raw\<open>\label{holtdefs-record-destr}\<close>

text \<open>
The only record destructors available are selectors which correspond to the field names.
Every record type definition \<^theory_text>\<open>record rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close> defines the
record selector functions
@{theory_text[display]
\<open>fname\<^sub>1 :: 'a rname_scheme \<Rightarrow> ftype\<^sub>1
 \<dots>
fname\<^sub>n :: 'a rname_scheme \<Rightarrow> ftype\<^sub>n\<close>}
Note that instead of \<open>rname\<close> their argument type is the record type scheme \<open>'a rname_scheme\<close>. Thus
a record selector function for a field is polymorphic and may also be applied to every extended
record to return the field value. However, to make a field name unique, it must be qualified
by the name of the record type where it has been introduced.

Additionally a record type definition always defines the selector named \<open>more\<close> for the more
part.

If \<open>r\<close> is a variable of type \<open>recrd\<close> as defined above, the term \<open>nums r\<close> selects the value of the
second field. The same works if \<open>r\<close> has the extended type \<open>recrd2\<close>. The term \<open>recrd.more r\<close>
selects the value of the more part which is the unit value if \<open>r\<close> has type \<open>recrd\<close> and the extension
fragment if \<open>r\<close> has type \<open>recrd2\<close>.

A field selector cannot be applied directly to a record fragment. The fields of the fragment can
only be selected if the fragment is embedded in the extended record.
\<close>

subsection "Record Updates"
text_raw\<open>\label{holtdefs-record-update}\<close>

text \<open>
In addition to the constructor and selector functions a record type definition \<^theory_text>\<open>record rname = 
fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close> defines the record update functions\index{record!update function}\index{function!record update $\sim$}
@{theory_text[display]
\<open>fname\<^sub>1_update :: (ftype\<^sub>1 \<Rightarrow> ftype\<^sub>1) \<Rightarrow> 'a rname_scheme \<Rightarrow> 'a rname_scheme
 \<dots>
fname\<^sub>n_update :: (ftype\<^sub>n \<Rightarrow> ftype\<^sub>n) \<Rightarrow> 'a rname_scheme \<Rightarrow> 'a rname_scheme\<close>}\index{update@$\_$update (constant name suffix)}
Each record update function \<open>fname\<^sub>i_update\<close> takes as argument an update function for values of
type \<open>ftype\<^sub>i\<close> (which maps an old value to a new value) and a record value. It returns
the record where the value of field \<open>fname\<^sub>i\<close> is the result of applying the update function to its
old value and the values of all other fields are unchanged.

Like the selector functions the update functions are defined for the polymorphic record type scheme
and can thus be also applied to all extended records.

A field may be set to a specific value \<open>term\<close> without regarding the old value by using the term
\<open>fname\<^sub>i_update (\<lambda>_.term) r\<close> where a constant function (see Section~\ref{theory-terms-lambda}) is
used as update function for the field value. For record update applications of this form the
alternative syntax\index{syntax!alternative $\sim$!for record updates}
@{text[display]
\<open>r\<lparr> fname\<^sub>i := term \<rparr>\<close>}
is available. Further notation for repeated updates is also available: \<open>r\<lparr>x := a\<rparr>\<lparr>y := b\<rparr>\<lparr>z := c\<rparr>\<close>
may be written
@{text[display]
\<open>r\<lparr>x := a, y := b, z := c\<rparr>\<close>}
Note that the former term is equivalent to \<open>z_update (\<lambda>_.c) (y_update (\<lambda>_.b) (x_update (\<lambda>_.a) r))\<close>,
so the fields are actually set in the order in which they occur in the alternative notation from
left to right.
\<close>

subsection "Record Rules"
text_raw\<open>\label{holtdefs-record-rules}\<close>

text\<open>
A record type definition also introduces a number of named facts about the constructors, selectors
and update functions. All fact names belong to the namespace of the record definition. The facts
are named automatically in the same way for all record types, therefore the fact names must always
be qualified by prefixing the record type name.

Several rules are configured for automatic application, e.g., they are added to the simpset for
automatic application by the simplifier (see Section~\ref{methods-simp-simp}). Other rules must
be explicitly used by referring them by their name. 

Only some basic rules are described here, for more information refer to 
\<^cite>\<open>"Section 11.6 on records" in "isar-ref"\<close>.
\<close>

subsubsection "Simplifier Rules"

text\<open>
The rules for injectivity of the record constructor have the form
@{text[display]
\<open>(\<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>n = ?x\<^sub>n, \<dots>= ?x\<rparr> = 
  \<lparr>fname\<^sub>1 = ?y\<^sub>1, \<dots>, fname\<^sub>n = ?y\<^sub>n, \<dots>= ?y\<rparr>)
= (?x\<^sub>1 = ?y\<^sub>1 \<and> \<dots> \<and> ?x\<^sub>n = ?y\<^sub>n \<and> ?x = ?y)\<close>}
and are named \<open>rname.iffs\<close>\index{iffs@.iffs (fact name suffix)} for the record type
\<open>rname\<close>.

Other rules added by a record definition to the simpset process terms where selectors or update
functions are applied to constructed record values. They have the form of equations
@{text[display]
\<open>fname\<^sub>i \<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>n = ?x\<^sub>n\<rparr> = ?x\<^sub>i
fname\<^sub>i_update ?f \<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>n = ?x\<^sub>n\<rparr> = 
   \<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>i = ?f ?x\<^sub>i, \<dots>, fname\<^sub>n = ?x\<^sub>n\<rparr>\<close>}
The set of all these rules is named \<open>rname.simps\<close>\index{simps@.simps (fact name suffix)} for the record type \<open>rname\<close>.

Additional internal simplifier rules process selectors applied to updated records such as
@{text[display]
\<open>fname\<^sub>i (fname\<^sub>i_update ?f ?r) = ?f (fname\<^sub>i ?r)
fname\<^sub>i (fname\<^sub>j_update ?f ?r) = fname\<^sub>i ?r\<close>}
where \<open>i\<noteq>j\<close>.
\<close>

subsubsection "Constructor Rules"

text\<open>
Additional rules provide definitional equations for the constructors of the defined record type,
such as 
@{text[display]
\<open>rname.make x\<^sub>1 \<dots> x\<^sub>n = \<lparr>fname\<^sub>1 = x\<^sub>1, \<dots>, fname\<^sub>n = x\<^sub>n\<rparr>\<close>}\index{make@.make (fact name suffix)}
Every rule provides a representation of a constructor application as a record expression.
The set of these rules is named \<open>rname.defs\<close>\index{defs@.defs (fact name suffix)} for the record type \<open>rname\<close>. It is not added to the
simpset, the rules must be explicitly applied by adding them to the simplifier method when needed
(as described in Section~\ref{methods-simp-config}).

The simplifier rules are mainly defined for record expressions. To apply them to record
terms specified by the constructor functions the constructor rules must be used to convert the
terms to record expressions.
\<close>

subsubsection "Case Rules"

text\<open>
Every definition for a record type \<open>rname\<close> introduces case rules
(see Section~\ref{case-reasoning-rules}) of the form
@{text[display]
\<open>rname.cases:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>n. ?y = \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n\<rparr> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P
rname.cases_scheme:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>n m. ?y = \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n, \<dots>=m\<rparr> \<Longrightarrow> ?P\<rbrakk>
  \<Longrightarrow> ?P\<close>}\index{cases@.cases (fact name suffix)}\index{cases-scheme@.cases$\_$scheme (fact name suffix)}
They are valid because the record expressions cover all possibilities of constructing a value
\<open>?y\<close> of the record type or record scheme type, respectively. 

Both rules are associated with the record type for use by the \<^theory_text>\<open>cases\<close> method
(see Section~\ref{case-reasoning-cases}), the method automatically selects the most sensible of
them. Therefore the application of the method
@{theory_text[display]
\<open>cases "term"\<close>}
where \<open>term\<close> is a record of type \<open>rname\<close> replaces an arbitrary goal by a goal where \<open>term\<close> is
set equal to a record constructed from explicit field values \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> and possibly a more part. 

The name used for the named context created by the \<^theory_text>\<open>cases\<close> method is ``fields''\index{fields (case name)}.
Therefore a structured proof using case based reasoning for a \<open>term\<close> of a record type \<open>rname\<close>
has the form
@{theory_text[display]
\<open>proof (cases "term")
  case (fields x\<^sub>1 \<dots> x\<^sub>n) \<dots> show ?thesis \<proof>
qed\<close>}
The names \<open>x\<^sub>i\<close> of the locally fixed variables can be freely selected, they denote the field
values of the record.

The main purpose of applying the case rules is to provide a record expression for a record term
which is not specified as such or by a constructor function, such as a variable of a record type.
Providing the record expression makes the simplifier rules applicable, therefore a proof for
a record often consists of an application of the \<^theory_text>\<open>cases\<close> method followed by an application of
the \<^theory_text>\<open>simp\<close> method.
\<close>

subsubsection "Induction Rule"

text\<open>
Every definition for a record type \<open>rname\<close> introduces induction rules
(see Section~\ref{case-induction-rules}) of the form
@{text[display]
\<open>rname.induct:
  (\<And>x\<^sub>1 \<dots> x\<^sub>n. ?P \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n\<rparr>) \<Longrightarrow> ?P ?a
rname.induct_scheme:
  (\<And>x\<^sub>1 \<dots> x\<^sub>n m. ?P \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n, \<dots>=m\<rparr>) \<Longrightarrow> ?P ?a\<close>}\index{induct@.induct (fact name suffix)}
Like the case rule it is valid because the record expressions 
cover all possibilities of constructing a value \<open>?a\<close> of the record type \<open>rname\<close>.

The rules are associated with the record type for use by the methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close>
(see Section~\ref{case-induction-naming}), the methods automatically select the most sensible of
them. Therefore the application of the method
@{theory_text[display]
\<open>induction x\<close>}
where \<open>x\<close> is a variable of type \<open>rname\<close> replaces a goal by a goal which uses a record expression
in the place of \<open>x\<close>.

As for the case rule and the \<^theory_text>\<open>cases\<close> method, the names used for the named contexts created by the 
methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close> are ``fields''\index{fields (case name)}. Therefore a structured
proof using induction for a variable \<open>x\<close> of record type \<open>rname\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (fields x\<^sub>1 \<dots> x\<^sub>n) \<dots> show ?case \<proof>
qed\<close>}

As an example, the induction rules for the record type \<open>recrd\<close> defined in 
Section~\ref{holtdefs-record-def} are
@{text[display]
\<open>recrd.induct:
  (\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. ?P \<lparr>num=x\<^sub>1, nums=x\<^sub>2, nice=x\<^sub>3\<rparr>) \<Longrightarrow> ?P ?a
recrd.induct_scheme:
  (\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3 m. ?P \<lparr>num=x\<^sub>1, nums=x\<^sub>2, nice=x\<^sub>3, \<dots>=m\<rparr>) \<Longrightarrow> ?P ?a\<close>}
By applying the method \<open>(induction x)\<close> the goal \<open>(num x) = y\<close> is replaced by
the goal \<open>\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. (num \<lparr>num = x\<^sub>1, nums = x\<^sub>2, nice = x\<^sub>3\<rparr>) = y\<close>.

Like the cases methods a transformation of this kind may enable the application of the simplifier
methods.
\<close>

subsection "Records as Bounded Natural Functors"
text_raw\<open>\label{holtdefs-record-bnf}\<close>

text\<open>
As described in Section~\ref{holtdefs-record-def} a record type is mainly equivalent to the tuple
type for all fields. Seen as type constructors, tuple types are BNFs (see
Section~\ref{holbasic-bnf-bounded}). Due to composability of BNFs this implies that a (polymorphic)
record type is a bounded natural functor as soon as all (polymorphic) field types are BNFs.
However, HOL does not register record types as BNFs automatically, this must be done manually.
\<close>

subsubsection "Record Type Constructors"

text\<open>
The actual type constructor introduced by a record definition \<^theory_text>\<open>record ('a\<^sub>1,\<dots>,'a\<^sub>m) rname = \<dots>\<close> is
named \<open>rname_ext\<close>\index{ext@$\_$ext (type name suffix)}. The record type scheme name \<open>rname_scheme\<close>
is a synonym for it, whereas \<open>('a\<^sub>1,\<dots>,'a\<^sub>m) rname\<close> is a synonym for \<open>('a\<^sub>1,\<dots>,'a\<^sub>m, unit) rname_ext\<close> (see
Section~\ref{holtdefs-record-def}).

The type constructor \<open>rname_ext\<close> is internally defined as a type copy (see
Section~\ref{holtdefs-sub-copies}) of a tuple type with all record field types as components. This
tuple type is constructed from pairs (see Section~\ref{holbasic-tuples}) in a balanced way, so that
the number of steps to access a component using the selectors \<open>fst\<close> and \<open>snd\<close> (see
Section~\ref{holbasic-tuples}) is always logarithmic in the number of components.

Using a type copy implies that different records with the same component types are different,
although isomorphic. It also makes it possible to define the field selector (see
Section~\ref{holtdefs-record-destr}) and update (see Section~\ref{holtdefs-record-update})
functions specifically for each record type.
\<close>

subsubsection "Registering Record Types as BNF"

text\<open>
As described in Section~\ref{holbasic-bnf-register} the type constructor \<open>prod\<close> for pairs is a BNF.
Due to composability of BNFs this is also true for every tuple type and the BNF property can be
lifted to the type copy for the record scheme from the underlying tuple type for the components
using the command \<^theory_text>\<open>copy_bnf\<close> (see Section~\ref{holbasic-quotlift-bnf}). As described in
Section~\ref{holtdefs-sub-bnf} the type copy must before be registered as quotient using the
command \<^theory_text>\<open>setup_lifting\<close>.

Together, a record type defined by 
\<open>record ('a\<^sub>1,\<dots>,'a\<^sub>m) rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close> is
registered as BNF by the command sequence
@{theory_text[display]
\<open>setup_lifting type_definition_rname_ext
copy_bnf ('a\<^sub>1,\<dots>,'a\<^sub>m, 'more) rname_ext\<close>}
Note the additional type parameter \<open>'more\<close> for the more part of the record type scheme. Its name
may be arbitrarily selected, it must only be distinct from the \<open>'a\<^sub>1,\<dots>,'a\<^sub>m\<close>.

If a polymorphic component type \<open>ftype\<^sub>i\<close> is not a registered BNF it is treated as BNF with all type
parameters as dead (see Section~\ref{holbasic-bnf-natural}). Every type parameter \<open>'a\<^sub>j\<close> of the
record type occurring on a dead parameter position in an \<open>ftype\<^sub>i\<close> is registered as dead by the
\<^theory_text>\<open>copy_bnf\<close> command. Since the more part always consists directly of the corresponding type
parameter, that parameter is always registered as live.

After registering the record type scheme \<open>rname_ext\<close> as BNF the record type \<open>('a\<^sub>1,\<dots>,'a\<^sub>m) rname\<close> is
immediately recognised as BNF because it is a synonym for the instantiation
\<open>('a\<^sub>1,\<dots>,'a\<^sub>m, unit) rname_ext\<close>. Extensions of \<open>rname\<close> (see Section~\ref{holtdefs-record-def}) are
usually not recognised as BNF, because they instantiate the more part differently, for them the
\<^theory_text>\<open>copy_bnf\<close> command must be applied separately to the extended type scheme.

The polymorphic example record type \<open>('a, 'b) recrdp\<close> defined in Section~\ref{holtdefs-record-def}
is registered as (quotient and) BNF by
@{theory_text[display]
\<open>setup_lifting type_definition_recrdp_ext
copy_bnf ('a, 'b, 'more) recrdp_ext\<close>}
The type parameters \<open>'b\<close> and \<open>'more\<close> are registered as live, whereas \<open>'a\<close> is registered as dead
because the second field has type \<open>'a set\<close> which is not a BNF.
\<close>

subsubsection "Subtypes and Quotients of Record Types"

text\<open>
Defining a subtype (see Section~\ref{holtdefs-sub}) of a record type \<open>rname\<close> is straightforward. If
this subtype shall be registered as quotient using \<^theory_text>\<open>setup_lifting\<close> the record type should be
registered as BNF before, so that the relator \<open>rel_rname_ext\<close> is defined for it and known to HOL.
Only then full transfer support is available for the subtype and no warning is issued by
\<^theory_text>\<open>setup_lifting\<close> (see Section~\ref{holbasic-quotlift-setup}).

If, however, the record type is registered as BNF with dead parameters (see above), the relator
cannot be used by \<^theory_text>\<open>setup_lifting\<close>. Then \<^theory_text>\<open>setup_lifting\<close> will still warn about not finding the
relator, although it has been defined by \<^theory_text>\<open>copy_bnf\<close>.

Note that due to the type parameter for the more part the record type scheme is always
polymorphic, even if the defined record type has no type parameters. Therefore the \<^theory_text>\<open>setup_lifting\<close>
command always expects the relator for \<open>rel_rname_ext\<close> for subtypes of arbitrary record types.

Since a quotient type definition includes the \<^theory_text>\<open>setup_lifting\<close> command (see
Section~\ref{holtdefs-quot-quot}) a record type \<open>rname\<close> should be registered as BNF
before a quotient type is defined for it. Additionally, the mapper \<open>map_rname_ext\<close>, introduced when
registering \<open>rname\<close> as BNF should be registered as functor (see Section~\ref{holbasic-bnf-register})
so that the \<^theory_text>\<open>quotient_type\<close> command does not signal a warning about an undefined map function.

The polymorphic example record type \<open>('a, 'b) recrdp\<close> has a dead type parameter when registered
as BNF (see above), therefore subtypes and quotient types for it cannot provide full transfer
support.\<close>

end
