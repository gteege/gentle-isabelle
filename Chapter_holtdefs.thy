theory Chapter_holtdefs
  imports Chapter_holbasic
begin

chapter "Isabelle HOL Type Definitions"
text_raw\<open>\label{holtdefs}\<close>

text \<open>
This chapter introduces mechanisms defined by HOL which are used to populate HOL with many of its
mathematical objects and functions and which can also be used to extend HOL to additional kinds of
objects. Basically these mechanisms support the definition of new types \cbstart in outer syntax\cbend.
\<close>

section "Algebraic Types"
text_raw\<open>\label{holtdefs-data}\<close>

text\<open>
Roughly an algebraic type is equivalent to a union of tuples with support for recursion, which
allows nested tuples. In this way most data types used in programming languages can be covered, such
as records, unions, enumerations, and pointer structures. Therefore HOL also uses the notion
``datatype'' for algebraic types.
\<close>

subsection "Definition of Algebraic Types"
text_raw\<open>\label{holtdefs-data-def}\<close>

text\<open>
Basically, an algebraic type is defined in the form
@{theory_text[display]
\<open>datatype name = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>}
where \<open>name\<close> is the name of the new algebraic type and every alternative \<open>alt\<^sub>i\<close> is a ``constructor
specification'' of the form
@{theory_text[display]
\<open>cname\<^sub>i "type\<^sub>i\<^sub>1" \<dots> "type\<^sub>i\<^sub>k\<^sub>i"\<close>}
The \<open>cname\<^sub>i\<close> are names and the \<open>type\<^sub>i\<^sub>j\<close> are types.
The types are specified in inner syntax and must be quoted, if they are not a single type name. All 
other parts belong to the outer syntax. 

Recursion is supported for the types, i.e., the name \<open>name\<close> of the defined type may occur in the 
type specifications \<open>type\<^sub>i\<^sub>j\<close>. However, there must be atleast one constructor specification which
is not recursive, otherwise the definition does not ``terminate''. Isabelle checks this condition
and signals an error if it is not satisfied.

As a convention, capitalized names are used in HOL for the \<open>cname\<^sub>i\<close>.

An example for a datatype definition with two constructor specifications is
@{theory_text[display]
\<open>datatype coord = 
  Dim2 nat nat
| Dim3 nat nat nat\<close>}
Its value set is equivalent to the union of pairs and triples of natural numbers.

An example for a recursive datatype definition with two constructor specifications is
@{theory_text[display]
\<open>datatype tree = 
  Leaf nat
| Tree nat tree tree\<close>}
Its value set is equivalent to the set of all binary trees with a natural number in every node.

Like declared types algebraic types may be parameterized (see Section~\ref{basic-theory-terms}):
@{theory_text[display]
\<open>datatype ('name\<^sub>1,\<dots>,'name\<^sub>m) name = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>}
where the \<open>'name\<^sub>i\<close> are the type parameters. They may occur in the type specifications \<open>type\<^sub>i\<^sub>j\<close>, i.e.,
the \<open>type\<^sub>i\<^sub>j\<close> may be polymorphic (see Section~\ref{basic-theory-terms}). As usual, the parentheses
may be omitted if there is only one type parameter.

An example for a parameterized datatype definition with one type parameter is
@{theory_text[display]
\<open>datatype 'a coordx = 
  Dim2 'a 'a
| Dim3 'a 'a 'a\<close>}
Its value set is equivalent to the union of pairs and triples of values of the type parameter. The
type \<open>coord\<close> is equivalent to the type \<open>nat coordx\<close>. The type \<open>real coordx\<close> is equivalent to the
union of pairs and triples of values of type \<open>real\<close> of the real numbers.
\<close>

subsection "Constructors"
text_raw\<open>\label{holtdefs-data-constr}\<close>

text\<open>
Every \<open>cname\<^sub>i\<close> is used by the definition to introduce a ``(value) constructor function'',
i.e., a constant
@{text[display]
\<open>cname\<^sub>i :: "type\<^sub>i\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> type\<^sub>i\<^sub>k\<^sub>i \<Rightarrow> name"\<close>}
which is a function with \<open>ki\<close> arguments mapping their arguments to values of the new type \<open>name\<close>.

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
\<open>cname\<^sub>i\<close> is equivalent to the tuples of the value sets of \<open>type\<^sub>i\<^sub>1 \<dots> type\<^sub>i\<^sub>k\<^sub>i\<close>: for every
tuple of arguments there is a constructed value and vice versa. Note, however, that as usual the
values of the new type are distinct from the values of all other types, in particular, they are
distinct from the argument tuples.

Moreover the result values of different constructor functions are also assumed to be different.
Together the set of all values of the defined type is equivalent to the (disjoint) union of the
cartesian products of all constructor argument types. Moreover, every value of the type may be 
denoted by a term
@{text[display]
\<open>cname\<^sub>i term\<^sub>1 \<dots> term\<^sub>k\<^sub>i\<close>}
where each \<open>term\<^sub>j\<close> is of type  \<open>type\<^sub>i\<^sub>j\<close> and specifies an argument for the constructor function
application.

Together, datatypes have what is called ``free constructors'' in Isabelle: the constructors are
injective, disjoint, and exhaustive (they cover all values of the type).

Values of type \<open>coord\<close> as defined above are denoted by terms such as \<open>Dim2 0 1\<close> and \<open>Dim3 10 5 21\<close>.
\<close>

subsubsection "Constant Constructors and Enumeration Types"

text\<open>
A constructor specification may consist of a single constructor name \<open>cname\<^sub>i\<close>, then the constructor 
function has no arguments and always constructs the same single value. The constructor is equivalent 
to a constant of type \<open>name\<close>. As a consequence an ``enumeration type'' can be defined in the form
@{theory_text[display]
\<open>datatype three = Zero | One | Two\<close>}
This type \<open>three\<close> has three values denoted by \<open>Zero\<close>, \<open>One\<close>, and \<open>Two\<close>.
\<close>

subsubsection "Types with a Single Constructor"

text\<open>
If a datatype definition consists of a single constructor specification its value set is equivalent 
to the constructor argument tuples. The corresponding tuples have a separate component for every
constructor argument type. As a consequence a ``record type'' can be defined in the form 
@{theory_text[display]
\<open>datatype recrd = MkRecrd nat "nat set" bool\<close>}
Its values are equivalent to triples where the first component is a natural number, the second
component is a set of natural numbers, and the third component is a boolean value. An example value
is denoted by \<open>MkRecrd 5 {1,2,3} True\<close>.

Since there must be atleast one nonrecursive constructor specification, definitions with a single
constructor specification cannot be recursive.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtdefs-data-destr}\<close>

text\<open>
Since constructor functions are injective it is possible to determine for every value of the defined
type the value of each constructor argument used to construct it. Corresponding mechanisms are 
called ``destructors'', there are three different types of them.
\<close>

subsubsection "Selectors"

text\<open>
The most immediate form of a destructor is a selector function. For the constructor argument specified
by \<open>type\<^sub>i\<^sub>j\<close> the selector function is a function of type \<open>name \<Rightarrow> type\<^sub>i\<^sub>j\<close>. For every value constructed
by \<open>cname\<^sub>i term\<^sub>1 \<dots> term\<^sub>k\<^sub>i\<close> it returns the value denoted by \<open>term\<^sub>j\<close>.

The names of selector functions must be specified explicitly. This is done using the extended form
of a constructor specification
@{theory_text[display]
\<open>cname\<^sub>i (sname\<^sub>i\<^sub>1 : "type\<^sub>i\<^sub>1") \<dots> (sname\<^sub>i\<^sub>k\<^sub>i : "type\<^sub>i\<^sub>k\<^sub>i")\<close>}
where the \<open>sname\<^sub>i\<^sub>j\<close> are the names used for the corresponding selector functions. Selector names
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
total, like all functions in Isabelle, but it is underspecified (see Section~\ref{basic-theory-terms}).
It maps values constructed by other constructors to a unique value of its result type, even if that
other constructor has no argument of this type. However, no information is available about that value.

For the type \<open>coord\<close> the selector function \<open>z :: coord \<Rightarrow> nat\<close> is also applicable to two-dimensional
coordinates, however, the values it returns for them is not specified.

Such selector values are called ``default selector values''. They may be specified in the extended
form of a datatype definition 
@{theory_text[display]
\<open>datatype name = alt\<^sub>1 | \<dots> | alt\<^sub>n
where "prop\<^sub>1" | \<dots> | "prop\<^sub>m"\<close>}
where every \<open>prop\<^sub>p\<close> is a proposition of the form
@{text[display]
\<open>sname\<^sub>i\<^sub>j (cname\<^sub>q var\<^sub>1 \<dots> var\<^sub>k\<^sub>q) = term\<^sub>p\<close>}
and specifies \<open>term\<^sub>p\<close> as the default value of selector \<open>sname\<^sub>i\<^sub>j\<close> for values constructed by \<open>cname\<^sub>q\<close>.

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
constructor has been used to construct the value. This is supported by discriminator functions.
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
Additionally to using discriminators and selectors HOL supports \<open>case\<close> terms. A \<open>case\<close>
term specifies depending on a datatype value a separate term variant for every constructor of the
datatype. In these variants the constructor arguments are available as bound variables. 

A \<open>case\<close> term for a datatype \<open>name\<close> defined as in Section~\ref{holtdefs-data-def} has the form
@{text[display]
\<open>case term of 
  cname\<^sub>1 var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1 \<Rightarrow> term\<^sub>1 
| \<dots>
| cname\<^sub>n var\<^sub>n\<^sub>1 \<dots> var\<^sub>n\<^sub>k\<^sub>n \<Rightarrow> term\<^sub>n\<close>}
where \<open>term\<close> is of type \<open>name\<close> and the \<open>term\<^sub>i\<close> have an arbitrary but common type which is also the
type of the \<open>case\<close> term. In the alternative for constructor \<open>cname\<^sub>i\<close> the \<open>var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1\<close> must be 
distinct variables, they are bound to the constructor arguments and may be used in \<open>term\<^sub>i\<close> to access
them. The value of \<open>var\<^sub>i\<^sub>j\<close> is the same as the value selected by \<open>sname\<^sub>i\<^sub>j term\<close>.

Actually, a \<open>case\<close> term is only an alternative syntax for the function application term
@{text[display]
\<open>case_name 
  (\<lambda> var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1. term\<^sub>1)
  \<dots>
  (\<lambda> var\<^sub>n\<^sub>1 \<dots> var\<^sub>n\<^sub>k\<^sub>n. term\<^sub>n)
  term\<close>}
Here \<open>case_name\<close> is the ``case combinator'' function for the datatype \<open>name\<close>. It takes as arguments
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
Section~\ref{basic-proof-let}). The statement 
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
As described in Section~\ref{holtdefs-data-constr} every datatype value can be thought of being
equivalent to a tuple of constructor argument values, so in some sense the constructor argument
values are ``contained'' in the datatype value. If an algebraic type has type parameters, these may
occur as constructor argument types or as parts thereof. In this sense every datatype value is a
``container'' of a certain number of values of every type parameter.

As an example, every value of the polymorphic datatype \<open>'a coordx\<close> defined in
Section~\ref{holtdefs-data-def} contains two or three values of the type parameter \<open>'a\<close>.
\<close>

subsubsection "Retrieving Contained Values"

text\<open>
More generally, a type constructor \<open>name\<close> is called a ``bounded natural functor'' (BNF), if it has
for every type parameter \<open>'p\<^sub>i\<close> a function \<open>('p\<^sub>1,\<dots>,'p\<^sub>m) name \<Rightarrow> 'p\<^sub>i set\<close> which returns for every
value of type \<open>('p\<^sub>1,\<dots>,'p\<^sub>m) name\<close> the set of contained values of type \<open>'p\<^sub>i\<close>, and if all these sets
are ``bounded'', i.e. their maximal size is only determined by \<open>name\<close> and not by the actual types
substituted for the type parameters.

As an example, values of type \<open>'a coordx\<close> contain maximally
\<open>3\<close> values of type \<open>'a\<close>, irrespective whether \<open>'a\<close> is substituted by type \<open>bool\<close>, where there are
only two possible values, or by type \<open>nat\<close>, where there are infinitely many possible values. For a
recursive datatype the set of contained values is often not bound by a number, instead it is bound
to be finite, even if the actual type argument has inifinitely many values.

Every definition
@{theory_text[display]
\<open>datatype ('p\<^sub>1,\<dots>,'p\<^sub>m) name = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>}
of a parameterized datatype with type parameters \<open>'p\<^sub>1,\<dots>,'p\<^sub>m\<close> introduces for every type parameter
\<open>'p\<^sub>i\<close> this ``set function'' as
@{text[display]
\<open>seti_name :: "('p\<^sub>1,\<dots>,'p\<^sub>m) name \<Rightarrow> 'p\<^sub>i set"\<close>}
If \<open>m = 1\<close> the single set function is named \<open>set_name\<close>, if \<open>m = 2\<close> the two set functions are named
\<open>set1_name\<close> and \<open>set2_name\<close>.

For the datatype \<open>coordx\<close> the only set function is \<open>set_coordx\<close>. It maps every value of a type
\<open>t coordx\<close> to the set of either two or three coordinate values of type \<open>t\<close>.
\<close>

subsubsection "Replacing Contained Values"

text\<open>
Moreover, for a bounded natural functor it must be possible to replace the contained values
``in-place'' without modifying any other parts of the container value. Contained values are replaced
by applying a function to them. This property can be modeled by a single function called a ``map
function''. It takes as arguments one function \<open>f\<^sub>i\<close> for every type parameter \<open>'p\<^sub>i\<close> and returns a
function on the container values which replaces every contained value \<open>x\<close> of type \<open>'p\<^sub>i\<close> by \<open>f\<^sub>i x\<close>.

Every datatype definition as above introduces the map function as
@{text[display]
\<open>map_name :: "('p\<^sub>1 \<Rightarrow> 'q\<^sub>1) \<Rightarrow> \<dots> \<Rightarrow> ('p\<^sub>m \<Rightarrow> 'q\<^sub>m)
   \<Rightarrow> ('p\<^sub>1,\<dots>,'p\<^sub>m) name \<Rightarrow> ('q\<^sub>1,\<dots>,'q\<^sub>m) name"\<close>}
It takes as arguments \<open>m\<close> functions \<open>f\<^sub>1, \<dots>, f\<^sub>m\<close> and a datatype value.
Every \<open>f\<^sub>i\<close> may map its arguments of type \<open>'p\<^sub>i\<close> to values of the same type or of a different type
\<open>'q\<^sub>i\<close>. In the latter case also the resulting datatype value is of a different type (a different
instance of the same parameterized datatype).

An alternative way of understanding \<open>map_name\<close> is that the partial application (see
Section~\ref{basic-theory-terms}) \<open>map_name f\<^sub>1 \<dots> f\<^sub>m\<close> ``lifts'' the \<open>m\<close> functions to a
function between instances of type \<open>('p\<^sub>1,\<dots>,'p\<^sub>m) name\<close> and \<open>('q\<^sub>1,\<dots>,'q\<^sub>m) name\<close>. In particular, if
\<open>m=1\<close> then \<open>map_name\<close> lifts every function \<open>f :: t\<^sub>1 \<Rightarrow> t\<^sub>2\<close> to the function \<open>(map_name f) :: t\<^sub>1 name
\<Rightarrow> t\<^sub>2 name\<close>.

The function \<open>map_coordx\<close> has type \<open>('p \<Rightarrow> 'q) \<Rightarrow> 'p coordx \<Rightarrow> 'q coordx\<close>. For instance, if
\<open>f :: real \<Rightarrow> nat\<close> is the function that rounds every real number to the next natural number, the
application \<open>map_coordx f cv\<close> replaces the real coordinates in \<open>cv\<close> of type \<open>real coordx\<close> by
rounded natural coordinates, resulting in a value of type \<open>nat coordx\<close>.

In general a type constructor with such a map function is called a ``functor''. It does not only
support constructing values from values of the parameter types, but also functions from functions
on the parameter types.
\<close>

subsubsection "Constructing Predicates and Relations"

text\<open>
A bounded natural functor can use the sets of contained values returned by the set functions to
lift predicates and relations (see Section~\ref{holbasic-pred}) in a similar way from contained
values to container values. This is modeled by a ``predicator function'' and a ``relator function''.

For a datatype definition as above the predicator function is provided as
@{text[display]
\<open>pred_name :: "('p\<^sub>1 \<Rightarrow> bool) \<Rightarrow> \<dots> \<Rightarrow> ('p\<^sub>m \<Rightarrow> bool)
    \<Rightarrow> ('p\<^sub>1,\<dots>,'p\<^sub>m) name \<Rightarrow> bool"\<close>}
It takes as arguments \<open>m\<close> unary predicates \<open>p\<^sub>1, \<dots>, p\<^sub>m\<close> and a datatype value \<open>x\<close> and tests whether
all values in \<open>seti_name x\<close> satisfy the corresponding predicate \<open>p\<^sub>i\<close>.

The partial application \<open>pred_name p\<^sub>1 \<dots> p\<^sub>m\<close> lifts the predicates \<open>p\<^sub>1, \<dots>, p\<^sub>m\<close> to a predicate on the
corresponding instance of type \<open>('p\<^sub>1,\<dots>,'p\<^sub>m) name\<close>.

The function \<open>pred_coordx\<close> has type \<open>('p \<Rightarrow> bool) \<Rightarrow> 'p coordx \<Rightarrow> bool\<close>. For
instance, if \<open>cv\<close> is of type \<open>nat coordx\<close> the term \<open>pred_coordx (\<lambda>n. n=0) cv\<close> tests whether
all coordinates of \<open>cv\<close> are \<open>0\<close>.

The relator function is provided as
@{text[display]
\<open>rel_name :: "('p\<^sub>1 \<Rightarrow> 'q\<^sub>1 \<Rightarrow> bool) \<Rightarrow> \<dots> \<Rightarrow> ('p\<^sub>m \<Rightarrow> 'q\<^sub>m \<Rightarrow> bool)
   \<Rightarrow> ('p\<^sub>1,\<dots>,'p\<^sub>m) name \<Rightarrow> ('q\<^sub>1,\<dots>,'q\<^sub>m) name \<Rightarrow> bool"\<close>}
It takes as arguments \<open>m\<close> binary relations \<open>r\<^sub>1, \<dots>, r\<^sub>m\<close> and two datatype values \<open>x, y\<close> and tests
whether all pairs of values contained at the same position in  \<open>x\<close> and \<open>y\<close> are related by the
corresponding \<open>r\<^sub>i\<close>. This is done by constructing a container of type \<open>('p\<^sub>1\<times>'q\<^sub>1, \<dots>, 'p\<^sub>m\<times>'q\<^sub>m) name\<close>
where all contained values are pairs (see Section~\ref{holbasic-tuples}) which can be retrieved
by the set functions and tested whether they are related. Using the map function every contained
pair can be replaced by its first or second component, respectively, resulting in the containers
to be tested for being related.

The partial application \<open>rel_name r\<^sub>1 \<dots> r\<^sub>m\<close> lifts the relations \<open>r\<^sub>1, \<dots>, r\<^sub>m\<close> to a relation between
the corresponding instances of the types \<open>('p\<^sub>1,\<dots>,'p\<^sub>m) name\<close> and \<open>('q\<^sub>1,\<dots>,'q\<^sub>m) name\<close>.

The function \<open>rel_coordx\<close> has type \<open>('p \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow> 'p coordx \<Rightarrow> 'q coordx \<Rightarrow> bool\<close>. For
instance, if \<open>cv\<^sub>1\<close> and \<open>cv\<^sub>2\<close> are of type \<open>nat coordx\<close> the term \<open>rel_coordx (\<le>) cv\<^sub>1 cv\<^sub>2\<close> tests
whether \<open>cv\<^sub>1\<close> and \<open>cv\<^sub>2\<close> have the same dimension and every coordinate in \<open>cv\<^sub>1\<close> is lower or equal to
the corresponding coordinate in \<open>cv\<^sub>2\<close>.
\<close>

subsubsection "Specifying Names for the BNF Functions"

text\<open>
The form
@{theory_text[display]
\<open>datatype (sname\<^sub>1: 'p\<^sub>1,\<dots>, sname\<^sub>m: 'p\<^sub>m) name = alt\<^sub>1 | \<dots> | alt\<^sub>n
  for map: mname pred: pname rel: rname\<close>}
of a datatype definition allows to define alternate names \<open>sname\<^sub>i\<close>, \<open>mname\<close>, \<open>pname\<close>, \<open>rname\<close>
for (some of) the set, map, predicator, and relator functions.
\<close>

subsection "Rules"
text_raw\<open>\label{holtdefs-data-rules}\<close>

text\<open>
A datatype definition also introduces a large number of named facts about the constructors and 
destructors of the defined type. All fact names belong to the namespace of the datatype definition.
Since the fact names cannot be specified explicitly, all datatype definitions use the same fact
names, therefore the fact names must always be qualified by prefixing the type name.

Several rules are configured for automatic application, e.g., they are added to the simpset for
automatic application by the simplifier (see Section~\ref{basic-methods-simp}). Other rules must
be explicitly used by referring them by their name. 

Only some basic rules are described here, for more information refer to the Isabelle documentation
about datatypes.
\<close>

subsubsection "Simplifier Rules"

text\<open>
The rules added by a definition for a datatype \<open>name\<close> to the simpset (see
Section~\ref{basic-methods-simp}) support many ways for the simplifier to process terms with
constructors and destructors.

The rule set \<open>name.inject\<close> states that every non-constant constructor is injective,
the rules are of the form
@{text[display]
\<open>((cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^sub>k\<^sub>i) = (cname\<^sub>i ?y\<^sub>1 \<dots> ?y\<^sub>k\<^sub>i)) =
  (?x\<^sub>1 = ?y\<^sub>1 \<and> \<dots> \<and> ?x\<^sub>k\<^sub>i = ?y\<^sub>k\<^sub>i)\<close>}

The rule set \<open>name.distinct\<close> states that values constructed by different constructors are different,
the rules are of the form
@{text[display]
\<open>(cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^sub>k\<^sub>i) \<noteq> (cname\<^sub>j ?y\<^sub>1 \<dots> ?y\<^sub>k\<^sub>j)\<close>}
where \<open>i \<noteq> j\<close>.

The rule set \<open>name.sel\<close> provides ``defining equations'' for the selectors of the form
@{text[display]
\<open>sname\<^sub>i\<^sub>j (cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^sub>k\<^sub>i) = ?x\<^sub>j\<close>}

The rule set \<open>name.case\<close> provides equations for simplifying \<open>case\<close> terms where the discriminating
term is directly specified by a constructor application. They have the form
@{text[display]
\<open>(case (cname\<^sub>i ?x\<^sub>1 \<dots> ?x\<^sub>k\<^sub>i) of 
    cname\<^sub>1 var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1 \<Rightarrow> ?f\<^sub>1 var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1
  | \<dots>
  | cname\<^sub>n var\<^sub>n\<^sub>1 \<dots> var\<^sub>n\<^sub>k\<^sub>n \<Rightarrow> ?f\<^sub>n var\<^sub>n\<^sub>1 \<dots> var\<^sub>n\<^sub>k\<^sub>n)
= ?f\<^sub>i ?x\<^sub>1 \<dots> ?x\<^sub>k\<^sub>i\<close>}
Note that each branch is specified as an application of a function \<open>?f\<^sub>i\<close> so that the variables
bound in the branch can be substituted by the arguments of the constructor application.

Depending on the datatype definition there may be additional simplifier rules. In particular, if
the datatype is parameterized, simplifier rules are generated for the functions described in
Section~\ref{holtdefs-data-bnf}.
The set of all rules added to the simpset is named \<open>name.simps\<close>. By displaying it using the
\<^theory_text>\<open>thm\<close> command (see Section~\ref{basic-theory-theorem}) it can be inspected to get an idea how
the simplifier processes terms for a specific datatype. 
\<close>

subsubsection "Case Rule"

text\<open>
Every definition for a datatype \<open>name\<close> introduces a rule corresponding to the exhaustiveness of
the free constructors (see Section~\ref{holtdefs-data-constr}). It has the form
@{text[display]
\<open>name.exhaust:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>1. ?y = cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1 \<Longrightarrow> ?P;
   \<dots> ;
   \<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>n. ?y = cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}

According to Section~\ref{basic-case-reasoning} this rule is a case rule. It is automatically
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
  case (cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1) \<dots> show ?thesis \<proof>
next
\<dots>
next
  case (cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n) \<dots> show ?thesis \<proof>
qed\<close>}
The names \<open>x\<^sub>i\<close> of the locally fixed variables can be freely selected, they denote the constructor
arguments of the corresponding constructor. Therefore the case specification \<open>(cname\<^sub>i x\<^sub>1 \<dots> x\<^sub>k\<^sub>i)\<close>
looks like a constructor application to variable arguments, although it is actually a context name
together with locally fixed variables.
\<close>

subsubsection "Split Rule"

text\<open>
A \<open>case\<close> term (see Section~\ref{holtdefs-data-destr}) is only processed automatically be the
simplifier, if the discriminating term is a constructor application (see the \<open>name.case\<close> rule set
above). Otherwise it is only processed if a corresponding split rule is configured for it (see
Section~\ref{basic-methods-simp}). Every definition for a datatype \<open>name\<close> introduces such a split
rule. It has the form
@{text[display]
\<open>name.split:
  ?P(case ?t of 
     cname\<^sub>1 x\<^sub>1\<^sub>1 \<dots> x\<^sub>1\<^sub>k\<^sub>1 \<Rightarrow> ?t\<^sub>1 x\<^sub>1\<^sub>1 \<dots> x\<^sub>1\<^sub>k\<^sub>1
   | \<dots>
   | cname\<^sub>n x\<^sub>n\<^sub>1 \<dots> x\<^sub>n\<^sub>k\<^sub>n \<Rightarrow> ?t\<^sub>n x\<^sub>n\<^sub>1 \<dots> x\<^sub>n\<^sub>k\<^sub>n) = 
  (  (?t = cname\<^sub>1 x\<^sub>1\<^sub>1 \<dots> x\<^sub>1\<^sub>k\<^sub>1 \<longrightarrow> ?P(?t\<^sub>1 x\<^sub>1\<^sub>1 \<dots> x\<^sub>1\<^sub>k\<^sub>1))
   \<and> \<dots>
   \<and> (?t = cname\<^sub>n x\<^sub>n\<^sub>1 \<dots> x\<^sub>n\<^sub>k\<^sub>n \<longrightarrow> ?P(?t\<^sub>n x\<^sub>n\<^sub>1 \<dots> x\<^sub>n\<^sub>k\<^sub>n)))\<close>}
As described in Section~\ref{basic-methods-simp} the rule splits a goal with a \<open>case\<close> term for type
\<open>name\<close> in the conclusion into goals where the \<open>case\<close> term is replaced by the terms in the cases.
Note that the sub-terms of the \<open>case\<close> term are specified by unknowns, so the rule unifies with
arbitrary \<open>case\<close> terms for type \<open>name\<close>. Also note, that the \<open>?t\<^sub>i\<close> are specified with arguments, so
that they will be matched by functions depending on the constructor arguments \<open>x\<^sub>i\<^sub>1,\<dots>,x\<^sub>i\<^sub>k\<^sub>i\<close>, as
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
Every definition for a datatype \<open>name\<close> introduces an induction rule (see Section~\ref{basic-case-induction})
of the form
@{text[display]
\<open>name.induct:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>1. \<lbrakk>?P x\<^sub>l\<^sub>1; \<dots> ?P x\<^sub>l\<^sub>m\<^sub>1\<rbrakk> \<Longrightarrow> ?P (cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1);
   \<dots> ;
   \<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>n. \<lbrakk>?P x\<^sub>l\<^sub>n; \<dots> ?P x\<^sub>l\<^sub>m\<^sub>n\<rbrakk> \<Longrightarrow> ?P (cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n)\<rbrakk>
  \<Longrightarrow> ?P ?a\<close>}
where the \<open>x\<^sub>l\<^sub>1 \<dots> x\<^sub>l\<^sub>m\<^sub>i\<close> are those \<open>x\<^sub>1 \<dots> x\<^sub>k\<^sub>i\<close> which have type \<open>name\<close> (i.e., the recursive
occurrences of the type name). Like the case rule it is valid because the constructor applications 
cover all possibilities of constructing a value \<open>?a\<close> of the datatype.

If the datatype \<open>name\<close> is not recursive there are no \<open>x\<^sub>l\<^sub>1 \<dots> x\<^sub>l\<^sub>m\<^sub>i\<close> and the assumptions of all
inner rules are empty, then the induction rule is simply a specialization of the case rule and is
redundant. However, for a recursive datatype \<open>name\<close> induction using rule \<open>name.induct\<close> is the
standard way of proving a property to hold for all values.

The rule \<open>name.induct\<close> is associated with datatype \<open>name\<close> for use by the methods \<^theory_text>\<open>induction\<close> and
\<^theory_text>\<open>induct\<close> (see Section~\ref{basic-case-induction}). Therefore the application of the method
@{theory_text[display]
\<open>induction x\<close>}
where \<open>x\<close> is a variable of type \<open>name\<close> splits a goal into \<open>n\<close> subgoals where every subgoal uses
a different constructor term in the place of \<open>x\<close>.

As for the case rule and the \<^theory_text>\<open>cases\<close> method, the names for the named contexts created by the 
methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close> are simply the constructor names \<open>cname\<^sub>i\<close>. Therefore a structured
proof using induction for a variable \<open>x\<close> of datatype \<open>name\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1) \<dots> show ?case \<proof>
next
\<dots>
next
  case (cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n) \<dots> show ?case \<proof>
qed\<close>}

In the rule \<open>name.induct\<close> all inner assumptions are of the form \<open>?P x\<^sub>l\<^sub>i\<close>, i.e., they are induction
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

subsection "Recursive Functions on Algebraic Types"
text_raw\<open>\label{holtdefs-data-recursive}\<close>

text\<open>
A term is called a ``constructor pattern'' if it only consists of variables and constructor function
applications. Note that this includes terms consisting of a single variable. More generally, a
constructor pattern may be a sequence of such terms used as arguments in a function application.
A constructor pattern is called ``linear'' if every variable occurs only once.

HOL provides specific support for recursive definitions (see
Section~\ref{holbasic-recursive}) of functions \<open>name :: t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type\<close> where every
defining equation \<open>eq\<^sub>i\<close> has the form
@{text[display]
\<open>\<And> x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>p\<^sub>i. name term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k = term\<^sub>i\<close>}
without assumptions \<open>Q\<^sub>i\<^sub>j\<close> and the sequence \<open>term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>k\<close> on the left side is a linear
constructor pattern.

Since the type of a constructor application term is always an algebraic type, an argument type \<open>t\<^sub>j\<close>
may only be a non-algebraic type if the corresponding \<open>term\<^sub>i\<^sub>j\<close> is a single variable in all \<open>eq\<^sub>i\<close>.
\<close>

subsubsection "The Proof Method \<open>pat_completeness\<close>"

text\<open>
For recursive definitions where all \<open>eq\<^sub>i\<close> are without assumptions and using a linear constructor
pattern on their left side HOL provides the proof method
@{theory_text[display]
\<open>pat_completeness\<close>}
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
where eq\<^sub>1 | \<dots> | eq\<^sub>n \<proof>\<close>}
Here the defining equations must be ordered such that equations with more specific patterns precede
those with more general patterns. HOL automatically replaces the latter equations so that the
argument spaces of all equations are pairwise disjoint. Note that the resulting equations are used
for the completeness and compatibility proofs and also in the rules provided for the recursive
definition such as \<open>name.cases\<close> or \<open>name.psimps\<close>.

If the equations do not cover all possile arguments because some constructors are omitted,
additional equations are added with patterns using the omitted constructors. These equations use
\<open>undefined\<close> (see Section~\ref{holbasic-undefined}) as \<open>term\<^sub>i\<close> on the right side.

The completeness and compatibility proof must still be specified explicitly, although it always
works in the form \<^theory_text>\<open>by pat_completeness auto\<close>.
\<close>

subsubsection "The \<open>fun\<close> Command"

text\<open>
HOL supports the abbreviation
@{theory_text[display]
\<open>fun name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n\<close>}
for the recursive definition
@{theory_text[display]
\<open>function (sequential) name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n
by pat_completeness auto
termination by lexicographic_order\<close>}
which includes the completeness and compatibility proof and a termination proof. If the termination
proof cannot be done by the proof method \<^theory_text>\<open>lexicographic_order\<close> (see
Section~\ref{holbasic-recursive-term}) an error is signaled, then the long form must be used to
specify another termination proof.

The faculty function definitions in Section~\ref{holbasic-recursive-defeqs} are not of the required
form: the definition(s) of \<open>fac\<close> use an assumption in their second equation, the definition of
\<open>fac2\<close> uses the argument term \<open>n+1\<close> on the left side which is no constructor pattern because the
function \<open>(+)\<close> is not a constructor. However, type \<open>nat\<close> is actually defined in a way equivalent
to an algebraic type with constructors \<open>0\<close> and \<open>Suc\<close> (see Section~\ref{holtypes-nat}) where the
term \<open>Suc n\<close> is equivalent to \<open>n+1\<close>. Therefore the faculty function can be defined as
@{theory_text[display]
\<open>fun fac3 :: "nat \<Rightarrow> nat" where
  "fac3 0 = 1"
| "fac3 (Suc n) = (Suc n) * fac3 n"\<close>}
because \<open>0\<close> and \<open>(Suc n)\<close> are linear constructor patterns.
\<close>

subsubsection "Primitive Recursion"

text\<open>
A linear constructor pattern consisting of a sequence of terms is called ``primitive'' if exactly
one term is a constructor application and all constructor arguments in this term are single
variables. Thus a primitive constructor pattern has the general form
@{text[display]
\<open>x\<^sub>1 \<dots> x\<^sub>(\<^sub>i\<^sub>-\<^sub>1\<^sub>) (cname x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>n) x\<^sub>(\<^sub>i\<^sub>+\<^sub>1\<^sub>) \<dots> x\<^sub>k\<close>}
where all \<open>x\<^sub>i\<close> and \<open>x\<^sub>i\<^sub>j\<close> are variables. In particular, if a linear constructor pattern consists of
a single term it is always primitive.

A recursive function definition
@{theory_text[display]
\<open>fun name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n\<close>}
is called primitive if all defining equations \<open>eq\<^sub>i\<close> use a primitive constructor pattern on their
left side and all arguments of recursive calls in \<open>term\<^sub>i\<close> on the right side are single variables. 

Note that since the equations must be ordered so that equations with more specific patterns precede
equations with more general patterns all constructor application terms must occur at the same
argument position in the patterns. Therefore only one argument type \<open>t\<^sub>i\<close> must be an algebraic type,
all others may be arbitrary types because the corresponding arguments are denoted by single
variables in all patterns.

For primitive recursive function definitions HOL provides the alternative syntax
@{theory_text[display]
\<open>primrec name :: "t\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> t\<^sub>k \<Rightarrow> type"
where eq\<^sub>1 | \<dots> | eq\<^sub>n\<close>}

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
| "fac3 (Suc n) = (Suc n) * fac3 n"\<close>}\<close>

section "Record Types"
text_raw\<open>\label{holtdefs-record}\<close>

text\<open>
Record types resemble algebraic types in that they are roughly equivalent to tuple types,
however, they are defined in a completely different way. They do not support recursion, instead
they support a simple form of inheritance. They can be used to model ``record types'' in programming
languages and object data in object oriented programming languages.
\<close>

subsection "Record Definitions"
text_raw\<open>\label{holtdefs-record-def}\<close>

text \<open>
A record type is defined in the form
@{theory_text[display]
\<open>record rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close>}
where \<open>rname\<close> is the name of the new type, the \<open>fname\<^sub>i\<close> are the pairwise distinct names of the
record components (also called ``fields'') and the \<open>ftype\<^sub>i\<close> are the corresponding component types.
Atleast one component must be specified. The resulting type \<open>rname\<close> is mainly equivalent to the
tuple type \<open>ftype\<^sub>1 \<times> \<dots> \<times> ftype\<^sub>n\<close> (see Section~\ref{holbasic-tuples}), however, every record type
definition introduces a new type, even if the component names and types are the same.

The record type defined as above can either be denoted by its \<open>rname\<close> or by its ``record type
expression'' (in inner syntax)
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
  nice :: bool\<close>}
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
defines a type constructor \<open>rname_scheme\<close> with a single type parameter and an additional component
of that type which is called the ``more part''. Every instantiation of \<open>('a rname_scheme)\<close> is called
a record type scheme, the most general one is \<open>('a rname_scheme)\<close> where the
more part has an arbitrary type \<open>'a\<close>. For the defined record type the more part has type
\<open>unit\<close> (see Section~\ref{holtypes-unit}), i.e., type \<open>rname\<close> is the same as \<open>(unit rname_scheme)\<close>.

Like record types, record type schemes may be denoted by record type expressions. They have the
same form, the more part is denoted by the pseudo field name \<open>\<dots>\<close> (three-dot symbol). Therefore
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
A record type is extended by instantiating the more part to a ``record fragment type''. Like a
record type it consists of a sequence of one or more fields, however it cannot be used on its
own, it must always be embedded as more part in another record.

A record type is extended by the definition:
@{theory_text[display]
\<open>record rname = "rtype"
          + efname\<^sub>1 :: "eftype\<^sub>1" \<dots> efname\<^sub>m :: "eftype\<^sub>m"\<close>}
where \<open>rtype\<close> is a previously defined record type. The fields specified by the \<open>efname\<^sub>i\<close> and
\<open>eftype\<^sub>i\<close> comprise the record fragment which is appended after the fields of \<open>rtype\<close>, even if 
(some of) the same field names have already been used for \<open>rtype\<close>. Type \<open>rtype\<close> is called the 
``parent type'' of type \<open>rname\<close>. A record type which does not extend another record type (has no 
parent type) is called a ``root record type''.

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
\<open>record recrd2 = recrd + full :: bool num :: nat\<close>}
Note that the resulting record type has two fields with name \<open>num\<close> and type \<open>nat\<close>, they must always
be referred by the qualified field names \<open>recrd.num\<close> and \<open>recrd2.num\<close>. A record type expression for
\<open>recrd2\<close> is
@{text[display]
\<open>\<lparr>recrd.num :: nat, nums :: nat set, nice :: bool, 
    full :: bool, recrd2.num :: nat\<rparr>\<close>}
\<close>

subsubsection "Parameterized Record Types"

text \<open>
Like declared types record types may be parameterized (see Section~\ref{basic-theory-terms}):
@{theory_text[display]
\<open>record ('name\<^sub>1,\<dots>,'name\<^sub>n) rname = fname\<^sub>1 :: "ftype\<^sub>1" \<dots>
                                    fname\<^sub>n :: "ftype\<^sub>n"\<close>}
where the \<open>'name\<^sub>i\<close> are the type parameters. They may occur in the component types \<open>ftype\<^sub>i\<close>, i.e.,
the \<open>ftype\<^sub>i\<close> may be polymorphic (see Section~\ref{basic-theory-terms}). As usual, the parentheses
may be omitted if there is only one type parameter.

For a parameterized record type a record type expression may be specified for every possible
instance. As usual, a record type expression with type variables denotes a polymorphic type.

In the record type scheme the parameter for the more part follows all other type parameters.

As an example, a parameterized record type with two type parameters is defined by
@{theory_text[display]
\<open>record ('a, 'b) recrdp = f1 :: 'a f2:: "'a set" f3 :: 'b\<close>}
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
\<open>make :: ftype\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> ftype\<^sub>n \<Rightarrow> rname\<close>}
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
\<open>extend :: rname \<Rightarrow> 'a \<Rightarrow> ('a rname_scheme)\<close>}
It replaces the more part of a record of type \<open>rname\<close> (which is the unit value) by a value of an
arbitrary type \<open>'a\<close>. The result will only be a proper record if \<open>'a\<close> is a record fragment type for
a defined extension of \<open>rname\<close>.

Additionally the definition of the extended record type \<open>rname2\<close> defines the constructor function
@{theory_text[display]
\<open>fields :: `ftype\<^sub>n\<^sub>+\<^sub>1` \<Rightarrow> \<dots> \<Rightarrow> ftype\<^sub>m \<Rightarrow>
       \<lparr>`fname\<^sub>n\<^sub>+\<^sub>1`::`ftype\<^sub>n\<^sub>+\<^sub>1`, \<dots>, fname\<^sub>m :: ftype\<^sub>m\<rparr>\<close>}
for the record fragment used as the more part of \<open>rname\<close>. For a root record type \<open>fields\<close> is
the same function as \<open>make\<close>.
\<close>

subsubsection "Constructing Values"

text\<open>
Like for a datatype every record constructor function is assumed to be injective, thus their result
values differ if atleast one argument value differs. This implies that the set of all values of the
constructor function \<open>make\<close> is equivalent to the set of all tuples of values of
the field types, which is equivalent to the set of all possible values of the record type \<open>rname\<close>.
Thus every value of \<open>rname\<close> may be denoted by a term
@{text[display]
\<open>rname.make term\<^sub>1 \<dots> term\<^sub>n\<close>}
where each \<open>term\<^sub>i\<close> is of type  \<open>ftype\<^sub>i\<close> and specifies the value for field \<open>i\<close>.

There is an alternative Syntax for applications of record constructors. The record expression
@{text[display]
\<open>\<lparr>fname\<^sub>1 = term\<^sub>1, \<dots>, fname\<^sub>n = term\<^sub>n\<rparr>\<close>}
denotes the same record value as the constructor application
above. If the name \<open>fname\<^sub>1\<close> of the first field has been used in more than one record type it must be
qualified. The record schema expression
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

If \<open>r\<close> is a variable of type \<open>recrd\<close> as defined above, the term \<open>nums r\<close> selects the value of the
second field. The same works if \<open>r\<close> has the extended type \<open>recrd2\<close>.

A field selector cannot be applied directly to a record fragment. The fields of the fragment can
only be selected if the fragment is embedded in the extended record.
\<close>

subsection "Record Updates"
text_raw\<open>\label{holtdefs-record-update}\<close>

text \<open>
In addition to the constructor and selector functions a record type definition \<^theory_text>\<open>record rname = 
fname\<^sub>1 :: "ftype\<^sub>1" \<dots> fname\<^sub>n :: "ftype\<^sub>n"\<close> defines the record update functions
@{theory_text[display]
\<open>fname\<^sub>1_update :: (ftype\<^sub>1 \<Rightarrow> ftype\<^sub>1) \<Rightarrow> 'a rname_scheme \<Rightarrow> 'a rname_scheme
 \<dots>
fname\<^sub>n_update :: (ftype\<^sub>n \<Rightarrow> ftype\<^sub>n) \<Rightarrow> 'a rname_scheme \<Rightarrow> 'a rname_scheme\<close>}
Each record update function \<open>fname\<^sub>i_update\<close> takes as argument an update function for values of
type \<open>ftype\<^sub>i\<close> (which maps an old value to a new value) and a record value. It returns
the record where the value of field \<open>fname\<^sub>i\<close> is the result of applying the update function to its
old value and the values of all other fields are unchanged.

Like the selector functions the update functions are defined for the polymorphic record type scheme
and can thus be also applied to all extended records.

A field may be set to a specific value \<open>term\<close> without regarding the old value by using the term
\<open>fname\<^sub>i_update (\<lambda>_.term) r\<close> where a constant function (see Section~\ref{basic-theory-terms}) is
used as update function for the field value. For record update applications of this form the
alternative syntax
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
automatic application by the simplifier (see Section~\ref{basic-methods-simp}). Other rules must
be explicitly used by referring them by their name. 

Only some basic rules are described here, for more information refer to the Isabelle documentation
about records.
\<close>

subsubsection "Simplifier Rules"

text\<open>
The rules for injectivity of the record constructor have the form
@{text[display]
\<open>(\<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>n = ?x\<^sub>n, \<dots>= ?x\<rparr> = 
  \<lparr>fname\<^sub>1 = ?y\<^sub>1, \<dots>, fname\<^sub>n = ?y\<^sub>n, \<dots>= ?y\<rparr>)
= (?x\<^sub>1 = ?y\<^sub>1 \<and> \<dots> \<and> ?x\<^sub>n = ?y\<^sub>n \<and> ?x = ?y)\<close>}
are named \<open>rname.iffs\<close> for the record type \<open>rname\<close>.

Other rules added by a record definition to the simpset process terms where selectors or update
functions are applied to constructed record values. They have the form of equations
@{text[display]
\<open>fname\<^sub>i \<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>n = ?x\<^sub>n\<rparr> = ?x\<^sub>i
fname\<^sub>i_update ?f \<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>n = ?x\<^sub>n\<rparr> = 
   \<lparr>fname\<^sub>1 = ?x\<^sub>1, \<dots>, fname\<^sub>i = ?f ?x\<^sub>i, \<dots>, fname\<^sub>n = ?x\<^sub>n\<rparr>\<close>}
The set of all these rules is named \<open>rname.simps\<close> for the record type \<open>rname\<close>.

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
\<open>rname.make x\<^sub>1 \<dots> x\<^sub>n = \<lparr>fname\<^sub>1 = x\<^sub>1, \<dots>, fname\<^sub>n = x\<^sub>n\<rparr>\<close>}
Every rule provides a representation of a constructor application as a record expression.
The set of these rules is named \<open>rname.defs\<close> for the record type \<open>rname\<close>. It is not added to the
simpset, the rules must be explicitly applied by adding them to the simplifier method when needed
(as described in Section~\ref{basic-methods-simp}).

The simplifier rules are mainly defined for record expressions. To apply them to record
terms specified by the constructor functions the constructor rules must be used to convert the
terms to record expressions.
\<close>

subsubsection "Case Rules"

text\<open>
Every definition for a record type \<open>rname\<close> introduces case rules
(see Section~\ref{basic-case-reasoning}) of the form
@{text[display]
\<open>rname.cases:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>n. ?y = \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n\<rparr> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P
rname.cases_scheme:
  \<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>n m. ?y = \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n, \<dots>=m\<rparr> \<Longrightarrow> ?P\<rbrakk>
  \<Longrightarrow> ?P\<close>}
They are valid because the record expressions cover all possibilities of constructing a value
\<open>?y\<close> of the record type or record scheme type, respectively. 

Both rules are associated with the record type for use by the \<^theory_text>\<open>cases\<close> method
(see Section~\ref{basic-case-reasoning}), the method automatically selects the most sensible of
them. Therefore the application of the method
@{theory_text[display]
\<open>cases "term"\<close>}
where \<open>term\<close> is a record of type \<open>rname\<close> replaces an arbitrary goal by a goal where \<open>term\<close> is
set equal to a record constructed from explicit field values \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> and possibly a more part. 

The name used for the named context created by the \<^theory_text>\<open>cases\<close> method is ``fields''.
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
(see Section~\ref{basic-case-induction}) of the form
@{text[display]
\<open>rname.induct:
  (\<And>x\<^sub>1 \<dots> x\<^sub>n. ?P \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n\<rparr>) \<Longrightarrow> ?P ?a
rname.induct_scheme:
  (\<And>x\<^sub>1 \<dots> x\<^sub>n m. ?P \<lparr>fname\<^sub>1=x\<^sub>1, \<dots>, fname\<^sub>n=x\<^sub>n, \<dots>=m\<rparr>) \<Longrightarrow> ?P ?a\<close>}
Like the case rule it is valid because the record expressions 
cover all possibilities of constructing a value \<open>?a\<close> of the record type \<open>rname\<close>.

The rules are associated with the record type for use by the methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close>
(see Section~\ref{basic-case-induction}), the methods automatically select the most sensible of
them. Therefore the application of the method
@{theory_text[display]
\<open>induction x\<close>}
where \<open>x\<close> is a variable of type \<open>rname\<close> replaces a goal by a goal which uses a record expression
in the place of \<open>x\<close>.

As for the case rule and the \<^theory_text>\<open>cases\<close> method, the names used for the named contexts created by the 
methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close> are ``fields''. Therefore a structured
proof using induction for a variable \<open>x\<close> of record type \<open>rname\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (fields x\<^sub>1 \<dots> x\<^sub>n) \<dots> show ?case \<proof>
qed\<close>}

As an example, the induction rules for the record type \<open>recrd\<close> defined in 
Section~\ref{holtdefs-record-def} are
@{text[display]
\<open>recrd_induct:
  (\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. ?P \<lparr>num=x\<^sub>1, nums=x\<^sub>2, nice=x\<^sub>3\<rparr>) \<Longrightarrow> ?P ?a
recrd_induct_scheme:
  (\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3 m. ?P \<lparr>num=x\<^sub>1, nums=x\<^sub>2, nice=x\<^sub>3, \<dots>=m\<rparr>) \<Longrightarrow> ?P ?a\<close>}
By applying the method \<open>(induction x)\<close> the goal \<open>(num x) = y\<close> is replaced by
the goal \<open>\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. (num \<lparr>num = x\<^sub>1, nums = x\<^sub>2, nice = x\<^sub>3\<rparr>) = y\<close>.

Like the cases methods a transformation of this kind may enable the application of the simplifier
methods.
\<close>

section "Subtypes"
text_raw\<open>\label{holtdefs-sub}\<close>

text \<open>
A subtype specifies the values of a type by a set of values of an existing type. However,
since the values of different types are always disjoint, the values in the set are not directly the
values of the new type, instead, there is a 1-1 relation between them, they are isomorphic. The 
values in the set are called ``representations'', the values in the new type are called
``abstractions''.\<close>

subsection "Subtype Definitions"
text_raw\<open>\label{holtdefs-sub-def}\<close>

text \<open>
A subtype is defined in the form
@{theory_text[display]
\<open>typedef name = "term" \<proof>\<close>}
where \<open>name\<close> is the name of the new type and \<open>term\<close> is a term for the representing set. The
\<open>\<proof>\<close> must prove that the representing set is not empty. A subtype definition implies that
for every value in the representing set there is a unique value in the defined subtype.

Note that the concept of subtypes actually depends on the specific HOL type \<open>set\<close> for specifying
the representing set. See Section~\ref{holtypes-set} for how to denote terms for this set. Also
note that the set is always of a type \<open>t' set\<close> where \<open>t'\<close> is the common type of all set elements.
This implies that the representing set is always a subset of the set of all values of a type \<open>t'\<close>
which explains the designation as ``subtype''.

A simple example is the type\<close>
typedef three = "{1::nat,2,3}" by auto
text \<open>
which has three values. The representations are natural numbers. As usual, the type \<open>nat\<close> must be
specified because the constants \<open>1, 2, 3\<close> may also denote values of other types. However, they do
not denote the values of the new type \<open>three\<close>, the type definition does not introduce constants
for them.

Instead, a subtype definition \<^theory_text>\<open>typedef t = rset \<proof>\<close> introduces two functions \<open>Abs_t\<close>
and \<open>Rep_t\<close>. These are morphisms between \<open>rset\<close> and the new type, \<open>Abs_t\<close> maps from \<open>rset\<close> 
to type \<open>t\<close>, \<open>Rep_t\<close> is its inverse. Both functions are injective, together they provide the
1-1 mapping between the subtype and the representing set. The function \<open>Abs_t\<close> can be used to
denote the values of the subtype. Thus, \<open>Abs_t\<close> plays the role of a constructor for type \<open>t\<close>,
whereas \<open>Rep_t\<close> can be thought of being a destructor for \<open>t\<close>.

Actually, if the representing set \<open>rset\<close> is of type \<open>t' set\<close>, the morphism  \<open>Abs_t\<close> is a function of
type \<open>t' \<Rightarrow> t\<close>, since it must be total like all functions in Isabelle. However, \<open>Abs_t\<close> is
underspecified as described in Section~\ref{basic-theory-terms}, no information is given about its
result values if applied to values which are not in \<open>rset\<close>.

In the example the morphisms are \<open>Abs_three :: nat \<Rightarrow> three\<close> and \<open>Rep_three :: three \<Rightarrow> nat\<close>. The
values of type \<open>three\<close> may be denoted as \<open>(Abs_three 1)\<close>, \<open>(Abs_three 2)\<close>, and \<open>(Abs_three 3)\<close>.
The term \<open>(Abs_three 42)\<close> is a valid term of type \<open>three\<close>, however, no information about its value
is available.

Alternative names may be specified for the morphisms in the form
@{theory_text[display]
\<open>typedef t = "term" morphisms rname aname \<proof>\<close>}
where \<open>rname\<close> replaces \<open>Rep_t\<close> and \<open>aname\<close> replaces \<open>Abs_t\<close>.

Like declared types subtypes may be parameterized (see Section~\ref{basic-theory-terms}):
@{theory_text[display]
\<open>typedef ('name\<^sub>1,\<dots>,'name\<^sub>n) name = "term" \<proof>\<close>}
where the \<open>'name\<^sub>i\<close> are the type parameters. They may occur in the type of the \<open>term\<close>, i.e., the 
\<open>term\<close> may be polymorphic (see Section~\ref{basic-theory-terms}).
\<close>

subsection "Type Copies"
text_raw\<open>\label{holtdefs-sub-copies}\<close>

text \<open>
A type copy is the special case of a subtype definition where the representing set is the universal
set (see Section~\ref{holtypes-set-values}) of another type \<open>t'\<close>:
@{theory_text[display]
\<open>typedef t = "UNIV :: t' set" by auto\<close>}
The non-emptiness proof can always be performed by the \<open>auto\<close> method, since the universal set covers
all values in type \<open>t'\<close> and types are always non-empty.

The result is a type \<open>t\<close> which is distinct from \<open>t'\<close> but is ``isomorphic'' to it. The values are in
1-1 relation, although, as usual for distinct types, the value sets are disjoint.
\<close>

subsection "Subtype Rules"
text_raw\<open>\label{holtdefs-sub-rules}\<close>

text \<open>
A subtype definition only introduces a small number of rules, no rules are added to the simpset.
\<close>

subsubsection "Basic Morphism Rules"

text\<open>
The two morphisms of a subtype definition \<^theory_text>\<open>typedef t = rset \<proof>\<close> are characterized to be
inverses of each other by two rules of the form
@{text[display]
\<open>Abs_t_inverse:
  ?y \<in> rset \<Longrightarrow> Rep_t (Abs_t ?y) = ?y
Rep_t_inverse:
  Abs_t (Rep_t ?x) = ?x\<close>}

This implies that both morphisms are injective which is stated explicitly by two rules of the form
@{text[display]
\<open>Abs_t_inject:
  \<lbrakk>?y\<^sub>1 \<in> rset; ?y\<^sub>2 \<in> rset\<rbrakk> \<Longrightarrow> (Abs_t ?y\<^sub>1 = Abs_t ?y\<^sub>2) = (?y\<^sub>1 = ?y\<^sub>2)
Rep_t_inject:
  (Rep_t ?x\<^sub>1 = Rep_t ?x\<^sub>2) = (?x\<^sub>1 = ?x\<^sub>2)\<close>}

Since all values of type \<open>t\<close> can be denoted as \<open>Abs_t y\<close> for some \<open>y\<close> in the representing set \<open>rset\<close>,
the rule \<open>Abs_t_inject\<close> can be used to prove equality or inequality for values of type \<open>t\<close> based on
the equality for values in \<open>rset\<close>.
\<close>

subsubsection "Case Rules"

text\<open>
Every subtype definition \<^theory_text>\<open>typedef t = rset \<proof>\<close> introduces a case rule (see
Section~\ref{basic-case-reasoning}) of the form
@{text[display]
\<open>Abs_t_cases:
  (\<And>y. \<lbrakk>?x = Abs_t y; y \<in> rset\<rbrakk> \<Longrightarrow> ?P) \<Longrightarrow> ?P\<close>}
It is valid because the \<open>Abs_t\<close> application covers all possibilities of constructing a
value \<open>?x\<close> of the subtype.

The rule \<open>Abs_t_cases\<close> is associated with the new subtype \<open>t\<close> for use by the \<^theory_text>\<open>cases\<close> method
(see Section~\ref{basic-case-reasoning}). Therefore the application of the method
@{theory_text[display]
\<open>cases "term"\<close>}
where \<open>term\<close> is of type \<open>t\<close> applies \<open>Abs_t_cases\<close> to replace the current goal. Since the rule has
only one case, it does not split the goal. Applying it to a goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>
as described in Section~\ref{basic-case-reasoning} results in the single new goal
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m y. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; term = Abs_t y; y \<in> rset\<rbrakk> \<Longrightarrow> C\<close>}
where the variable \<open>y\<close> and the two assumptions from the case rule have been added. Together the new
goal provides a representation of \<open>term\<close> by applying \<open>Abs_t\<close> to a value \<open>y\<close> from the representing
set \<open>rset\<close>. This may allow to use facts about \<open>y\<close> to prove the goal.

The name for the named context created by the \<^theory_text>\<open>cases\<close> method is simply the morphism name
\<open>Abs_t\<close>. Therefore a structured proof using case based reasoning for a \<open>term\<close> of subtype \<open>t\<close>
has the form
@{theory_text[display]
\<open>proof (cases "term")
  case (Abs_t y) \<dots> show ?thesis \<proof>
qed\<close>}
The name \<open>y\<close> of the locally fixed variable can be freely selected, it denotes the morphism
argument, i.e., the representation value for \<open>term\<close>.

Every subtype definition \<^theory_text>\<open>typedef t = rset \<proof>\<close> also introduces an elimination rule (see
Section~\ref{basic-case-elim}) of the form
@{text[display]
\<open>Rep_t_cases:
  \<lbrakk>?y \<in> rset; \<And>x. ?y = Rep_t x \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
It is valid because the \<open>Rep_t\<close> application covers all possibilities to determine a representation
value \<open>?y\<close> in \<open>rset\<close>.

With the help of this rule it is possible to introduce an abstraction value \<open>x\<close> corresponding to
a representation value \<open>?y\<close>, consuming an assumption or input fact that \<open>?y\<close> is in \<open>rset\<close>. For
application by the method \<^theory_text>\<open>cases\<close> the rule is annotated by \<open>[consumes 1]\<close> and the name for the
created named context is the morphism name \<open>Rep_t\<close>. As described in Section~\ref{basic-case-elim}
a pattern for using the rule in a structured proof is
@{theory_text[display]
\<open>theorem "C" if "y \<in> rset"
  using that
proof (cases rule: Rep_t_cases)
  case (Rep_t x) \<dots> show ?thesis \<proof>
qed\<close>}\<close>

subsubsection "Induction Rules"

text\<open>
Every subtype definition \<^theory_text>\<open>typedef t = rset \<proof>\<close> introduces two induction rules (see
Section~\ref{basic-case-induction}) of the form
@{text[display]
\<open>Abs_t_induct:
  (\<And>y. y \<in> rset \<Longrightarrow> ?P (Abs_t y)) \<Longrightarrow> ?P ?a
Rep_t_induct:
  \<lbrakk>?a \<in> rset; \<And>x. ?P (Rep_t x)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}
The former rule is a plain induction rule, the latter is an induction rule with elimination where
the major premise states that the value \<open>?a\<close> is in \<open>rset\<close>. Both rules only contain a ``base case''
and no ``induction step'' with a recursive occurrence of values of the defined type \<open>t\<close>. Like for
the case rules they are valid because the morphism applications cover all possibilities of
constructing values of \<open>t\<close> or values in \<open>rset\<close>, respectively.

Since the rules only consist of a base case they are mainly equivalent to the case rules. However,
when applied by the \<open>induct\<close> method, they not only provide a representation by a morphism for a
specified variable, they also substitute every occurrence of the variable by the morphism
representation.

The rule \<open>Abs_t_induct\<close> is associated with subtype \<open>t\<close> for use by the methods \<^theory_text>\<open>induction\<close> and
\<^theory_text>\<open>induct\<close> (see Section~\ref{basic-case-induction}). Therefore the application of the method
@{theory_text[display]
\<open>induction x\<close>}
where \<open>x\<close> is a variable of type \<open>t\<close> replaces a goal by a goal where every occurrence of \<open>x\<close> is
substituted by the term \<open>Abs_t y\<close> and \<open>y\<close> is a new bound variable with the additional assumption
\<open>y \<in> rset\<close> named \<open>Abs_t.hyps\<close>. As usual for the induction methods, \<open>x\<close> is substituted in the goal
conclusion and also in all goal assumptions.

As for the case rule and the \<^theory_text>\<open>cases\<close> method, the name for the named context created by the 
methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close> is simply the morphism name \<open>Abs_t\<close>. Therefore a structured
proof using induction for a variable \<open>x\<close> of subtype \<open>t\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (Abs_t y) \<dots> show ?case \<proof>
qed\<close>}

As an example, the induction rule for the subtype \<open>three\<close> defined in 
Section~\ref{holtdefs-sub-def} is
@{text[display]
\<open>Abs_three_induct:
  "\<And>y. y \<in> {1, 2, 3} \<Longrightarrow> ?P (Abs_three y)) \<Longrightarrow> ?P ?a\<close>}
By applying the method \<open>(induction x)\<close> the goal \<open>x = Abs_three 0 \<Longrightarrow> x \<noteq> Abs_three 1\<close> is replaced by
the goal \<open>\<And>y.  \<lbrakk>y \<in> {1, 2, 3}; Abs_three y = Abs_three 0\<rbrakk> \<Longrightarrow> Abs_three y \<noteq> Abs_three 1\<close>
(which does not help for the proof, but shows the effect of the induction rule).

The rule \<open>Rep_t_induct\<close> is annotated by \<open>[consumes 1]\<close> for application by the methods \<^theory_text>\<open>induction\<close>
and \<^theory_text>\<open>induct\<close> and the name for the created named context is the morphism name \<open>Rep_t\<close>. As described
in Section~\ref{basic-case-induct} a pattern for using the rule in a structured proof is
@{theory_text[display]
\<open>theorem "C" if "y \<in> rset"
  using that
proof (induction rule: Rep_t_induct)
  case (Rep_t x) \<dots> show ?case \<proof>
qed\<close>}

As an example, the induction rule with elimination for the subtype \<open>three\<close> defined in 
Section~\ref{holtdefs-sub-def} is
@{text[display]
\<open>Rep_three_induct:
  \<lbrakk>?a \<in> {1, 2, 3}; \<And>x. ?P (Rep_three x)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}\<close>

section "Quotient Types"
text_raw\<open>\label{holtdefs-quot}\<close>

(* Achtung: siehe HOL-Library: Quotient_Type, Quotient_* *)
text\<open>
**todo**
\<close>

section "Lifting and Transfer"
text_raw\<open>\label{holtdefs-lift}\<close>

text\<open>
**todo**
\<close>

end
