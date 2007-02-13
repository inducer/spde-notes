<TeXmacs|1.0.6>

<style|<tuple|article|number-long-article>>

<\body>
  <doc-data|<doc-title|Stochastic PDEs>|<doc-author-data|<author-name|Boris
  Rozovsky>>>

  Send corrections to <with|font-family|tt|kloeckner@dam.brown.edu>.

  \;

  Example: Heat Equation. Suppose <with|mode|math|\<omega\>\<in\>\<Omega\>>
  is part of a probability space. Then chance can come in at any or all of
  these points:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<frac|\<partial\>u(t,x)|\<partial\>t>>|<cell|=>|<cell|a(x,<with|color|orange|\<omega\>>)<frac|\<partial\><rsup|2>|\<partial\>x<rsup|2>>u(t,x)+f(t,x,<with|color|orange|\<omega\>>)<space|1em>x\<in\>(a,b)>>|<row|<cell|u(0,x)>|<cell|=>|<cell|\<varphi\>(x,<with|color|orange|\<omega\>>)>>|<row|<cell|u(t,a)>|<cell|=>|<cell|\<psi\><rsub|1>(t,<with|color|orange|\<omega\>>)>>|<row|<cell|u(t,b)>|<cell|=>|<cell|\<psi\><rsub|2>(t,<with|color|orange|\<omega\>>)>>>>
  </eqnarray*>

  <section|Basic Facts from Stochastic Processes>

  <tabular|<tformat|<cwith|1|1|1|-1|cell-bborder|0.5pt>|<cwith|1|-1|2|2|cell-lborder|0.5pt>|<table|<row|<cell|Probability
  Theory>|<cell|Measure Theory>>|<row|<cell|<with|mode|math|\<omega\>> --
  elementary random event (outcomes)>|<cell|>>|<row|<cell|<with|mode|math|\<Omega\>=<big|cup>\<omega\>>
  -- probability space/space of outcomes>|<cell|<with|mode|math|\<Omega\>> --
  set>>|<row|<cell|Random events <with|mode|math|\<leftrightarrow\>> subsets
  of <with|mode|math|\<Omega\>\<supset\>A>>|<cell|Algebra
  <with|mode|math|\<cal-A\>\<subset\>\<cal-P\>(\<Omega\>)> closed w.r.t.
  <with|mode|math|\<cap\>>/<with|mode|math|\<cup\>>/<with|mode|math|<wide|\<cdot\>|\<bar\>>>.>>|<row|<cell|Operations
  on events: <with|mode|math|\<cup\>>, <with|mode|math|\<cap\>>,
  <with|mode|math|<wide|A|\<bar\>>=\<Omega\>\<setminus\>A>.>|<cell|>>|<row|<cell|<with|mode|math|\<varnothing\>\<assign\>\<Omega\>\<setminus\>\<Omega\>>>|<cell|>>|<row|<cell|If
  <with|mode|math|A> and <with|mode|math|B> are random events, then
  <with|mode|math|A\<cup\>B>, <with|mode|math|A\<cap\>B>,
  <with|mode|math|<wide|A|\<bar\>>> are r.e.>|<cell|>>|<row|<cell|Elementary
  properties of probability:>|<cell|Measures (see
  below)>>|<row|<cell|<with|mode|math|P(A)\<in\>[0,1]>,
  <with|mode|math|P(\<Omega\>)=1>, additive for disjoint events.>|<cell|>>>>>

  <\definition>
    A function <with|mode|math|\<mu\>(A)> on the sets of an algebra
    <with|mode|math|\<cal-A\>> is called a <em|measure> if

    <\enumerate-alpha>
      <item>the values of <with|mode|math|\<mu\>> are non-negative and real,

      <item><with|mode|math|\<mu\>> is an additive function for any finite
      expression--explicitly, if <with|mode|math|A=<big|cup><rsub|i>A<rsub|i>>
      and <with|mode|math|A<rsub|i>\<cap\>A<rsub|j>=\<varnothing\>> iff
      <with|mode|math|i\<neq\>j>, then

      <\equation*>
        \<mu\>(A)=<big|sum><rsub|i=1><rsup|n>\<mu\>(A<rsub|i>).
      </equation*>
    </enumerate-alpha>
  </definition>

  <\definition>
    A system <with|mode|math|\<cal-F\>\<subset\>\<cal-P\>(\<Omega\>)> is
    called a <em|<with|mode|math|\<sigma\>>-algebra> if it is an algebra and,
    in addition, if <with|mode|math|(A<rsub|i>)<rsub|i=1,2,\<ldots\>>>, then
    also <with|mode|math|<big|cup><rsub|i>A<rsub|i>\<in\>\<cal-F\>>.
  </definition>

  It is an easy consequence that <with|mode|math|<big|cap><rsub|i>A<rsub|i>\<in\>\<cal-F\>>.

  <\definition>
    A measure is called <em|<with|mode|math|\<sigma\>>-additive> if

    <\equation*>
      \<mu\><left|(><big|cup><rsub|i=1><rsup|\<infty\>>A<rsub|i><right|)>=<big|sum><rsub|i=1><rsup|\<infty\>>\<mu\>(A<rsub|i>)
    </equation*>

    if the <with|mode|math|A<rsub|i>> are mutually disjoint.
  </definition>

  The above together form <em|Kolmogorov's Axioms of Probability:> A tuple
  <with|mode|math|(\<Omega\>,\<cal-F\>,P)> is called a <em|probability space>
  (<with|mode|math|\<Omega\>> a set, <with|mode|math|\<cal-F\>> a
  <with|mode|math|\<sigma\>>-algebra, <with|mode|math|P> a probability
  measure).

  <\lemma>
    Let <with|mode|math|\<varepsilon\>> be a set of events. Then there is a
    smallest <with|mode|math|\<sigma\>>-algebra <with|mode|math|\<cal-F\>>
    such that <with|mode|math|\<varepsilon\>\<subset\>\<cal-F\>>.
  </lemma>

  <\definition>
    A function <with|mode|math|X:\<Omega\>\<rightarrow\>\<bbb-R\><rsup|n>> is
    called a <em|random variable> if it is
    <with|mode|math|\<cal-F\>>-measurable, i.e. for arbitrary
    <with|mode|math|A> belonging to the Borel-<with|mode|math|\<sigma\>>-algebra
    <with|mode|math|\<cal-B\>(\<bbb-R\><rsup|n>)>, the set
    <with|mode|math|X<rsup|-1>(A)\<in\>\<cal-F\>>.
  </definition>

  <\definition>
    <em|Completion of <with|mode|math|\<cal-F\>> with respect to
    <with|mode|math|P>>: For simplicity, <with|mode|math|\<Omega\>=(0,1)>.
    <with|mode|math|P> is the <em|Lebesgue measure>,
    <with|mode|math|\<cal-F\>> the Borel-<with|mode|math|\<sigma\>>-algebra
    <with|mode|math|\<cal-B\>(0,1)> on <with|mode|math|\<Omega\>=(0,1)>.
    <with|mode|math|\<cal-F\>> is called complete if it contains all subsets
    <with|mode|math|B> of <with|mode|math|\<Omega\>> with the property:

    <\quote-env>
      There are subsets <with|mode|math|B<rsup|->> and
      <with|mode|math|B<rsup|+>> from <with|mode|math|\<cal-B\>(0,1)> such
      that <with|mode|math|B<rsup|->\<subset\>B\<subset\>B<rsup|+>> and
      <with|mode|math|P(B<rsup|+>\<setminus\>B<rsup|->)=0>.
    </quote-env>

    This process maps <with|mode|math|(\<Omega\>,\<cal-F\>,P)> to
    <with|mode|math|(\<Omega\>,<wide|\<cal-F\>|\<bar\>><rsup|P>,P)>, where
    <with|mode|math|<wide|\<cal-F\>|\<bar\>><rsup|P>> is the <em|completion>
    of <with|mode|math|\<cal-F\>> w.r.t. <with|mode|math|P>.
  </definition>

  Now suppose <with|mode|math|X> is a random variable in
  <with|mode|math|(\<Omega\>,\<cal-F\>,P)> in
  <with|mode|math|\<bbb-R\><rsup|n>>. <with|mode|math|X<rsup|-1>(\<cal-B\>(\<bbb-R\><rsup|n>))\<assign\>{X<rsup|-1>(A):A\<in\>\<cal-B\>(\<bbb-R\><rsup|n>)}={\<Gamma\>:X(\<Gamma\>)\<in\>\<cal-B\>(\<bbb-R\><rsup|n>)}>.
  <with|mode|math|\<cal-H\><rsub|X>> is called the
  <with|mode|math|\<sigma\>>-algebra generated by <with|mode|math|X>.

  One reason to use this definition of a random variable is this:

  <\lemma>
    <dueto|Doob-Dynkin>If <with|mode|math|\<cal-F\>> is generated by a random
    variable <with|mode|math|Y>, then there exists a Borel function
    <with|mode|math|g> such that <with|mode|math|X=g(Y)>.
  </lemma>

  <subsection|Lebesgue Integral>

  <\definition>
    <with|mode|math|X> on <with|mode|math|(\<Omega\>,\<cal-F\>,P)> is called
    simple if it is <with|mode|math|\<cal-F\>>-measurable and takes a finite
    number of values: <with|mode|math|x<rsub|1>,x<rsub|2>,\<ldots\>,x<rsub|n>>.

    <with|mode|math|\<Omega\><rsub|i>={\<omega\>:X(\<omega\>)=x<rsub|i>}=X<rsup|-1>(x<rsub|i>)>.
    Then the Lebesuge integral is

    <\equation*>
      <big|int><rsub|\<Omega\>>X\<mathd\>P=<big|sum><rsub|i=1><rsup|n>x<rsub|i>P(\<Omega\><rsub|i>).
    </equation*>
  </definition>

  <\definition>
    An arbitrary measurable function <with|mode|math|X> on
    <with|mode|math|(\<Omega\>,\<cal-F\>,P)> is called
    <with|mode|math|P>-integrable if there exists a sequence of such simple
    functions <with|mode|math|X<rsub|n>> so that
    <with|mode|math|X<rsub|n>\<rightarrow\>X> a.s. and

    <\equation*>
      lim<rsub|n,m\<rightarrow\>\<infty\>><big|int><rsub|\<Omega\>>\|X<rsub|n>-X<rsub|m>\|\<mathd\>P=0.
    </equation*>
  </definition>

  <\lemma>
    If <with|mode|math|X> is <with|mode|math|P>-integrable, then

    <\enumerate-numeric>
      <item>There exists a <em|finite> limit

      <\equation*>
        <big|int><rsub|\<Omega\>>X\<mathd\>P=lim<rsub|n\<rightarrow\>\<infty\>><big|int><rsub|\<Omega\>>X<rsub|n>\<mathd\>P.
      </equation*>

      <item>This limit does not depend on the choice of the approximating
      system.
    </enumerate-numeric>
  </lemma>

  If <with|mode|math|X> is a random variable
  <with|mode|math|X:\<Omega\>\<rightarrow\>\<bbb-R\><rsup|n>>. Let
  <with|mode|math|\<cal-B\>> be Borel's <with|mode|math|\<sigma\>>-algebra on
  <with|mode|math|\<bbb-R\><rsup|n>>. Then

  <\equation*>
    \<mu\><rsub|X>(<wide*|A|\<wide-underbrace\>><rsub|\<in\>\<cal-B\>>)=P(X<rsup|-1>(A))=P(\<omega\>:X(\<omega\>)\<in\>A)
  </equation*>

  is called the <em|distribution function> of <with|mode|math|X>.

  <\theorem>
    <\equation*>
      <big|int><rsub|\<Omega\>>f(X)\<mathd\>P=<big|int><rsub|\<bbb-R\><rsup|n>>f(x)\<mu\><rsub|X>(\<mathd\>x).
    </equation*>

    Thus

    <\equation*>
      E[X]=<big|int><rsub|\<bbb-R\><rsup|n>>X\<mu\><rsub|X>(\<mathd\>X).
    </equation*>
  </theorem>

  <\example>
    Let <with|mode|math|X> have values <with|mode|math|x<rsub|1>,\<ldots\>,x<rsub|n>>.
    <with|mode|math|\<Omega\><rsub|i>=X<rsup|-1>(x<rsub|i>).>
    <with|mode|math|\<mu\><rsub|X>(x<rsub|i>)=P(\<Omega\><rsub|i>)>. Then

    <\equation*>
      E[X]=<big|sum>x<rsub|i>\<mu\><rsub|X>(x<rsub|i>)=<big|sum>x<rsub|i>P(\<Omega\><rsub|i>).
    </equation*>
  </example>

  <subsection|Conditional Expectation>

  <with|mode|math|\<xi\>> and <with|mode|math|\<eta\>> are are random
  variables with a joint density <with|mode|math|p(x,y)>.

  <em|Motivation:>

  <\equation*>
    E[\<xi\>\|\<eta\>=y]=<big|int>x*p(x\|y)\<mathd\>x.
  </equation*>

  <\equation*>
    P(A\|B)=<frac|P(A\<cap\>B)|P(B)>.
  </equation*>

  Now suppose <with|mode|math|X> is a <with|mode|math|P>-integrable random
  variable <with|mode|math|(\<Omega\>,\<cal-F\>,P)>. <with|mode|math|G> is a
  <with|mode|math|\<sigma\>>-algebra on <with|mode|math|\<Omega\>>,
  <with|mode|math|\<cal-G\>\<subset\>\<cal-F\>>.

  <\definition>
    Let <with|mode|math|\<eta\>> be <with|mode|math|\<cal-F\>>-measurable
    random variable. If there exists a <with|mode|math|P>-integrable
    <with|mode|math|\<cal-G\>>-measurable function <with|mode|math|\<xi\>>
    such that for any bounded <with|mode|math|\<cal-G\>>-measurable function
    <with|mode|math|\<varphi\>>

    <\equation*>
      E(\<xi\>\<varphi\>)=E(\<eta\>\<varphi\>),
    </equation*>

    the <with|mode|math|\<xi\>> will be called <em|conditional expectation>
    of <with|mode|math|\<eta\>> and denoted
    <with|mode|math|E[\<eta\>\|\<cal-G\>]>.
  </definition>

  Properties of conditional expectation:

  <\enumerate-numeric>
    <item>If <with|mode|math|\<eta\>> is <with|mode|math|\<cal-G\>>-measurable,
    then <with|mode|math|E[\<eta\>\|\<cal-G\>]=\<eta\>>.

    <\proof>
      (1) By assumption, <with|mode|math|\<eta\>> is
      <with|mode|math|\<cal-G\>>-measurable. (2) Let
      <with|mode|math|\<varphi\>> be an arbitrary
      <with|mode|math|\<cal-G\>>-measurable function. Then

      <\equation*>
        E(\<eta\>\<varphi\>)=E(E(\<eta\>\|\<cal-G\>)\<varphi\>)=E(\<eta\>\<varphi\>).
      </equation*>
    </proof>

    <item><with|color|orange|HW:> Prove that the conditional expectation is
    unique.

    <item>If <with|mode|math|f> is bounded,
    <with|mode|math|\<cal-G\>>-measurable, then

    <\equation*>
      E[f(\<omega\>)X\|\<cal-G\>](\<omega\>)=f*(\<omega\>)E[X\|\<cal-G\>]<space|1em>(<with|mode|text|a.s.>)
    </equation*>

    <item>Let <with|mode|math|g(\<omega\>,X)> be an
    <with|mode|math|\<cal-F\>>-measurable function. Then

    <\equation*>
      E[g(\<omega\>,X)\|\<sigma\>(X)]=E[g(\<omega\>,c)\|\<sigma\>(X)]\|<rsub|c=X>.
    </equation*>

    <item>Let <with|mode|math|\<cal-G\><rsub|1>\<subset\>\<cal-G\>> be
    <with|mode|math|\<sigma\>>-algebras. Then

    <\equation*>
      E[E[X\|\<cal-G\>]\|\<cal-G\><rsub|1>]=E[X\|\<cal-G\><rsub|1>].
    </equation*>

    This property can be memorized as ``Small eats big''.
  </enumerate-numeric>

  <\example>
    <with|mode|math|\<Omega\>=<big|cup><rsub|n>\<Omega\><rsub|n>>,
    <with|mode|math|\<Omega\><rsub|i>\<cap\>\<Omega\><rsub|j>=\<varnothing\>>.
    Let <with|mode|math|\<cal-E\>={\<Omega\><rsub|1>,\<Omega\><rsub|2>,\<ldots\>}>.
    Then <with|mode|math|\<sigma\>(\<cal-E\>)={\<Omega\><rsub|i<rsub|1>>\<cup\>\<Omega\><rsub|i<rsub|2>>\<cup\>\<ldots\>}>.
    <with|mode|math|\<Omega\><rsub|0>=<with|color|red|\<Omega\>\<setminus\>\<Omega\>>?>.
    Let <with|mode|math|\<xi\>> be a random variable

    <\equation>
      <label|eq:ce-example-exp>E[\<xi\>\|\<sigma\>(\<cal-E\>)]=<big|sum><rsub|i><frac|E[\<xi\>\<b-1\><rsub|\<Omega\><rsub|i>>]|P(\<Omega\><rsub|i>)>\<b-1\><rsub|\<Omega\><rsub|i>>.
    </equation>

    Proof of (<reference|eq:ce-example-exp>):

    <\enumerate-alpha>
      <item>The right-hand side is a function of indicators of
      <with|mode|math|\<Omega\><rsub|i>><with|mode|math|\<Rightarrow\>>it is
      <with|mode|math|\<sigma\>(\<cal-E\>)>-measurable.

      <item><with|mode|math|E<left|[>E[\<xi\>\|\<sigma\>(\<cal-E\>)]g]=E\<xi\>g>
      for all <with|mode|math|g> which are
      <with|mode|math|\<sigma\>(\<cal-E\>)>-measurable.

      Suppose <with|mode|math|g=1<rsub|\<Omega\><rsub|k>>>. Then

      <\equation*>
        E[rhs*\<b-1\><rsub|\<Omega\><rsub|k>>]=E<left|[><frac|E[\<xi\>\<b-1\><rsub|\<Omega\>k>]|P(\<Omega\><rsub|k>)>\<b-1\><rsub|\<Omega\><rsub|k>><right|]>=<frac|E[\<xi\>\<b-1\><rsub|\<Omega\><rsub|k>>]|<neg|P(\<Omega\><rsub|k>)>><neg|P(\<Omega\><rsub|k>)>=E(\<xi\>\<b-1\><rsub|\<Omega\><rsub|k>>).
      </equation*>

      rhs: <with|mode|math|E(\<xi\>\<b-1\><rsub|\<Omega\><rsub|k>>)>. What is
      a <with|mode|math|\<sigma\>(\<cal-E\>)>-measurable function? Answer: It
      is a function of the form

      <\equation*>
        \<xi\>=<big|sum><rsub|i>y<rsub|i>\<b-1\><rsub|\<Omega\><rsub|i>>.
      </equation*>

      <with|color|red|What?>
    </enumerate-alpha>
  </example>

  <subsection|Stochastic Processes>

  Assume that for all <with|mode|math|t>, we are given a random variable
  <with|mode|math|X<rsub|t>=X<rsub|t>(\<omega\>)\<in\>\<bbb-R\><rsup|n>>.
  <with|mode|math|t> could be from <with|mode|math|{0,1,2,3,\<ldots\>}> or
  from <with|mode|math|(a,b)>, it does not matter. In the former case,
  <with|mode|math|X<rsub|t>> is called a sequence of r.v. or a discrete time
  stochastic process. In the latter, it is called a continuous time
  stochastic process. If <with|mode|math|t\<in\>\<bbb-R\><rsup|2>>, then
  <with|mode|math|X<rsub|t>> is a two-parameter random field.

  <em|Motivation:> If <with|mode|math|X> is a random variable,
  <with|mode|math|\<mu\><rsub|X>(A)=P(\<omega\>:X(\<omega\>)\<in\>A>.

  <\definition>
    The (finite-dimensional) distribution of the stochastic process
    <with|mode|math|(X<rsub|t>)<rsub|t\<in\>T>> are the measures defined on
    <with|mode|math|\<bbb-R\><rsup|n*k>=\<bbb-R\><rsup|n>\<otimes\>\<cdots\>\<bbb-R\><rsup|n>>
    given by

    <\equation*>
      \<mu\><rsub|t<rsub|1>,\<ldots\>,t<rsub|k>>(F<rsub|1>\<otimes\>F<rsub|2>\<otimes\>\<cdots\>\<otimes\>F<rsub|k>)=P(\<omega\>:X<rsub|t<rsub|1>>\<in\>F<rsub|1>,\<ldots\>,X<rsub|t<rsub|k>>\<in\>F<rsub|k>),
    </equation*>

    where the <with|mode|math|F<rsub|i>\<in\>\<cal-B\>(\<bbb-R\><rsup|n>)>.
  </definition>

  <subsection|Brownian Motion (Wiener Processes)>

  <\definition>
    A real-valued process <with|mode|math|X<rsub|t>> is called Gaussian if
    its finite dimensional distributions are
    Gaussian<with|mode|math|\<Leftrightarrow\>><with|mode|math|(X<rsub|t<rsub|1>>,\<ldots\>,X<rsub|t<rsub|k>>)\<sim\>\<cal-N\>(k)>.
  </definition>

  Remember: A random variable <with|mode|math|\<xi\>> in
  <with|mode|math|\<bbb-R\><rsup|k>> is called <em|normal (multinormal)> if
  there exists a vector <with|mode|math|m\<in\>\<bbb-R\><rsup|k>> and a
  symmetric non-negative <with|mode|math|k\<times\>k>-matrix
  <with|mode|math|R=(R<rsub|i j>)> such that

  <\equation*>
    \<varphi\>(\<lambda\>)\<assign\>E[e<rsup|i(\<xi\>,\<lambda\>)>]=e<rsup|i(m,\<lambda\>)-(R\<lambda\>,\<lambda\>)/2>
  </equation*>

  for all <with|mode|math|\<lambda\>\<in\>\<bbb-R\><rsup|k>>, where
  <with|mode|math|(\<cdot\>,\<cdot\>)> represents an inner product,
  <with|mode|math|m=E[\<xi\>]> and <with|mode|math|R=cov(\<xi\><rsub|i>,\<xi\><rsub|j>)>.

  <em|Independence:> Fact: <with|mode|math|Y=(Y<rsub|1>,\<ldots\>,Y<rsub|n>)>
  are normal vectors in <with|mode|math|\<bbb-R\><rsup|k>> with
  <with|mode|math|(m<rsub|i>,R<rsub|i>)>. Then elements of <with|mode|math|Y>
  are independent iff

  <\equation*>
    \<varphi\><rsub|\<lambda\>>(Y)=<big|prod><rsub|i=1><rsup|n>\<varphi\><rsub|\<lambda\><rsub|i>>(Y<rsub|i>),
  </equation*>

  where <with|mode|math|\<lambda\>=(\<lambda\><rsub|1>,\<ldots\>,\<lambda\><rsub|n>)>,
  where <with|mode|math|\<lambda\><rsub|i>\<in\>\<bbb-R\><rsup|n>>.

  Fact 2: <with|mode|math|\<zeta\>=(\<zeta\><rsub|1>,\<ldots\>,\<zeta\><rsub|m>)>
  is Gaussian iff for any <with|mode|math|\<lambda\>\<in\>\<bbb-R\><rsup|m>>,

  <\equation*>
    (\<zeta\>,\<lambda\>)=<big|sum>\<lambda\><rsub|i>\<zeta\><rsub|i>
  </equation*>

  is Gaussian in 1D.

  <\definition>
    Brownian motion <with|mode|math|W<rsub|t>> is a one-dimensional
    continuous Gaussian process with

    <\equation*>
      E[W<rsub|t>]=0,<space|1em>E[W<rsub|t>W<rsub|s>]=t\<wedge\>s\<assign\>min(t,s).
    </equation*>
  </definition>

  Alternative Definition:

  <\definition>
    <label|def:bm-def2>Brownian motion <with|mode|math|W<rsub|t>> is a
    Brownian motion iff

    <\enumerate>
      <item><with|mode|math|W<rsub|0>=0>

      <item><with|mode|math|><with|mode|math|\<forall\>t,s:W<rsub|t>-W<rsub|s>\<sim\>\<cal-N\>(0,t-s)>

      <item><with|mode|math|W<rsub|t<rsub|1>>>,
      <with|mode|math|W<rsub|t<rsub|2>>-W<rsub|t<rsub|1>>,\<ldots\>> are
      independent for all partitions <with|mode|math|t<rsub|1>\<less\>t<rsub|2>\<less\>t<rsub|3>\<less\>\<cdots\>>.
    </enumerate>
  </definition>

  Yet another:

  <\definition>
    The property (3) in Definition <reference|def:bm-def2> may be replaced by

    3<with|mode|math|<rprime|'>>. <with|mode|math|W<rsub|t<rsub|n>>-W<rsub|t<rsub|n-1>>>
    is independent of <with|mode|math|W<rsub|t<rsub|n-1>>-W<rsub|t<rsub|n-2>>>,<with|mode|math|\<ldots\>>
  </definition>

  <\definition>
    <\equation*>
      \<cal-F\><rsub|t><rsup|W>\<assign\>\<sigma\>({W<rsub|s<rsub|1>>,W<rsub|s<rsub|2>>,\<ldots\>:s<rsub|i>\<leqslant\>t}).
    </equation*>
  </definition>

  <\theorem>
    Brownian motion is a <em|martingale> w.r.t.
    <with|mode|math|\<cal-F\><rsub|t><rsup|W>><with|mode|math|\<Leftrightarrow\>>

    <\equation*>
      E[W<rsub|t>\|\<cal-F\><rsub|s><rsup|W>]=W<rsub|s>
    </equation*>

    for <with|mode|math|s\<less\>t>. (This is also the definition of a
    martingale.)
  </theorem>

  <\remark>
    <with|mode|math|\<sigma\>(W<rsub|t<rsub|1>>,W<rsub|t<rsub|2>>,\<ldots\>,W<rsub|t<rsub|n>>)=\<sigma\>(W<rsub|t<rsub|1>>,W<rsub|t<rsub|2>>-W<rsub|t<rsub|1>>,\<ldots\>,W<rsub|t<rsub|n>>-W<rsub|t<rsub|n-1>>)>
    (knowledge of one gives the other--add or subtract). This is important
    because RHS is independent, but LHS is not.
  </remark>

  <\corollary>
    \;

    <\enumerate>
      <item><with|mode|math|E[W<rsub|t><rsup|2>]=t>. (So
      <with|mode|math|W<rsub|t>> grows roughly as <with|mode|math|<sqrt|t>>.)

      <item><with|mode|math|W<rsub|t><rsup|2>/t\<rightarrow\>0> almost
      surely.

      Proof: By Chebyshev's inequality, <with|mode|math|P(\|W<rsub|t>/t\|\<gtr\>c)\<less\>E[\|W<rsub|t>/t\|<rsup|2>]/c<rsup|2>=t/t<rsup|2>c<rsup|2>\<rightarrow\>0>
      as <with|mode|math|t\<rightarrow\>\<infty\>>.
    </enumerate>
  </corollary>

  <em|Law of iterated logarithm:>\ 

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<varphi\><rsub|t><rsup|0>=<frac|W<rsub|t>|<sqrt|2t*log
    log(1/t)>>,>|<cell|>|<cell|\<varphi\><rsub|t><rsup|\<infty\>>=<frac|W<rsub|t>|<sqrt|2t
    log log(t)>>,>>|<row|<cell|limsup<rsub|t\<rightarrow\>0>\<varphi\><rsub|t><rsup|0>=1,>|<cell|>|<cell|limsup<rsub|t\<rightarrow\>\<infty\>>\<varphi\><rsub|t><rsup|\<infty\>>=1,>>|<row|<cell|liminf<rsub|t\<rightarrow\>0>
    \<varphi\><rsub|t><rsup|0>=-1,>|<cell|>|<cell|liminf<rsub|t\<rightarrow\>\<infty\>>
    \<varphi\><rsub|t><rsup|\<infty\>>=-1.>>>>
  </eqnarray*>

  <em|Continuity and Differentiability:>

  <\itemize>
    <item><with|mode|math|W<rsub|t>> is continuous.

    <item><with|mode|math|W<rsub|t>> is nowhere differentiable.
  </itemize>

  <em|Spectral representation of Brownian motion:>

  <\theorem>
    \;

    <\eqnarray*>
      <tformat|<table|<row|<cell|W<rsub|t>>|<cell|=>|<cell|t\<eta\><rsub|0>+<big|sum><rsub|n=1><rsup|\<infty\>>\<eta\><rsub|n>sin(n*t)\<approx\>t*\<eta\><rsub|0>+<big|sum><rsub|n=1><rsup|N>\<eta\><rsub|n>sin(n*t),<space|1em><with|mode|text|where>>>|<row|<cell|\<eta\><rsub|n>>|<cell|\<sim\>>|<cell|\<cal-N\>(0,2/\<pi\>n<rsup|2>)
      <space|1em>(n\<geqslant\>1),>>|<row|<cell|\<eta\><rsub|0>>|<cell|\<sim\>>|<cell|\<cal-N\>(0,1/\<pi\>).>>>>
    </eqnarray*>
  </theorem>

  <\proof>
    Consider <with|mode|math|t\<in\>[0,\<pi\>]>.

    <\equation*>
      <wide|W<rsub|>|~><rsub|t>\<assign\>W<rsub|t>-<frac|t|\<pi\>>W<rsub|\<pi\>><space|1em><with|mode|text|for
      <with|mode|math|t\<in\>[0,\<pi\>]>>.
    </equation*>

    Then

    <\equation*>
      <wide|W|~>(t)=<big|sum><rsub|n=1><rsup|\<infty\>>\<eta\><rsub|n>sin(n*t),
    </equation*>

    where

    <\equation*>
      \<eta\><rsub|n>=<frac|2|\<pi\>><big|int><rsub|0><rsup|\<pi\>><wide|W|~>(t)sin(n*t)\<mathd\>t<space|1em>(n\<gtr\>0)
    </equation*>

    and

    <\equation*>
      \<eta\><rsub|0>=<frac|W(\<pi\>)|\<pi\>>.
    </equation*>

    First fact: <with|mode|math|\<eta\><rsub|n>> are Gaussian because linear
    combinations of normal r.v.s. are normal.

    <\equation*>
      E\<eta\><rsub|k>\<eta\><rsub|n>=<frac|4|\<pi\><rsup|2>><big|int><rsub|0><rsup|\<pi\>><big|int><rsub|0><rsup|\<pi\>>(t\<wedge\>s-t*s/\<pi\>)sin(<with|color|red|n*t?>)sin(k*s)=<choice|<tformat|<table|<row|<cell|0>|<cell|k\<neq\>n,>>|<row|<cell|<frac|2|\<pi\>n<rsup|2>>>|<cell|k=n\<gtr\>0.>>>>>
    </equation*>

    For <with|mode|math|n=0>,

    <\equation*>
      E[\<eta\><rsub|0><rsup|2>]=E<frac|W<rsup|2>[\<pi\>]|\<pi\><rsup|2>>=<frac|1|\<pi\>>.
    </equation*>

    \;
  </proof>

  <\equation*>
    \;
  </equation*>
</body>

<\initial>
  <\collection>
    <associate|page-type|letter>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-2|<tuple|1.1|2>>
    <associate|auto-3|<tuple|1.2|3>>
    <associate|auto-4|<tuple|1.3|4>>
    <associate|auto-5|<tuple|1.4|4>>
    <associate|def:bm-def2|<tuple|1.18|4>>
    <associate|eq:ce-example-exp|<tuple|1.1|3>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Basic
      Facts from Stochastic Processes> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|1.1<space|2spc>Lebesgue Integral
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1.5fn>|1.2<space|2spc>Conditional Expectation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1.5fn>|1.3<space|2spc>Stochastic Processes
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1.5fn>|1.4<space|2spc>Brownian Motion (Wiener
      Processes) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>
    </associate>
  </collection>
</auxiliary>