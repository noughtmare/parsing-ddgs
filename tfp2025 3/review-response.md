> Thank you for your submission to the TFP post-proceedings. I am delighted to inform you that your paper has been accepted. I hope you find the reviews helpful in making final revisions. Please complete these by Weds 16th April. If you need an extra page or two, that's fine.
> 
> ----------------
>  REPORT
> ----------------
> 
> ## Synopsis
> 
> This paper describes parsers for a (subset of) context free languages,
> implemented in Agda, inspired by Elliott's recent work in this
> direction. The major hurdle to overcome is establishing such parsers are
> structurally recursive. The solution, as is used more widely in parsing
> of regular expressions, is to compute the derivative of a context free
> grammar -- and then perform induction on the input string.
> 
> ## Review
> 
> The paper is much improved from the submitted version. It now gives a
> fairly clean account of parsing using derivatives. Even though not all
> context free languages can be parsed in this fashion -- it is entirely
> plausible that this approach can be scaled to handle them. The main
> result, the correct parser in section 3.3 gives an extremely clean
> treatment of recursion.
> 
> I would like to offer a few suggestions on how the presentation and
> material may be improved.
> 
> ### Major suggestions
> 
> * I found the terminology used by the paper a bit confusing at
>  times. Languages are String -> Set; parsers decide languages – so much
>  is clear. But there is an (implicit) mix of (data) types and parsers -
>  why else would you want to have operations such as · operation in your
>  languages used? Similarly, the fragment of context free grammars
>  introduced in section 3 is called 'Desc' (suggesting it is a
>  description of a data type) – where I would expect this to be a (deep
>  embedding of a fragment of) context free grammars.

Done (kind of): State somewhere that grammars and data types are tightly connected.

NO_TIME: See if an example of naive ambiguous expressions could show the usefulness
of the scalar multiplication operation. I think it will show that the scalar
multiplication operation means that we can preserve the number of solutions. So
the type of parse results will be isomorphic to the abstract syntax type
data `Tree = X | Bin Tree Tree`. We don't always preserve the number of
solutions but that is only when infinite (unproductive) derivation trees are
involved as those are hard to even specify. We leave finding a more principled
approach to future work.

Sketch: data types are not that much different from grammars. Both are initial
algebras of endofunctors. The difference is the category on which they are
defined. I think it would be good to state this explicitly somewhere early on in
the paper.

Also, we should explain that we use fairly rigid terminology when we say
'languages', 'grammars', and 'parsers'. A *language* is an abstract concept that
can be described concretely in various ways, traditionally: by a set of strings,
by a grammar, by an automaton, etc. We stretch this definition somewhat with our
type theoretic approach. Instead of a set of strings (a function from strings to bool), we consider a function from strings to types to be a concrete representation of a language. The crucial difference is that a string can now be
"in" a language in multiple distinct ways, allowing us to model ambiguity.

Traditionally, a *grammar* is a list of nonterminals and collection of rewrite 
rules from the nonterminals to lists of nonterminals and terminals. A grammar
defines a language, namely the set of all strings (lists of nonterminals)
reachable by applying rewrite rules starting from a designated the starting
nonterminal. Note that grammars have more structure than languages. For example,
a string can be generated by a grammar in multiple different ways. Our type
theoretic definition of language correlates, in that respect, more directly to
traditional grammars. 
However, in this paper we define grammars in a slightly different way. We use an
algebraic/expression based definition ...

A *parser* is usually defined as a function from strings to booleans in theory
or a program which turns a string into a parse tree in practice.


> * One of the main technical contributions of the paper is the treatment
>  of the recursion and derivatives. To compute the derivative, there is
>  an additional mu constructor, introducing an indirection to
>  distinguish between the original language and the recursive calls to
>  the newly computed derivative. Given that the paper is mostly
>  interested in parsing, one might wonder if the indirection is strictly
>  necessary: couldn't the intended semantics (i.e. recursive call to the
>  derivative function of the _original_ grammar) not be passed as an
>  argument to δ₀? If this isn't the case, it might be worth
>  explaining/motivating why the direct solution does not work - I could
>  imagine it causes problems for the termination checker, for instance.

I don't understand the suggestion, actually. We use the mu to preserve
the original grammar, so passing the derivative of that to `δ₀` does not
help us. We cannot reconstruct the original grammar from the derivative of it.

The only way we might hope to avoid `mu` is if we take a more
big-step/recursive descent approach with memoization, then it might be possible.
We could explain this in the discussion of possible future work.


> ### Minor suggestions and clarifications
> 
> * Remark 2 : (either here or in the future work) – what changes would be
>  necessary to enumerate all parse trees?

One of the main difficulties is that our nullability correctness theorem is
not a one-to-one equivalence. We intentionally exclude parses which take 
unproductive recursive iterations.

Furthermore, I don't think ambiguous grammars are useful in practice (in CS), so
our effort would be better spent developing better tools to check and prove
that our languages are not ambiguous, avoiding the whole issue of having
multiple parse trees.

> * One important reason for separating out nullability and derivatives is
>  that it becomes possible to define the parser by induction on the
>  input string. Otherwise, it is not so clear that parsing will
>  terminate at all – and often does not. I'd suggest clarifying this
>  point halfway through page 6.

Good point. Although, this is not obvious. I need some time to think about this.
Also, this is strongly related to your second major suggestion. If 

> * Another reason to avoid · would be that it makes the Desc type
>  large... Removing it would allow Desc to live in Set - unless there
>  are particular applications, but these are not given in the paper.

The · is necessary for the derivative of sequencing of grammars. Well, you
could possibly replace is by a Sigma type, perhaps? Let me think about that.
We also use it in the derivative of characters, but that is easier to replace.

I don't think `Desc` being large is a problem at all. You could also define your
own closed universe of types if you really want to keep `Desc` small.

> * I found the ⋄ notation rather confusing... Is it worthwhile? The
>  definitions are not so long - why not inline them when introducing the
>  semantics of Desc?

It is clear that I at least need to spend some more time explaining ⋄.

> * The fixpoint operation on Desc to produce a Lang is not the standard
>  one - presumably because you want to define a predicate on strings
>  rather than a Set. Given that this is a key contribution - perhaps it
>  worth explaining a bit better.

The fixed point is really not that much different from the normal fixed point.
The only difference is that it passes along the input string `w`. I could try
to spend a paragraph explaining that.

I would like to say that this is the normal fixed point - just in a different
category - but I don't think that translates directly to this Agda definition.

I do wonder if there is a simple way to show that this fixed point is equivalent
to the standard fixed point.

> * I am not sure that the limitation mentioned just before section 3.2 is
>  not so much related to nesting of languages, but rather due to only
>  having a single recursive variable...

The limitation is about nesting. How can it then not be related to nesting?
There is a second limitation that mutual recursion is not possible which is
because we only have a single variable. I should make those two more
clear in the paper. Our mu fixes the nesting problem, but still does not allow
mutual recursion.

> * I am not entirely convinced by the nu-notation for nullability. The
>  same notation is also used for the greatest fixpoint of a
>  functor. Given that the paper also uses the (standard) mu notation for
>  the least fixpoint, perhaps it might be more clear to write empty (or
>  something along these lines).

DONE: The `ν` notation is quite standard. Perhaps we could explain where we got it
from. Brzozowski originally used delta-zero, but I already use that for a
different purpose and I think that would also be similarly confusing.

> * There is quite some work on (generic programming with) fixpoints of
>  indexed functors or mutually recursive families of datatypes. Citing
>  this as an avenue for further work might help substantiate the
>  argument that these ideas can be extended to handle richer grammars.

DONE: Yes, in the discussion on expressiveness we should cite indexed data type
descriptions and how they can be used to model mutually recursive data types.
That work does port over directly to our grammars. However, I did not manage to
finish all the proofs yet, because the indexing makes them quite a bit more
complicated.

> ### Typos
> 
> * book-keeping -> bookkeeping
> 
> * a program which can prove for us -> proves whether or not ...
> 
> * condintional -> conditional
> 
> * 'Most practical programming languages' and 'Many practical programming languages' - repitition.
> 
> * allowed to take the fixpoint of -> of which we are allowed to take the
>  fixpoint (never end a sentence with a proposition).
> * D But (missing punctuation mark)
> * Hocroft -> Hopcroft
> 
> * Danielsson and Anders -> Danielsson
> 
> 
> ----------------
>  REPORT
> ----------------
> 
> This paper formalizes derivative-based parsing for context-free
> grammars with the restriction that there are no mutual recursions
> (i.e., the number of nonterminal is at most one).
> 
> I have a mixed attitude about the paper. On the one hand, since the
> formalization of derivative-based parsing for CFG itself is new, this
> work would be worth to be published in TFP. On the other hand, since
> the technical difficulty of handling derivative-based parsing for
> context-free grammars lies only in the treatment of nonterminals,
> having the restriction on it is a limitation.
> 
> Let me first explain my understanding to assess the limitation. In my
> understanding, the starting point of Might+ 2011 is symbolic
> derivation of both sides of rules, where the derivation of a
> nonterminal is treated as a new nonterminal. For example, consider the
> grammar in p3. From <expr> ::= <expr> + <expr> | 0 | 1 | <stmt>, we
> have
> 
>    d0 <expr> ::= (d0 <expr>) + <expr> | ε | d0 <stmt>
> 
> because we have
> 
>    d0 RHS
>    = d0 (<expr> + <expr> | 0 | 1 | <stmt>)
>    = d0 (<expr> + <expr>) | d0 0 | d0 1 | d0 <stmt>
>    = d0 <expr> + <expr> | ε | ∅ | d0 <stmt>
>    = (d0 <expr>) + <expr> | ε | d0 <stmt>
> 
> Also, from <stmt> ::= <expr> | <stmt> ; <stmt>, we have
> 
>    d0 <stmt> ::= d0 <expr> | (d0 <stmt>) ; <stmt>
> 
> because we have:
> 
>    d0 RHS
>    = d0 (<expr> | <stmt> ; <stmt>)
>    = d0 <expr> | d0 (<stmt> ; <stmt>)
>    = d0 <expr> | (d0 <stmt>) ; <stmt>
> 
> Here, we used the fact that neither <expr> nor <stmt> is
> nullable.
> 
> As this example demonstrates, essentially, the treatment of
> concatenation, choice, empty string, and terminals is nothing
> different from the regular-expression case. Hence, the only difficulty
> lies in the treatment of nonterminals. (Actually, this is highlighted
> in the definition of ⟦_⟧ₒ and its treatment.) As we treat a derivative
> of a nonterminal as a new nonterminal, a derivative of a grammar may
> have twice the number of nonterminals of the original one.
> 
> In a pen-and-paper proof, I expect the correctness of a derivation of
> a grammar would be proved by using the following three steps.
> 
>  1. Correctness of nullability test
> 
>  2. Preservation of the languages of kept nonterminals (such as
>     <expr> and <stml> in the derived grammar)
> 
>  3. The language of a derived nonterminal is indeed a derivative
>     (left quotient) of the language of an original one.
> 
> (Maybe, the Steps 2 and 3 can be proved simultaneously using induction
> on production.) In this paper, Steps 1 and 3 are proved by induction
> on a grammar structure and Step 2 is avoided by having μ.
> 
> I suspect that what will be complicated most by allowing mutual
> recursions (or more than one nonterminal) would be Step 1 because it
> would require at least as many unfoldings as the number of
> nonterminals. In contrast, I may think that Steps 2 and 3 would not
> get so complicated.
> 
> Considering these points, whether I should think of the limitation as
> a severe one or a simplification depends on whether I should think the
> correctness of the nullability test is a core part of the
> derivative-based parsing. I think that there are different standing
> points about this. Some may say that nullability is a common concern
> with CFGs and thus not specific to the derivative-based
> parsing. Others may say that it must be in the core part as the
> derivative-based parsing heavily relies on nullability checks.
> 
> Eventually, I have found the following paper, which involves the
> correctness of the nullability check as a part of their formalization
> (I don't know whether it is the first one).
> 
>    Denis Firsov, Tarmo Uustalu: Certified normalization of context-free
>    grammars, CPP 2015. https://dl.acm.org/doi/10.1145/2676724.2693177
> 
> This means, the correctness of nullability check cannot be a
> contribution by itself. So, I think the authors can state that the
> restriction is a simplification by citing such a paper, clarifying the
> standing point. However, at the same time, I also think that, since we
> can rely on such results for the correctness of the nullability check,
> the authors can support mutual recursion with reasonable effort.
> 
> In conclusion, putting these points in consideration, my evaluation of
> this paper is in-between 0 and 1. I am slightly positive but not that
> positive to score 1. 

Not done: We should add that paper to the related work section, it will be similar
to the paper on the left-corner transformation. We should list the differences
and how it presents an alternative approach that we could have drawn inspiration
from for how to extend our approach.

Edit: I don't actually think that paper is that relevant, because it is only
concerned with normalization of grammars. It uses a traditional representation
of grammars as a list of production rules. I don't know how much of their
results can transfer over to our representation.

Not done after all: Additionally, we should clarify that none of the theorems or their formalization
are novel. Instead, our approach is novel and useful because it is simpler and
more direct than traditional approaches (our code is roughly one tenth of the
size of Firsov and Uustalu's code: ~400 vs. 4159 lines).

> To improve the paper's presentation, I suggest
> the authors to consider showing the picture of the formalization:
> especially, what is the core idea of the derivation of context-free
> grammars and what will be the point in proving its correctness.

Kind of done: We could try to give a better high level overview of the proof.

> Also,
> please consider citing the above paper to justify your restriction on
> grammars. 

Not done: read and cite the paper

> In addition, I would strongly suggest that the author change
> the title, because the present paper is not the first one that shows
> mechanized formalization of context-free grammars.

DONE

> 
> ## Individual Comments
> 
> p1. "new research continuously emerge". To support this, it would be
> better to cite more recent papers in addition. The latest paper cited
> in this paragraph is published in 2015.

Done

Perhaps:
* Fusing lexing and parsing: https://dl.acm.org/doi/abs/10.1145/3591269
* SGLR modularity: https://repository.tudelft.nl/file/File_7cb9b919-e018-47c3-9fbe-c83247d78c23
* Partial parsing (Hazel-like): https://dl.acm.org/doi/abs/10.1145/3567512.3567522
* Parameterized nonterminals in Happy: https://arxiv.org/abs/2303.08044
* From EVCS, Jurgen's and Eric's papers?

> p2. "<pal> ::= 0 | 1 | 0 <pal> 0 | 1 <pal> 1". Reading the following
> discussions, I suspect that the production of ϵ is missing and the
> correct one should be:
> 
>    <pal> ::= ϵ | 0 | 1 | 0 <pal> 0 | 1 <pal> 1


DONE


> p2. "The idea of automatic differentiation." I would feel that the
> idea here would be more similar to symbolic differentiation.

DONE

> p3. "... the recursive unfolding we performed ..." However, I don't
> think there is an issue in symbolic treatment, which can derive the
> grammar (d0 <rec>) ::= (d0 <rec>) from <rec> ::= <rec>. Both are valid
> CFGs.

I have clarified that we explain a naive derivation producedure based on recursive unfolding in this section. 

> p3. "Another challenge ... is how to encode their recursive nature." I
> suspect this is still a challenge, because we already have a number of
> existing approaches of mechanized formalization of CFGs. Also, we can
> use a general technique that works for general DSLs, such as de Bruijn
> index and parametric HOAS.
> 
> This is in Haskell, but the following paper discusses CFGs represented
> by using de Bruijn index:
> 
>    Arthur Baars, S. Doaitse Swierstra, Marcos Viera: Typed
>    Transformations of Typed Grammars: The Left Corner Transform.
>    ENTCS 253 (7), 2010.  https://eur03.safelinks.protection.outlook.com/?url=https%3A%2F%2Fdoi.org%2F10.1016%2Fj.entcs.2010.08.031&data=05%7C02%7Cj.s.reinders%40tudelft.nl%7C4020b24233f24d08a73f08dd6c64e624%7C096e524d692940308cd38ab42de0887b%7C0%7C0%7C638785902816949725%7CUnknown%7CTWFpbGZsb3d8eyJFbXB0eU1hcGkiOnRydWUsIlYiOiIwLjAuMDAwMCIsIlAiOiJXaW4zMiIsIkFOIjoiTWFpbCIsIldUIjoyfQ%3D%3D%7C0%7C%7C%7C&sdata=knSvdZ8cwmqrVnAbyGZJFQk4MThzcmaUZ6bV5Q3xWbw%3D&reserved=0

I have simply removed this paragraph, because I don't think it is relevant.

> p6. Explain "Dec.map" and "mk⇔".

DONE

> p10. "... we have learned the following three lessons." I suspect that
> at least the first two of the three lessons can be obtained
> straightforwardly from the existing results.

Done: I've rewritten this to make it clearer that these are not necessarily contributions of this paper. 

> p15 "His work does cover mutually recursive nonterminals ..." He is
> discussing μ-regular expressions, which is not mutually recursive,
> whereas their languages are the same as the ones of CFGs.

DONE: μ-regular expressions can be mutually recursive. For example, the expr-stmt example in our introduction can be written like this:

expr = μ (\expr -> expr '+' expr | 0 | 1 | μ (\stmt -> expr | stmt * ';' * stmt))

We should perhaps make this clear in the discussion section

"he supports mu regular expressions without the restrictions of our approach which allows him to encode context free grammars with mutually recursive nonterminals."

> p15. "... parsing is only the boolean ..." I think that this applies
> also to the proposed approach.

DONE: Our approach constructs a full parse tree. We do indeed produce only (at
most) a single parse tree and not all possible parse trees, but that does not
mean we only produce a boolean.

How can we explain this more clearly?

> p15. What are "μ-regular languages"? Anyway, I suspect that at least
> [13] discuss CFGs.

Done: Indeed, we should explain clearly somewhere what μ-regular expressions are
and how they relate to context-free languages/grammars.
Probably in the introduction.

> p16. "... we have formalized (acyclic) context-free grammars ...". In
> my understanding, the proposed approach can handle cyclic ones like
> <rec> ::= <rec>.

Done: we have replaced 'acyclic' with 'non mutually recursive'

> ----------------
>  REPORT
> ----------------
> 
> As it says on the tin, this paper addresses treating context free languages within a type-theoretic framework. Authors extend on existing work in formal languages mechanized in Agda and the line of work lifting derivatives to context-free languages.
> 
> Key technical contributions include defining a suitable fixed-point construction in Agda to safely encode recursive grammars, formalizing language derivatives to parse strings incrementally, and proving correctness of the parsing. Authors identify some present limitations of their approach and indicate those as directions for future work.
> 
> The background section is nice, gentle, readable. The whole thing is well written and explained. This is straight-down-the-middle nice line of work. "Here's some interesting pieces of work by some folk, but they haven't been put together in this way, and there's obviously a missing hole in our knowledge in this area, let me fix it." Overall, this work effectively fills a gap in formal parsing literature.  providing a clean, foundational formalization of context-free language parsing, type theoretically.
> 
> I have only minor notes.
> 
> Forgive me if this is silly, but we should explicitly include the empty string in the grammar; unless we do so, "0110" is not in the language of the given grammar; as written all productions are of odd-length strings.
> 
> The footnote from 2.1 appears on the next page, and that both got me confused looking for where it came from, and also confused as the return type of Parser, making me think "is this 'Set' deliberate here or not?" (and I think it's a mistake)

We have managed to shorten some of the text so that the footnote can be laid out on the same page.  I have fixed the Set in the signature of Parser,
that was indeed a mistake.

> 
> * small
> 
> ** "Doing so for the <pal> grammar" -> "Performing this unfolding for the <pal> grammar"
> 
> ** I know it's not what you mean, but what you said is that recursively unfolding the <pal> nonterminal produces the derivative of <pal0> wrt 1.
> 
> "Now, how do we take the derivative of the grammar <pal0> w.r.t. the next bit (1) in our string? [Say explicitly why it can't be done for <pal0> as written.] A simple solution [to the just-mentioned problem] is to recursively unfold the ⟨pal⟩ non-terminal. [After this unfolding, we can take the derivative]."
> 
> ** "see similarity between this type and the"
> 
> Repeat it. "similarity between the type (w : String) → Dec (P w) and". Remove the room for ambiguity.
> 
> ** speficying [specifying] and parsing context-free languages.

Fixed

> ** to accept it any way [anyway]

Fixed

> ** if we restrict the [class of] functions

Fixed

> ** and the[n] we take the derivative of the second

Fixed

> ** from which our disired [desired]

Fixed

> ** an anonymous reviewer of a draft of this paper have [has]

Fixed

> ** the interested reader to Hocroft et al. [Hopcroft]
> 
> Use cleveref and you'll never again misspell an author in text.

Fixed
