\begin{code}[hide]
{-# OPTIONS --cubical --guarded #-}
module 1-introduction where

\end{code}

\section{Introduction}

\iffalse
Parsing is one of the oldest problems in the field of programming languages. 

Parsing theory has given us parser generators, which are tools that generate efficient parsers from a simple description of a language.

However, many popular programming languages (GNU C, GNU C++, Clang, V8 JavaScript, TypeScript, OpenJDK Java, Golang, Lua, Swift) do not make use of these advancements.

Some reasons might be: performance, flexibility, tooling. For new and smaller languages, learning barriers (time to first working parser) might also be a significant factor.

Historically (roughly 1950-1980), the focus of parsing research was on correctness and performance (perhaps with LALR and yacc as crowning achievements).

In 2006, the GNU C compiler, one of the largest and most mature compilers, switched from a parser generator to a handwritten parser.

Recently (roughly 1990-now), the focus has shifted to expressiveness and flexibility (parser combinators, generalized parsing, data-dependent grammars).

Some of these new approaches (parser combinators and data-dependent grammars) break from the traditional context-free grammars.
\fi

Parser combinators are a flexible and elegant approach to parsing~\cite{monadic-parsing,combinator-parsing-short-tutorial}. They seamlessly interleave semantic actions into the parsing process and they can be implemented as an embedded domain specific language using only a handful of lines of code. Furthermore, practical implementations of parser combinators like Parsec~\cite{parsec} add features, such as better error handling, and improve performance. However, parser combinators are not perfect.

Parser combinators lack properties that we have come to expect from traditional approaches. For example, parser combinators can easily get stuck if the programmer accidentally introduces left-recursion. Similarly, parser combinators can take much more time than expected if the programmer uses too much backtracking. Can we find a middle ground between the flexibility and elegance of parser combinator and the reliability of traditional parsing techniques?

Recent work has proposed data dependent grammars~\cite{one-parser-to-rule-them-all,general-parser-combinators} as an answer to that question. However, implementations of data dependent grammars are complicated and implementation details intended only for improving performance, such as mutable memoization tables, obscure their semantics. Furthermore, the general parser combinators~\cite{general-parser-combinators} only provide a rigid, applicative interface, rather than give full access to the underlying data-dependent grammars. So, there currently is no reliable, simple, and flexible implementation of data-dependent parser combinators.

In this paper, we simplify data dependent grammars to a succinct specification and we derive an implementation from it. To achieve this goal we use the Brzozowski derivatives~\cite{brzozowski}. Though they are a proven technique that simplifies parsing~\cite{parsing-with-derivatives,conal-languages,fix-ing-regular-expressions}, they have not been applied to data-dependent grammars. Concretely, we make the following contributions:

\begin{itemize}
\item We present a simple specification of data dependent grammars (Section 2). We show through representative examples of grammars and inputs that this specification means what we intend.
\item We derive a sufficiently efficient implementation of data dependent grammars from that specification (Section 3). We run this implementation on examples to show that it produces the results that we expect in a reasonable amount of time (TODO: figure out what we can claim here, linear time?).
\end{itemize}