%%
%% This is file `aomart.cls',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% aomart.dtx  (with options: `class')
%% 
%% IMPORTANT NOTICE:
%% 
%% For the copyright see the source file.
%% 
%% Any modified versions of this file must be renamed
%% with new filenames distinct from aomart.cls.
%% 
%% For distribution of the original source see the terms
%% for copying and modification in the file aomart.dtx.
%% 
%% This generated file may be distributed as long as the
%% original source files, as listed above, are part of the
%% same distribution. (The sources need not necessarily be
%% in the same archive or directory.)
%% \CharacterTable
%%  {Upper-case    \A\B\C\D\E\F\G\H\I\J\K\L\M\N\O\P\Q\R\S\T\U\V\W\X\Y\Z
%%   Lower-case    \a\b\c\d\e\f\g\h\i\j\k\l\m\n\o\p\q\r\s\t\u\v\w\x\y\z
%%   Digits        \0\1\2\3\4\5\6\7\8\9
%%   Exclamation   \!     Double quote  \"     Hash (number) \#
%%   Dollar        \$     Percent       \%     Ampersand     \&
%%   Acute accent  \'     Left paren    \(     Right paren   \)
%%   Asterisk      \*     Plus          \+     Comma         \,
%%   Minus         \-     Point         \.     Solidus       \/
%%   Colon         \:     Semicolon     \;     Less than     \<
%%   Equals        \=     Greater than  \>     Question mark \?
%%   Commercial at \@     Left bracket  \[     Backslash     \\
%%   Right bracket \]     Circumflex    \^     Underscore    \_
%%   Grave accent  \`     Left brace    \{     Vertical bar  \|
%%   Right brace   \}     Tilde         \~}
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{aomart}
[2026/01/31 v1.37 Typesetting articles for the Annals of Mathematics]
\long\def\aom@size@warning#1{%
  \ClassWarning{aomart}{Size-changing option #1 will not be
    honored}}%
\DeclareOption{8pt}{\aom@size@warning{\CurrentOption}}%
\DeclareOption{9pt}{\aom@size@warning{\CurrentOption}}%
\DeclareOption{10pt}{\aom@size@warning{\CurrentOption}}%
\DeclareOption{11pt}{\aom@size@warning{\CurrentOption}}%
\DeclareOption{12pt}{\aom@size@warning{\CurrentOption}}%
\newif\if@aom@manuscript@mode
\@aom@manuscript@modefalse
\DeclareOption{manuscript}{\@aom@manuscript@modetrue}
\newif\if@aom@screen@mode
\@aom@screen@modefalse
\DeclareOption{screen}{\@aom@screen@modetrue}
\newif\if@aom@olddoi
\@aom@olddoifalse
\DeclareOption{olddoi}{\@aom@olddoitrue}
\newif\if@aom@doiMMXVI
\@aom@doiMMXVIfalse
\DeclareOption{doi2016}{\@aom@doiMMXVItrue}
\newif\if@aom@oldkeywords
\@aom@oldkeywordsfalse
\DeclareOption{oldkeywords}{\@aom@oldkeywordstrue}
\newif\if@aom@printscheme
\@aom@printschemefalse
\DeclareOption{printscheme}{\@aom@printschemetrue}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{amsart}}
\InputIfFileExists{aomart.cfg}{%
  \ClassInfo{aomart}{%
    Loading configuration file aomart.cfg}}{%
  \ClassInfo{aomart}{%
    Configuration file aomart.cfg is not found}}
\ProcessOptions\relax
\let\@makefnmark@kernel\@makefnmark
\LoadClass[11pt]{amsart}
\let\@makefnmark\@makefnmark@kernel
\def\@citex[#1]#2{\leavevmode
  \@tempcnta=0
  \@for\@citeb:=#2\do{\advance\@tempcnta by 1}%
  \@tempcntb=1
  \let\@citea\@empty
  \@cite{\@for\@citeb:=#2\do
    {\@citea\def\@citea{], [}%
     \advance\@tempcntb by 1
     \ifnum\@tempcnta=\@tempcntb\relax
        \ifnum\@tempcnta=2\relax
           \def\@citea{] and~[}%
        \else
           \def\@citea{], and~[}%
         \fi
     \fi
     \edef\@citeb{\expandafter\@firstofone\@citeb\@empty}%
     \if@filesw\immediate\write\@auxout{\string\citation{\@citeb}}\fi
     \@ifundefined{b@\@citeb}{\hbox{\reset@font\bfseries ?}%
       \G@refundefinedtrue
       \@latex@warning
         {Citation `\@citeb' on page \thepage \space undefined}}%
       {\@cite@ofmt{\csname b@\@citeb\endcsname}}}}{#1}}
\RequirePackage{fancyhdr, lastpage, ifpdf, graphicx}
\RequirePackage{zref-savepos}
\RequirePackage[breaklinks,colorlinks]{hyperref}
\if@aom@screen@mode
\hypersetup{linkcolor=blue,citecolor=blue,
  urlcolor=blue}%
\else\if@aom@manuscript@mode
\hypersetup{linkcolor=blue,citecolor=blue,
  urlcolor=blue}%
\else
\hypersetup{linkcolor=black,citecolor=black,
  urlcolor=black}%
\fi\fi
\urlstyle{rm}
\RequirePackage{environ}
\def\@aom@by{By}
\def\@aom@and{and}
\AtBeginDocument{\@ifpackageloaded{babel}{%
  \addto\captionsfrench{\def\@aom@by{Par}\def\@aom@and{et}}%
  \addto\captionsgerman{\def\@aom@by{Von}\def\@aom@and{und}}%
  \addto\captionsenglish{\def\@aom@by{By}\def\@aom@and{and}}}{}}
\RequirePackage{yhmath}
\DeclareSymbolFont{largesymbols}{OMX}{yhex}{m}{n}
\xdef\widehat#1{\noexpand\@mathmeasure\z@\textstyle{#1}%
  \noexpand\ifdim\noexpand\wd\z@>\tw@ em%
  \mathaccent"0\hexnumber@\symAMSb 5B{#1}%
  \noexpand\else\mathaccent"0362{#1}\noexpand\fi}
\xdef\widetilde#1{\noexpand\@mathmeasure\z@\textstyle{#1}%
  \noexpand\ifdim\noexpand\wd\z@>\tw@ em%
  \mathaccent"0\hexnumber@\symAMSb 5D{#1}%
  \noexpand\else\mathaccent"0365{#1}\noexpand\fi}
\IfFileExists{cmtiup.sty}{%
  \RequirePackage{cmtiup}}{%
  \ClassWarning{aomart}{The package mdputu is not found.\MessageBreak
    You need this package to get italics with upright digits!}}
\def\specialdigits{}%
\let\sishape=\itshape
\let\textsi=\textit
\def\@typesizes{%
  \or{\@vipt}{9}\or{\@viipt}{9}\or{\@viiipt}{9}\or{\@ixpt}{12}%
  \or{\@xpt}{13}%
  \or{\@xipt}{14}% normalsize
  \or{\@xiipt}{15}\or{13}{17}\or{\@xviipt}{20}%
  \or{19}{23.2}\or{22}{27.8}}%
\normalsize \linespacing=\baselineskip
\let\widebar\overline
\setlength{\textwidth}{31pc}
\setlength{\textheight}{48pc}
\oddsidemargin=.65in
\evensidemargin=.65in
\setlength{\topskip}{12pt}
\setlength{\abovedisplayskip}{6.95pt plus3.5pt minus 3pt}
\setlength{\belowdisplayskip}{6.95pt plus4.5pt minus 3pt}
\setlength{\skip\footins}{20pt}
\setlength{\dimen\footins}{3in}
\setlength\footskip{30pt}
\setlength{\parindent}{22pt}
\setlength{\parskip}{\z@}
\widowpenalty=10000
\clubpenalty=10000
\AtBeginDocument{%
  \labelsep=5pt\relax
  \settowidth\leftmargini{\labelenumi\hskip\labelsep}%
  \leftmargin=\leftmargini
  \labelwidth=\leftmargini \advance\labelwidth-\labelsep
  \@listi}
\renewenvironment{itemize}{%
  \ifnum\@itemdepth>3 \@toodeep
  \else \advance\@itemdepth\@ne
    \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
    \list{\csname\@itemitem\endcsname}%
    {\settowidth\leftmargin{\labelitemi\hskip\labelsep}%
      \def\makelabel##1{\hss\llap{\upshape##1}}}%
  \fi
}{%
  \endlist
}
\setlength{\headsep}{14pt}
\setlength{\headheight}{18.0pt}
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0pt}
\if@aom@manuscript@mode
  \newsavebox{\@aom@linecount}
  \savebox{\@aom@linecount}[4em][t]{\parbox[t]{4em}{%
      \@tempcnta\@ne\relax
      \loop{\underline{\scriptsize\the\@tempcnta}}\\
      \advance\@tempcnta by \@ne\ifnum\@tempcnta<43\repeat}}
\fi
\pagestyle{fancy}
\fancyhead{}
\fancyfoot{}
\fancyhead[CO]{\scriptsize\shorttitle}
\fancyhead[RO,LE]{\footnotesize\thepage}
\if@aom@manuscript@mode
  \fancyhead[LE]{\footnotesize\thepage\begin{picture}(0,0)%
      \put(-26,-25){\usebox{\@aom@linecount}}%
    \end{picture}}
  \fancyhead[LO]{\begin{picture}(0,0)%
      \put(-21,-25){\usebox{\@aom@linecount}}%
    \end{picture}}
  \fancyfoot[C]{\scriptsize Proof: page numbers may be temporary}
\fi
\fancyhead[CE]{\scriptsize\MakeUppercase\shortauthors}
\fancypagestyle{firstpage}{%
  \fancyhf{}%
  \if@aom@manuscript@mode
    \lhead{\begin{picture}(0,0)%
        \put(-21,-25){\usebox{\@aom@linecount}}%
      \end{picture}}
  \fi
  \chead{\scriptsize%
    \href{\@annalsurl}{Annals of Mathematics} \textbf{\currentvolume}
    (\currentyear),
    \start@page%
    \def\tempa{\pageref{LastPage}}%
    \edef\tempb{\start@page}%
    \ifx\tempa\end@page
      \edef\tempa{\HyPsd@@@pageref{LastPage}}%
    \else
       \edef\tempa{\end@page}%
    \fi
    \ifx\tempa\tempb\else--\end@page\fi\\
  \ifx\@doinumber\@empty\else
  \edef\@doinumber{\@doinumber}%
  \expandafter\doi\expandafter{\@doinumber}\fi}%
   \cfoot{\footnotesize\thepage}}%
\def\annalsurl#1{\gdef\@annalsurl{#1}}
\annalsurl{http://annals.math.princeton.edu/about}
\@onlypreamble{\title}
\@onlypreamble{\author}
\@onlypreamble{\contrib}
\@onlypreamble{\email}
\@onlypreamble{\address}
\@onlypreamble{\curraddr}
\@onlypreamble{\urladdr}
\@onlypreamble{\orcid}
\@onlypreamble{\givenname}
\@onlypreamble{\fulladdress}
\@onlypreamble{\surname}
\@onlypreamble{\thanks}
\@onlypreamble{\keyword}
\@onlypreamble{\subject}
\@onlypreamble{\received}
\@onlypreamble{\revised}
\@onlypreamble{\accepted}
\@onlypreamble{\published}
\@onlypreamble{\publishedonline}
\@onlypreamble{\proposed}
\@onlypreamble{\seconded}
\@onlypreamble{\corresponding}
\@onlypreamble{\editor}
\@onlypreamble{\version}
\@onlypreamble{\volumenumber}
\@onlypreamble{\issuenumber}
\@onlypreamble{\publicationyear}
\@onlypreamble{\copyrightnote}
\@onlypreamble{\copyrighyear}
\@onlypreamble{\papernumber}
\@onlypreamble{\startpage}
\@onlypreamble{\endpage}
\@onlypreamble{\doinumber}
\@onlypreamble{\mrnumber}
\@onlypreamble{\zblnumber}
\@onlypreamble{\arxivnumber}
\def\@names{}
\def\givenname#1{\g@addto@macro\@names{givenname=#1;}}
\def\surname#1{\g@addto@macro\@names{surname=#1;}}
\def\fulladdress#1{\g@addto@macro\@names{fulladdress=#1;}}
\renewcommand{\author}[2][]{%
  \ifx\@empty\authors
    \gdef\authors{#2}%
    \g@addto@macro\@names{author=#2;}%
  \else
    \g@addto@macro\authors{\and#2}%
    \g@addto@macro\@names{\and author=#2;}%
  \fi
  \gdef\aom@current@orcid@target{\authors}%
  \@ifnotempty{#1}{%
    \ifx\@empty\shortauthors
      \gdef\shortauthors{#1}%
    \else
      \g@addto@macro\shortauthors{\and#1}%
    \fi
  }%
  \g@addto@macro\addresses{\author{#2}}%
}
\edef\author{\@nx\@dblarg
  \@xp\@nx\csname\string\author\endcsname}
\def\@currentcontribution{}
\def\@currentcontributors{}
\def\contribs{}
\newif\if@startcontribgroup
\@startcontribgroupfalse
\def\@processcurrentcontribgroup{%
  \ifx\@currentcontributors\@empty\else
    \def\@@and{{\upshape \@aom@and}}%
    \author@andify\@currentcontributors
    \ifx\contribs\@empty\else
      \g@addto@macro\contribs{\and}%
    \fi
    \expandafter\g@addto@macro\expandafter\contribs
    \expandafter{\@currentcontribution}%
    \g@addto@macro\contribs{\space}%
    \expandafter\g@addto@macro\expandafter\contribs
    \expandafter{\@currentcontributors}%
  \fi
}
\renewcommand{\contrib}[2][]{%
  \def\@tempa{#1}%
  \gdef\aom@current@orcid@target{\@currentcontributors}%
  \@startcontribgrouptrue
  \ifx\@tempa\@empty\relax
    \ifx\@currentcontribution\@empty\relax
      \ClassError{aomart}{You must define contribution for
        contributors}{The first \contrib command must have the
        optional argument indicating the contribution}%
    \else
      \@startcontribgroupfalse
    \fi
  \fi
  \ifx\@currentcontribution\@tempa\relax
    \@startcontribgroupfalse
  \fi
  \if@startcontribgroup
     \@processcurrentcontribgroup
     \gdef\@currentcontribution{#1}%
     \gdef\@currentcontributors{#2}%
  \else
    \g@addto@macro\@currentcontributors{\and#2}%
  \fi
  \g@addto@macro\@names{\and contributor=#2;}%
  \g@addto@macro\@names{role=}%
  \expandafter\g@addto@macro\expandafter%
  \@names\expandafter{\@currentcontribution}%
  \g@addto@macro\@names{;}%
  \g@addto@macro\addresses{\author{#2}}%
}
\renewcommand{\email}[2][]{%
  \g@addto@macro\addresses{\email{#1}{#2}}%
  \g@addto@macro\@names{email=#2;}%
}
\renewcommand{\urladdr}[2][]{%
  \g@addto@macro\addresses{\urladdr{#1}{#2}}%
  \g@addto@macro\@names{urladdr=#2;}%
}
\def\aom@current@orcid@target{\authors}
\newcommand{\orcid}[1]{%
  \g@addto@macro\addresses{\orcid{#1}}%
  \g@addto@macro\@names{orcid=#1;}%
  \expandafter\g@addto@macro\aom@current@orcid@target{\aom@orcidlink{#1}}%
}
\newcommand\aom@orcidlink[1]{\kern0.2ex\href{https://orcid.org/#1}{\includecolorgraphics[height=2ex]{aom_orcid_logo}{aom_orcid_logo_bw}}}
\def\keyword#1{\ifx\@keywords\@empty\gdef\@keywords{#1}\else
  \g@addto@macro\@keywords{, #1}\fi}
\let\@primarysubjects\@empty
\let\@secondarysubjects\@empty
\let\@primaryscheme\@empty
\let\@secondaryschme\@empty
\def\subject#1#2#3{%
  \expandafter\ifx\csname @#1subjects\endcsname\@empty\relax
     \expandafter\gdef\csname @#1subjects\endcsname{#3}%
  \else
     \expandafter\g@addto@macro\csname @#1subjects\endcsname{, #3}%
  \fi
  \if@aom@printscheme
  \expandafter\g@addto@macro\csname @#1subjects\endcsname{%
    ~(#2)}%
  \fi}
\def\formatdate#1{\@formatdate#1\@endformatdate}
\def\@formatdate#1-#2-#3\@endformatdate{%
  \@tempcnta=#3\relax
  \ifcase#2\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \space\the\@tempcnta,\space#1}
\def\received#1{\def\@received{#1}}
\let\@received\@empty
\def\revised#1{\def\@revised{#1}}
\let\@revised\@empty
\def\accepted#1{\def\@accepted{#1}}
\let\@accepted\@empty
\def\published#1{\def\@published{#1}}
\let\@published\@empty
\def\publishedonline#1{\def\@publishedonline{#1}}
\let\@publishedonline\@empty
\def\volumenumber#1{\def\currentvolume{#1}}
\def\issuenumber#1{\def\currentissue{#1}}
\def\publicationyear#1{\def\currentyear{#1}}
\def\papernumber#1{\def\currentpaper{#1}}
\papernumber{0000}
\def\startpage#1{\pagenumbering{arabic}\setcounter{page}{#1}%
  \def\start@page{#1}%
  \ifnum\c@page<\z@ \pagenumbering{roman}\setcounter{page}{-#1}%
    \def\start@page{\romannumeral#1}%
  \fi}
\def\endpage#1{\def\@tempa{#1}%
  \ifx\@tempa\@empty\def\end@page{\pageref{LastPage}}%
  \else\def\end@page{#1}\fi}
\def\pagespan#1#2{\startpage{#1}\endpage{#2}}
\pagespan{1}{}
\def\g@addto@abstract#1{\g@addto@macro{\@aom@abstract}{#1}}
\long\def\@aom@abstract{}
\long\def\@getabstract#1{%
  \bgroup
    \ifx\languagename\undefined
      \def\languagename{english}%
    \fi
    \g@addto@abstract{<begin abstract }%
    \expandafter\g@addto@abstract\expandafter{\languagename>}%
    \g@addto@macro\@aom@abstract{#1}%
    \g@addto@abstract{<end abstract }%
    \expandafter\g@addto@abstract\expandafter{\languagename>}%
  \egroup
  \ifx\maketitle\relax
    \ClassWarning{aomart}{Abstract should precede
      \protect\maketitle\space in AMS derived classes}%
  \fi
  \global\setbox\abstractbox=\vtop\bgroup%
    \box\abstractbox
    \vglue1pc%
    {\centering\normalfont\normalsize\bfseries\abstractname\par\vglue1pc}%
    \list{}{\labelwidth\z@%
      \leftmargin3pc \rightmargin\leftmargin%
      \listparindent\normalparindent \itemindent\normalparindent%
      \parsep\z@ \@plus\p@%
      \let\fullwidthdisplay\relax%
    }%
    \item[]\normalfont\Small#1
  \endlist\egroup}
\renewenvironment{abstract}{\Collect@Body\@getabstract}{%
  \ifx\@setabstract\relax\@setabstracta\fi}
\let\proposed\@gobble
\let\seconded\@gobble
\let\corresponding\@gobble
\let\version\@gobble
\def\doinumber#1{\gdef\@doinumber{#1}}
\doinumber{10.4007/annals.\currentyear.\currentvolume.\currentissue.\currentpaper}
\def\mrnumber#1{\gdef\@mrnumber{#1}}
\mrnumber{}
\def\zblnumber#1{\gdef\@zblnumber{#1}}
\zblnumber{}
\def\arxivnumber#1{\gdef\@arxivnumber{#1}}
\arxivnumber{}
\def\copyrightyear#1{\def\@copyrightyear{#1}}
\copyrightyear{}
\def\copyrightnote#1{\def\@copyrightnote{#1}}
\copyrightnote{\textcopyright~%
  \ifx\@empty\@copyrightyear\currentyear\else\@copyrightyear\fi~%
  Department of Mathematics, Princeton University}
\newwrite\@mainrpi
\def\aom@write@paper@info{%
  \bgroup
  \if@filesw
    \openout\@mainrpi\jobname.rpi%
    \def\and{\string\and\space}%
    \ifx\r@LastPage\@undefined
       \edef\@tempa{\start@page}%
    \else
       \def\@tempc##1##2##3##4##5{##2}%
       \edef\@tempa{\expandafter\@tempc\r@LastPage}%
   \fi
   \ifx\languagename\undefined
     \def\languagename{english}%
   \fi
   \protected@write\@mainrpi{}%
    {\@percentchar authors=\authors}%
   \protected@write\@mainrpi{}%
    {\@percentchar authors.information={\@names}}%
   \protected@write\@mainrpi{}%
    {\@percentchar title=\@title}%
   \protected@write\@mainrpi{}%
    {\@percentchar year=\currentyear}%
   \protected@write\@mainrpi{}%
    {\@percentchar volume=\currentvolume}%
   \protected@write\@mainrpi{}%
    {\@percentchar issue=\currentissue}%
   \protected@write\@mainrpi{}%
    {\@percentchar paper=\currentpaper}%
   \protected@write\@mainrpi{}%
    {\@percentchar startpage=\start@page}%
   \protected@write\@mainrpi{}%
    {\@percentchar endpage=\@tempa}%
   \protected@write\@mainrpi{}%
    {\@percentchar doi=\@doinumber}%
   \ifx\@zblnumber\@empty\else
   \protected@write\@mainrpi{}%
    {\@percentchar zbl=\@zblnumber}%
   \fi
   \ifx\@mrnumber\@empty\else
   \protected@write\@mainrpi{}%
    {\@percentchar mr=\@mrnumber}%
   \fi
   \ifx\@arxivnumber\@empty\else
   \protected@write\@mainrpi{}%
    {\@percentchar arxiv=\@arxivnumber}%
   \fi
   \protected@write\@mainrpi{}%
    {\@percentchar subjects=Primary \@primarysubjects; Secondary:
      \@secondarysubjects}%
   \protected@write\@mainrpi{}%
    {\@percentchar keywords=\@keywords}%
   \protected@write\@mainrpi{}%
    {\@percentchar abstract=\@aom@abstract}%
   \protected@write\@mainrpi{}%
     {\@percentchar articlelanguage=\languagename}%
   \def\paperUrl{https://annals.math.princeton.edu/\currentyear/\currentvolume-\currentissue/p\currentpaper}%
   \protected@write\@mainrpi{}%
     {\@percentchar paperUrl=\paperUrl}%
    \AtEndDocument{\closeout\@mainrpi}%
    \fi
\egroup}
\def\@maketitle@hook{\aom@write@paper@info\global\let\@maketitle@hook\@empty}
\def\@settitle{\begin{center}%
  \baselineskip20\p@\relax
    \bfseries\LARGE
  \@title
  \ifpdf
    \hypersetup{pdftitle=\@title}%
  \fi
  \end{center}%
}
\def\@setauthors{%
  \ifx\authors\@empty\relax\else
    \begingroup
    \def\thanks{\protect\thanks@warning}%
    \trivlist
    \centering\footnotesize \@topsep30\p@\relax
    \advance\@topsep by -\baselineskip
    \item\relax
    \def\@@and{{\upshape \@aom@and}}%
    \author@andify\authors
    \ifpdf
      \bgroup
         \def\aom@orcidlink##1{}%
         \xdef\@tempa{\authors}%
      \egroup
      \hypersetup{pdfauthor=\@tempa}%
    \fi
    \def\\{\protect\linebreak}%
    \small \@aom@by{} \scshape\authors%
    \@processcurrentcontribgroup
    \ifx\@empty\contribs
    \else
      ,\penalty-3 \space \@setcontribs
    \fi
    \endtrivlist
    \endgroup
    \fi}
\def\@setcontribs{%
    \def\@@and{{\upshape \@aom@and}}%
    \author@andify\contribs
    \contribs
}
\def\@adminfootnotes{%
  \let\@makefnmark\relax  \let\@thefnmark\relax
  \ifx\@empty\@date\else \@footnotetext{\@setdate}\fi
  \ifx\@empty\@subjclass\else \@footnotetext{\@setsubjclass}\fi
  \ifx\@empty\@keywords\else\@setkeywords\fi
  \ifx\@empty\@primarysubjects
     \ifx\@empty\@secondarysubjects
     \else\@setsubjects\fi
  \else\@setsubjects\fi
  \ifx\@empty\thankses\else \@footnotetext{%
    \def\par{\let\par\@par}\@setthanks}%
  \fi
  \ifx\@empty\@copyrightnote\else \@footnotetext{%
    \def\par{\let\par\@par}\@copyrightnote\@addpunct.}%
  \fi
}
\def\@setkeywords{%
    \ifpdf
      \hypersetup{pdfkeywords=\@keywords}%
    \fi
    \if@aom@oldkeywords\else
    \@footnotetext{Keywords: \@keywords}%
    \fi
}
\def\@setsubjects{%
  \let\@subjects\@empty
   \ifx\@primarysubjects\@empty\else
     \edef\@subjects{Primary:~\@primarysubjects}%
    \fi
   \ifx\@secondarysubjects\@empty\else
     \ifx\@primarysubjects\@empty
       \edef\@subjects{Secondary:~\@secondarysubjects}%
     \else
       \edef\@subjects{\@subjects; Secondary:~\@secondarysubjects}%
     \fi
    \fi
    \ifpdf
      \hypersetup{pdfsubject=\@subjects}%
    \fi
    \if@aom@oldkeywords\else
    \@footnotetext{AMS Classification:~\@subjects.}%
    \fi
}
\def\@@and{\MakeLowercase{\@aom@and}}
\def\enddoc@text{%
  \ifx\@empty\@translators \else\@settranslators\fi
  \ifx\@empty\@received \else\@setreceived\fi
  \ifx\@empty\@revised \else\@setrevised\fi
  \ifx\@empty\addresses \else\@setaddresses\fi}
\def\@setreceived{{\centering(Received: \@received)\par}}
\def\@setrevised{{\centering(Revised: \@revised)\par}}
\def\@setaccepted{{\centering(Accepted: \@accepted)\par}}
\def\@setpublished{{\centering(Published: \@published)\par}}
\def\@setpublishedonline{{\centering(Published online: \@publishedonline)\par}}
\def\emailaddrname{{\itshape E-mail}}
\def\@setaddresses{\par
  \nobreak \begingroup
\footnotesize
  \def\author##1{\goodbreak\addvspace\bigskipamount{\scshape##1\par\nobreak}}%
  \def\\{\unskip, \ignorespaces}%
  \interlinepenalty\@M
  \def\address##1##2{\begingroup\nobreak
    \par\hangindent=22pt\hangafter=0\parindent=0pt
    \@ifnotempty{##1}{(\ignorespaces##1\unskip) }%
    {\ignorespaces##2}\par\endgroup}%
  \def\curraddr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\par
          \par\hangindent=22pt\hangafter=0\parindent=0pt\curraddrname
      \@ifnotempty{##1}{, \ignorespaces\scshape##1\unskip}\hskip0.2em:\space
      ##2\par}\endgroup}%
  \def\email##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak
      \par\hangindent=22pt\hangafter=0\parindent=0pt\emailaddrname
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\hskip0.2em:\space
      \href{mailto:##2}{\nolinkurl{##2}}\par\nobreak}\endgroup}%
  \def\urladdr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak
      \par\hangindent=22pt\hangafter=0\parindent=0pt%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}%
      \url{##2}\par\nobreak}\endgroup}%
  \def\orcid##1{\begingroup
    \@ifnotempty{##1}{\nobreak
      \par\hangindent=22pt\hangafter=0\parindent=0pt%
      \url{https://orcid.org/##1}\par\nobreak}\endgroup}%
  \addresses
  \endgroup
}
\renewcommand\contentsnamefont{\bfseries}
\def\section{\@startsection{section}{1}%
  \z@{.7\linespacing\@plus\linespacing}{.5\linespacing}%
  {\normalfont\bfseries\centering}}
\def\subsection{\@startsection{subsection}{2}%
  {\parindent}{.5\linespacing}{-.5em}%
  {\normalfont\itshape}}
\def\oldsubsections{%
\gdef\subsection{\@startsection{subsection}{2}%
  {\parindent}{.5\linespacing\@plus.7\linespacing}{-.5em}%
  {\normalfont\itshape}}}
\def\subsubsection{\@startsection{subsubsection}{3}%
  {\parindent}{.5\linespacing}{-.5em}%
  {\normalfont\itshape}}
\providecommand\Hy@AlphNoErr[1]{%
  \ifnum\value{#1}>26 %
    Alph\number\value{#1}%
  \else
    \ifnum\value{#1}<1 %
      Alph\number\value{#1}%
    \else
      \Alph{#1}%
    \fi
  \fi
}%
\def\appendix{\par\c@section\z@ \c@subsection\z@
  \gdef\theHsection{\Hy@AlphNoErr{section}}%
   \let\sectionname\appendixname
   \def\thesection{{\upshape\@Alph\c@section}}}
\def\@captionheadfont{\normalfont}
\newtheoremstyle{plain}{0.5\linespacing}{0.5\linespacing}{\sishape}%
   {\parindent}{\scshape}{.}{0.5em}%
   {\thmname{#1}\thmnumber{ #2}\thmnote{\normalfont{} (#3)}}
\newtheoremstyle{definition}{0.5\linespacing}{0.5\linespacing}%
   {\upshape}{\parindent}%
   {\sishape}{.}{0.5em}%
   {\thmname{#1}\thmnumber{ #2}\thmnote{\normalfont{} (#3)}}
\newtheoremstyle{remark}{0.5\linespacing}{0.5\linespacing}%
   {\upshape}{\parindent}%
   {\sishape}{.}{0.5em}%
   {\thmname{#1}\thmnumber{ #2}\thmnote{\normalfont{} (#3)}}
\renewcommand{\newtheorem}{\@ifstar{\@aom@newthm@star}{\@aom@newthm}}
\def\@aom@newthm@star{\@ifnextchar[{\@aom@newthm@star@}{\@aom@newthm@star@[]}}
\def\@aom@newthm{\@ifnextchar[{\@aom@newthm@}{\@aom@newthm@[]}}
\def\@aom@newthm@star@[#1]{\@xnthm *}
\def\@aom@newthm@[#1]{\@xnthm \relax}
\renewenvironment{proof}[1][\proofname]{\par
  \pushQED{\qed}%
  \normalfont \topsep6\p@\@plus6\p@\relax
  \trivlist
  \item[\hskip\labelsep\hskip\parindent
        \itshape
    #1\@addpunct{.}]\ignorespaces
}{%
  \popQED\endtrivlist\@endpefalse
}
\def\repeatedauthors#1{\ClassWarning{aomart}{The command is obsolte}#1}
\let\bysame@@orig=\bysame
\def\bysame{\ClassWarning{aomart}{We no longer omit
    repeated authors}\bysame@@orig}
\def\doi#1{%
  \if@aom@doiMMXVI
     \url{http://dx.doi.org/#1}%
  \else
     \if@aom@olddoi
         \href{http://dx.doi.org/#1}{doi: \path{#1}}%
      \else
          \url{https://doi.org/#1}%
      \fi
  \fi}
\def\mr#1{\href{http://www.ams.org/mathscinet-getitem?mr=#1}{MR~\path{#1}}}
\def\zbl#1{\href{http://www.zentralblatt-math.org/zmath/en/search/?q=an:#1}{Zbl~\path{#1}}}
\def\arxiv#1{\href{http://www.arxiv.org/abs/#1}{arXiv~\path{#1}}}
\def\jfm#1{\href{http://www.emis.de/cgi-bin/JFM-item?#1}{JFM~\path{#1}}}
\renewcommand{\bibliofont}{\small}
\newcounter{aom@EC@counter}
\NewDocumentCommand\EditorialComment{O{default} +m O{0pt}}{%
  \if@aom@manuscript@mode\bgroup
  \expandafter\ifx\csname EditorialComment@#1\endcsname\relax\else
    \stepcounter{aom@EC@counter}%
    \setlength\unitlength{1sp}%
    \zsavepos{aom@EC@position\arabic{aom@EC@counter}}%
    \begin{picture}(0,0)%
      \put(\the\dimexpr
      -\zposx{aom@EC@position\arabic{aom@EC@counter}}sp + 15pt,#3){%
        \parbox{80pt}{\raggedright
          \normalfont\scriptsize\raggedright\expandafter\color\expandafter{%
            \csname EditorialComment@#1\endcsname}#2}}%
    \end{picture}%
  \fi
  \egroup
\fi}
\newcommand\ECSelect[2][black]{\if@aom@manuscript@mode
    \expandafter\gdef\csname
    EditorialComment@#2\endcsname{#1}%
  \fi}
\AtBeginDocument{\ECSelect{default}}
\newcommand\Highlight[2][default]{%
  \expandafter\ifx\csname Highlight@#1\endcsname\relax
  #2\else
  \csname Highlight@#1\endcsname{#2}\fi}
\newcommand\HSelect[2][red]{\if@aom@manuscript@mode
  \@for\TC@level:=#2\do{\expandafter
    \gdef\csname Highlight@\TC@level\endcsname##1{\bgroup
      \Hy@colorlinksfalse
      \def\Hy@colorlink####1{\begingroup}%
      \def\Hy@endcolorlink{\endgroup}%
      \color{#1}##1\egroup}}%
  \fi}
\AtBeginDocument{\HSelect{default}}
\def\@fullref#1#2#3#4{\hyperref[#3]{#1~#2\ref*{#3}#4}}
\newcommand{\fullref}[2]{\@fullref{#1}{}{#2}{}}
\newcommand{\pfullref}[2]{\@fullref{#1}{(}{#2}{)}}
\newcommand{\bfullref}[2]{\@fullref{#1}{[}{#2}{]}}
\newcommand{\eqfullref}[2]{\hyperref[#2]{#1~\textup{\tagform@{\ref*{#2}}}}}
\newcommand{\fullpageref}[2][page]{\hyperref[#2]{#1~\pageref*{#2}}}
\def\eqnarray{%
   \stepcounter{equation}%
   \def\@currentlabel{\p@equation\theequation}%
   \global\@eqnswtrue
   \m@th
   \global\@eqcnt\z@
   \tabskip\@centering
   \let\\\@eqncr
   $$\arraycolsep1\p@
   \everycr{}\halign to\displaywidth\bgroup
       \hskip\@centering$\displaystyle\tabskip\z@skip{##}$\@eqnsel
      &\global\@eqcnt\@ne\hskip \tw@\arraycolsep \hfil${##}$\hfil
      &\global\@eqcnt\tw@ \hskip \tw@\arraycolsep
         $\displaystyle{##}$\hfil\tabskip\@centering
      &\global\@eqcnt\thr@@ \hb@xt@\z@\bgroup\hss##\egroup
         \tabskip\z@skip
      \cr
}
\newcommand\includecolorgraphics[3][]{\if@aom@screen@mode
  \includegraphics[#1]{#2}\else
  \includegraphics[#1]{#3}\fi}
\def\@aom@sponsors{}
\AtEndDocument{%
  \ifx\@aom@sponsort\@empty\else
     \protected@write\@mainrpi{}%
     {\@percentchar grants=\@aom@sponsors}%
  \fi}
\newcommand\funding[3][]{%
  \ifx\@aom@sponsors\@empty
     \gdef\@aom@sponsors{sponsor=#2, grantid=#3}%
  \else
     \g@addto@macro{\@aom@sponsors}{\protect\and sponsor=#2, grantid=#3}%
  \fi
     \def\@tempa{#1}\relax%
     \ifx\@tempa\@empty\relax
       \def\@tempb{#3}%
        #2%
        \ifx\@tempb\@empty\relax\else\ (grant~#3)\fi
     \else
        #1
     \fi}
\endinput
%%
%% End of file `aomart.cls'.
