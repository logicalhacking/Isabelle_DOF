(*<*)
theory
  "C2_TextElements"
imports
  "C1_Installation"
begin
define_shortcut* ijedit \<rightleftharpoons> \<open>Isabelle/jEdit\<close>
declare_reference*[example3::float]
declare_reference*[example2::figure]
declare_reference*[example1::figure]

(*>*)
chapter*[anti::text_section]\<open>Text Elements\<close>

text\<open>
In this section, you will come to see the mention to \<^ijedit> , this is a reference to
the default user-interface for Isabelle. It is the main application of PIDE, which is the framework
 for Prover IDEs. More information can be found in the Isabelle/jEdit manual \<^cite>\<open>"mwenzel:jedit:2025"\<close>.
\<close>

section*[macro::technical]\<open>Macros\<close>

text\<open>
There is a mechanism for defining document-local macros that are PIDE-supported but expand within
 the integrated source.  This feature allows for the creation of shortcuts as well as macros.
 Usually these are placed at the very beginning of your new document, creating the shorthands that
 will be useful to the writing of your current paper.\<close>

subsection*[shrtcut::technical]\<open>Shortcuts\<close>

text\<open>
Shortcuts serve as shorthands for other commands, typically \<^LaTeX>  enhancing both the readability
 of your \<^isadof> code and the flow of writing.

A simple example of this is my use of the \<^LaTeX> logo in my texts.
You define the shortcut whenever you want in your paper, and then when you want to use 
it you simply use it antiquotation. Usually you will surround the
definition by (*<*) and (*>*) so that it does not appear in the pdf.

\begin{isarbox}
\begin{isabelle}
\isakeywordONE{define{\isacharunderscore}{\kern0pt}shortcut{\isacharasterisk}{\kern0pt}}\ LaTeX\ {\isasymrightleftharpoons}\ {\isacartoucheopen}{\isacharbackslash}{\kern0pt}LaTeX{\isacharbraceleft}{\kern0pt}{\isacharbraceright}{\kern0pt}{\isacartoucheclose}\isanewline
\isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
 You need a full \textit{\textbf{LaTeX}} installation to use the pdf generator of \textit{\textbf{isadof}}
\begin{isabelle}{\isacartoucheclose}\isanewline
\end{isabelle}
\end{isarbox}

%@ {boxed_theory_text [display]\<open>
%  define_shortcut* LaTeX \<rightleftharpoons> \<open>\LaTeX{}\<close>
%  text\<open> You need a full \^LaTeX> installation to use the pdf generator of \isadof.\<close>\<close>}

\begin{outmat}
 You need a full \LaTeX{} installation to use the pdf generator of \isadof{}.
\end{outmat}

%@ {boxed_pdf [display]
%\<open> You need a full \LaTeX installation to use the pdf generator of.\<close>}
\<close>



subsection*[mac::technical]\<open>Macro's\<close>

text\<open>
Macro commands are shortcuts that allow you to give in parameters, or parameterized short-cuts.

Here we may want to create a macro for a specific math symbol from \<^LaTeX>, that repeatedly appears in 
a paper, helping with the overall readibility.

\<^isarbox>\<open>
\begin{isabelle}
\isakeywordONE{define{\isacharunderscore}{\kern0pt}macro{\isacharasterisk}{\kern0pt}}\ sqrt {\isasymrightleftharpoons}\ 
{\isacartoucheopen}{\isacharbackslash}ensuremath{\isacharbraceleft}{\isacharbackslash}{\kern0pt}sqrt{\isacharbraceleft}{\kern0pt}{\isacartoucheclose} {\isacharunderscore}
 {\isacartoucheopen}{\isacharbraceright}{\kern0pt}{\isacharbraceright}{\isacartoucheclose}\isanewline
\isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
 The square root of 121 is written \textit{\textbf{sqrt}}<121> and is equal to 11.
\begin{isabelle}{\isacartoucheclose}\isanewline
\end{isabelle}
\<close>
\begin{outmat}
   The square root of 121 is written $\sqrt{121}$ and is equal to 11.
\end{outmat}
\<close>

section*[lists::technical]\<open>Lists\<close>
text\<open>
There are two ways to create to create lists in \<^isadof>: unordered lists and numbered list.
\<close>
subsection*[blist::introduction]\<open>Unordered lists\<close>
text\<open>Unordered lists are made up of elements that all start with the \<^emph>\<open>item\<close> antiquotation, written
 \<^verbatim>\<open>\<^item>\<close> and displayed in \<^ijedit> as $\blacksquare$.


\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Let us make a list:
  \begin{itemize}
    \item[$\blacksquare$] list element 
    \item[$\blacksquare$] list element
  \end{itemize}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Let us make a list:
  \begin{itemize}
    \item list element 
    \item list element
  \end{itemize}
\<close>
\<close>


subsection*[nlist::technical]\<open>Numbered Lists\<close>
text\<open>Numbered lists are exactly the same but they use the \<^emph>\<open>enum\<close> antiquotation, written \<^verbatim>\<open>\<^enum>\<close> and
 displayed in \<^ijedit> as $\blacktriangleright$.


\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Let us make a list:
  \begin{enumerate}
    \item[$\blacktriangleright$] list element 
    \item[$\blacktriangleright$] list element
  \end{enumerate}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Let us make a list:
  \begin{enumerate}
    \item list element 
    \item list element
  \end{enumerate}
\<close>
\<close>

subsection*[nestlist::technical]\<open>Complex Lists\<close>
text\<open>In \<^isadof>, indentation matters lot in \<^isadof> when making list. This also allows to 
combine ordered and unordered lists, in many ways. Here are a few examples.
\<close>

paragraph\<open>Example 1: Leveled lists\<close>
text\<open>When you use the \<^emph>\<open>enum\<close> antiquotation you can create levels of lists with different labels.
\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Leveled list:
  \begin{enumerate}
    \item[$\blacktriangleright$] level 1
    \item[$\blacktriangleright$] level 1
      \begin{enumerate}
        \item[$\blacktriangleright$] level 2
        \item[$\blacktriangleright$] level 2
        \begin{enumerate}
          \item[$\blacktriangleright$] level 3 ...
        \end{enumerate}
      \end{enumerate}
    \item[$\blacktriangleright$] level 1
  \end{enumerate}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Leveled list:
  \begin{enumerate}
    \item level 1
    \item level 1
      \begin{enumerate}
        \item level 2
        \item level 2
        \begin{enumerate}
          \item level 3 ...
        \end{enumerate}
      \end{enumerate}
    \item level 1
  \end{enumerate}
\<close>
\<close>


paragraph\<open>Example 2: Nested lists\<close>
text\<open>
Similar to the precedent example except we combine ordered and unordered lists.
\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Let us make a list within a list:
  \begin{enumerate}
    \item[$\blacktriangleright$] list 1 element 1
    \item[$\blacktriangleright$] list 1 element 2
    \begin{itemize}
      \item[$\blacksquare$] list 2 element 1
      \item[$\blacksquare$] list 2 element 2
    \end{itemize}
    \item[$\blacktriangleright$] list 1 element 3
  \end{enumerate}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Let us make a list within a list:
  \begin{enumerate}
    \item list 1 element 1
    \item list 1 element 2
    \begin{itemize}
      \item list 2 element 1
      \item list 2 element 2
    \end{itemize}
    \item list 1 element 3
  \end{enumerate}
\<close>
\<close>


text\<open>
The end of a list in Isabelle/Isar is defined as an empty line in Isabelle, switching type list 
with no change in indentation is therefore implicitly also ends a list.
\<close>

section\<open>Figures\<close>

subsection*[simpfig::technical]\<open>Simple Figures\<close>

text\<open>The figure macro is provided by the \<^isadof> ontology, and allows you to display a file as
 a figure in your document. The path towards the document (pdf, png) is given in the \<^verbatim>\<open>file_source\<close>
 parameter.This macro has a few others parameter values that you can change such as :
  \<^item> \<^verbatim>\<open>relative_width\<close> (int) : allows you to change the scale of the image. It is equal to the percentage
 of the text width, default value is 100.
  \<^item> \<^verbatim>\<open>relative_height\<close> (int) : allows you to change the scale of the image. It is equal to the percentage
of a document page, default value is 100.
  \<^item> \<^verbatim>\<open>caption\<close> (Isabelle/HOL) : allows you to define a caption for your figure. It is defined within the
 cartouches after the macro, if left empty the caption will be empty as it is it's default value.

For example, if "figures/LatexLogo.png" is the path towards your image in your document folder, the
 following \<^isadof> code:

@{boxed_theory_text[display]\<open>
figure*[example1::figure,relative_width="95",file_src="''figures/LatexLogo.png''"]\<open> 
     Latex Logo on white background \<close>
\<close>
}
produces the result @{figure(unchecked)\<open>example1\<close>}.
\<close>

figure*[example1::figure,relative_width="95",file_src="''figures/LatexLogo.png''"]\<open> 
     Latex Logo on white background \<close>

subsection*[compfid::technical]\<open>Complex Figures\<close>

text\<open>It you wanted a more liberal use of your images/figures you may use the \<^verbatim>\<open>text\<close> macro from the
\<^isadof> ontology. This has many uses when formatting your document, such as allowing to have figures
side by side. This is easier to understand with examples.
Firstly, an example were we display a single figure, similarly to the use of the \<^verbatim>\<open>figure\<close> macro.
In contrast to the previous (inline) case, this time, we wrap it into an own referentiable 
\<^theory_text>\<open>text*\<close>-command:
@{boxed_theory_text[display]\<open>
text*[example2::float,  main_caption="''\<open>Latex Logo on white background\<close>''"]
\<open>@{fig_content (width=35, caption="''''") "''figures/LatexLogo.png''"}\<close>
\<close>
}
The result is shown in @{figure(unchecked)\<open>example2\<close>}.
\<close>
text*[example2::float,  main_caption="\<open>Latex Logo on white background\<close>"]
\<open>@{fig_content (width=95, caption="") "figures/LatexLogo.png"}\<close>
text\<open>
As you can see the result is identical to the previous \<^theory_text>\<open>figure*\<close>-command. Now, combining
these two things --- the reference to \<^theory_text>\<open>fig_content\<close> and the \<^theory_text>\<open>text*-float\<close>-box around, we can
two or more figures side by side.

@{boxed_theory_text[display]\<open>
text*[example3::float, 
      main_caption="\<open>Latex logos\<close>"]
\<open>
@{fig_content (width=35, caption="In white") "figures/LatexLogo.png"
}@{fig_content (width=35, caption="In black") "figures/LatexLogoBlack.png"}
\<close>
\<close>
}
This bit of \<^isadof> code would generate this result  @{float(unchecked)\<open>example3\<close>}.
\<close>

text*[example3::float,  main_caption="\<open>Latex logos\<close>"]
\<open>
@{fig_content (width=35, caption="In white") "figures/LatexLogo.png"
}@{fig_content (width=35, caption="In black") "figures/LatexLogoBlack.png"}
\<close>

text\<open>As you can clearly tell the placement seems a bit off. This is because each figure is placed at
the first available place to the right of the current content. We can resolve this by adding a \<^verbatim>\<open>hs\<open>2.5cm\<close>\<close>
macro command between our two \<^verbatim>\<open>fig_content\<close>, and a \<^verbatim>\<open>hs\<open>0.5cm\<close>\<close> before the first one and after the
 second one.\<close>

text*[example4::float,  main_caption="\<open>Latex logos\<close>"]
\<open>
\<^hs>\<open>0.5cm\<close>@{fig_content (width=35, caption="In white") "figures/LatexLogo.png"
}\<^hs>\<open>2.5cm\<close>@{fig_content (width=35, caption="In black") "figures/LatexLogoBlack.png"}\<^hs>\<open>0.5cm\<close>
\<close>
text\<open> Placing figures within a \<^isadof> document can be somewhat impredictable and needs some
experimenting to get the wanted result. @{float\<open>example4\<close>}\<close>

section*[hlinks::technical]\<open>Hyperlinks\<close>

text\<open>Hyperlinks let you add links to websites. The url antiquotation in \<^isadof> is written \<^verbatim>\<open>\<^url>\<close>.
Below is an example of creating a hyperlink towards the installation page of \<^isadof>.


\<^isarbox>\<open>\<^isatext>\<open>
 This is the link where you may install Isabelle/DOF :
\textbf{\textit{url}}<https://www.isa-afp.org/entries/Isabelle\_DOF.html>
\<close>\<close>
\<^outmat>\<open> This is the link where you may install Isabelle/DOF : \\
\url{https://www.isa-afp.org/entries/Isabelle_DOF.html}
\<close>
\<close>

section*[loc_target::technical]\<open>Annotated Text in a Locale\<close>

text\<open>
As with the standard \<^theory_text>\<open>text\<close> command, an annotated text element can be checked in the 
context of a locale or a class, by adding a target \<^theory_text>\<open>(in name)\<close> after the command: 
@{boxed_theory_text [display]
\<open>locale L = fixes c :: nat assumes c_pos: "c > 0"

text* (in L) [t1::technical] \<open>Fact @{thm c_pos} about @{term c}.\<close>
section* (in L) [s1] \<open>Properties of @{term c}\<close>\<close>}
The text, with its antiquotations, is checked in \<^theory_text>\<open>L\<close>: it may refer to the parameter
\<open>c\<close> and to the fact \<open>c_pos\<close>. The part in square brackets is not concerned by the target:
it is an annotation of the text, evaluated in the theory before the command, and the instance 
\<open>t1\<close> it creates is an ordinary global instance that can be referenced after the command, for 
example by \<^theory_text>\<open>@{technical \<open>t1\<close>}\<close>. Hence attribute values must not 
mention \<open>c\<close> or \<open>c_pos\<close>.

When you edit a document, \<^isadof> evaluates the attributes and checks the invariants of a new 
instance in parallel to the following commands. Type errors in the attributes are reported at once; 
errors of the evaluation and of the invariants also appear at the command that creates the instance,
but possibly with some delay. If you prefer to see them before the following commands are 
evaluated, switch the parallel evaluation off with
@{boxed_theory_text [display]\<open>declare[[invariants_parallel = false]]\<close>}
\<close>

section*[ref::technical]\<open>References\<close>
text\<open> References allow you to create pointers to certain figures and sections in your document
 allowing a quick access and good navigation in your PDF file.\<close>

paragraph\<open>Referencing backwards\<close>
text\<open>This is an easy way to add a reference to chapter, section or figure that has already occurred in
your document. 
@{boxed_theory_text[display]\<open>
subsection*[refexample1::technical]\<open>Reference Example 1\<close>
text\<open>We have just created a reference to the subsection  @{technical\<open>refexample1\<close>}, defined right above.\<close>
\<close>}
\<^outmat>\<open>
 \begin{isamarkupsubsection*}
[label = {CTWOUNDERSCOREBasicsDOTrefexample1},type = {scholarlyUNDERSCOREpaperDOTtechnical},
 args={label = {CTWOUNDERSCOREBasicsDOTrefexample1},type = {scholarlyUNDERSCOREpaperDOTtechnical},
 IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTreferentiable = {False},
 IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTvariants = {{STR ''outline'', STR ''document''}},
 scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTmainUNDERSCOREauthor = {}, scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTfixmeUNDERSCORElist = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTdefinitionUNDERSCORElist = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTstatus = {description}}]Reference Example 1
\end{isamarkupsubsection*}\isamarkuptrue%
\begin{isamarkuptext}
We have just created a reference to the subsection  {\isaDofDOTref[type={scholarlyUNDERSCOREpaperDOTtechnical}]     {CTWOUNDERSCOREBasicsDOTrefexample1}}, defined right above.
\end{isamarkuptext}\isamarkuptrue
\<close>\<close>

paragraph\<open>Referencing forwards\<close>
text\<open>Sometimes, however, one would like to add a future chapter or figure, this also possible to do
although a bit longer, by declaring a references to an object that does not yet exist. \<^isadof> will 
then ignore the fact that is does not know such an object, and will not produce an error. It is important 
to note that if a object is declared and used as a reference but never defined it will create a problem
at the very end of the building.
@{boxed_theory_text[display]\<open>
declare_reference*[refexample2::technical]
text\<open>We have just created a reference to the subsection  @{technical(unchecked)\<open>refexample2\<close>}, defined right beneath.\<close>
subsection*[refexample2::technical]\<open>Reference Example 2\<close>
\<close>}
\<^outmat>\<open>          
\isakeywordONE{declare{\isacharunderscore}{\kern0pt}reference{\isacharasterisk}{\kern0pt}}\isamarkupfalse%
{\isacharbrackleft}{\kern0pt}refexample{\isadigit{2}}{\isacharcolon}{\kern0pt}{\isacharcolon}{\kern0pt}technical{\isacharbrackright}{\kern0pt}
\begin{isamarkuptext}
We have just created a reference to the subsection  {\isaDofDOTref[type={scholarlyUNDERSCOREpaperDOTtechnical}]     {CTWOUNDERSCOREBasicsDOTrefexampleTWO}}, defined right beneath.
\end{isamarkuptext}\isamarkuptrue%

\begin{isamarkupsubsection*}
[label = {CTWOUNDERSCOREBasicsDOTrefexampleTWO},type = {scholarlyUNDERSCOREpaperDOTtechnical}, args={label = {CTWOUNDERSCOREBasicsDOTrefexampleTWO},type = {scholarlyUNDERSCOREpaperDOTtechnical}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTreferentiable = {False}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTvariants = {{STR ''outline'', STR ''document''}}, scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTmainUNDERSCOREauthor = {}, scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTfixmeUNDERSCORElist = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTdefinitionUNDERSCORElist = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTstatus = {description}}]Reference Example 2
\end{isamarkupsubsection*}\isamarkuptrue
\<close>
\<close>


section*[cit::technical]\<open>Citations and Bibliography\<close>
text\<open>Providing a bibliography, is vital to  writing accurate papers and reports. It allows people to
the sources as well as know where to go for more information on the subject, it is why \<^isadof> uses
\<^BibTeX>  (\<^url>\<open>https://www.bibtex.org/Using/\<close>) to generate its bibliography.
 
For this you need a 'root.bib' file that will be in the document directory of your paper. Here is an 
example, with the extract of the 'root.bib' file, of the code and the generated end result. 

\begin{config}{root.bib}
@Manual{	  brucker.ea:isabelledof:2026,
  title		= {The Isabelle/DOF User and Implementation Manual},
  author	= {Achim D. Brucker, Nicolas Méric and Burkhart Wolff},
  year		= 2026,
  url     = "www.isa-afp.org/browser_info/current/AFP/Isabelle_DOF/document.pdf"
}
\end{config}

\<^isarbox>\<open>\<^isatext>\<open>
 While writing this user manual,I often used the Implementation and Reference Manual
\textit{\textbf{cite}}<"brucker.ea:isabelledof:2026"> to check on how antiquotations are most often used.
\<close>\<close>
\<^outmat>\<open>
While writing this user manual, I often used the Implementation and \\
 Reference Manual \cite{brucker.ea:isabelledof:2026} to check how antiquotations are most often used.
\<close>
\<close>

section*[footnotes::technical]\<open>Footnotes\<close>
text\<open>Footnotes are often used in academic or technical papers to offer parenthetical or background
 information. In \<^isadof> the footnote antiquotation is written as \<^verbatim>\<open>\<^footnote>\<close>, it appears as the symbol $\P$ in
\<^ijedit>.
\<^isarbox>\<open>\<^isatext>\<open>
Footnotes could be considered references $\P$<You may notice that they appear in the same color, red, as
 references in our PDF>, as they also allow an easy navigation in our document between the footnote
 and it's original paragraph.
\<close>\<close>
\<^outmat>\<open>
Footnotes could be considered references \footnote{You may notice that they appear in the same color, red, as
 references in our PDF}, as in our document they also \\ allow an easy navigation between the footnote
 and it's original paragraph.
\<close>\<close>

section*[tables::technical]\<open>Tables\<close>
text\<open>Tables are written either as \<^emph>\<open>grid tables\<close> directly in the text, or, for layouts beyond 
their scope, in \<^LaTeX>. Grid tables are the preferred way: their cells are ordinary text, so
they may contain markup and antiquotations of \<^isadof> and Isabelle, they are checked while editing,
and they are highlighted and reported as the rest of the text.\<close>

subsection*[gridtbl::technical]\<open>Grid Tables\<close>
text\<open>A grid table is written with the antiquotation \<^verbatim>\<open>\<^gridtbl>\<open>\<dots>\<close>\<close> (or 
\<^verbatim>\<open>@{gridtbl \<open>\<dots>\<close>}\<close>) inside any \<^theory_text>\<open>text\<close> or \<^theory_text>\<open>text*\<close>. Its argument is drawn in ASCII-art, 
following the grid tables of reStructuredText: the borders are made of \<^verbatim>\<open>+\<close>, \<^verbatim>\<open>-\<close> and \<^verbatim>\<open>|\<close>, 
a border of \<^verbatim>\<open>=\<close> is typeset as a double ruler, and a cell is a rectangle closed by borders, 
so it can span several rows and columns. The columns of all lines must be aligned; otherwise an 
error is reported at the position of the problem. As extensions, a ruler may occur on any border 
(also the first and the last), a cell may contain cartouches \<^verbatim>\<open>\<open>\<dots>\<close>\<close> (analysed like any text; they 
may even contain a \<^verbatim>\<open>|\<close>), and the lines of a cell form one paragraph. Alignment is based on logical 
length, in which each symbol counts one; \<^verbatim>\<open>\<^bold>\<open>|\<close>\<close> may replace a \<^verbatim>\<open>|\<close>, \<^verbatim>\<open>\<^bold>\<open>---\<close>\<close> counts three. 
As in markdown, \<^verbatim>\<open>:---:\<close>, \<^verbatim>\<open>:---\<close> and \<^verbatim>\<open>---:\<close> in the border of a cell center, left-align and 
right-align its content.\<close>
text\<open>The first example has a head ruler and a column each of left, centered and right-aligned content:
\<^vs>\<open>0.5cm\<close>
@{boxed_grid [display]\<open>+:-------------+:----------:+-----------:+
| Class        | Checks     | Time (s)   |
+:=============+:==========:+===========:+
| figure       | 12         | 0.31       |
+:-------------+:----------:+-----------:+
| listing      | 3          | 0.05       |
+:-------------+:----------:+-----------:+
| technical    | 128        | 7.24       |
+:-------------+:----------:+-----------:+\<close>}

\<^vs>\<open>0.5cm\<close>
\<^noindent>  gives the output:
\<^vs>\<open>0.5cm\<close>

\<^outmat>\<open>
\<^gridtbl>\<open>
+:-------------+:----------:+-----------:+
\<^bold> Class        \<^bold> Checks     \<^bold> Time (s)   \<^bold>
+:=============+:==========:+===========:+
\<^bold> figure       \<^bold> 12         \<^bold> 0.31       \<^bold>
+:-------------+:----------:+-----------:+
\<^bold> listing      \<^bold> 3          \<^bold> 0.05       \<^bold>
+:-------------+:----------:+-----------:+
\<^bold> technical    \<^bold> 128        \<^bold> 7.24       \<^bold> 
+:-------------+:----------:+-----------:+
\<close>\<close>\<close>
text\<open>Cells can span rows and columns, and rulers can be placed everywhere:

@{boxed_grid [display]\<open>+-------+---------------+
|       | L2 and L3     |
| L1    +-------+-------+
|       | L2    | L3    |
+=======+=======+=======+
|       | B     | CCC   |
| AAA   +-------+-------+
|       |   DDDDD       |
+-------+-------+-------+
|               | FFF   |
|     EEEEE     +-------+
|               | GGG   |
+---------------+-------+\<close>}
\<^outmat>\<open>
\<^gridtbl>\<open>
+-------+---------------+
|       | L2 and L3     |
| L1    +-------+-------+
|       | L2    | L3    |
+=======+=======+=======+
|       | B     | CCC   |
| AAA   +-------+-------+
|       |   DDDDD       |
+-------+-------+-------+
|               | FFF   |
|     EEEEE     +-------+
|               | GGG   |
+---------------+-------+
\<close>\<close>\<close>

text*[example5::float,  main_caption="\<open>A Grid-Table Animated in Isabelle/PIDE\<close>"]
\<open>@{fig_content (width=95, caption="") "figures/GridTable-I.png"}\<close>

text\<open>Result:\<close>

text\<open>Cells can contain antiquotations. This is the table of the definitions of some
logical constants, that is, the data of a typical \<^LaTeX> table:

\<^outmat>\<open>
\<^gridtbl>\<open>
+----------------------------+---------------------+
| Name                       | Theorem             |
+============================+=====================+
| @{thm[source]HOL.True_def} | @{thm HOL.True_def} |
+----------------------------+---------------------+
| @{thm[source]HOL.All_def}  | @{thm HOL.All_def}  |
+----------------------------+---------------------+
| @{thm[source]HOL.Ex_def}   | @{thm HOL.Ex_def}   |
+----------------------------+---------------------+
| @{thm[source]HOL.not_def}  | @{thm HOL.not_def}  |
+----------------------------+---------------------+
\<close>\<close>\<close>


text\<open>The text of a cell may flow over several lines, and a multi-row cell is centered vertically:

@{boxed_grid [display]
\<open>+---------------+-----------------------+
| Phase         | Activity              |
+===============+=======================+
|               | \<open>@{term \<open>x\<close>}\<close>         |
| Verification  +-----------------------+
|               | \<open>\<^emph>\<open>proof\<close>\<close> and tests  |
+---------------+-----------------------+\<close>}
\<^outmat>\<open>
\<^gridtbl>\<open>
+---------------+-----------------------+
| Phase         | Activity              |
+===============+=======================+
|               | \<open>@{term \<open>x\<close>}\<close>         |
| Verification  +-----------------------+
|               | \<open>\<^emph>\<open>proof\<close>\<close> and tests  |
+---------------+-----------------------+
\<close>\<close>\<close>


subsection*[texopt::technical]\<open>\<^LaTeX> Typesetting as an Opt-out\<close>
text\<open>Tables with typographic requirements that go beyond grid tables have to be written in \<^LaTeX>, 
which is passed through unchanged (see \<^cite>\<open>"int:latextable:2020"\<close> for the many possibilities).
Typical examples are decimal alignment of numbers (package \<^verbatim>\<open>siunitx\<close>), partial rulers
(\<^verbatim>\<open>\cmidrule\<close> of \<^verbatim>\<open>booktabs\<close>), coloured rows (\<^verbatim>\<open>colortbl\<close>) or tables that break across pages. 
The following table needs all of these; it cannot be expressed as a grid table:
@{boxed_latex[display]\<open>\begin{tabular}{@{}l S[table-format=2.2] S[table-format=3.1] @{}}
\toprule
 & \multicolumn{2}{c}{Measured} \\
\cmidrule(l){2-3}
Ontology & {Time (s)} & {Speed-up} \\
\midrule
CENELEC\_50128 & 12.40 & 105.0 \\
\rowcolor{gray!15} technical\_report & 3.17 & 98.5 \\
\bottomrule
\end{tabular}\<close>}
\<^outmat>\<open>
\<^vs>\<open>0.3cm\<close>
\<^latex>\<open>
\begin{tabular}{@{}l S[table-format=2.2] S[table-format=3.1] @{}}
\toprule
 & \multicolumn{2}{c}{Measured} \\
\cmidrule(l){2-3}
Ontology & {Time (s)} & {Speed-up} \\
\midrule
CENELEC\_50128 & 12.40 & 105.0 \\
\rowcolor{gray!15} technical\_report & 3.17 & 98.5 \\
\bottomrule
\end{tabular}\<close>
\<close>
The cells of such a table are opaque to \<^isadof> (no checking of their content, and no
antiquotations unless \<^LaTeX> expands them itself), and the packages used have to be loaded in
the preamble of the document (here: \<^verbatim>\<open>booktabs\<close>, \<^verbatim>\<open>siunitx\<close> and \<^verbatim>\<open>colortbl\<close>). Whenever possible,
prefer a grid table.\<close>
section*[railroads::technical]\<open>Railroad Diagrams\<close>
text\<open>
Syntax diagrams, also called railroad diagrams, are the standard way to explain the syntax of a 
language to a reader: a path through the diagram, from left to right, is a legal phrase. They 
are used for the commands of Isabelle and of \<^isadof>, and you can use them in your own documents,
for example to describe a small input language, a file format or the commands of a tool. 
The diagrams are not drawn by hand: you write their grammar as text, with the antiquotation 
\<^verbatim>\<open>\<^rail>\<close>, and \<^isadof> (more precisely, Isabelle) typesets it with \<^LaTeX>.
\<close>

paragraph\<open>The key elements\<close>
text\<open>
A diagram is described by one or several \<^emph>\<open>rules\<close> of the form \<^verbatim>\<open>name: body\<close>, which are 
separated by semicolons (a single anonymous body is also possible). The body is written with a 
small number of elements:
\<^item> a \<^emph>\<open>terminal\<close> is written in single quotes, \<^eg>, \<^verbatim>\<open>'text*'\<close>; with a leading \<^verbatim>\<open>@\<close>, it is shown as 
  a keyword;
\<^item> a \<^emph>\<open>nonterminal\<close> is a plain identifier, \<^eg>, \<^verbatim>\<open>class_id\<close>; if a rule of this name exists, it is the 
  start of another diagram;
\<^item> elements written one after the other form a sequence, alternatives are separated by \<^verbatim>\<open>|\<close>, and 
  parentheses group;
\<^item> a postfix \<^verbatim>\<open>?\<close> makes an element optional, \<^verbatim>\<open>*\<close> repeats it zero or more times, and \<^verbatim>\<open>+\<close> one or more 
  times; an element after the repetition operator, as in \<^verbatim>\<open>attribute * ','\<close>, is the separator
  between the repetitions;
\<^item> \<^verbatim>\<open>\<newline>\<close> starts a new line in the middle of a long sequence.
\<close>

paragraph\<open>An example\<close>
text\<open>
The following rules describe how a document element with attributes is written: the commands 
\<^verbatim>\<open>text*\<close> and \<^verbatim>\<open>section*\<close> are followed by an object name, a class and an optional, comma-separated 
list of attributes in square brackets, and the text.
@{boxed_theory_text [display]\<open>
\<^rail>\<open>
  element: ( @'text*' | @'section*' ) '[' oid '::' class_id attributes ? ']' \<newline> text
  ;
  attributes: ',' attribute + ','
  ;
  attribute: name '=' value
\<close>\<close>}
\<^outmat>\<open>
\<^rail>\<open>
  element: ( @'text*' | @'section*' ) '[' oid '::' class_id attributes ? ']' \<newline> text
  ;
  attributes: ',' attribute + ','
  ;
  attribute: name '=' value
\<close>\<close>
Each rule yields one diagram: the first shows the choice between the two commands, the optional 
attribute list, and the continuation on a second line; the other two show the list with its 
separator and an attribute. 
\<close>

paragraph\<open>Further reading\<close>
text\<open>
The \<^verbatim>\<open>\<^rail>\<close> antiquotation has more features, for example to refer to the syntax categories of
Isabelle or to commands by name. They are described in the section ``Railroad diagrams'' of the 
chapter on document preparation in the Isabelle/Isar Reference Manual \<^cite>\<open>"mwenzel:isaref:2025"\<close>, 
which is the reference for further reading.
\<close>
(*<*)
end
(*>*)